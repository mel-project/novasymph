use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    sync::Arc,
};

use lru::LruCache;
use novasmt::ContentAddrStore;
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};

use stdcode::StdcodeSerializeExt;
use tap::TapOptional;
use themelio_stf::SealedState;
use themelio_structs::{Block, BlockHeight};
use thiserror::Error;
use tmelcrypt::Hashable;
use tmelcrypt::{Ed25519PK, Ed25519SK, HashVal};

use crate::msg::{ProposalSig, VoteSig};

/// A mapping from proposal block hash to hash of serialized signatures
pub type Summary = BTreeMap<HashVal, HashVal>;

pub struct BlockGraph<C: ContentAddrStore> {
    /// Latest sealed state
    root: SealedState<C>,
    /// Mapping from a block hash to the hashes of blocks that reference it
    parent_to_child: BTreeMap<HashVal, BTreeSet<HashVal>>,
    /// Mapping of block proposals by their hashes
    proposals: BTreeMap<HashVal, Proposal>,
    /// Mapping of pub-key with signature to a block hash that it is voting for
    votes: BTreeMap<HashVal, BTreeMap<Ed25519PK, VoteSig>>,
    /// Mapping of voting power (amount staked / total staked) by public key
    vote_weights: BTreeMap<Ed25519PK, f64>,
    /// A function to get the block proposer's public key for a given block height (consensus round)
    correct_proposer: Box<dyn Fn(BlockHeight) -> Ed25519PK + Send + Sync + 'static>,

    /// A state cache
    state_cache: Mutex<LruCache<HashVal, SealedState<C>>>,

    /// Last drained
    last_drained: BlockHeight,
}

impl<C: ContentAddrStore> BlockGraph<C> {
    pub fn new(root: SealedState<C>, vote_weights: BTreeMap<Ed25519PK, f64>) -> Self {
        // Add root to the parent->child map for a blockgraph
        let mut parent_to_child = BTreeMap::new();
        parent_to_child.insert(root.header().hash(), BTreeSet::new());

        let correct_proposer = Box::new(crate::protocol::gen_get_proposer(root.clone()));
        let last_drained = root.inner_ref().height;

        BlockGraph {
            root,
            parent_to_child,
            proposals: BTreeMap::new(),
            votes: BTreeMap::new(),
            state_cache: LruCache::new(100).into(),
            vote_weights,
            correct_proposer,
            last_drained,
        }
    }

    /// Returns the root.
    pub fn root(&self) -> SealedState<C> {
        self.root.clone()
    }

    /// Returns whether a node has the right number of votes.
    fn is_notarized(&self, hash: HashVal) -> bool {
        if let Some(votes) = self.votes.get(&hash) {
            let total_voting_for: f64 = votes.keys().map(|k| self.vote_weights[k]).sum();
            //let total_stake: u128 = self.vote_weights.values().copied().sum();
            //total_voting_for > (total_stake * 2).div_ceil(&3)
            // log::debug!("{} voting for {}", total_voting_for, hash);
            total_voting_for > 0.667 //2.div_ceil(&3)
        } else {
            // Root is notarized by default
            self.root.header().hash() == hash
        }
    }

    /// Votes for all the proposals that deserve our votes
    pub fn vote_all(&mut self, voter_key: Ed25519SK) {
        // Get the lnc tips and vote for them
        let lnc_tips = self.lnc_tips();
        let mut stack = lnc_tips
            .iter()
            .chain(vec![self.root.header().hash()].iter())
            .flat_map(|tip| {
                self.parent_to_child
                    .get(tip)
                    .unwrap_or(&BTreeSet::new())
                    .clone()
            })
            .collect::<Vec<HashVal>>();

        // Vote for all the descendants of LNC tips
        while let Some(prop) = stack.pop() {
            let votes = self.votes.entry(prop).or_default();

            // Add a vote if its not already there
            if let Entry::Vacant(e) = votes.entry(voter_key.to_public()) {
                let header_hash = self
                    .proposals
                    .get(&prop)
                    .expect("Votes entry is not in proposals of blockgraph")
                    .block
                    .header
                    .hash();

                // Insert vote for prop
                e.insert(VoteSig::generate(voter_key, header_hash));
            }

            // Add prop children to stack as well
            stack.extend(
                self.parent_to_child
                    .get(&prop)
                    .unwrap_or(&BTreeSet::new())
                    .clone(),
            );
        }
    }

    // Get the [SealedState] of blocks applied on the canonical longest notarized chain in the blockgraph
    pub fn lnc_state(&self) -> Option<SealedState<C>> {
        self.lnc_tips()
            .into_iter()
            .min()
            .and_then(|lowest_lnc_hash| self.get_state(lowest_lnc_hash))
    }

    /// Gets the state at a given hash
    fn get_state(&self, hash: HashVal) -> Option<SealedState<C>> {
        if hash == self.root.header().hash() {
            Some(self.root.clone())
        } else {
            let prop = self.proposals.get(&hash).cloned()?;
            if let Some(v) = self
                .state_cache
                .try_lock()
                .and_then(|mut c| c.get(&hash).cloned())
            {
                Some(v)
            } else {
                let mut previous = self
                    .get_state(prop.extends_from)
                    .expect("dangling pointer within block graph");
                while previous.inner_ref().height + BlockHeight(1) < prop.block.header.height {
                    eprintln!("building {}", previous.inner_ref().height);
                    previous = previous.next_state().seal(None);
                }
                let res = previous
                    .apply_block(&prop.block)
                    .expect("invalid blocks inside the block graph");
                self.state_cache
                    .try_lock()
                    .map(|mut c| c.put(hash, res.clone()));
                Some(res)
            }
        }
    }

    /// Get a vote weight
    pub fn vote_weight(&self, pk: Ed25519PK) -> f64 {
        self.vote_weights.get(&pk).copied().unwrap_or_default()
    }

    /// Sets a new root and removes all proposals/votes which are not descendants of the new root
    pub fn update_root(&mut self, root: SealedState<C>) {
        if self.root.header() == root.header() {
            return;
        }
        log::debug!("pre-reset graphviz: {}", self.graphviz());
        log::debug!(
            "updating root to {} at height {}",
            root.header().hash(),
            root.inner_ref().height
        );
        self.root = root;

        // Remove all non-descendants of root
        let mut root_and_descendants = BTreeSet::new();

        let mut stack = vec![self.root().header().hash()];

        // Build a set of root's descendants
        while let Some(child) = stack.pop() {
            root_and_descendants.insert(child);

            stack.extend(self.parent_to_child.get(&child).unwrap_or(&BTreeSet::new()));
        }

        // Retain only the reoots and descendants
        self.parent_to_child = self
            .parent_to_child
            .iter()
            .filter(|(hash, _)| root_and_descendants.contains(hash))
            .map(|(hash, val)| (*hash, val.clone()))
            .collect::<BTreeMap<_, _>>();

        self.proposals = self
            .proposals
            .iter()
            .filter(|(hash, _)| {
                root_and_descendants.contains(hash) && **hash != self.root.header().hash()
            })
            .map(|(hash, val)| (*hash, val.clone()))
            .collect::<BTreeMap<_, _>>();

        self.votes = self
            .votes
            .iter()
            .filter(|(hash, _)| {
                root_and_descendants.contains(hash) && **hash != self.root.header().hash()
            })
            .map(|(hash, val)| (*hash, val.clone()))
            .collect::<BTreeMap<_, _>>();
        log::debug!("post-reset graphviz: {}", self.graphviz());
    }

    fn chain_weight(&self, mut tip: HashVal) -> u64 {
        let mut weight = 0;
        while let Some(parent) = self.proposals.get(&tip).map(|prop| prop.extends_from) {
            tip = parent;
            weight += 1;
        }
        weight
    }

    /// Get all blocks (proposals or the root) which do not have children
    fn tips(&self) -> BTreeSet<HashVal> {
        self.proposals
            .keys()
            .cloned()
            .chain(vec![self.root.header().hash()])
            .filter(|hash| {
                self.parent_to_child
                    .get(hash)
                    .map(|children| children.is_empty())
                    .unwrap_or(true)
            })
            .collect()
    }

    /// Get the tips of the longest chains of fully notarized blocks.
    /// An lnc block tip may have children which are not notarized.
    #[allow(clippy::needless_collect)]
    pub fn lnc_tips(&self) -> BTreeSet<HashVal> {
        let tips = self.tips();
        let tips = tips
            .iter()
            .cloned()
            .map(|mut tip| {
                while !self.is_notarized(tip) {
                    tip = self
                        .proposals
                        .get(&tip)
                        .tap_none(|| log::error!("bad! graphviz {}", self.graphviz()))
                        .expect("Expected to find provided tip in blockgraph proposals")
                        .extends_from;
                }
                tip
            })
            .collect::<Vec<HashVal>>();

        let opt_max = tips
            .iter()
            .map(|block_hash| self.chain_weight(*block_hash))
            .max();

        // Return max notarized chain weight tips
        if let Some(max_weight) = opt_max {
            tips.into_iter()
                .filter(|tip| self.chain_weight(*tip) == max_weight)
                .collect::<BTreeSet<_>>()
        } else {
            // Notarized tips is empty, so lnc tips is empty
            BTreeSet::new()
        }
    }

    /// Drains out finalized blocks.
    pub fn drain_finalized(&mut self) -> Vec<SealedState<C>> {
        // DFS through the whole thing, keeping track of how many consecutively increasing notarized blocks we see
        let mut dfs_stack: Vec<(HashVal, BlockHeight, usize)> =
            vec![(self.root.header().hash(), self.root.inner_ref().height, 1)];
        while let Some((fringe_node, height, consec)) = dfs_stack.pop() {
            if consec >= 3 && height > self.last_drained + BlockHeight(1) {
                log::debug!("*** drain candidate {}", height);
                // Get the block that the 3rd consecutive extends from
                // Get all blocks from this "finalized tip" to the root
                // This list of blocks are all finalized
                let finalized_tip = self.proposals[&fringe_node].extends_from;
                let mut finalized_props = vec![self.proposals[&finalized_tip].clone()];
                while let Some(previous) = finalized_props
                    .last()
                    .and_then(|b| self.proposals.get(&b.extends_from))
                    .cloned()
                {
                    finalized_props.push(previous);
                }
                // log::debug!("got {} finalized proposals: {:?}",
                //     finalized_props.len(),
                //     finalized_props.iter().map(|p| p.block.header.hash()).collect::<Vec<_>>());
                finalized_props.reverse();
                let mut accum: Vec<SealedState<C>> = vec![];
                for prop in finalized_props {
                    // Apply empty blocks to fill the distance between prop and previous block in accum
                    while accum.last().unwrap_or(&self.root).header().hash()
                        != prop.block.header.previous
                    {
                        accum.push(accum.last().unwrap_or(&self.root).next_state().seal(None));
                    }
                    // Apply prop to last block in accum to get the next sealed state
                    accum.push(
                        accum
                            .last()
                            .cloned()
                            .unwrap_or_else(|| self.root.clone())
                            .apply_block(&prop.block)
                            .map_err(|e| {
                                log::error!("{e}");
                                e
                            })
                            .expect("finalized some bad blocks"),
                    );
                }
                accum.retain(|a| a.inner_ref().height > self.last_drained);
                if let Some(val) = accum.iter().map(|a| a.inner_ref().height).max() {
                    self.last_drained = val;
                }
                return accum;
            }
            //println!("Searching {:?} for {fringe_node}", self.parent_to_child);
            for child_hash in self
                .parent_to_child
                .get(&fringe_node)
                .cloned()
                .unwrap_or_default()
                .iter()
                .copied()
            {
                let child = self.proposals[&child_hash].clone();
                let child_height = child.block.header.height;
                if self.is_notarized(child_hash) {
                    if child_height == height + BlockHeight(1) {
                        dfs_stack.push((child_hash, child_height, consec + 1))
                    } else {
                        dfs_stack.push((child_hash, child_height, 1))
                    }
                }
            }
        }
        vec![]
    }

    /// Inserts a proposal to the block graph. If it fails, returns exactly why the proposal failed.
    pub fn insert_proposal(&mut self, prop: Proposal) -> Result<(), ProposalRejection> {
        if self.proposals.contains_key(&prop.block.header.hash()) {
            log::warn!("duplicate proposal skipped");
            return Ok(());
        }
        if prop.proposer != (self.correct_proposer)(prop.block.header.height) {
            return Err(ProposalRejection::WrongTurn);
        }

        if !prop
            .signature
            .verify(prop.proposer, &prop.block.abbreviate())
        {
            return Err(ProposalRejection::BadSignature);
        }

        let mut previous = match self.get_state(prop.extends_from) {
            Some(s) => s,
            None => return Err(ProposalRejection::NoPrevious(prop.extends_from)),
        };
        if previous.inner_ref().height >= prop.block.header.height {
            return Err(ProposalRejection::InvalidBlock(anyhow::anyhow!(
                "previous block at the same or higher height"
            )));
        }
        while previous.inner_ref().height + BlockHeight(1) < prop.block.header.height {
            previous = previous.next_state().seal(None);
        }
        if let Err(err) = previous.apply_block(&prop.block) {
            return Err(ProposalRejection::InvalidBlock(err.into()));
        }

        // Add to blockgraph
        let header_hash = prop.block.header.hash();
        self.parent_to_child
            .entry(prop.extends_from)
            .or_default()
            .insert(header_hash);
        assert!(self
            .parent_to_child
            .insert(header_hash, BTreeSet::new())
            .is_none());
        self.proposals.insert(header_hash, prop);

        log::debug!("post-insert graphviz: {}", self.graphviz());

        // TODO check for turn info
        Ok(())
    }

    /// Insert a vote to the block graph.
    pub fn insert_vote(&mut self, vote_for: HashVal, voter: Ed25519PK, vote: VoteSig) {
        if vote.verify(voter, vote_for) && self.proposals.contains_key(&vote_for) {
            log::debug!(
                "inserting vote for {}.. at height {}",
                &vote_for.to_string()[..10],
                self.proposals[&vote_for].block.header.height
            );
            log::debug!("lnc tips are now {:?}", self.lnc_tips());
            let votes = self.votes.entry(vote_for).or_default();
            votes.insert(voter, vote);
            log::debug!("gathered {} votes", votes.len());
        }
    }

    /// Merge a vector of [BlockGraphDiff]s into the [BlockGraph], consuming and returning the
    /// final form.
    pub fn merge_diff(&mut self, diffs: Vec<BlockGraphDiff>) {
        for d in diffs.into_iter() {
            match d {
                BlockGraphDiff::Proposal(prop) => {
                    if let Err(err) = self.insert_proposal(prop) {
                        log::warn!("skipping proposal from diff due to {:?}", err);
                    }
                }
                BlockGraphDiff::Vote(hash, pk, sig) => {
                    self.insert_vote(hash, pk, sig);
                }
            }
        }
    }

    /// Create a summary of this block graph to compare with somebody else's block graph.
    pub fn summarize(&self) -> Summary {
        self.proposals
            .iter()
            .map(|(k, _)| {
                let other = self
                    .votes
                    .get(k)
                    .cloned()
                    .unwrap_or_default()
                    .stdcode()
                    .hash();
                (*k, other)
            })
            .collect()
    }

    /// Create a PARTIAL diff between this block graph and the given summary
    pub fn partial_summary_diff(&self, their_summary: &Summary) -> Vec<BlockGraphDiff> {
        // Votes on blocks they have are more important,
        // so we accumulate all blocks for which they have a different set of votes than us.
        let mut toret = Vec::new();
        for (k, v) in their_summary.iter() {
            if let Some(our_votes) = self.votes.get(k) {
                if our_votes.stdcode().hash() != *v {
                    for (pk, vote) in our_votes {
                        toret.push(BlockGraphDiff::Vote(*k, *pk, vote.clone()));
                    }
                }
            }
        }
        // return early now if we got differences in votes
        if !toret.is_empty() {
            return toret;
        }
        // find proposals that
        // 1. they don't have
        // 2. would be accepted by them because they extend from things that they do have
        for (hash, prop) in self.proposals.iter() {
            if !their_summary.contains_key(hash)
                // The summary contains the direct predecessor block we want to share, or the
                // predecessor is the blockgraph root (meaning its finalized and implicit)
                && (their_summary.contains_key(&prop.extends_from)
                    || prop.extends_from == self.root.header().hash())
            {
                toret.push(BlockGraphDiff::Proposal(prop.clone()));
                break;
            }
        }
        //log::debug!("generated diff\n{toret:?} from summary\n{their_summary:?} and internal {:?}", self.proposals);
        toret
    }

    /// Create the graphviz representation of the blockgraph
    pub fn graphviz(&self) -> String {
        let mut accum = "digraph G {\n".to_string();
        for (k, v) in self.parent_to_child.iter() {
            for v in v.iter() {
                accum.push_str(&format!("\"{}\" -> \"{}\"\n", k, v));
            }
        }
        for (k, v) in self.proposals.iter() {
            accum.push_str(&format!(
                "\"{}\" -> \"{}\" [constraint=false]\n",
                k, v.extends_from
            ));
            accum.push_str(&format!(
                "\"{}\" [label={}, shape=rect]\n",
                k,
                if self.is_notarized(*k) {
                    format!("\"[{}]\"", v.block.header.height)
                } else {
                    v.block.header.height.to_string()
                },
            ))
        }
        accum.push_str(&format!(
            "\"{}\" [label=ROOT, shape=rect]\n",
            self.root.header().hash(),
        ));
        accum.push_str("}\n");
        accum
    }
}

/// A diff
#[derive(Serialize, Deserialize, Debug)]
pub enum BlockGraphDiff {
    Proposal(Proposal),
    Vote(HashVal, Ed25519PK, VoteSig),
}

/// Why a proposal might be rejected.
#[derive(Error, Debug)]
pub enum ProposalRejection {
    #[error("proposer proposed when it's not their turn")]
    WrongTurn,
    #[error("invalid block ({0:?})")]
    InvalidBlock(anyhow::Error),
    #[error("missing extends_from")]
    NoPrevious(HashVal),
    #[error("bad signature")]
    BadSignature,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Proposal {
    pub extends_from: HashVal,
    pub block: Arc<Block>,
    pub proposer: Ed25519PK,
    pub signature: ProposalSig,
}
