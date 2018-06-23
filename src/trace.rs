//! Record sequences of rewrites.

use rand::{distributions::{Distribution, Uniform},
           Rng};
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::f64;
use std::sync::{Arc, RwLock, Weak};

use {Term, TRS};

pub struct Trace<'a> {
    trs: &'a TRS,
    root: TraceNode,
    unobserved: BinaryHeap<TraceNode>,
    p_observe: f64,
    max_term_size: Option<usize>,
}
impl<'a> Trace<'a> {
    /// Create a trace initialized with `term` undergoing rewrites in `trs`. Every step for a node
    /// in the trace multiplies the node's probability score by `p_observe`.
    pub fn new(
        trs: &'a TRS,
        term: &Term,
        p_observe: f64,
        max_term_size: Option<usize>,
    ) -> Trace<'a> {
        let root = TraceNode::new(term.clone(), TraceState::Start, 0.0, 0, None, vec![]);
        let mut unobserved = BinaryHeap::new();
        unobserved.push(root.clone());
        Trace {
            trs,
            root,
            unobserved,
            p_observe,
            max_term_size,
        }
    }
    fn new_node(
        &mut self,
        term: Term,
        parent: Option<&TraceNode>,
        state: TraceState,
        log_p: f64,
    ) -> TraceNode {
        let depth = if let Some(ref n) = parent {
            n.depth() + 1
        } else {
            0
        };
        let node = TraceNode::new(term, state, log_p, depth, parent, vec![]);
        self.unobserved.push(node.clone());
        node
    }
    /// The initial node of the `Trace`.
    pub fn root(&self) -> &TraceNode {
        &self.root
    }
    /// The length of the longest chain of evaluation steps.
    pub fn depth(&self) -> usize {
        let mut deepest = 0;
        self.root.walk(|n| {
            deepest = deepest.max(n.depth());
        });
        deepest
    }
    /// The total count of nodes maintained by the `Trace`.
    pub fn size(&self) -> usize {
        let mut count = 0;
        self.root.walk(|_| count += 1);
        count
    }
    /// The probability mass that has been explored by the Trace.
    pub fn mass(&self) -> f64 {
        // the mass is 1 - the mass in unobserved leaves
        let mut masses = self.root.accumulate(|n| {
            if [TraceState::Start, TraceState::Unobserved].contains(&n.state()) && n.is_leaf() {
                Some(n.log_p())
            } else {
                None
            }
        });
        masses.push(f64::NEG_INFINITY);
        1.0 - logsumexp(masses.as_slice()).exp()
    }
    /// Sample a possible outcome in proportion to its probability.
    pub fn sample<R: Rng>(&self, rng: &mut R) -> TraceNode {
        let leaves = self.root.leaves(&[TraceState::Normal]);
        let ws = leaves.iter().map(|x| x.log_p().exp()).collect::<Vec<f64>>();
        weighted_sample(rng, &leaves, &ws).clone()
    }
    /// Attempt to record rewrites on the highest-scoring unobserved node.
    pub fn step(&mut self) -> Option<TraceNode> {
        if let Some(node) = self.unobserved.pop() {
            // scope in for write access to node
            {
                let mut node_w = node.0.write().expect("poisoned TraceNode");
                if let Some(max_term_size) = self.max_term_size {
                    if node_w.term.size() > max_term_size {
                        node_w.state = TraceState::TooBig;
                        return None;
                    }
                }
                match self.trs.rewrite(&node_w.term) {
                    Some(ref rewrites) if !rewrites.is_empty() => {
                        let term_selection_p = -(rewrites.len() as f64).ln();
                        for term in rewrites {
                            let new_p =
                                node_w.log_p + (1.0 - self.p_observe).ln() - term_selection_p;
                            let new_node = self.new_node(
                                term.clone(),
                                Some(&node),
                                TraceState::Unobserved,
                                new_p,
                            );
                            node_w.children.push(new_node);
                        }
                        node_w.log_p += self.p_observe.ln()
                    }
                    _ => node_w.state = TraceState::Normal,
                }
            }
            Some(node)
        } else {
            None
        }
    }
    /// Run the `Trace` until a fruitful step is reached.
    pub fn run(&mut self, mut max_steps: usize) {
        while let None = self.step() {
            max_steps -= 1;
            if max_steps == 0 {
                break;
            }
        }
    }
    /// Run the `Trace` until a fruitful step is reached and return the leaf terms.
    pub fn rewrite(&mut self, max_steps: usize, states: &[TraceState]) -> Vec<Term> {
        self.run(max_steps);
        self.root.leaf_terms(states)
    }
    /// An estimate of the probability that `self` rewrite to `term`.
    pub fn rewrites_to(&mut self, max_steps: usize, term: &Term) -> f64 {
        // NOTE: we only use tree equality and don't consider tree edit distance
        self.run(max_steps);
        let lps = self.root.accumulate(|n| {
            let n_r = &n.0.read().expect("poisoned TraceNode");
            Term::alpha(term, &n_r.term).map(|_| n_r.log_p)
        });
        if lps.is_empty() {
            f64::NEG_INFINITY
        } else {
            logsumexp(&lps)
        }
    }
}

/// A single node in a Trace.
#[derive(Debug, Clone)]
struct TraceNodeStore {
    term: Term,
    state: TraceState,
    log_p: f64,
    depth: usize,
    parent: Option<Weak<RwLock<TraceNodeStore>>>,
    children: Vec<TraceNode>,
}

/// The state of a Node in a Trace
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TraceState {
    Start,
    Normal,
    Unobserved,
    TooBig,
}

#[derive(Debug, Clone)]
pub struct TraceNode(Arc<RwLock<TraceNodeStore>>);
impl TraceNode {
    fn new(
        term: Term,
        state: TraceState,
        log_p: f64,
        depth: usize,
        parent: Option<&TraceNode>,
        children: Vec<TraceNode>,
    ) -> TraceNode {
        let parent = parent.map(|n| Arc::downgrade(&n.0));
        TraceNode(Arc::new(RwLock::new(TraceNodeStore {
            term,
            state,
            log_p,
            depth,
            parent,
            children,
        })))
    }
    pub fn state(&self) -> TraceState {
        self.0.read().expect("poisoned TraceNode").state
    }
    pub fn term(&self) -> Term {
        self.0.read().expect("poisoned TraceNode").term.clone()
    }
    pub fn log_p(&self) -> f64 {
        self.0.read().expect("poisoned TraceNode").log_p
    }
    pub fn depth(&self) -> usize {
        self.0.read().expect("poisoned TraceNode").depth
    }
    pub fn parent(&self) -> Option<TraceNode> {
        self.0
            .read()
            .expect("poisoned TraceNode")
            .parent
            .as_ref()
            .and_then(|w| w.upgrade())
            .map(TraceNode)
    }
    pub fn children(&self) -> Vec<TraceNode> {
        self.0.read().expect("poisoned TraceNode").children.clone()
    }
    pub fn is_leaf(&self) -> bool {
        self.0
            .read()
            .expect("poisoned TraceNode")
            .children
            .is_empty()
    }

    fn accumulate<T, F>(&self, condition: F) -> Vec<T>
    where
        F: Fn(&TraceNode) -> Option<T>,
    {
        let mut values = Vec::new();
        self.walk(|n| {
            if let Some(v) = condition(n) {
                values.push(v)
            }
        });
        values
    }
    fn walk<F>(&self, mut callback: F)
    where
        F: FnMut(&TraceNode),
    {
        self.walk_helper(&mut callback)
    }
    fn walk_helper<F>(&self, callback: &mut F)
    where
        F: FnMut(&TraceNode),
    {
        callback(self);
        for child in &self.0.read().expect("poisoned TraceNode").children {
            child.walk_helper(callback)
        }
    }

    /// All the nodes descending from this node.
    pub fn progeny(&self, states: &[TraceState]) -> Vec<TraceNode> {
        self.accumulate(|n| {
            if states.contains(&n.state()) {
                Some(n.clone())
            } else {
                None
            }
        })
    }
    /// All the leaf nodes that descend from this node.
    pub fn leaves(&self, states: &[TraceState]) -> Vec<TraceNode> {
        self.accumulate(|n| {
            if states.contains(&n.state()) && n.is_leaf() {
                Some(n.clone())
            } else {
                None
            }
        })
    }
    /// Like `leaves`, but returns `Term`s instead of `TraceNodes`s.
    pub fn leaf_terms(&self, states: &[TraceState]) -> Vec<Term> {
        self.accumulate(|n| {
            if states.contains(&n.state()) && n.is_leaf() {
                Some(n.term())
            } else {
                None
            }
        })
    }
}
impl PartialEq for TraceNode {
    fn eq(&self, other: &TraceNode) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for TraceNode {}
impl PartialOrd for TraceNode {
    fn partial_cmp(&self, other: &TraceNode) -> Option<Ordering> {
        self.log_p().partial_cmp(&other.log_p())
    }
}
impl Ord for TraceNode {
    fn cmp(&self, other: &TraceNode) -> Ordering {
        if let Some(x) = self.partial_cmp(&other) {
            x
        } else {
            Ordering::Equal
        }
    }
}

#[inline(always)]
fn logsumexp(lps: &[f64]) -> f64 {
    let largest = lps.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    let x = lps.iter().map(|lp| (lp - largest).exp()).sum::<f64>().ln();
    largest + x
}

/// Samples an item from `xs` given the weights `ws`.
fn weighted_sample<'a, T, R: Rng>(rng: &mut R, xs: &'a [T], ws: &[f64]) -> &'a T {
    assert_eq!(xs.len(), ws.len(), "weighted sample given invalid inputs");
    let total = ws.iter().fold(0f64, |acc, x| acc + x);
    let threshold: f64 = Uniform::new(0f64, total).sample(rng);
    let mut cum = 0f64;
    for (wp, x) in ws.into_iter().zip(xs) {
        cum += *wp;
        if threshold <= cum {
            return x;
        }
    }
    unreachable!()
}
