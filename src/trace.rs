//! Record sequences of rewrites.
//!
//! # Examples
//!
//! A TRS with mutually exclusive rules gives a straightfoward linear record of
//! rewrites:
//!
//! ```
//! use term_rewriting::{parse, trace::Trace, Signature, Strategy};
//!
//! let mut sig = Signature::default();
//! let inp = "
//!     PLUS(SUCC(x_) y_) = PLUS(x_ SUCC(y_));
//!     PLUS(ZERO x_) = x_;
//!
//!     PLUS(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO));"
//!     .trim();
//! let (trs, mut terms) = parse(&mut sig, inp).unwrap();
//! let mut term = terms.pop().unwrap();
//! let mut trace = Trace::new(&trs, &sig, &term, 0.5, None, None, Strategy::Normal);
//!
//! let expected = vec!["PLUS(3, 1)", "PLUS(2, 2)", "PLUS(1, 3)", "PLUS(0, 4)", "4"];
//! let got = trace
//!     .by_ref()
//!     .take(5)
//!     .map(|n| n.term().pretty(&sig))
//!     .collect::<Vec<_>>();
//! assert_eq!(got, expected);
//! assert!(trace.next().is_none());
//! ```

use rand::{
    distributions::{Distribution, Uniform},
    Rng,
};
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::f64;
use std::fmt;
use std::sync::{Arc, RwLock, Weak};

use super::{Signature, Strategy, Term, TRS};

/// A `Trace` provides first-class control over [`Term`] rewriting.
///
/// It gives access to each evaluation step which has already occurred or could immediately descend
/// from a previously occurring step and provides tools for introducing new evaluation steps.
///
/// Each evaluation step from a source term gets yielded via the [`Iterator` implementation].
///
/// [`Term`]: ../enum.Term.html
/// [`Iterator` implementation]: #impl-Iterator
pub struct Trace<'a> {
    trs: &'a TRS,
    sig: &'a Signature,
    root: TraceNode,
    unobserved: BinaryHeap<TraceNode>,
    p_observe: f64,
    max_term_size: Option<usize>,
    max_depth: Option<usize>,
    strategy: Strategy,
}
impl<'a> Trace<'a> {
    /// Create a trace initialized with `term` undergoing rewrites in `trs`. Every step for a node
    /// in the trace multiplies the node's probability score by `p_observe`.
    pub fn new(
        trs: &'a TRS,
        sig: &'a Signature,
        term: &Term,
        p_observe: f64,
        max_term_size: Option<usize>,
        max_depth: Option<usize>,
        strategy: Strategy,
    ) -> Trace<'a> {
        let root = TraceNode::new(term.clone(), TraceState::Unobserved, 0.0, 0, None, vec![]);
        let mut unobserved = BinaryHeap::new();
        unobserved.push(root.clone());
        Trace {
            trs,
            sig,
            root,
            unobserved,
            p_observe,
            max_term_size,
            max_depth,
            strategy,
        }
    }
    fn new_node(
        &mut self,
        term: Term,
        parent: Option<&TraceNode>,
        depth: usize,
        state: TraceState,
        log_p: f64,
    ) -> TraceNode {
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
            if [TraceState::Unobserved].contains(&n.state()) && n.is_leaf() {
                Some(n.log_p())
            } else {
                None
            }
        });
        masses.push(f64::NEG_INFINITY);
        1.0 - logsumexp(masses.as_slice()).exp()
    }
    /// Give all possible outcomes within `max_steps` of evaluation.
    pub fn outcomes(&mut self, max_steps: usize) -> Vec<TraceNode> {
        self.rewrite(max_steps);
        self.root.leaves(&[TraceState::Normal])
    }
    /// Sample a possible outcome in proportion to its probability.
    pub fn sample<R: Rng>(&self, rng: &mut R) -> TraceNode {
        let leaves = self.root.leaves(&[TraceState::Normal]);
        let ws = leaves.iter().map(|x| x.log_p().exp()).collect::<Vec<f64>>();
        weighted_sample(rng, &leaves, &ws).clone()
    }
    /// Run the `Trace` until no further steps are possible, or until `max_steps` is reached.
    pub fn rewrite(&mut self, max_steps: usize) {
        if max_steps > self.size() {
            let n_steps = max_steps - self.size();
            self.nth(n_steps);
        }
    }
    /// A lower bound on the probability that `self` rewrites to `term`.
    pub fn rewrites_to<T>(&mut self, max_steps: usize, term: &Term, weighter: T) -> f64
    where
        T: Fn(&Term, &Term) -> f64,
    {
        self.rewrite(max_steps);
        let lps = self.root.accumulate(|n| {
            let n_r = &n.0.read().expect("poisoned TraceNode");
            // weight the log-probability by some parameterizable function
            let weight = weighter(term, &n_r.term);
            Some(n_r.log_p + weight)
        });
        if lps.is_empty() {
            f64::NEG_INFINITY
        } else {
            logsumexp(&lps)
        }
    }
}
impl<'a> Iterator for Trace<'a> {
    type Item = TraceNode;
    /// Record single-step rewrites on the highest-scoring unobserved node. `None` if there are no
    /// remaining unobserved nodes.
    fn next(&mut self) -> Option<TraceNode> {
        if let Some(node) = self.unobserved.pop() {
            {
                let mut node_w = node.0.write().expect("poisoned TraceNode");
                match (self.max_term_size, self.max_depth) {
                    (Some(n), _) if node_w.term.size() > n => node_w.state = TraceState::TooBig,
                    (_, Some(n)) if node_w.depth >= n => node_w.state = TraceState::TooDeep,
                    _ => match self.trs.rewrite(&node_w.term, self.strategy, self.sig) {
                        None => node_w.state = TraceState::Normal,
                        Some(ref rewrites) if rewrites.is_empty() => {
                            node_w.state = TraceState::Normal
                        }
                        Some(rewrites) => {
                            let (small_enough, too_big): (Vec<_>, Vec<_>) =
                                rewrites.into_iter().partition(|t| {
                                    self.max_term_size.is_none()
                                        || t.size() <= self.max_term_size.unwrap()
                                });
                            node_w.state = TraceState::Rewritten;
                            if !small_enough.is_empty() {
                                let term_selection_p = -(small_enough.len() as f64).ln();
                                let branch_mass = (1.0 - self.p_observe).ln() + node_w.log_p;
                                let child_mass = branch_mass + term_selection_p;
                                node_w.log_p += self.p_observe.ln();
                                for term in small_enough {
                                    let new_node = self.new_node(
                                        term,
                                        Some(&node),
                                        node_w.depth + 1,
                                        TraceState::Unobserved,
                                        child_mass,
                                    );
                                    node_w.children.push(new_node);
                                }
                            }
                            for term in too_big {
                                let new_node = self.new_node(
                                    term,
                                    Some(&node),
                                    node_w.depth + 1,
                                    TraceState::TooBig,
                                    f64::NEG_INFINITY,
                                );
                                node_w.children.push(new_node);
                            }
                        }
                    },
                }
            }
            Some(node)
        } else {
            None
        }
    }
}

/// All the data pertaining to a single evaluation step in a Trace.
#[derive(Debug, Clone)]
struct TraceNodeStore {
    term: Term,
    state: TraceState,
    log_p: f64,
    depth: usize,
    parent: Option<Weak<RwLock<TraceNodeStore>>>,
    children: Vec<TraceNode>,
}

/// The state of a [`Term`] at a particular evaluation step in a [`Trace`].
///
/// [`Term`]: ../enum.Term.html
/// [`Trace`]: struct.Trace.html
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TraceState {
    /// For a [`TraceNode`] which is part of the [`Trace`] but has not yet itself been examined or
    /// rewritten.
    ///
    /// [`Trace`]: struct.Trace.html
    /// [`TraceNode`]: struct.TraceNode.html
    Unobserved,
    /// For a [`TraceNode`] which has been examined and found to have a [`Term`] too large for
    /// efficient rewriting.
    ///
    /// [`Term`]: ../struct.Term.html
    /// [`TraceNode`]: struct.TraceNode.html
    TooBig,
    /// For a [`TraceNode`] which has been examined and found to be too deep in the [`Trace`].
    ///
    /// [`TraceNode`]: struct.TraceNode.html
    /// [`Trace`]: struct.Trace.html
    TooDeep,
    /// For a [`TraceNode`] which has been examined and whose [`Term`] is already in normal form.
    ///
    /// [`Term`]: ../struct.Term.html
    /// [`TraceNode`]: struct.TraceNode.html
    Normal,
    /// For a [`TraceNode`] which has been examined and is no longer a leaf node.
    ///
    /// [`TraceNode`]: struct.TraceNode.html
    Rewritten,
}
impl fmt::Display for TraceState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TraceState::Unobserved => write!(f, "Unobserved"),
            TraceState::TooBig => write!(f, "TooBig"),
            TraceState::TooDeep => write!(f, "TooDeep"),
            TraceState::Normal => write!(f, "Normal"),
            TraceState::Rewritten => write!(f, "Rewritten"),
        }
    }
}

/// A `TraceNode` describes a specific evaluation step in the [`Trace`].
///
/// [`Trace`]: struct.Trace.html
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
    /// The [`TraceState`] associated with this evaluation step.
    ///
    /// [`TraceState`]: enum.TraceState.html
    pub fn state(&self) -> TraceState {
        self.0.read().expect("poisoned TraceNode").state
    }
    /// The [`Term`] associated with this evaluation step.
    ///
    /// [`Term`]: ../enum.Term.html
    pub fn term(&self) -> Term {
        self.0.read().expect("poisoned TraceNode").term.clone()
    }
    /// The log probability of reaching this particular evaluation step.
    pub fn log_p(&self) -> f64 {
        self.0.read().expect("poisoned TraceNode").log_p
    }
    /// The depth (i.e. number of previous evaluation steps) of this evaluation step.
    pub fn depth(&self) -> usize {
        self.0.read().expect("poisoned TraceNode").depth
    }
    /// The parent `TraceNode` of this evaluation step.
    pub fn parent(&self) -> Option<TraceNode> {
        self.0
            .read()
            .expect("poisoned TraceNode")
            .parent
            .as_ref()
            .and_then(Weak::upgrade)
            .map(TraceNode)
    }
    /// The children `TraceNode`s of this evaluation step.
    pub fn children(&self) -> Vec<TraceNode> {
        self.0.read().expect("poisoned TraceNode").children.clone()
    }
    /// Whether this evaluation step has no associated children.
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
    /// Returns an iterator over all nodes that descend from this node.
    pub fn iter(&self) -> TraceNodeIter {
        TraceNodeIter::new(self.clone())
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
impl<'a> IntoIterator for &'a TraceNode {
    type Item = TraceNode;
    type IntoIter = TraceNodeIter;
    fn into_iter(self) -> TraceNodeIter {
        self.iter()
    }
}
impl IntoIterator for TraceNode {
    type Item = TraceNode;
    type IntoIter = TraceNodeIter;
    fn into_iter(self) -> TraceNodeIter {
        TraceNodeIter::new(self)
    }
}

pub struct TraceNodeIter {
    queue: Vec<TraceNode>,
}
impl TraceNodeIter {
    fn new(root: TraceNode) -> TraceNodeIter {
        TraceNodeIter { queue: vec![root] }
    }
}
impl Iterator for TraceNodeIter {
    type Item = TraceNode;
    fn next(&mut self) -> Option<TraceNode> {
        let node = self.queue.pop()?;
        self.queue.append(&mut node.children());
        Some(node)
    }
}

fn logsumexp(lps: &[f64]) -> f64 {
    let largest = lps.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    if largest == f64::NEG_INFINITY {
        f64::NEG_INFINITY
    } else {
        let x = lps.iter().map(|lp| (lp - largest).exp()).sum::<f64>().ln();
        largest + x
    }
}

/// Samples an item from `xs` given the weights `ws`.
fn weighted_sample<'a, T, R: Rng>(rng: &mut R, xs: &'a [T], ws: &[f64]) -> &'a T {
    assert_eq!(xs.len(), ws.len(), "weighted sample given invalid inputs");
    let total = ws.iter().fold(0f64, |acc, x| acc + x);
    let threshold: f64 = Uniform::new(0f64, total).sample(rng);
    let mut cum = 0f64;
    for (wp, x) in ws.iter().zip(xs) {
        cum += *wp;
        if threshold <= cum {
            return x;
        }
    }
    unreachable!()
}
