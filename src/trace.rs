//! Record sequences of rewrites.
//!
//! # Examples
//!
//! A TRS with mutually exclusive rules gives a straightfoward linear record of
//! rewrites:
//!
//! ```
//! # use term_rewriting::{parse, trace::Trace, Signature, Strategy, NumberRepresentation};
//! # use itertools::Itertools;
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
//! let trace = Trace::new(&trs, &sig, &term, 0.5, 10, None, Strategy::Normal, NumberRepresentation::default());
//!
//! let expected = vec!["PLUS(3, 1)", "PLUS(2, 2)", "PLUS(1, 3)", "PLUS(0, 4)", "4"];
//! let got = trace
//!     .iter()
//!     .map(|n| trace[n].term().pretty(&sig))
//!     .collect::<Vec<_>>();
//! assert_eq!(trace.size(), 5);
//! assert_eq!(got, expected);
//! ```
//!
//! ```
//! # use term_rewriting::{NumberRepresentation, parse_term, parse_trs, trace::Trace, Signature, Strategy};
//! # use itertools::Itertools;
//!
//! let mut sig = Signature::default();
//! let trs_str =
//!     "PLUS(SUCC(v0_) v1_) = PLUS(v0_ SUCC(v1_)) | SUCC(PLUS(v0_ v1_)); PLUS(ZERO v2_) = v2_;";
//! let trs = parse_trs(&mut sig, trs_str).expect("parsed trs");
//! let input_str = "PLUS(SUCC(SUCC(SUCC(ZERO))) PLUS(SUCC(ZERO) ZERO))";
//! let input = parse_term(&mut sig, input_str).expect("parsed input");
//! let mut trace = Trace::new(&trs, &sig, &input, 0.5, 100, None, Strategy::Normal, NumberRepresentation::default());
//!
//! let formatter = trace
//!     .iter()
//!     .format_with("\n", |n, f| f(&format_args!("{:?}, {:?}, {}", n, trace.children(n).collect_vec(), trace[n].term().pretty(&sig))));
//! println!("{}", formatter);
//! assert_eq!(trace.size(), 55);
//! ```

use smallvec::{smallvec, SmallVec};
use std::f64;
use std::fmt;

use super::{NumberRepresentation, Patterns, Signature, Strategy, Term, TRS};

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
    // tree
    root: Option<NodeHandle>,
    nodes: Vec<Node>,
    unobserved: Vec<Unobserved>,
    // parameters
    trs: &'a TRS,
    sig: &'a Signature,
    p_observe: f64,
    max_steps: usize,
    max_term_size: Option<usize>,
    strategy: Strategy,
    patterns: &'a Patterns,
    rep: NumberRepresentation,
}

pub struct TraceIter<'a> {
    trace: &'a Trace<'a>,
    stack: Option<SmallVec<[NodeHandle; 32]>>,
}

pub struct ChildIter<'a> {
    trace: &'a Trace<'a>,
    front: Option<NodeHandle>,
    back: Option<NodeHandle>,
}

/// All the data pertaining to a single evaluation step in a Trace.
#[derive(Debug, Clone)]
pub struct Node {
    data: NodeData,
    depth: usize,
    parent: Option<NodeHandle>,
    first_child: Option<NodeHandle>,
    last_child: Option<NodeHandle>,
    next_sibling: Option<NodeHandle>,
    prev_sibling: Option<NodeHandle>,
}

#[derive(Debug, Clone)]
pub struct NodeData {
    term: Term,
    state: TraceState,
    log_p: f64,
}

/// A `NodeHandle` references a specific evaluation step in the [`Trace`].
///
/// [`Trace`]: struct.Trace.html
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeHandle(usize);

#[derive(Clone, Debug)]
struct Unobserved(Term, usize, Option<NodeHandle>, f64);

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

impl<'a> Trace<'a> {
    /// Create a trace initialized with `term` undergoing rewrites in `trs`. Every step for a node
    /// in the trace multiplies the node's probability score by `p_observe`.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        trs: &'a TRS,
        sig: &'a Signature,
        term: &Term,
        p_observe: f64,
        max_steps: usize,
        max_term_size: Option<usize>,
        patterns: &'a Patterns,
        strategy: Strategy,
        rep: NumberRepresentation,
    ) -> Trace<'a> {
        let mut trace = Trace {
            root: None,
            nodes: Vec::with_capacity(max_steps),
            unobserved: Vec::with_capacity(max_steps),
            patterns,
            trs,
            sig,
            p_observe,
            max_steps,
            max_term_size,
            strategy,
            rep,
        };
        trace
            .unobserved
            .push(Unobserved(term.clone(), 0, None, 0.0));
        while trace.nodes.len() < max_steps && trace.step().is_some() {}
        trace
    }
    fn new_node(
        &mut self,
        term: Term,
        parent: Option<NodeHandle>,
        state: TraceState,
        log_p: f64,
    ) -> NodeHandle {
        let depth = parent.map(|ph| self[ph].depth + 1).unwrap_or(0);
        let node = Node::new(term, state, log_p, depth);
        let nh = NodeHandle(self.nodes.len());
        self.nodes.push(node);
        match parent {
            None if self.root.is_none() => self.root = Some(nh),
            None => panic!("cannot have multiple roots"),
            Some(ph) => self.append(ph, nh),
        }
        nh
    }
    fn append(&mut self, ph: NodeHandle, ch: NodeHandle) {
        self.nodes[ch.0].parent = Some(ph);
        self.nodes[ch.0].prev_sibling = self.nodes[ph.0].last_child.take();
        //lf.nodes[ch.0].next_sibling = None;
        if let Some(sh) = self.nodes[ch.0].prev_sibling {
            self.nodes[sh.0].next_sibling = Some(ch);
        }
        self.nodes[ph.0].last_child.replace(ch);
        self.nodes[ph.0].first_child = self.nodes[ph.0].first_child.or(Some(ch));
    }
    fn enqueue(&mut self, term: Term, depth: usize, parent: Option<NodeHandle>, log_p: f64) {
        self.unobserved.push(Unobserved(term, depth, parent, log_p))
    }
    fn next_best(&mut self) -> Option<Unobserved> {
        (0..self.unobserved.len())
            .rev()
            .max_by(|i, j| {
                self.unobserved[*i]
                    .3
                    .partial_cmp(&self.unobserved[*j].3)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .map(|idx| self.unobserved.swap_remove(idx))
    }
    /// The initial node of the `Trace`.
    pub fn root(&self) -> Option<NodeHandle> {
        self.root
    }
    /// The length of the longest chain of evaluation steps.
    pub fn depth(&self) -> usize {
        self.nodes.iter().map(|x| x.depth).max().unwrap_or(0)
    }
    /// The total count of nodes maintained by the `Trace`.
    pub fn size(&self) -> usize {
        self.nodes.len()
    }
    /// The probability mass that has been explored by the Trace.
    pub fn mass(&self) -> f64 {
        let lps = self
            .nodes
            .iter()
            .filter(|n| n.data.state != TraceState::Unobserved)
            .map(|n| n.data.log_p)
            .collect::<Vec<_>>();
        logsumexp(&lps).exp()
    }
    /// A lower bound on the probability that `self` rewrites to `term`.
    pub fn rewrites_to<T>(&mut self, term: &Term, weighter: T) -> f64
    where
        T: Fn(&Term, &Term) -> f64,
    {
        let lps = self
            .nodes
            .iter()
            .map(|n| n.data.log_p + weighter(term, &n.data.term))
            .collect::<Vec<_>>();
        logsumexp(&lps)
    }
    /// Record single-step rewrites on the highest-scoring unobserved node. `None` if there are no
    /// remaining unobserved nodes.
    fn step(&mut self) -> Option<NodeHandle> {
        let Unobserved(term, depth, parent, log_p) = self.next_best()?;
        if self.nodes.len() >= self.max_steps {
            None
        } else if self
            .max_term_size
            .map(|max| term.size() > max)
            .unwrap_or(false)
        {
            Some(self.new_node(term, parent, TraceState::TooBig, f64::NEG_INFINITY))
        } else {
            let (new_state, new_node_lp, nh, n) = {
                let mut rewrites = self
                    .trs
                    .rewrite(&term, &self.patterns, self.strategy, self.rep, self.sig)
                    .peekable();
                let (new_state, new_node_lp) = if rewrites.peek().is_some() {
                    (TraceState::Rewritten, log_p + self.p_observe.ln())
                } else {
                    (TraceState::Normal, log_p)
                };
                let nh = NodeHandle(self.nodes.len());
                let mut n = 0;
                for new_term in rewrites {
                    let new_lp = log_p + (1.0 - self.p_observe).ln();

                    self.enqueue(new_term, depth + 1, Some(nh), new_lp);
                    n += 1;
                }
                (new_state, new_node_lp, nh, n)
            };
            for u in self.unobserved.iter_mut() {
                if u.2 == Some(nh) {
                    u.3 += -(n as f64).ln();
                }
            }
            Some(self.new_node(term, parent, new_state, new_node_lp))
        }
    }
    /// Iterates over all nodes in the trace.
    pub fn iter(&self) -> TraceIter {
        TraceIter::new(&self, self.root)
    }
    pub fn children(&'a self, nh: NodeHandle) -> ChildIter<'a> {
        ChildIter::new(&self, nh)
    }
}

impl<'a> std::ops::Index<NodeHandle> for Trace<'a> {
    type Output = Node;
    fn index(&self, index: NodeHandle) -> &Self::Output {
        &self.nodes[index.0]
    }
}

impl fmt::Display for TraceState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TraceState::Unobserved => write!(f, "Unobserved"),
            TraceState::TooBig => write!(f, "TooBig"),
            TraceState::Normal => write!(f, "Normal"),
            TraceState::Rewritten => write!(f, "Rewritten"),
        }
    }
}

impl Node {
    fn new(term: Term, state: TraceState, log_p: f64, depth: usize) -> Self {
        Node {
            data: NodeData { term, state, log_p },
            depth,
            parent: None,
            first_child: None,
            last_child: None,
            prev_sibling: None,
            next_sibling: None,
        }
    }
    /// The [`TraceState`] associated with this evaluation step.
    ///
    /// [`TraceState`]: enum.TraceState.html
    pub fn state(&self) -> TraceState {
        self.data.state
    }
    /// The [`Term`] associated with this evaluation step.
    ///
    /// [`Term`]: ../enum.Term.html
    pub fn term(&self) -> &Term {
        &self.data.term
    }
    /// The log probability of reaching this particular evaluation step.
    pub fn log_p(&self) -> f64 {
        self.data.log_p
    }
    /// The depth (i.e. number of previous evaluation steps) of this evaluation step.
    pub fn depth(&self) -> usize {
        self.depth
    }
    /// The parent `TraceNode` of this evaluation step.
    pub fn parent(&self) -> Option<NodeHandle> {
        self.parent
    }
    /// Whether this evaluation step has no associated children.
    pub fn is_leaf(&self) -> bool {
        self.first_child.is_none()
    }
}

impl<'a> TraceIter<'a> {
    fn new(trace: &'a Trace, nh: Option<NodeHandle>) -> TraceIter<'a> {
        TraceIter {
            trace,
            stack: nh.map(|nh| smallvec![nh]),
        }
    }
}
impl<'a> Iterator for TraceIter<'a> {
    type Item = NodeHandle;
    fn next(&mut self) -> Option<Self::Item> {
        let mut stack = self.stack.take()?;
        let nh = stack.pop()?;
        for child in self.trace.children(nh).rev() {
            stack.push(child);
        }
        self.stack.replace(stack);
        Some(nh)
    }
}

impl<'a> ChildIter<'a> {
    fn new(trace: &'a Trace, nh: NodeHandle) -> ChildIter<'a> {
        ChildIter {
            trace,
            front: trace.nodes.get(nh.0).and_then(|node| node.first_child),
            back: trace.nodes.get(nh.0).and_then(|node| node.last_child),
        }
    }
}

impl<'a> Iterator for ChildIter<'a> {
    type Item = NodeHandle;
    fn next(&mut self) -> Option<Self::Item> {
        if self.front == self.back {
            self.back = None;
            self.front.take()
        } else {
            let nh = self.front.take();
            if let Some(nh) = nh {
                self.front = self.trace[nh].next_sibling;
            }
            nh
        }
    }
}
impl<'a> DoubleEndedIterator for ChildIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.back == self.front {
            self.front = None;
            self.back.take()
        } else {
            let nh = self.back.take();
            if let Some(nh) = nh {
                self.back = self.trace[nh].prev_sibling;
            }
            nh
        }
    }
}

impl PartialEq for Unobserved {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1.eq(&other.1)
    }
}

impl Eq for Unobserved {}

impl PartialOrd for Unobserved {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.1.partial_cmp(&other.1)
    }
}

impl Ord for Unobserved {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap_or(std::cmp::Ordering::Equal)
    }
}

pub(crate) fn logsumexp(lps: &[f64]) -> f64 {
    let largest = lps.iter().fold(f64::NEG_INFINITY, |acc, lp| acc.max(*lp));
    if largest == f64::NEG_INFINITY {
        f64::NEG_INFINITY
    } else {
        let x = lps.iter().map(|lp| (lp - largest).exp()).sum::<f64>().ln();
        largest + x
    }
}
