use itertools::Itertools;
use rand::seq::sample_iter;
use rand::Rng;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::iter;

use super::pretty::Pretty;

/// Represents a place in a [`Term`].
///
/// [`Term`]: enum.Term.html
pub type Place = Vec<usize>;

/// A symbol for an unspecified term. Only carries meaning alongside a [`Signature`].
///
/// To construct a `Variable`, use [`Signature::new_var`]
///
/// [`Signature`]: struct.Signature.html
/// [`Signature::new_var`]: struct.Signature.html#method.new_var
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    pub(crate) id: usize,
}
impl Variable {
    /// Returns a `Variable`'s name.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let var = sig.new_var(Some("Z".to_string()));
    /// assert_eq!(var.name(&sig), Some("Z"));
    /// ```
    pub fn name(self, sig: &Signature) -> Option<&str> {
        let opt = &sig.variables[self.id];
        opt.as_ref().map(|s| s.as_str())
    }
    /// Returns a human-readable, string representation of a `Variable`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let var = sig.new_var(Some("Z".to_string()));
    /// assert_eq!(var.display(&sig), "Z_");
    /// ```
    pub fn display(self, sig: &Signature) -> String {
        if let Some(ref name) = sig.variables[self.id] {
            format!("{}_", name)
        } else {
            format!("var{}_", self.id)
        }
    }
}

/// A symbol with fixed arity. Only carries meaning alongside a [`Signature`].
///
/// To construct an `Operator`, use [`Signature::new_op`].
///
/// [`Signature`]: struct.Signature.html
/// [`Signature::new_op`]: struct.Signature.html#method.new_op
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Operator {
    pub(crate) id: usize,
}
impl Operator {
    /// Returns an `Operator`'s arity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(2, Some("Z".to_string()));
    /// assert_eq!(op.arity(&sig), 2);
    /// ```
    pub fn arity(self, sig: &Signature) -> u32 {
        sig.operators[self.id].0
    }
    /// Returns an `Operator`'s name.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(2, Some("Z".to_string()));
    /// assert_eq!(op.name(&sig), Some("Z"));
    /// ```
    pub fn name(self, sig: &Signature) -> Option<&str> {
        let opt = &sig.operators[self.id].1;
        opt.as_ref().map(|s| s.as_str())
    }
    /// Returns a human-readable, string representation of an `Operator`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(2, Some("Z".to_string()));
    /// assert_eq!(op.display(&sig), "Z");
    /// ```
    pub fn display(self, sig: &Signature) -> String {
        if let (_, Some(ref name)) = sig.operators[self.id] {
            name.clone()
        } else {
            format!("op{}", self.id)
        }
    }
}

/// `Atom`s are the parts of a [`TRS`] that are not constructed from smaller parts: [`Variable`]s and [`Operator`]s.
///
/// [`TRS`]: struct.TRS.html
/// [`Variable`]: struct.Variable.html
/// [`Operator`]: struct.Operator.html
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Atom {
    Variable(Variable),
    Operator(Operator),
}
impl Atom {
    pub fn display(&self, sig: &Signature) -> String {
        match *self {
            Atom::Variable(v) => v.display(sig),
            Atom::Operator(o) => o.display(sig),
        }
    }
}
impl From<Variable> for Atom {
    fn from(var: Variable) -> Atom {
        Atom::Variable(var)
    }
}
impl From<Operator> for Atom {
    fn from(op: Operator) -> Atom {
        Atom::Operator(op)
    }
}

/// Records a universe of symbols.
///
/// Use [`Signature::default`] for a blank signature, or [`Signature::new`] to initialize a
/// signature with given operators.
///
/// [`Signature::default`]: #method.default
/// [`Signature::new`]: #method.new
#[derive(Clone, Debug)]
pub struct Signature {
    /// Stores the (arity, name) for every operator.
    pub(crate) operators: Vec<(u32, Option<String>)>,
    /// Stores the name for every variable.
    pub(crate) variables: Vec<Option<String>>,
}
impl Signature {
    /// Construct a signature with the given operators.
    ///
    /// Each operator is specified in the form of `(arity, Some(name))` or
    /// `(arity, None)`, where `arity` is the number of arguments a term takes
    /// (for example, an `arity` of 0 gives a "constant" operator). A `name` for
    /// the operator is unnecessary, but may be supplied for more readable
    /// formatting.
    ///
    /// The returned vector of [`Operator`]s corresponds to the supplied spec.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    ///
    /// ```
    /// # use term_rewriting::{Signature};
    /// // Constructs a new signature with the operators ".","S","K' from the vector
    /// let (mut sig,ops) = Signature:: new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// let (mut sig2,ops2) = Signature:: new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// let (mut sig3,ops3) = Signature:: new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    /// ]);
    ///
    /// assert_eq!(sig,sig2);
    /// assert_ne!(sig,sig3);
    ///```
    pub fn new(operator_spec: Vec<(u32, Option<String>)>) -> (Signature, Vec<Operator>) {
        let variables = Vec::new();
        let sig = Signature {
            operators: operator_spec,
            variables,
        };
        let ops = sig.operators();
        (sig, ops)
    }
    /// Returns every [`Operator`] known to the signature, in the order they were created.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    ///
    /// ```
    /// # use term_rewriting::{Signature};
    /// // Constructs a new signature with the operators ".","S","K' from the vector
    /// let (mut sig,ops) = Signature:: new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// // Returns the operators in the signature above
    /// let example_ops = sig.operators();
    ///
    /// assert_eq!(ops,example_ops);
    ///```
    pub fn operators(&self) -> Vec<Operator> {
        (0..self.operators.len())
            .map(|id| Operator { id })
            .collect()
    }
    /// Returns every [`Variable`] known to the signature, in the order they were created.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    ///
    /// ```
    /// # use term_rewriting::{Signature};
    /// // Constructs a new signature with the variables ".","S","K' from the vector
    /// let (mut sig,ops) = Signature:: new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// // Returns the variables in the signature above
    /// let vars = sig.variables();
    /// let vars2 = sig.variables();
    ///
    /// let newVar = sig.new_var(Some("A".to_string()));
    /// let vars3 = sig.variables();
    ///
    /// assert_eq!(vars,vars2);
    /// assert_ne!(vars,vars3);
    ///```
    pub fn variables(&self) -> Vec<Variable> {
        (0..self.variables.len())
            .map(|id| Variable { id })
            .collect()
    }
    /// Returns every [`Atom`] known to the signature.
    ///
    /// [`Atom`]: enum.Atom.html
    pub fn atoms(&self) -> Vec<Atom> {
        let vars = self.variables().into_iter().map(Atom::Variable);
        let ops = self.operators().into_iter().map(Atom::Operator);
        vars.chain(ops).collect()
    }
    /// Create a new [`Operator`] distinct from all existing operators.
    ///
    /// [`Operator`]: struct.Operator.html
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature};
    /// let mut sig = Signature::default();
    /// let a = sig.new_op(1, Some(".".to_string()));
    /// let s = sig.new_op(2, Some("S".to_string()));
    /// let s2 = sig.new_op(2, Some("S".to_string()));
    ///
    /// assert_ne!(a,s);
    /// assert_ne!(a,s2);
    /// assert_ne!(s,s2);
    /// ```
    pub fn new_op(&mut self, arity: u32, name: Option<String>) -> Operator {
        let id = self.operators.len();
        self.operators.push((arity, name));
        Operator { id }
    }
    /// Create a new [`Variable`] distinct from all existing variables.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature};
    /// let mut sig = Signature::default();
    /// let z = sig.new_var(Some("Z".to_string()));
    /// let z2 = sig.new_var(Some("Z".to_string()));
    ///
    /// assert_ne!(z,z2);
    /// ```
    pub fn new_var(&mut self, name: Option<String>) -> Variable {
        let id = self.variables.len();
        self.variables.push(name);
        Variable { id }
    }
    /// Merge two [`Signature`]s. All terms, contexts, rules, and TRSs associated
    /// with the `other` signature should be `reified` using methods provided
    /// by the returned [`SignatureChange`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{MergeStrategy, Signature, parse_term, parse_trs};
    /// let (mut sig1, _ops) = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// let mut sig2 = sig1.clone();
    ///
    /// let s1 = "S K K";
    /// let term = parse_term(&mut sig1, s1).unwrap();
    /// let s2 = "S x_ y_ z_ = (x_ z_) (y_ z_);";
    /// let trs = parse_trs(&mut sig2, s2).unwrap();
    ///
    /// let sigchange = sig1.merge(sig2, MergeStrategy::SameOperators);
    /// // we only reify terms/rules/TRSs associated with sig2
    /// let trs = sigchange.reify_trs(trs);
    /// // now term and rule both exist with symbols according to sig1.
    /// ```
    /// [`Signature`]: struct.Signature.html
    /// [`SignatureChange`]: struct.SignatureChange.html
    pub fn merge(&mut self, mut other: Signature, strategy: MergeStrategy) -> SignatureChange {
        let delta_op = match strategy {
            MergeStrategy::SameOperators => 0,
            MergeStrategy::OperatorsByArityAndName => {
                let old_len = self.operators.len();
                for op_spec in other.operators {
                    if !self.operators.contains(&op_spec) {
                        self.operators.push(op_spec)
                    }
                }
                old_len
            }
            MergeStrategy::DistinctOperators => {
                let old_len = self.operators.len();
                self.operators.append(&mut other.operators);
                old_len
            }
        };
        let delta_var = self.variables.len();
        self.variables.append(&mut other.variables);
        SignatureChange {
            delta_op,
            delta_var,
        }
    }
}
/// Creates a new Signature without any Operators or Variables
///
/// # Usage
///
/// ```
/// # use term_rewriting::{Signature};
/// let mut sig = Signature::default();
/// let (mut sig2,ops) = Signature::new(vec![]);
/// let (mut sig3,ops) = Signature::new(vec![
///     (2, Some(".".to_string())),
///     (0, Some("S".to_string())),
///     (0, Some("K".to_string())),
///     ]);
/// assert_eq!(sig,sig2);
/// assert_ne!(sig,sig3);
/// ```
impl Default for Signature {
    fn default() -> Signature {
        Signature {
            operators: Vec::new(),
            variables: Vec::new(),
        }
    }
}
/// Compares two Signatures to test if they should be considered equal
///
/// # Examples
///
/// ```
/// # use term_rewriting::{Signature};
/// let mut sig = Signature::default();
/// let mut sig2 = Signature::default();
///
/// assert!(sig.eq(&sig2));
/// ```
impl PartialEq for Signature {
    fn eq(&self, other: &Signature) -> bool {
        self.variables.len() == other.variables.len()
            && self.operators.len() == other.operators.len()
            && self.operators
                .iter()
                .zip(&other.operators)
                .all(|(&(arity1, _), &(arity2, _))| arity1 == arity2)
    }
}

/// Specifies how to merge two signatures.
/// See [`Signature::merge`].
///
/// [`Signature::merge`]: struct.Signature.html#method.merge
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MergeStrategy {
    /// Operators won't be added to the signature:
    /// this must mean all operators were added in the same order for both
    /// signatures.
    SameOperators,
    /// Operators are added to the signature only when there is no existing
    /// operator with the same arity and name.
    OperatorsByArityAndName,
    /// Operators are always added distinctly:
    /// no operators associated with the first signature will every equate to
    /// those associated with the second signature.
    DistinctOperators,
}

/// Allows terms/rules/TRSs to be reified for use with another signature.
/// See [`Signature::merge`].
///
/// [`Signature::merge`]: struct.Signature.html#method.merge
pub struct SignatureChange {
    delta_op: usize,
    delta_var: usize,
}
impl SignatureChange {
    /// Reifies term for use with another signature
    /// See [`SignatureChange`]
    ///
    /// [`SignatureChange`]: struct.SignatureChange
    pub fn reify_term(&self, term: Term) -> Term {
        match term {
            Term::Variable(Variable { id }) => {
                let id = id + self.delta_var;
                Term::Variable(Variable { id })
            }
            Term::Application {
                op: Operator { id },
                args,
            } => {
                let id = id + self.delta_op;
                Term::Application {
                    op: Operator { id },
                    args: args.into_iter().map(|t| self.reify_term(t)).collect(),
                }
            }
        }
    }
    /// Reifies context for use with another signature
    /// See [`SignatureChange`]
    ///
    /// [`SignatureChange`]: struct.SignatureChange
    pub fn reify_context(&self, context: Context) -> Context {
        match context {
            Context::Hole => Context::Hole,
            Context::Variable(Variable { id }) => {
                let id = id + self.delta_var;
                Context::Variable(Variable { id })
            }
            Context::Application {
                op: Operator { id },
                args,
            } => {
                let id = id + self.delta_op;
                Context::Application {
                    op: Operator { id },
                    args: args.into_iter().map(|t| self.reify_context(t)).collect(),
                }
            }
        }
    }
    /// Reifies rule for use with another signature
    /// See [`SignatureChange`]
    ///
    /// [`SignatureChange`]: struct.SignatureChange
    pub fn reify_rule(&self, rule: Rule) -> Rule {
        let Rule { lhs, rhs } = rule;
        let lhs = self.reify_term(lhs);
        let rhs = rhs.into_iter().map(|t| self.reify_term(t)).collect();
        Rule { lhs, rhs }
    }
    /// Reifies TRS for use with another signature
    /// See [`SignatureChange`]
    ///
    /// [`SignatureChange`]: struct.SignatureChange
    pub fn reify_trs(&self, trs: TRS) -> TRS {
        let rules = trs.rules.into_iter().map(|r| self.reify_rule(r)).collect();
        TRS { rules, ..trs }
    }
}

/// A way of signifying what type of unification is being performed
#[derive(PartialEq, Eq)]
enum Unification {
    Match,
    Unify,
}

/// A first-order context: a [`Term`] that may have [`Hole`]s; a sort of [`Term`] template.
///
/// [`Term`]: enum.Term.html
/// [`Hole`]: enum.Context.html#variant.Hole
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Context {
    /// An empty place in the `Context`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Context};
    /// // How to construct a hole manually
    /// let h = Context::Hole;
    /// ```
    Hole,
    /// A concrete but unspecified `Context` (e.g. `x`, `y`)
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Context};
    /// let mut sig = Signature::default();
    ///
    /// // How to construct a Context Variable manually
    /// let v = sig.new_var(Some("x_".to_string()));
    /// let var = Context::Variable(v);
    /// ```
    Variable(Variable),
    /// An [`Operator`] applied to zero or more `Context`s (e.g. (`f(x, y)`, `g()`)
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Context};
    /// let mut sig = Signature::default();
    /// // How to construct a Context Application manually
    /// let a = sig.new_op(0, Some("A".to_string()));
    /// let app = Context::Application { op: a, args: vec![] };
    /// ```
    /// [`Operator`]: struct.Operator.html
    Application { op: Operator, args: Vec<Context> },
}
impl Context {
    /// A serialized representation of the Context.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Context, Variable, Operator};
    ///
    /// let mut sig = Signature::default();
    ///
    /// let h = Context::Hole;
    /// assert_eq!(h.display(&sig), "[!]".to_string());
    ///
    /// let var = sig.new_var(Some("y".to_string()));
    /// let context_var = Context::Variable(var);
    /// assert_eq!(context_var.display(&sig), "y_".to_string());
    ///
    /// let op = sig.new_op(0,Some("S".to_string()));
    /// let args = vec![];
    /// let context_app = Context::Application {op, args};
    /// assert_eq!(context_app.display(&sig), "S".to_string());
    ///
    /// let var = sig.new_var(Some("x".to_string()));
    /// let a = sig.new_op(2, Some("A".to_string()));
    /// let example_context = Context::Application {
    ///     op: a,
    ///     args: vec![Context::Hole, Context::Variable(var)],
    /// };
    /// assert_eq!(example_context.display(&sig), "A([!] x_)".to_string());
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        match self {
            Context::Hole => "[!]".to_string(),
            Context::Variable(v) => v.display(sig),
            Context::Application { op, args } => {
                let op_str = op.display(sig);
                if args.is_empty() {
                    op_str
                } else {
                    let args_str = args.iter().map(|arg| arg.display(sig)).join(" ");
                    format!("{}({})", op_str, args_str)
                }
            }
        }
    }
    /// A human-readable serialization of the Context.
    pub fn pretty(&self, sig: &Signature) -> String {
        Pretty::pretty(self, sig)
    }
    /// Every [`Atom`] used in `self`.
    ///
    /// [`Atom`]: enum.Atom.html
    pub fn atoms(&self) -> Vec<Atom> {
        let vars = self.variables().into_iter().map(Atom::Variable);
        let ops = self.operators().into_iter().map(Atom::Operator);
        vars.chain(ops).collect()
    }
    /// Every [`Variable`] used in `self`.
    ///
    /// [`Variable`]: struct.Variable.html
    pub fn variables(&self) -> Vec<Variable> {
        match *self {
            Context::Hole => vec![],
            Context::Variable(v) => vec![v],
            Context::Application { ref args, .. } => {
                args.iter().flat_map(Context::variables).unique().collect()
            }
        }
    }
    /// Every [`Operator`] used in `self`.
    ///
    /// [`Operator`]: struct.Operator.html
    pub fn operators(&self) -> Vec<Operator> {
        if let Context::Application { op, ref args } = *self {
            args.iter()
                .flat_map(Context::operators)
                .chain(iter::once(op))
                .unique()
                .collect()
        } else {
            vec![]
        }
    }
    /// A list of the [`Place`]s in `self` that are holes.
    ///
    /// [`Place`]: type.Place.html
    pub fn holes(&self) -> Vec<Place> {
        self.subcontexts()
            .into_iter()
            .filter_map(|(c, p)| {
                if let Context::Hole = *c {
                    Some(p)
                } else {
                    None
                }
            })
            .collect()
    }
    /// The head of the `Context`.
    pub fn head(&self) -> Option<Atom> {
        match self {
            Context::Hole => None,
            Context::Variable(v) => Some(Atom::Variable(*v)),
            Context::Application { op, .. } => Some(Atom::Operator(*op)),
        }
    }
    /// The args of the `Context`.
    pub fn args(&self) -> Vec<Context> {
        if let Context::Application { args, .. } = self {
            args.clone()
        } else {
            vec![]
        }
    }
    /// Every subcontext and its place, starting with the original context itself.
    pub fn subcontexts(&self) -> Vec<(&Context, Place)> {
        if let Context::Application { ref args, .. } = *self {
            let here = iter::once((self, vec![]));
            let subcontexts = args.iter().enumerate().flat_map(|(i, arg)| {
                arg.subcontexts()
                    .into_iter()
                    .zip(iter::repeat(i))
                    .map(|((t, p), i)| {
                        let mut a = vec![i];
                        a.extend(p);
                        (t, a)
                    })
            });
            here.chain(subcontexts).collect()
        } else {
            vec![(self, vec![])]
        }
    }
    /// The number of distinct [`Place`]s in `self`.
    ///
    /// [`Place`]: type.Place.html
    pub fn size(&self) -> usize {
        self.subcontexts().len()
    }
    /// Get the subcontext at the given [`Place`], or `None` if the place does not exist.
    ///
    /// [`Place`]: type.Place.html
    #[cfg_attr(feature = "cargo-clippy", allow(ptr_arg))]
    pub fn at(&self, place: &[usize]) -> Option<&Context> {
        self.at_helper(&*place)
    }
    fn at_helper(&self, place: &[usize]) -> Option<&Context> {
        if place.is_empty() {
            return Some(self);
        }
        match *self {
            Context::Application { ref args, .. } if place[0] <= args.len() => {
                args[place[0]].at_helper(&place[1..].to_vec())
            }
            _ => None,
        }
    }
    /// Create a copy of `self` where the `Context` at the given [`Place`] has been replaced with
    /// `subcontext`.
    ///
    /// [`Place`]: type.Place.html
    pub fn replace(&self, place: &[usize], subcontext: Context) -> Option<Context> {
        self.replace_helper(&*place, subcontext)
    }
    fn replace_helper(&self, place: &[usize], subcontext: Context) -> Option<Context> {
        if place.is_empty() {
            Some(subcontext)
        } else {
            match *self {
                Context::Application { op, ref args } if place[0] <= args.len() => {
                    if let Some(context) =
                        args[place[0]].replace_helper(&place[1..].to_vec(), subcontext)
                    {
                        let mut new_args = args.clone();
                        new_args.remove(place[0]);
                        new_args.insert(place[0], context);
                        Some(Context::Application { op, args: new_args })
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
    }
    /// Translate `self` into a [`Term`], if possible.
    ///
    /// [`Term`]: enum.Term.html
    pub fn to_term(&self) -> Result<Term, ()> {
        match *self {
            Context::Hole => Err(()),
            Context::Variable(v) => Ok(Term::Variable(v)),
            Context::Application { op, ref args } => {
                let mut mapped_args = vec![];
                for arg in args {
                    mapped_args.push(arg.to_term()?);
                }
                Ok(Term::Application {
                    op,
                    args: mapped_args,
                })
            }
        }
    }
}
impl From<Term> for Context {
    fn from(t: Term) -> Context {
        match t {
            Term::Variable(v) => Context::Variable(v),
            Term::Application { op, args } => {
                let args = args.into_iter().map(Context::from).collect();
                Context::Application { op, args }
            }
        }
    }
}

/// A first-order term: either a [`Variable`] or an application of an [`Operator`].
///
/// [`Variable`]: struct.Variable.html
/// [`Operator`]: struct.Operator.html
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Term {
    /// A concrete but unspecified `Term` (e.g. `x`, `y`).
    /// See [`Variable`] for more information.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// // Constructing a Variable manually
    /// let var = sig.new_var(Some("x_".to_string()));
    /// let var_term = Term::Variable(var);
    ///
    /// // Constructing a Variable using the parser
    /// let var = parse_term(&mut sig, "x_");
    /// ```
    Variable(Variable),
    /// An [`Operator`] applied to zero or more `Term`s (e.g. (`f(x, y)`, `g()`).
    ///
    /// A `Term` that is an application of an [`Operator`] with arity 0 applied to 0 `Term`s can be considered a constant.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// // Constructing a Constant manually
    /// let a = sig.new_op(0, Some("A".to_string()));
    /// let const_term = Term::Application {
    ///     op: a,
    ///      args: vec![],
    /// };
    ///
    /// // Constructing a Constant using the parser
    /// let const_term = parse_term(&mut sig, "A");
    ///
    /// // Constructing an Application manually
    /// let x = sig.new_var(Some("x_".to_string()));
    /// let b = sig.new_op(1, Some("B".to_string()));
    /// let op_term = Term::Application {
    ///     op: b,
    ///     args: vec![Term::Variable(x)],
    /// };
    ///
    /// // Constructing an Application using the parser
    /// let op_term = parse_term(&mut sig, "B(x_)");
    /// ```
    Application { op: Operator, args: Vec<Term> },
}
impl Term {
    /// A serialized representation of the Term.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "A(B x_)").expect("parse of A(B x_)");
    ///
    /// assert_eq!(t.display(&sig), "A(B x_)".to_string());
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        match self {
            Term::Variable(v) => v.display(sig),
            Term::Application { op, args } => {
                let op_str = op.display(sig);
                if args.is_empty() {
                    op_str
                } else {
                    let args_str = args.iter().map(|arg| arg.display(sig)).join(" ");
                    format!("{}({})", op_str, args_str)
                }
            }
        }
    }
    /// A human-readable serialization of the Term.
    pub fn pretty(&self, sig: &Signature) -> String {
        Pretty::pretty(self, sig)
    }
    /// Every [`Atom`] used in the term.
    ///
    /// [`Atom`]: enum.Atom.html
    ///
    /// # Examples
    ///
    /// ```
    /// //A(B x_)
    /// # use term_rewriting::{Signature, Term, Atom};
    /// let mut sig = Signature::default();
    /// let x = sig.new_var(Some("x".to_string()));
    /// let a = sig.new_op(2, Some("A".to_string()));
    /// let b = sig.new_op(0, Some("B".to_string()));
    ///
    /// let example_term = Term::Application {
    ///     op: a,
    ///     args: vec![
    ///         Term::Application { op: b, args: vec![] },
    ///         Term::Variable(x),
    ///     ],
    /// };
    /// let expected_atoms = vec![
    ///     Atom::Variable(x),
    ///     Atom::Operator(b),
    ///     Atom::Operator(a),
    /// ];
    ///
    /// assert_eq!(example_term.atoms(), expected_atoms);
    /// ```
    pub fn atoms(&self) -> Vec<Atom> {
        let vars = self.variables().into_iter().map(Atom::Variable);
        let ops = self.operators().into_iter().map(Atom::Operator);
        vars.chain(ops).collect()
    }
    /// Every [`Variable`] used in the `Term`.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "A B y_ z_").expect("parse of A B y_ z_");
    ///
    /// let vars = t.variables();
    /// let var_names: Vec<String> = vars.iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(var_names, vec!["y_".to_string(), "z_".to_string()]);
    /// ```
    pub fn variables(&self) -> Vec<Variable> {
        match *self {
            Term::Variable(v) => vec![v],
            Term::Application { ref args, .. } => {
                args.iter().flat_map(Term::variables).unique().collect()
            }
        }
    }
    /// Every [`Operator`] used in the `Term`.
    ///
    /// [`Operator`]: struct.Operator.html
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    ///
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "A B y_ z_").expect("parse of A B y_ z_");
    ///
    /// let ops = t.operators();
    /// let op_names: Vec<String> = ops.iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(
    ///     op_names,
    ///      vec!["A".to_string(), "B".to_string(), ".".to_string()]
    /// );
    /// ```
    pub fn operators(&self) -> Vec<Operator> {
        match *self {
            Term::Variable(_) => vec![],
            Term::Application { op, ref args } => args.iter()
                .flat_map(Term::operators)
                .chain(iter::once(op))
                .unique()
                .collect(),
        }
    }
    /// The head of the `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term, Atom};
    ///
    /// let mut sig = Signature::default();
    ///
    /// let op = sig.new_op(2, Some("A".to_string()));
    /// let t = parse_term(&mut sig, "A(B z_)").expect("parse of A(B z_)");
    ///
    /// assert_eq!(t.atoms().len(), 3);
    /// assert_eq!(t.head(), Atom::Operator(op));
    /// ```
    pub fn head(&self) -> Atom {
        match self {
            Term::Variable(v) => Atom::Variable(*v),
            Term::Application { op, .. } => Atom::Operator(*op),
        }
    }
    /// The arguments of the `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term, Atom};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "A B").expect("parse of A B");
    /// let arg0 = parse_term(&mut sig, "A").expect("parse of A");
    /// let arg1 = parse_term(&mut sig, "B").expect("parse of B");
    /// assert_eq!(t.atoms().len(), 3);
    /// assert_eq!(t.args(), vec![arg0, arg1]);
    ///
    /// let t2 = parse_term(&mut sig, "A").expect("parse of A");
    /// assert_eq!(t2.atoms().len(), 1);
    /// assert_eq!(t2.args(), vec![]);
    ///
    /// let t3 = parse_term(&mut sig, "A(y_)").expect("parse of A(y_)");
    /// let arg = Term::Variable(t3.variables()[0]);
    /// assert_eq!(t3.atoms().len(), 2);
    /// assert_eq!(t3.args(), vec![arg]);
    /// ```
    pub fn args(&self) -> Vec<Term> {
        match self {
            Term::Variable(_) => vec![],
            Term::Application { args, .. } => args.clone(),
        }
    }
    /// Every subterm and its [`Place`], starting with `self` and the empty [`Place`].
    ///
    /// [`Place`]: struct.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// let mut sig = Signature::default();
    /// let b = sig.new_op(0, Some("B".to_string()));
    /// let a = sig.new_op(1, Some("A".to_string()));
    ///
    /// let p: Vec<usize> = vec![];
    /// let p1: Vec<usize> = vec![0];
    /// let t = parse_term(&mut sig, "A(B)").expect("parse of A(B)");
    /// let subterm0 = Term::Application {
    ///     op: a,
    ///     args: vec![Term::Application {
    ///         op: b,
    ///         args: vec![],
    ///     }],
    /// };
    /// let subterm1 = Term::Application {
    ///     op: b,
    ///     args: vec![],
    /// };
    ///
    /// assert_eq!(t.subterms(), vec![(&subterm0, p), (&subterm1, p1)]);
    /// ```
    pub fn subterms(&self) -> Vec<(&Term, Place)> {
        match *self {
            Term::Variable(_) => vec![(self, vec![])],
            Term::Application { ref args, .. } => {
                let here = iter::once((self, vec![]));
                let subterms = args.iter().enumerate().flat_map(|(i, arg)| {
                    arg.subterms()
                        .into_iter()
                        .zip(iter::repeat(i))
                        .map(|((t, p), i)| {
                            let mut a = vec![i];
                            a.extend(p);
                            (t, a)
                        })
                });
                here.chain(subterms).collect()
            }
        }
    }
    /// The number of distinct [`Place`]s in the `Term`.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    ///
    /// let mut sig = Signature::default();
    /// let t = parse_term(&mut sig, "A B").expect("parse of A B");
    /// let t2 = parse_term(&mut sig, "A(B)").expect("parse of A(B)");
    ///
    /// assert_eq!(t.size(), 3);
    /// assert_eq!(t2.size(), 2);
    /// ```
    pub fn size(&self) -> usize {
        self.subterms().len()
    }
    /// Get the subterm at the given [`Place`] if possible.  Otherwise, return `None`.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    ///
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(0, Some("A".to_string()));
    /// let t = parse_term(&mut sig, "B(A)").expect("parse of B(A)");
    ///
    /// assert_eq!(t.size(), 2);
    /// let p: &[usize] = &[7];
    /// assert_eq!(t.at(p), None);
    ///
    /// let p: &[usize] = &[0];
    /// let args = vec![];
    /// assert_eq!(t.at(p), Some(&Term::Application { op, args }));
    /// ```
    #[cfg_attr(feature = "cargo-clippy", allow(ptr_arg))]
    pub fn at(&self, place: &[usize]) -> Option<&Term> {
        self.at_helper(&*place)
    }
    fn at_helper(&self, place: &[usize]) -> Option<&Term> {
        if place.is_empty() {
            Some(self)
        } else {
            match *self {
                Term::Variable(_) => None,
                Term::Application { ref args, .. } => if place[0] <= args.len() {
                    args[place[0]].at_helper(&place[1..].to_vec())
                } else {
                    None
                },
            }
        }
    }
    /// Create a copy of `self` where the term at the given [`Place`] has been replaced with
    /// `subterm`.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    ///
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "B(A)").expect("parse of B(A)");
    /// let t2 = parse_term(&mut sig, "C").expect("parse of C");
    /// let expected_term = parse_term(&mut sig, "B(C)").expect("parse of B(C)");
    ///
    /// let p: &[usize] = &[0];
    /// let new_term = t.replace(p, t2);
    ///
    /// assert_eq!(new_term, Some(expected_term));
    /// ```
    #[cfg_attr(feature = "cargo-clippy", allow(ptr_arg))]
    pub fn replace(&self, place: &[usize], subterm: Term) -> Option<Term> {
        self.replace_helper(&*place, subterm)
    }
    fn replace_helper(&self, place: &[usize], subterm: Term) -> Option<Term> {
        if place.is_empty() {
            Some(subterm)
        } else {
            match *self {
                Term::Application { op, ref args } if place[0] <= args.len() => {
                    if let Some(term) = args[place[0]].replace_helper(&place[1..].to_vec(), subterm)
                    {
                        let mut new_args = args.clone();
                        new_args.remove(place[0]);
                        new_args.insert(place[0], term);
                        Some(Term::Application { op, args: new_args })
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
    }
    /// Given a mapping from [`Variable`]s to `Term`s, perform a substitution.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// # use std::collections::HashMap;
    /// let mut sig = Signature::default();
    ///
    /// let term_before = parse_term(&mut sig, "S K y_ z_").expect("parse of S K y_ z_");
    /// let s_term = parse_term(&mut sig, "S").expect("parse of S");
    /// let k_term = parse_term(&mut sig, "K").expect("parse of K");
    ///
    /// let vars = sig.variables();
    /// let y = vars[0];
    /// let z = vars[1];
    ///
    /// let mut sub = HashMap::new();
    /// sub.insert(y, s_term);
    /// sub.insert(z, k_term);
    ///
    /// let expected_term = parse_term(&mut sig, "S K S K").expect("parse of S K S K");
    /// let subbed_term = term_before.substitute(&sub);
    ///
    /// assert_eq!(subbed_term, expected_term);
    /// ```
    pub fn substitute(&self, sub: &HashMap<Variable, Term>) -> Term {
        match *self {
            Term::Variable(ref v) => sub.get(v).unwrap_or(self).clone(),
            Term::Application { op, ref args } => Term::Application {
                op,
                args: args.iter().map(|t| t.substitute(sub)).collect(),
            },
        }
    }
    /// Take a vector of pairs of terms and perform a substitution on each term.
    fn constraint_substitute(
        cs: &[(Term, Term)],
        sub: &HashMap<Variable, Term>,
    ) -> Vec<(Term, Term)> {
        cs.iter()
            .map(|&(ref s, ref t)| (s.substitute(sub), t.substitute(sub)))
            .collect()
    }
    /// Compose two substitutions.
    fn compose(
        sub1: Option<HashMap<Variable, Term>>,
        sub2: Option<HashMap<Variable, Term>>,
    ) -> Option<HashMap<Variable, Term>> {
        match (sub1, sub2) {
            (Some(mut s1), Some(s2)) => {
                for (k, v) in s2 {
                    let v = v.substitute(&s1);
                    s1.insert(k, v);
                }
                Some(s1)
            }
            _ => None,
        }
    }
    /// Compute the [alpha equivalence] for two `Term`s.
    ///
    /// [alpha equivalence]: https://en.wikipedia.org/wiki/Lambda_calculus#Alpha_equivalence
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term, Variable};
    /// # use std::collections::{HashMap, HashSet};
    /// let mut sig = Signature::default();
    /// let s = sig.new_op(0, Some("S".to_string()));
    ///
    /// let t = parse_term(&mut sig, "S K y_ z_").expect("parse of S K y_ z_");
    /// let t2 = parse_term(&mut sig, "S K a_ b_").expect("parse of S K a_ b_");
    /// let t3 = parse_term(&mut sig, "S K y_").expect("parse of S K y_");
    ///
    /// let vars = sig.variables();
    /// let (y, z, a, b) = (vars[0], vars[1], vars[2], vars[3]);
    ///
    /// assert_eq!(y.display(&sig), "y_".to_string());
    /// assert_eq!(z.display(&sig), "z_".to_string());
    /// assert_eq!(a.display(&sig), "a_".to_string());
    /// assert_eq!(b.display(&sig), "b_".to_string());
    ///
    /// let mut expected_alpha: HashMap<Variable, Term> = HashMap::new();
    /// expected_alpha.insert(y, Term::Variable(a));
    /// expected_alpha.insert(z, Term::Variable(b));
    ///
    /// assert_eq!(Term::alpha(&t, &t2), Some(expected_alpha));
    /// assert_eq!(Term::alpha(&t, &t3), None);
    /// ```
    pub fn alpha(t1: &Term, t2: &Term) -> Option<HashMap<Variable, Term>> {
        if Term::pmatch(vec![(t2.clone(), t1.clone())]).is_some() {
            Term::pmatch(vec![(t1.clone(), t2.clone())])
        } else {
            None
        }
    }
    /// Returns whether two `Term`s are shape equivalent.
    ///
    /// Shape equivalence is where two `Term`s may not contain the same subterms, but they share the same structure(a.k.a. shape).
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "S K y_ z_").expect("parse of S K y_ z_");
    /// let t2 = parse_term(&mut sig, "A B x_ w_").expect("parse of A B x_ w_");
    /// let t3 = parse_term(&mut sig, "S K y_").expect("parse of S K y_");
    ///
    /// assert!(Term::shape_equivalent(&t, &t2));
    /// assert!(!Term::shape_equivalent(&t, &t3));
    /// ```
    pub fn shape_equivalent(t1: &Term, t2: &Term) -> bool {
        let mut vmap = HashMap::new();
        let mut omap = HashMap::new();
        Term::se_helper(t1, t2, &mut vmap, &mut omap)
    }
    fn se_helper(
        t1: &Term,
        t2: &Term,
        vmap: &mut HashMap<Variable, Variable>,
        omap: &mut HashMap<Operator, Operator>,
    ) -> bool {
        match (t1, t2) {
            (&Term::Variable(v1), &Term::Variable(v2)) => v2 == *vmap.entry(v1).or_insert(v2),
            (
                &Term::Application {
                    op: op1,
                    args: ref args1,
                },
                &Term::Application {
                    op: op2,
                    args: ref args2,
                },
            ) => {
                op2 == *omap.entry(op1).or_insert(op2)
                    && args1
                        .into_iter()
                        .zip(args2)
                        .all(|(a1, a2)| Term::se_helper(a1, a2, vmap, omap))
            }
            _ => false,
        }
    }
    /// Given a vector of contraints, return a substitution which satisfies the constrants.
    /// If the constraints are not satisfiable, return `None`. Constraints are in the form of
    /// patterns, where substitutions are only considered for variables in the first term of each
    /// pair.
    ///
    /// For more information see [`Pattern Matching`].
    ///
    /// [`Pattern Matching`]: https://en.wikipedia.org/wiki/Pattern_matching
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// # use std::collections::{HashMap, HashSet};
    ///
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "C(A)").expect("parse of C(A)");
    ///
    /// let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    ///
    /// let t3 = parse_term(&mut sig, "C(y_)").expect("parse of C(y_)");
    ///
    /// let t4 = parse_term(&mut sig, "A(x_)").expect("parse of A(x_)");
    ///
    /// assert_eq!(Term::pmatch(vec![(t, t2)]), None);
    ///
    /// # let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    /// let mut expected_sub = HashMap::new();
    /// // maps variable x in term t2 to variable y in term t3
    /// expected_sub.insert(t2.variables()[0], Term::Variable(t3.variables()[0]));
    /// assert_eq!(Term::pmatch(vec![(t2, t3)]), Some(expected_sub));
    ///
    /// # let t3 = parse_term(&mut sig, "C(y_)").expect("parse of C(y_)");
    /// assert_eq!(Term::pmatch(vec![(t3, t4)]), None);
    /// ```
    pub fn pmatch(cs: Vec<(Term, Term)>) -> Option<HashMap<Variable, Term>> {
        Term::unify_internal(cs, Unification::Match)
    }
    /// Given a vector of contraints, return a substitution which satisfies the constrants.
    /// If the constraints are not satisfiable, return `None`.
    ///
    /// For more information see [`Unification`].
    ///
    /// [`Unification`]: https://en.wikipedia.org/wiki/Unification_(computer_science)
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// # use std::collections::{HashMap, HashSet};
    ///
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "C(A)").expect("parse of C(A)");
    ///
    /// let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    ///
    /// let t3 = parse_term(&mut sig, "C(y_)").expect("parse of C(y_)");
    ///
    /// let t4 = parse_term(&mut sig, "B(x_)").expect("parse of B(x_)");
    ///
    /// let mut expected_sub = HashMap::new();
    /// // maps variable x in term t2 to constant A in term t
    /// expected_sub.insert(
    ///     t2.variables()[0],
    ///     Term::Application {
    ///         op: t.operators()[0],
    ///         args:vec![],
    ///     },
    /// );
    /// assert_eq!(Term::unify(vec![(t, t2)]), Some(expected_sub));
    ///
    /// # let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    /// let mut expected_sub = HashMap::new();
    /// // maps variable x in term t2 to variable y in term t3
    /// expected_sub.insert(t2.variables()[0], Term::Variable(t3.variables()[0]));
    /// assert_eq!(Term::unify(vec![(t2, t3)]), Some(expected_sub));
    ///
    /// # let t3 = parse_term(&mut sig, "C(y_)").expect("parse of C(y_)");
    /// assert_eq!(Term::unify(vec![(t3, t4)]), None);
    /// ```
    pub fn unify(cs: Vec<(Term, Term)>) -> Option<HashMap<Variable, Term>> {
        Term::unify_internal(cs, Unification::Unify)
    }
    /// the internal implementation of unify and match.
    fn unify_internal(
        mut cs: Vec<(Term, Term)>,
        utype: Unification,
    ) -> Option<HashMap<Variable, Term>> {
        let c = cs.pop();
        match c {
            None => Some(HashMap::new()),
            Some((ref s, ref t)) if s == t => Term::unify_internal(cs, utype),
            Some((
                Term::Application {
                    op: h1,
                    args: ref a1,
                },
                Term::Application {
                    op: h2,
                    args: ref a2,
                },
            )) if h1 == h2 =>
            {
                cs.append(&mut a1.clone().into_iter().zip(a2.clone().into_iter()).collect());
                Term::unify_internal(cs, utype)
            }
            Some((Term::Variable(var), ref t)) if !t.variables().contains(&&var) => {
                let mut st = HashMap::new();
                st.insert(var, t.clone());
                let mut cs = Term::constraint_substitute(&cs, &st);
                Term::compose(Term::unify_internal(cs, utype), Some(st))
            }
            Some((ref s, Term::Variable(var)))
                if !s.variables().contains(&&var) && utype != Unification::Match =>
            {
                let mut ts = HashMap::new();
                ts.insert(var, s.clone());
                let mut cs = Term::constraint_substitute(&cs, &ts);
                Term::compose(Term::unify_internal(cs, utype), Some(ts))
            }
            _ => None,
        }
    }
}

/// A rewrite rule equating a left-hand-side [`Term`] with one or more
/// right-hand-side [`Term`]s.
///
/// [`Term`]: enum.Term.html
///
/// # Examples
///
/// ```
/// # use term_rewriting::{Signature, Term, parse_term, Rule, parse_rule};
/// let mut sig = Signature::default();
///
/// // Constructing a Rule manually
/// let a = parse_term(&mut sig, "A(B C)").expect("parse of A(B C)");
/// let b = parse_term(&mut sig, "B").expect("parse of B");
/// let c = parse_term(&mut sig, "C").expect("parse of C");
///
/// let r = Rule::new(a, vec![b, c]);
///
/// // When constructing rules manually, keep in mind that each call to
/// // ``parse_term`` uses a distinct set of variables.
/// let x0 = parse_term(&mut sig, "x_").expect("parse of x_");
/// let x1 = parse_term(&mut sig, "x_").expect("parse of x_");
/// let vars: Vec<_> = sig.variables().into_iter().map(Term::Variable).collect();
///
/// assert_eq!(x0, vars[0]);
/// assert_eq!(x1, vars[1]);
/// assert_ne!(x0, x1);
///
/// // Constructing a Rule using parser
/// let r = parse_rule(&mut sig, "A(x_ y_) = B(x_) | C(y)").expect("parse of A(x_ y_) = B(x_) | C(y_)");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Rule {
    /// The left hand side (lhs) of the Rule.
    pub lhs: Term,
    /// The right hand sides (rhs) of the Rule.
    pub rhs: Vec<Term>,
}
impl Rule {
    /// A serialized representation of the Rule.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, Term, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A = B").expect("parse of A = B");
    ///
    /// assert_eq!(r.display(&sig), "A = B");
    ///
    /// let r = parse_rule(&mut sig, "A(x_) = B | C(x_)").expect("parse of A(x_) = B | C(x_)");
    ///
    /// assert_eq!(r.display(&sig), "A(x_) = B | C(x_)");
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        let lhs_str = self.lhs.display(sig);
        let rhs_str = self.rhs.iter().map(|rhs| rhs.display(sig)).join(" | ");
        format!("{} = {}", lhs_str, rhs_str)
    }
    /// A human-readable serialization of the Rule.
    pub fn pretty(&self, sig: &Signature) -> String {
        let lhs_str = self.lhs.pretty(sig);
        let rhs_str = self.rhs.iter().map(|rhs| rhs.pretty(sig)).join(" | ");
        format!("{} = {}", lhs_str, rhs_str)
    }
    /// The total number of subterms across all [`Term`]s in the `Rule`.
    ///
    /// [`Term`]: struct.Term.html
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, Term, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");
    ///
    /// assert_eq!(r.size(), 5);
    /// ```
    pub fn size(&self) -> usize {
        self.lhs.size() + self.rhs.iter().map(Term::size).sum::<usize>()
    }
    /// The number of RHSs in the `Rule`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, Term, parse_rule};
    /// let mut sig = Signature::default();
    /// let r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");
    ///
    /// assert_eq!(r.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.rhs.len()
    }
    /// Is the `Rule` empty?
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, Term, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");
    ///
    /// assert!(!r.is_empty());
    ///
    /// let lhs = parse_term(&mut sig, "A").expect("parse of A");
    /// let rhs : Vec<Term> = vec![];
    /// let r = Rule::new(lhs, rhs).unwrap();
    ///
    /// assert!(r.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.rhs.is_empty()
    }
    /// The lone RHS, if it exists. Otherwise, return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, Term, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A = B").expect("parse of A = B");
    /// let b = parse_term(&mut sig, "B").expect("parse of B");
    ///
    /// assert_eq!(r.rhs().unwrap(), b);
    ///
    /// let r = parse_rule(&mut sig, "A = B | C").expect("parse of A = B | C");
    ///
    /// assert_eq!(r.rhs(), Option::None);
    /// ```
    pub fn rhs(&self) -> Option<Term> {
        if self.rhs.len() == 1 {
            Some(self.rhs[0].clone())
        } else {
            None
        }
    }
    /// A list of the clauses in the `Rule`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, Term, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A = B").expect("parse of A = B");
    ///
    /// assert_eq!(r.clauses(), vec![r]);
    ///
    /// let r = parse_rule(&mut sig, "A = B | C").expect("parse of A = B | C");
    /// let r1 = parse_rule(&mut sig, "A = B").expect("parse of A = B");
    /// let r2 = parse_rule(&mut sig, "A = C").expect("parse of A = C");
    ///
    /// assert_eq!(r.clauses(), vec![r1, r2]);
    /// ```
    pub fn clauses(&self) -> Vec<Rule> {
        self.rhs
            .iter()
            .map(|rhs| Rule::new(self.lhs.clone(), vec![rhs.clone()]).unwrap())
            .collect()
    }
    /// logic ensuring that the `lhs` and `rhs` are compatible.
    fn is_valid(lhs: &Term, rhs: &[Term]) -> bool {
        // the lhs must be an application
        if let Term::Application { .. } = *lhs {
            // variables(rhs) must be a subset of variables(lhs)
            let lhs_vars: HashSet<_> = lhs.variables().into_iter().collect();
            let rhs_vars: HashSet<_> = rhs.iter().flat_map(Term::variables).collect();
            rhs_vars.is_subset(&lhs_vars)
        } else {
            false
        }
    }
    /// Construct a rewrite `Rule` from a left-hand-side (LHS) [`Term`] with one
    /// or more right-hand-side (RHS) [`Term`]s. Return `None` if the `Rule` is
    /// not valid.
    ///
    /// Valid rules meet two conditions:
    ///
    /// 1. `lhs` is an [`Application`]. This prevents a single rule from
    ///    matching all possible [`Term`]s
    /// 2. A [`Term`] in `rhs` can only use a [`Variable`] if it appears in
    ///    `lhs`. This prevents rewrites from inventing arbitrary [`Term`]s.
    ///
    /// [`Term`]: enum.Term.html
    /// [`Application`]: enum.Term.html#variant.Application
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let lhs = parse_term(&mut sig, "A").expect("parse of A");
    /// let rhs = vec![parse_term(&mut sig, "B").expect("parse of B")];
    /// let r = Rule::new(lhs, rhs).unwrap();
    ///
    /// let r2 = parse_rule(&mut sig, "A = B").expect("parse of A = B");
    ///
    /// assert_eq!(r, r2);
    ///
    /// let left = parse_term(&mut sig, "A").expect("parse of A");
    /// let right = vec![parse_term(&mut sig, "B").expect("parse of B")];
    /// let r2 = Rule { lhs: left, rhs: right };
    ///
    /// assert_eq!(r, r2);
    /// ```
    pub fn new(lhs: Term, rhs: Vec<Term>) -> Option<Rule> {
        if Rule::is_valid(&lhs, &rhs) {
            Some(Rule { lhs, rhs })
        } else {
            None
        }
    }
    /// Add a clause to the `Rule` from a [`Term`].
    ///
    /// [`Term`]: enum.Term.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let c = parse_term(&mut sig, "C").expect("parse of C");
    /// let mut r = parse_rule(&mut sig, "A = B").expect("parse of A = B");
    ///
    /// assert_eq!(r.display(&sig), "A = B");
    ///
    /// r.add(c);
    ///
    /// assert_eq!(r.display(&sig), "A = B | C");
    /// ```
    pub fn add(&mut self, t: Term) {
        let self_vars = self.lhs.variables();
        if t.variables().iter().all(|x| self_vars.contains(x)) {
            self.rhs.push(t)
        }
    }
    /// Add clauses to the `Rule` from another `Rule`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut r = parse_rule(&mut sig, "A = B").expect("parse A = B");
    /// let r2 = parse_rule(&mut sig, "A = C").expect("parse A = C");
    /// r.merge(&r2);
    ///
    /// assert_eq!(r.display(&sig), "A = B | C");
    /// ```
    pub fn merge(&mut self, r: &Rule) {
        if let Some(s) = Term::alpha(&self.lhs, &r.lhs) {
            for rhs in r.rhs.clone() {
                self.rhs.push(rhs.substitute(&s));
            }
        }
    }
    /// Discard clauses from the `Rule`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");
    /// let mut r2 = parse_rule(&mut sig, "A(y_) = B(y_)").expect("parse of A(y_) = B(y_)");
    /// r.discard(&r2);
    ///
    /// assert_eq!(r.display(&sig), "A(x_) = C");
    /// ```
    pub fn discard(&mut self, r: &Rule) -> Option<Rule> {
        if let Some(sub) = Term::alpha(&r.lhs, &self.lhs) {
            let terms = r.rhs
                .iter()
                .map(|rhs| rhs.substitute(&sub))
                .collect::<Vec<Term>>();
            self.rhs.retain(|x| !terms.contains(x));
            let lhs = r.lhs.substitute(&sub);
            Some(Rule::new(lhs, terms).unwrap())
        } else {
            None
        }
    }
    /// Check whether the `Rule` contains certain clauses, and if so, return the alpha-equivalence mapping.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_rule};
    /// # use std::collections::HashMap;
    /// let mut sig = Signature::default();
    ///
    /// let mut r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");
    /// let mut r2 = parse_rule(&mut sig, "A(y_) = B(y_)").expect("parse of A(y_) = B(y_)");
    ///
    /// assert_eq!(r2.contains(&r), None);
    ///
    /// let mut sub = HashMap::default();
    /// let x = r.variables()[0];
    /// let y = r2.variables()[0];
    /// sub.insert(y, Term::Variable(x));
    ///
    /// assert_eq!(r.contains(&r2).unwrap(), sub);
    /// ```
    pub fn contains(&self, r: &Rule) -> Option<HashMap<Variable, Term>> {
        if let Some(sub) = Term::alpha(&r.lhs, &self.lhs) {
            if r.rhs
                .iter()
                .all(|rhs| self.rhs.contains(&rhs.substitute(&sub)))
            {
                Some(sub)
            } else {
                None
            }
        } else {
            None
        }
    }
    /// All the [`Variable`]s in the `Rule`.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A(x_) = C(x_)").expect("parse of A(x_) = C(x_)");
    /// let r_variables: Vec<String> = r.variables().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(r_variables, vec!["x_"]);
    ///
    /// let r = parse_rule(&mut sig, "B(y_ z_) = C").expect("parse of B(y_ z_) = C");
    /// let r_variables: Vec<String> = r.variables().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(r_variables, vec!["y_", "z_"]);
    /// ```
    pub fn variables(&self) -> Vec<Variable> {
        self.lhs.variables()
    }
    /// All the [`Operator`]s in the `Rule`.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A(D E) = C").expect("parse of A(D E) = C");
    /// let r_ops: Vec<String> = r.operators().iter().map(|o| o.display(&sig)).collect();
    ///
    /// assert_eq!(r_ops, vec!["D", "E", "A", "C"]);
    ///
    /// let r = parse_rule(&mut sig, "B(F x_) = C").expect("parse of B(F x_) = C");
    /// let r_ops: Vec<String> = r.operators().iter().map(|o| o.display(&sig)).collect();
    ///
    /// assert_eq!(r_ops, vec!["F", "B", "C"]);
    /// ```
    pub fn operators(&self) -> Vec<Operator> {
        let lhs = self.lhs.operators().into_iter();
        let rhs = self.rhs.iter().flat_map(Term::operators);
        lhs.chain(rhs).unique().collect()
    }
    /// All the subterms and places in a `Rule`.
    ///
    /// See [`Term`] for more information.
    ///
    /// [`Term`]: enum.Term.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r =
    ///     parse_rule(&mut sig, "A(x_ B) = C(x_) | D(B)").expect("parse of A(x_ B) = C(x_) | D(B)");
    ///
    /// let subterms: Vec<String> = r.subterms()
    ///     .iter()
    ///     .map(|(i, t, p)| format!("{},Subterm:{},Place:{:?}", i, t.display(&sig), p))
    ///     .collect();
    ///
    /// assert_eq!(
    ///     subterms,
    ///     vec![
    ///         "0,Subterm:A(x_ B),Place:[]",
    ///         "0,Subterm:x_,Place:[0]",
    ///         "0,Subterm:B,Place:[1]",
    ///         "1,Subterm:C(x_),Place:[]",
    ///         "1,Subterm:x_,Place:[0]",
    ///         "2,Subterm:D(B),Place:[]",
    ///         "2,Subterm:B,Place:[0]",
    ///     ]
    /// );
    /// ```
    pub fn subterms(&self) -> Vec<(usize, &Term, Place)> {
        let lhs = self.lhs.subterms().into_iter().map(|(t, p)| (0, t, p));
        let rhs = self.rhs.iter().enumerate().flat_map(|(i, rhs)| {
            iter::repeat(i + 1)
                .zip(rhs.subterms())
                .into_iter()
                .map(|(i, (t, p))| (i, t, p))
        });
        lhs.chain(rhs).collect()
    }
    /// Get a specific subterm in a `Rule`.
    ///
    /// See [`Term::at`] for more information.
    ///
    /// [`Term::at`]: enum.Term.html#method.at
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Rule, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A(x_) = B | C(x_)").expect("parse of A(x_) = B | C(x_)");
    ///
    /// assert_eq!(r.at(&[0]).unwrap().display(&sig), "A(x_)");
    /// assert_eq!(r.at(&[0,0]).unwrap().display(&sig), "x_");
    /// assert_eq!(r.at(&[1]).unwrap().display(&sig), "B");
    /// assert_eq!(r.at(&[2]).unwrap().display(&sig), "C(x_)");
    /// ```
    pub fn at(&self, p: &[usize]) -> Option<&Term> {
        if p[0] == 0 {
            self.lhs.at(&p[1..].to_vec())
        } else {
            self.rhs[p[0] - 1].at(&p[1..].to_vec())
        }
    }
    /// Replace one subterm with another in a `Rule`.
    /// Returns a new `Rule` without changing the original.
    ///
    /// See [`Term::at`] for more information.
    ///
    /// [`Term::at`]: enum.Term.html#method.at
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term, parse_rule, Rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut r = parse_rule(&mut sig, "A(x_) = B | C(x_)").expect("parse of A(x_) = B| C(x_)");
    /// let new_term = parse_term(&mut sig, "E").expect("parse of E");
    /// let new_rule = r.replace(&[1], new_term);
    ///
    /// assert_ne!(r, new_rule.clone().unwrap());
    ///
    /// assert_eq!(new_rule.unwrap().display(&sig), "A(x_) = E | C(x_)");
    /// ```
    pub fn replace(&self, place: &[usize], subterm: Term) -> Option<Rule> {
        if place[0] == 0 {
            if let Some(lhs) = self.lhs.replace(&place[1..].to_vec(), subterm) {
                Rule::new(lhs, self.rhs.clone())
            } else {
                None
            }
        } else if let Some(an_rhs) = self.rhs[place[0] - 1].replace(&place[1..].to_vec(), subterm) {
            let mut rhs = self.rhs.clone();
            rhs.remove(place[0] - 1);
            rhs.insert(place[0] - 1, an_rhs);
            Rule::new(self.lhs.clone(), rhs)
        } else {
            None
        }
    }
    /// [`Pattern Match`] one `Rule` against another.
    ///
    /// [`Pattern Match`]: https://en.wikipedia.org/wiki/Pattern_matching
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, parse_rule, Term, parse_term};
    /// # use std::collections::HashMap;
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A(x_) = B").expect("parse of A(x_) = B");
    /// let r2 = parse_rule(&mut sig, "A(y_) = y_").expect("parse of A(y_) = y_");
    /// let r3 = parse_rule(&mut sig, "A(z_) = C").expect("parse of A(z_) = C");
    /// let r4 = parse_rule(&mut sig, "D(w_) = B").expect("parse of D(w_) = B");
    /// let r5 = parse_rule(&mut sig, "A(t_) = B").expect("parse of A(t_) = B");
    ///
    /// assert_eq!(Rule::pmatch(r.clone(), r2), None);
    /// assert_eq!(Rule::pmatch(r.clone(), r3), None);
    /// assert_eq!(Rule::pmatch(r.clone(), r4), None);
    ///
    /// let mut expected_map = HashMap::default();
    /// expected_map.insert(
    ///     r.clone().variables()[0],
    ///     Term::Variable(r5.clone().variables()[0]),
    /// );
    ///
    /// assert_eq!(Rule::pmatch(r, r5), Some(expected_map));
    /// ```
    pub fn pmatch(r1: Rule, r2: Rule) -> Option<HashMap<Variable, Term>> {
        let cs = iter::once((r1.lhs, r2.lhs)).chain(r1.rhs.into_iter().zip(r2.rhs));
        Term::pmatch(cs.collect())
    }
    /// [`Unify`] two [`Rule`]s.
    ///
    /// [`Unify`]: https://en.wikipedia.org/wiki/Unification_(computer_science)
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, parse_rule, Term, parse_term};
    /// # use std::collections::HashMap;
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A(x_) = B").expect("parse of A(x_) = B");
    /// let r2 = parse_rule(&mut sig, "A(y_) = y_").expect("parse of A(y_) = y_");
    /// let r3 = parse_rule(&mut sig, "A(z_) = C").expect("parse of A(z_) = C");
    /// let r4 = parse_rule(&mut sig, "D(w_) = B").expect("parse of D(w_) = B");
    /// let r5 = parse_rule(&mut sig, "A(t_) = B").expect("parse of A(t_) = B");
    ///
    /// let b = parse_term(&mut sig, "B").expect("parse of B");
    /// let mut expected_map = HashMap::default();
    /// expected_map.insert(r.clone().variables()[0], b.clone());
    /// expected_map.insert(r2.clone().variables()[0], b);
    ///
    /// assert_eq!(Rule::unify(r.clone(), r2), Some(expected_map));
    ///
    /// assert_eq!(Rule::unify(r.clone(), r3), None);
    /// assert_eq!(Rule::unify(r.clone(), r4), None);
    ///
    /// let mut expected_map = HashMap::default();
    /// expected_map.insert(
    ///     r.clone().variables()[0],
    ///     Term::Variable(r5.clone().variables()[0]),
    /// );
    ///
    /// assert_eq!(Rule::unify(r, r5), Some(expected_map));
    /// ```
    pub fn unify(r1: Rule, r2: Rule) -> Option<HashMap<Variable, Term>> {
        let cs = iter::once((r1.lhs, r2.lhs)).chain(r1.rhs.into_iter().zip(r2.rhs));
        Term::unify(cs.collect())
    }
    /// Compute the [`Alpha Equivalence`] between two `Rule`s.
    ///
    /// [`Alpha Equivalence`]: https://en.wikipedia.org/wiki/lambda_calculus#Alpha_equivalence
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, parse_rule, Term, parse_term};
    /// # use std::collections::HashMap;
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rule(&mut sig, "A(x_) = B").expect("parse of A(x_) = B");
    /// let r2 = parse_rule(&mut sig, "A(y_) = y_").expect("parse of A(y_) = y_");
    /// let r3 = parse_rule(&mut sig, "A(z_) = C").expect("parse of A(z_) = C");
    /// let r4 = parse_rule(&mut sig, "D(w_) = B").expect("parse of D(w_) = B");
    /// let r5 = parse_rule(&mut sig, "A(t_) = B").expect("parse of A(t_) = B");
    ///
    /// assert_eq!(Rule::alpha(&r, &r2), None);
    /// assert_eq!(Rule::alpha(&r, &r3), None);
    /// assert_eq!(Rule::alpha(&r, &r4), None);
    ///
    /// let mut expected_map = HashMap::default();
    /// expected_map.insert(
    ///     r.clone().variables()[0],
    ///     Term::Variable(r5.clone().variables()[0])
    /// );
    ///
    /// assert_eq!(Rule::alpha(&r, &r5), Some(expected_map));
    /// ```
    pub fn alpha(r1: &Rule, r2: &Rule) -> Option<HashMap<Variable, Term>> {
        if Rule::pmatch(r2.clone(), r1.clone()).is_some() {
            Rule::pmatch(r1.clone(), r2.clone())
        } else {
            None
        }
    }
    /// Substitute through a `Rule`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, parse_rule, Term, parse_term};
    /// # use std::collections::HashMap;
    /// let mut sig = Signature::default();
    ///
    /// let mut r = parse_rule(&mut sig, "A(x_ y_) = A(x_) | B(y_)").expect("parse of A(x_ y_) = A(x_) | B(y_)");
    /// let c = parse_term(&mut sig, "C").expect("parse of C");
    /// let vars = r.variables();
    /// let (x, y) = (vars[0], vars[1]);
    ///
    /// let mut substitution = HashMap::default();
    /// substitution.insert(x, c);
    ///
    /// let r2 = r.substitute(&substitution);
    ///
    /// assert_eq!(r2.display(&sig), "A(C y_) = A(C) | B(y_)");
    /// ```
    pub fn substitute(&self, sub: &HashMap<Variable, Term>) -> Rule {
        Rule::new(
            self.lhs.substitute(sub),
            self.rhs.iter().map(|rhs| rhs.substitute(sub)).collect(),
        ).unwrap()
    }
}

/// A [`Rule`] with [`Hole`]s; a sort of [`Rule`] template.
///
/// See [`Context`] for more information.
///
/// [`Context`]: enum.Context.html
/// [`Rule`]: struct.Rule.html
/// [`Hole`]: enum.Context.html#variant.Hole
///
/// # Examples
///
/// ```
/// # use term_rewriting::{Signature, parse_rulecontext, RuleContext, Context, parse_context};
/// let mut sig = Signature::default();
///
/// // Constructing a RuleContext manually.
/// let left = parse_context(&mut sig, "A(B C [!])").expect("parse of A(B C [!])");
/// let b = parse_context(&mut sig, "B [!]").expect("parse of B [!]");
/// let c = parse_context(&mut sig, "C").expect("parse of C");
///
/// let r = RuleContext::new(left, vec![b, c]).unwrap();
///
/// // Constructing a RuleContext using the parser.
/// let r2 = parse_rulecontext(&mut sig, "A(B C [!]) = B [!] | C").expect("parse of A(B C [!]) = B [!] | C");
///
/// assert_eq!(r, r2);
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RuleContext {
    /// The left hand side (lhs) of a RuleContext.
    pub lhs: Context,
    /// The right hand sides (rhs) of a RuleContext.
    pub rhs: Vec<Context>,
}
impl RuleContext {
    /// Create a new `RuleContext` if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, RuleContext, parse_context};
    /// let mut sig = Signature::default();
    ///
    /// let left = parse_context(&mut sig, "A(B C [!])").expect("parse of A(B C [!])");
    /// let b = parse_context(&mut sig, "B [!]").expect("parse of B [!]");
    /// let c = parse_context(&mut sig, "C").expect("parse of C");
    ///
    /// let r = RuleContext::new(left, vec![b, c]).unwrap();
    ///
    /// assert_eq!(r.pretty(&sig), "A(B, C, [!]) = B [!] | C");
    /// ```
    pub fn new(lhs: Context, rhs: Vec<Context>) -> Option<RuleContext> {
        if RuleContext::is_valid(&lhs, &rhs) {
            Some(RuleContext { lhs, rhs })
        } else {
            None
        }
    }
    /// Could `lhs` and `rhs` form a valid `RuleContext`?
    fn is_valid(lhs: &Context, rhs: &[Context]) -> bool {
        // the lhs must be an application
        if let Context::Variable(_) = *lhs {
            false
        } else {
            // variables(rhs) must be a subset of variables(lhs)
            let lhs_vars: HashSet<_> = lhs.variables().into_iter().collect();
            let rhs_vars: HashSet<_> = rhs.iter().flat_map(Context::variables).collect();
            rhs_vars.is_subset(&lhs_vars)
        }
    }
    /// A human-readable serialization of the `RuleContext`.
    pub fn pretty(&self, sig: &Signature) -> String {
        let lhs_str = self.lhs.pretty(sig);
        let rhs_str = self.rhs.iter().map(|rhs| rhs.pretty(sig)).join(" | ");
        format!("{} = {}", lhs_str, rhs_str)
    }
    /// Get all the [`subcontexts`] and [`Place`]s in a `RuleContext`.
    ///
    /// [`Subcontexts`]: struct.Context.html
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, RuleContext, Context, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let r =
    ///     parse_rulecontext(&mut sig, "A(x_ [!]) = C(x_) | D([!])").expect("parse of A(x_ B[!]) = C(x_) | D([!])");
    ///
    /// let subcontexts: Vec<String> = r.subcontexts()
    ///     .iter()
    ///     .map(|(c, p)| format!("Subcontext:{},Place:{:?}", c.display(&sig), p))
    ///     .collect();
    ///
    /// assert_eq!(
    ///     subcontexts,
    ///     vec![
    ///         "Subcontext:A(x_ [!]),Place:[0]",
    ///         "Subcontext:x_,Place:[0, 0]",
    ///         "Subcontext:[!],Place:[0, 1]",
    ///         "Subcontext:C(x_),Place:[1]",
    ///         "Subcontext:x_,Place:[1, 0]",
    ///         "Subcontext:D([!]),Place:[2]",
    ///         "Subcontext:[!],Place:[2, 0]",
    ///     ]
    /// );
    /// ```
    pub fn subcontexts(&self) -> Vec<(&Context, Place)> {
        let lhs = self.lhs.subcontexts().into_iter().map(|(t, mut p)| {
            p.insert(0, 0);
            (t, p)
        });
        let rhs = self.rhs.iter().enumerate().flat_map(|(i, rhs)| {
            iter::repeat(i + 1)
                .zip(rhs.subcontexts())
                .into_iter()
                .map(|(i, (t, mut p))| {
                    p.insert(0, i);
                    (t, p)
                })
        });
        lhs.chain(rhs).collect()
    }
    /// The [`Place`]s of all of the [`Hole`]s in the `RuleContext`.
    ///
    /// [`Place`]: type.Place.html
    /// [`Hole`]: enum.Context.html#variant.Hole
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, RuleContext, Context, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let r =
    ///     parse_rulecontext(&mut sig, "A(x_ [!]) = C(x_) | D([!])").expect("parse of A(x_ B[!]) = C(x_) | D([!])");
    ///
    /// let p: &[usize] = &[0, 1];
    /// let p2: &[usize] = &[2, 0];
    ///
    /// assert_eq!(r.holes(), vec![p, p2]);
    /// ```
    pub fn holes(&self) -> Vec<Place> {
        self.subcontexts()
            .into_iter()
            .filter_map(|(t, p)| match *t {
                Context::Hole => Some(p),
                _ => None,
            })
            .collect()
    }
    /// All the [`Variables`] in a `RuleContext`.
    ///
    /// [`Variables`]: struct.Variables.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, RuleContext, parse_context, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rulecontext(&mut sig, "A(x_ [!]) = C(x_)").expect("parse of A(x_ [!]) = C(x_)");
    /// let r_variables: Vec<String> = r.variables().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(r_variables, vec!["x_"]);
    ///
    /// let r = parse_rulecontext(&mut sig, "B(y_ z_) = C [!]").expect("parse of B(y_ z_) = C [!]");
    /// let r_variables: Vec<String> = r.variables().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(r_variables, vec!["y_", "z_"]);
    /// ```
    pub fn variables(&self) -> Vec<Variable> {
        self.lhs.variables()
    }
    /// All the [`Operators`] in a `RuleContext`.
    ///
    /// [`Operators`]: struct.Operators.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, RuleContext, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rulecontext(&mut sig, "A(D E) = C([!])").expect("parse of A(D E) = C([!])");
    /// let r_ops: Vec<String> = r.operators().iter().map(|o| o.display(&sig)).collect();
    ///
    /// assert_eq!(r_ops, vec!["D", "E", "A", "C"]);
    ///
    /// let r = parse_rulecontext(&mut sig, "B(F x_) = C [!]").expect("parse of B(F x_) = C [!]");
    /// let r_ops: Vec<String> = r.operators().iter().map(|o| o.display(&sig)).collect();
    ///
    /// assert_eq!(r_ops, vec!["F", "B", "C", "."]);
    /// ```
    pub fn operators(&self) -> Vec<Operator> {
        let lhs = self.lhs.operators().into_iter();
        let rhs = self.rhs.iter().flat_map(Context::operators);
        lhs.chain(rhs).unique().collect()
    }
    /// Get a specific [`subcontext`] in a `RuleContext`.
    ///
    /// [`subcontext`]: struct.Context.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rulecontext(&mut sig, "A(x_ [!]) = B | C(x_ [!])").expect("parse of A(x_ [!]) = B | C(x_ [!])");
    ///
    /// assert_eq!(r.at(&[0]).unwrap().display(&sig), "A(x_ [!])");
    /// assert_eq!(r.at(&[0,1]).unwrap().display(&sig), "[!]");
    /// assert_eq!(r.at(&[0,0]).unwrap().display(&sig), "x_");
    /// assert_eq!(r.at(&[1]).unwrap().display(&sig), "B");
    /// assert_eq!(r.at(&[2]).unwrap().display(&sig), "C(x_ [!])");
    /// ```
    pub fn at(&self, p: &[usize]) -> Option<&Context> {
        if p[0] == 0 {
            self.lhs.at(&p[1..].to_vec())
        } else {
            self.rhs[p[0] - 1].at(&p[1..].to_vec())
        }
    }
    /// Replace one [`subcontext`] with another [`Context`].
    ///
    /// [`subcontext`]: struct.Context.html
    /// [`Context`]: struct.Context.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_rulecontext, parse_context};
    /// let mut sig = Signature::default();
    ///
    /// let mut r = parse_rulecontext(&mut sig, "A(x_) = B | C(x_) | [!]").expect("parse of A(x_) = B| C(x_) | [!]");
    /// let new_context = parse_context(&mut sig, "E [!]").expect("parse of E [!]");
    /// let new_r = r.replace(&[1], new_context);
    ///
    /// assert_ne!(r, new_r.clone().unwrap());
    /// assert_eq!(new_r.unwrap().pretty(&sig), "A(x_) = E [!] | C(x_) | [!]");
    /// ```
    pub fn replace(&self, place: &[usize], subcontext: Context) -> Option<RuleContext> {
        if place[0] == 0 {
            if let Some(lhs) = self.lhs.replace(&place[1..].to_vec(), subcontext) {
                Some(RuleContext {
                    lhs,
                    rhs: self.rhs.clone(),
                })
            } else {
                None
            }
        } else if let Some(an_rhs) =
            self.rhs[place[0] - 1].replace(&place[1..].to_vec(), subcontext)
        {
            let mut rhs = self.rhs.clone();
            rhs.remove(place[0] - 1);
            rhs.insert(place[0] - 1, an_rhs);
            Some(RuleContext {
                lhs: self.lhs.clone(),
                rhs,
            })
        } else {
            None
        }
    }
    /// Convert a `RuleContext` to a [`Rule`] if possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let r = parse_rulecontext(&mut sig, "A(x_ [!]) = B | C(x_ [!])").expect("parse of A(x_ [!]) = B | C(x_ [!])");
    ///
    /// assert!(r.to_rule().is_err());
    ///
    /// let r = parse_rulecontext(&mut sig, "A(x_) = B | C(x_)").expect("parse of A(x_) = B | C(x_)");
    /// let rule = r.to_rule().expect("converting RuleContext to Rule");
    ///
    /// assert_eq!(rule.pretty(&sig), "A(x_) = B | C(x_)");
    /// ```
    pub fn to_rule(&self) -> Result<Rule, ()> {
        let lhs = self.lhs.to_term()?;
        let rhs = self.rhs
            .iter()
            .map(|rhs| rhs.to_term())
            .collect::<Result<_, _>>()?;
        Rule::new(lhs, rhs).ok_or(())
    }
}

/// A first-order term rewriting system.
/// # Examples
///
/// ```
/// # use term_rewriting::{Signature, Rule, parse_rule, TRS, parse_trs};
/// let mut sig = Signature::default();
///
/// // Constructing a TRS manually
/// let r0 = parse_rule(&mut sig, "A(x_) = A(B)").expect("parse of A(x_) = A(B)");
/// let r1 = parse_rule(&mut sig, "B = C | D").expect("parse of B = C | D");
/// let r2 = parse_rule(&mut sig, "E(F) = G").expect("parse of E(F) = G");
///
/// let t = TRS::new(vec![r0, r1, r2]);
///
/// // Constructing a TRS using the parser
/// let t = parse_trs(&mut sig, "A(x_) = A(B);\nB = C | D;\nE(F) = G;")
///     .expect("parse of A(x_) = A(B); B = C | D; E(F) = G;");
///
/// // For better readability of the TRS
/// let t = parse_trs(&mut sig,
/// "A(x_) = A(B);
/// B = C | D;
/// E(F) = G;").expect("parse of A(x_) = A(B); B = C | D; E(F) = G;");
/// ```
#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct TRS {
    is_deterministic: bool,
    pub rules: Vec<Rule>,
}
impl TRS {
    /// Constructs a [`Term Rewriting System`] from a list of [`Rule`]s.
    ///
    /// [`Rule`]: struct.Rule.html
    /// [`Term Rewriting System`]: https://en.wikipedia.ord/wiki/Rewriting#Term_rewriting_systems
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, parse_rule, TRS};
    /// let mut sig = Signature::default();
    ///
    /// let r0 = parse_rule(&mut sig, "A = B").expect("parse of A = B");
    /// let r1 = parse_rule(&mut sig, "C(x_) = x_").expect("parse of C(x_) = x_");
    /// let r2 = parse_rule(&mut sig, "D(y_) = D(E)").expect("parse of D(y_) = D(E)");
    /// let new_trs = TRS::new(vec![r0, r1, r2]);
    ///
    /// assert_eq!(new_trs.display(&sig),
    /// "A = B;
    /// C(x_) = x_;
    /// D(y_) = D(E);"
    /// );
    /// ```
    pub fn new(rules: Vec<Rule>) -> TRS {
        TRS {
            rules,
            is_deterministic: false,
        }
    }
    /// Make `self` [`deterministic`] and restrict it to be so until further notice.
    ///
    /// Return `true` if `self` was changed, otherwise `false`.
    ///
    /// [`deterministic`]: http://en.wikipedia.org/wiki/Deterministic_system
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate term_rewriting;
    /// # fn main(){
    /// # use term_rewriting::{Signature, Rule, parse_rule, TRS, parse_trs};
    /// # use rand::{thread_rng,Rng};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B | C;
    /// D = E;").expect("parse of A = B | C; D = E");
    /// let mut r = rand::thread_rng();
    ///
    /// let str_before = t.display(&sig);
    ///
    /// assert!(t.make_deterministic(& mut r));
    ///
    /// assert_ne!(t.display(&sig), str_before);
    ///
    /// let str_before = t.display(&sig);
    /// let r = parse_rule(&mut sig, "C = B | D").expect("parse of C = B | D");
    ///
    /// if t.insert_idx(1, r.clone()).is_err() {
    ///     assert!(true);
    /// }
    ///
    /// assert_eq!(str_before, t.display(&sig));
    ///
    /// assert!((t.display(&sig) ==
    /// "A = B;
    /// D = E;") ||
    ///     (t.display(&sig) ==
    /// "A = C;
    /// D = E;"));
    /// # }
    /// ```
    pub fn make_deterministic<R: Rng>(&mut self, rng: &mut R) -> bool {
        if !self.is_deterministic {
            self.rules = self.rules
                .iter()
                .cloned()
                .map(|r| {
                    let new_rhs = sample_iter(rng, r.rhs, 1).expect("sample_iter failed.");
                    Rule::new(r.lhs, new_rhs).expect("making new rule from old rule failed")
                })
                .collect();
            self.is_deterministic = true;
            true
        } else {
            false
        }
    }
    /// Remove any [`determinism`] restriction `self` might be under.
    ///
    /// Return `true` if `self` was changed, otherwise `false`.
    ///
    /// See [`determinism`] for more information.
    ///
    /// [`Deterministic System`]: http://en.wikipedia.org/wiki/Deterministic_system
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate term_rewriting;
    /// # fn main(){
    /// # use term_rewriting::{Signature, Rule, parse_rule, TRS, parse_trs, TRSError};
    /// # use rand::{thread_rng,Rng};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B | C;
    /// D = E;").expect("parse of A = B | C; D = E");
    /// let mut r = rand::thread_rng();
    ///
    /// t.make_deterministic(& mut r);
    ///
    /// let str_before = t.display(&sig);
    /// let r = parse_rule(&mut sig, "C = B | D").expect("parse of C = B | D");
    /// assert!(t.insert_idx(1, r.clone()).is_err());
    /// assert_eq!(str_before, t.display(&sig));
    ///
    /// assert!(t.make_nondeterministic());
    ///
    /// t.insert_idx(1, r).expect("inserting C = B | D");
    ///
    /// assert!((t.display(&sig) ==
    /// "A = B;
    /// C = B | D;
    /// D = E;") ||
    ///     (t.display(&sig) ==
    /// "A = C;
    /// C = B | D;
    /// D = E;"));
    /// # }
    /// ```
    pub fn make_nondeterministic(&mut self) -> bool {
        let previous_state = self.is_deterministic;
        self.is_deterministic = false;
        previous_state
    }
    /// Report whether `self` is currently deterministic.
    ///
    /// See [`Deterministic System`] for more information.
    ///
    /// [`Deterministic System`]: http://en.wikipedia.org/wiki/Deterministic_system
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate term_rewriting;
    /// # fn main(){
    /// # use term_rewriting::{Signature, Rule, parse_rule, TRS, parse_trs};
    /// # use rand::{thread_rng,Rng};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B | C;
    /// D = E;").expect("parse of A = B | C; D = E");
    /// let mut r = rand::thread_rng();
    ///
    /// assert!(!t.is_deterministic());
    ///
    /// t.make_deterministic(& mut r);
    ///
    /// assert!(t.is_deterministic());
    /// # }
    /// ```
    pub fn is_deterministic(&self) -> bool {
        self.is_deterministic
    }
    /// The number of [`Rule`]s in the `TRS`.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// assert_eq!(t.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.rules.len()
    }
    /// Are there any [`Rule`]s in the `TRS`?
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// assert!(!t.is_empty());
    ///
    /// let t = parse_trs(&mut sig, "").expect("parse of blank string");
    ///
    /// assert!(t.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
    /// Return the number of total number of subterms across all [`Rule`]s in the `TRS`.
    ///
    /// See [`Term`] for more information.
    ///
    /// [`Term`]: struct.Term.html
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// assert_eq!(t.size(), 8);
    /// ```
    pub fn size(&self) -> usize {
        self.rules.iter().map(Rule::size).sum()
    }
    /// A serialized representation of the `TRS`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;");
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        self.rules
            .iter()
            .map(|r| format!("{};", r.display(sig)))
            .join("\n")
    }
    /// A human-readable serialization of the `TRS`.
    pub fn pretty(&self, sig: &Signature) -> String {
        self.rules
            .iter()
            .map(|r| format!("{};", r.pretty(sig)))
            .join("\n")
    }
    /// All the clauses in the `TRS`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F = G;").expect("parse of A = B; C = D | E; F = G;");
    ///
    /// let r0 = parse_rule(&mut sig, "A = B").expect("parse of A = B");
    /// let r1 = parse_rule(&mut sig, "C = D").expect("parse of C = D");
    /// let r2 = parse_rule(&mut sig, "C = E").expect("parse of C = E");
    /// let r3 = parse_rule(&mut sig, "F = G").expect("parse of F = G");
    ///
    /// assert_eq!(t.clauses(), vec![r0, r1, r2, r3]);
    /// ```
    pub fn clauses(&self) -> Vec<Rule> {
        self.rules.iter().flat_map(Rule::clauses).collect()
    }
    /// All the [`Operator`]s in the `TRS`.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let ops: Vec<String> = t.operators().iter().map(|o| o.display(&sig)).collect();
    ///
    /// assert_eq!(ops, vec!["A", "B", "C", "D", "E", "F", "G"]);
    /// ```
    pub fn operators(&self) -> Vec<Operator> {
        self.rules
            .iter()
            .flat_map(Rule::operators)
            .unique()
            .collect()
    }
    /// Do two TRSs [`unify`]?
    ///
    /// [`unify`]: https://en.wikipedia.org/wiki/Unification_(computer_science)
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t0 = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let t1 = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(H) = G;").expect("parse of A = B; C = D | E; F(H) = G;");
    ///
    /// assert!(TRS::unifies(t0.clone(), t1));
    ///
    /// let t2 = parse_trs(&mut sig,
    /// "B = A;
    /// C = D | E;
    /// F(y_) = G;").expect("parse of A = B; C = D | E; F(y_) = G;");
    ///
    /// assert!(!TRS::unifies(t0, t2));
    /// ```
    pub fn unifies(trs1: TRS, trs2: TRS) -> bool {
        trs1.len() == trs2.len()
            && trs1.rules
                .into_iter()
                .zip(trs2.rules)
                .all(|(r1, r2)| Rule::unify(r1, r2).is_some())
    }
    /// Does one TRS [`match`] another?
    ///
    /// See [`match`] for more information.
    ///
    /// [`Pattern Matching`]: https://en.wikipedia.org/wiki/Pattern_matching
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t0 = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let t1 = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(H) = G;").expect("parse of A = B; C = D | E; F(H) = G;");
    ///
    /// assert!(TRS::pmatches(t0.clone(), t1));
    ///
    /// let t2 = parse_trs(&mut sig,
    /// "B = A;
    /// C = D | E;
    /// F(y_) = G;").expect("parse of A = B; C = D | E; F(y_) = G;");
    ///
    /// assert!(!TRS::pmatches(t0.clone(), t2));
    ///
    /// let t3 = parse_trs(&mut sig,
    /// "A = B | C;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B | C; C = D | E; F(x_) = G");
    ///
    /// assert!(TRS::pmatches(t0.clone(), t3));
    ///
    /// let t4 = parse_trs(&mut sig,
    /// "A = B;
    /// C = D;
    /// D = E;").expect("parse of A = B; C = D; D = E;");
    ///
    /// assert!(!TRS::pmatches(t0, t4));
    /// ```
    pub fn pmatches(trs1: TRS, trs2: TRS) -> bool {
        trs1.len() == trs2.len()
            && trs1.rules
                .into_iter()
                .zip(trs2.rules)
                .all(|(r1, r2)| Rule::pmatch(r1, r2).is_some())
    }
    /// Are two TRSs [`Alpha Equivalent`]?
    ///
    /// [`Alpha Equivalent`]: https://en.wikipedia.org/wiki/lambda_calculus#Alpha_equivalence
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t0 = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let t1 = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(H) = G;").expect("parse of A = B; C = D | E; F(H) = G;");
    ///
    /// assert!(!TRS::alphas(&t0, &t1));
    ///
    /// let t2 = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(y_) = G;").expect("parse of A = B; C = D | E; F(y_) = G;");
    ///
    /// assert!(TRS::alphas(&t0, &t2));
    /// ```
    pub fn alphas(trs1: &TRS, trs2: &TRS) -> bool {
        TRS::pmatches(trs2.clone(), trs1.clone()) && TRS::pmatches(trs1.clone(), trs2.clone())
    }
    // Return rewrites modifying the entire term, if possible, else None.
    fn rewrite_head(&self, term: &Term) -> Option<Vec<Term>> {
        for rule in &self.rules {
            if let Some(ref sub) = Term::pmatch(vec![(rule.lhs.clone(), term.clone())]) {
                return Some(rule.rhs.iter().map(|x| x.substitute(sub)).collect());
            }
        }
        None
    }
    // Return rewrites modifying subterms, if possible, else None.
    fn rewrite_args(&self, term: &Term) -> Option<Vec<Term>> {
        if let Term::Application { op, ref args } = *term {
            for (i, arg) in args.iter().enumerate() {
                if let Some(v) = self.rewrite(arg) {
                    let res = v.iter()
                        .map(|x| {
                            let mut args = args.clone();
                            args[i] = x.clone();
                            Term::Application { op, args }
                        })
                        .collect();
                    return Some(res);
                }
            }
            None
        } else {
            None
        }
    }
    /// Perform a single rewrite step using a normal-order (leftmost-outermost)
    /// rewrite strategy.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let mut term = parse_term(&mut sig, "J(A K(C A))").expect("parse of J(A K(C A))");
    ///
    /// let rewriten_term = &t.rewrite(&term).unwrap()[0];
    ///
    /// assert_eq!(rewriten_term.display(&sig), "J(B K(C A))");
    /// ```
    pub fn rewrite(&self, term: &Term) -> Option<Vec<Term>> {
        match *term {
            Term::Variable(_) => None,
            ref app => self.rewrite_head(app).or_else(|| self.rewrite_args(app)),
        }
    }
    /// Query a `TRS` for a [`Rule`] based on its left-hand-side; return both
    /// the [`Rule`] and its index if possible
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let a = parse_term(&mut sig, "A").expect("parse of A");
    ///
    /// assert_eq!(t.get(&a).unwrap().1.display(&sig), "A = B");
    ///
    /// let c = parse_term(&mut sig, "C").expect("parse of C");
    ///
    /// assert_eq!(t.get(&c).unwrap().1.display(&sig), "C = D | E");
    /// ```
    pub fn get(&self, lhs: &Term) -> Option<(usize, Rule)> {
        for (idx, rule) in self.rules.iter().enumerate() {
            if Term::alpha(lhs, &rule.lhs).is_some() {
                return Some((idx, rule.clone()));
            }
        }
        None
    }
    /// Query a `TRS` for a [`Rule`] based on its index; return the [`Rule`] if
    /// possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// assert_eq!(t.get_idx(0).unwrap().display(&sig), "A = B");
    ///
    /// assert_eq!(t.get_idx(1).unwrap().display(&sig), "C = D | E");
    /// ```
    pub fn get_idx(&self, idx: usize) -> Option<Rule> {
        if self.rules.len() > idx {
            Some(self.rules[idx].clone())
        } else {
            None
        }
    }
    /// Query a `TRS` for specific [`Rule`] clauses; return them if possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A(a_ b_) = B(b_ b_);
    /// D(c_ e_) = D(E F);").expect("parse of A(a_ b_) = B(b_ b_); D(c_ e_) = D(E F);");
    ///
    /// let r = parse_rule(&mut sig, "A(x_ y_) = B(y_ y_)").expect("parse of A(x_ y_) = B(y_ y_)");
    ///
    /// assert_eq!(t.get_clause(&r).unwrap().1.display(&sig), "A(a_ b_) = B(b_ b_)");
    ///
    /// let r = parse_rule(&mut sig, "D(w_ q_) = D(E F)").expect("parse of D(w_ q_) = D(E F)");
    ///
    /// assert_eq!(t.get_clause(&r).unwrap().1.display(&sig), "D(c_ e_) = D(E F)");
    /// ```
    pub fn get_clause(&self, rule: &Rule) -> Option<(usize, Rule)> {
        for (i, r) in self.rules.iter().enumerate() {
            if let Some(sub) = r.contains(rule) {
                return Some((i, rule.substitute(&sub)));
            }
        }
        None
    }
    /// Query a `TRS` for a [`Rule`] based on its left-hand-side; delete and
    /// return the [`Rule`] if it exists.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let a = parse_term(&mut sig, "A").expect("parse of A");
    /// let c = parse_term(&mut sig, "C").expect("parse of C");
    ///
    /// assert_eq!(t.remove(&a).expect("removing A = B").display(&sig), "A = B");
    ///
    /// assert_eq!(t.remove(&c).expect("removing C = D").display(&sig), "C = D | E");
    ///
    /// assert_eq!(t.display(&sig), "F(x_) = G;");
    /// ```
    pub fn remove(&mut self, lhs: &Term) -> Result<Rule, TRSError> {
        if let Some((idx, _)) = self.get(lhs) {
            Ok(self.rules.remove(idx))
        } else {
            Err(TRSError::NotInTRS)
        }
    }
    /// Query a `TRS` for a [`Rule`] based on its index; delete and return the
    /// [`Rule`] if it exists.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// assert_eq!(t.remove_idx(0).expect("removing A = B").display(&sig), "A = B");
    ///
    /// assert_eq!(t.remove_idx(0).expect("removing C = D").display(&sig), "C = D | E");
    ///
    /// assert_eq!(t.display(&sig), "F(x_) = G;");
    /// ```
    pub fn remove_idx(&mut self, idx: usize) -> Result<Rule, TRSError> {
        if self.rules.len() > idx {
            Ok(self.rules.remove(idx))
        } else {
            Err(TRSError::InvalidIndex(idx, self.rules.len()))
        }
    }
    /// Query a `TRS` for a [`Rule`] based on its left-hand-side; delete and
    /// return the [`Rule`] if it exists.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "C = D").expect("parse of C = D");
    ///
    /// assert_eq!(t.remove_clauses(&r).expect("removing C = D").display(&sig), "C = D");
    ///
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// C = E;
    /// F(x_) = G;");
    /// ```
    pub fn remove_clauses(&mut self, rule: &Rule) -> Result<Rule, TRSError> {
        self.rules
            .iter_mut()
            .filter_map(|r| r.discard(&rule))
            .next()
            .ok_or(TRSError::NotInTRS)
            .and_then(|discarded| {
                self.rules.retain(|rule| !rule.is_empty());
                Ok(discarded)
            })
    }
    /// Try to merge a [`Rule`] with an existing [`Rule`] or else insert it at index `i` in the `TRS` if possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "D = G").expect("parse of D = G");
    ///
    /// t.insert(1, r).expect("inserting D = G at index 1");
    ///
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// D = G;
    /// C = D | E;
    /// F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "D = A").expect("parse of D = A");
    ///
    /// t.insert(0, r).expect("inserting D = A with D = G");
    ///
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// D = G | A;
    /// C = D | E;
    /// F(x_) = G;");
    /// ```
    pub fn insert(&mut self, idx: usize, rule: Rule) -> Result<&mut TRS, TRSError> {
        if self.insert_clauses(&rule).is_err() {
            self.insert_idx(idx, rule)
        } else {
            Ok(self)
        }
    }
    /// Insert a [`Rule`] at index `i` in the `TRS` if possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "D = G").expect("parse of D = G");
    ///
    /// t.insert_idx(1, r).expect("inserting D = G at index 1");
    ///
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// D = G;
    /// C = D | E;
    /// F(x_) = G;");
    /// ```
    pub fn insert_idx(&mut self, idx: usize, rule: Rule) -> Result<&mut TRS, TRSError> {
        if self.is_deterministic && rule.len() > 1 {
            return Err(TRSError::NondeterministicRule);
        } else if idx > self.rules.len() {
            return Err(TRSError::InvalidIndex(idx, self.rules.len()));
        } else if self.get(&rule.lhs).is_some() {
            return Err(TRSError::AlreadyInTRS);
        }
        self.rules.insert(idx, rule);
        Ok(self)
    }
    /// Merge a [`Rule`] with an existing [`Rule`] in the `TRS` if possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "A = H").expect("parse of A = H");
    ///
    /// let t = t.insert_clauses(&r).expect("inserting A = H with A = B");
    ///
    /// assert_eq!(t.display(&sig),
    /// "A = B | H;
    /// C = D | E;
    /// F(x_) = G;");
    /// ```
    pub fn insert_clauses(&mut self, rule: &Rule) -> Result<&mut TRS, TRSError> {
        if self.is_deterministic {
            Err(TRSError::NondeterministicRule)
        } else if let Some((idx, _)) = self.get(&rule.lhs) {
            self.rules[idx].merge(rule);
            Ok(self)
        } else {
            Err(TRSError::NotInTRS)
        }
    }
    /// Insert new [`Rule`] clauses if possible and move the entire [`Rule`] if
    /// necessary to be the first in the `TRS`.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "G(y_) = y_").expect("parse of G(y_) = y_");
    ///
    /// t.push(r).expect("inserting G(y_) = y_ at index 0");
    ///
    /// assert_eq!(t.display(&sig),
    /// "G(y_) = y_;
    /// A = B;
    /// C = D | E;
    /// F(x_) = G;");
    /// ```
    pub fn push(&mut self, rule: Rule) -> Result<&mut TRS, TRSError> {
        let lhs = rule.lhs.clone();
        self.insert(0, rule)?
            .get(&lhs)
            .ok_or(TRSError::NotInTRS)
            .and_then(move |(idx, _)| self.move_rule(idx, 0))
    }
    /// Inserts a series of [`Rule`]s at the beginning of the `TRS` if possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = H;").expect("parse of A = B; C = D | E; F(x_) = H;");
    ///
    /// let r0 = parse_rule(&mut sig, "G(y_) = y_").expect("parse of G(y_) = y_");
    /// let r1 = parse_rule(&mut sig, "B = C").expect("parse of B = C");
    /// let r2 = parse_rule(&mut sig, "E = F | B").expect("parse of E = F | B");
    ///
    /// t.pushes(vec![r0, r1, r2]).expect("inserting 3 rules at index 0");
    ///
    /// assert_eq!(t.display(&sig),
    /// "G(y_) = y_;
    /// B = C;
    /// E = F | B;
    /// A = B;
    /// C = D | E;
    /// F(x_) = H;");
    /// ```
    pub fn pushes(&mut self, rules: Vec<Rule>) -> Result<&mut TRS, TRSError> {
        for rule in rules.into_iter().rev() {
            self.push(rule)?;
        }
        Ok(self)
    }
    /// Move a [`Rule`] from index `i` to `j` if possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;
    /// H = I;").expect("parse of A = B; C = D | E; F(x_) = G; H = I;");
    ///
    /// t.move_rule(0, 2).expect("moving rule from index 0 to index 2");
    ///
    /// assert_eq!(t.display(&sig),
    /// "C = D | E;
    /// F(x_) = G;
    /// A = B;
    /// H = I;");
    /// ```
    pub fn move_rule(&mut self, i: usize, j: usize) -> Result<&mut TRS, TRSError> {
        if i != j {
            let rule = self.remove_idx(i)?;
            self.insert(j, rule)
        } else {
            Ok(self)
        }
    }
    /// Remove some [`Rule`] clauses while also inserting others if possible.
    ///
    /// The index `i` is used only in the case that the new clauses cannot be
    /// added to an existing [`Rule`].
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "C = D").expect("parse of C = D");
    /// let r_new = parse_rule(&mut sig, "C = A").expect("parse of C = A");
    ///
    /// t.replace(0, &r, r_new).expect("replaceing C = D with C = A");
    ///
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// C = E | A;
    /// F(x_) = G;");
    /// ```
    pub fn replace(&mut self, idx: usize, rule1: &Rule, rule2: Rule) -> Result<&mut TRS, TRSError> {
        self.remove_clauses(rule1)?;
        self.insert(idx, rule2)
    }
}

#[derive(Debug, Clone)]
/// The error type for [`TRS`] manipulations.
///
/// [`TRS`]: struct.TRS.html
pub enum TRSError {
    NotInTRS,
    AlreadyInTRS,
    NondeterministicRule,
    InvalidIndex(usize, usize),
}
impl fmt::Display for TRSError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TRSError::NotInTRS => write!(f, "query rule not in TRS"),
            TRSError::AlreadyInTRS => write!(f, "pre-existing rule with same LHS in TRS"),
            TRSError::NondeterministicRule => {
                write!(f, "proposed rule is nondeterministic in deterministic TRS")
            }
            TRSError::InvalidIndex(length, max_length) => {
                write!(f, "index {} greater than max index {}", length, max_length)
            }
        }
    }
}
impl ::std::error::Error for TRSError {
    fn description(&self) -> &'static str {
        "TRS error"
    }
}
