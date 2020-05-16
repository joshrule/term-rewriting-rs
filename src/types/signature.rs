use super::{Atom, Context, Operator, Rule, Term, Variable, TRS};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

/// Records a universe of symbols.
///
/// Use [`Signature::default`] for a blank `Signature`, or [`Signature::new`] to initialize a
/// `Signature` with given [`Operator`]s.
///
/// [`Signature::default`]: #method.default
/// [`Signature::new`]: #method.new
/// [`Operator`]: struct.Operator.html
///
/// # Examples
///
/// ```
/// # use term_rewriting::{Signature, parse_term};
/// // Constructing a Signature using the default
/// let mut sig1 = Signature::default();
/// let a = sig1.new_op(2, Some("A".to_string()));
/// let b = sig1.new_op(0, Some("B".to_string()));
/// let c = sig1.new_op(0, Some("C".to_string()));
///
/// // Constructing a Signature using Signature::new
/// let mut sig2 = Signature::new(vec![
///     (2, Some("A".to_string())),
///     (0, Some("B".to_string())),
///     (0, Some("C".to_string())),
/// ]);
///
/// assert_eq!(sig1, sig2);
/// ```
#[derive(Clone, Debug, PartialOrd, Ord)]
pub struct Signature {
    /// Stores the (arity, name) for every [`Operator`].
    /// [`Operator`]: struct.Operator.html
    pub(crate) operators: Vec<(u8, Option<String>)>,
    /// Stores the name for every [`Variable`].
    /// [`Variable`]: struct.Variable.html
    pub(crate) variables: Vec<Option<String>>,
}
impl Signature {
    /// Construct a `Signature` with the given [`Operator`]s.
    ///
    /// Each [`Operator`] is specified in the form of `(arity, Some(name))` or
    /// `(arity, None)`, where `arity` is the number of arguments a [`Term`] takes
    /// (for example, an `arity` of 0 gives a "constant" [`Operator`]). A `name` for
    /// the [`Operator`] is unnecessary, but may be supplied for more readable
    /// formatting.
    ///
    /// The returned vector of [`Operator`]s corresponds to the supplied spec.
    ///
    /// [`Operator`]: struct.Operator.html
    /// [`Term`]: struct.Term.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// let ops = sig.operators();
    ///
    /// let op_names: Vec<String> = ops.iter().map(|op| op.display(&sig)).collect();
    /// assert_eq!(op_names, vec![".", "S", "K"]);
    ///
    /// let mut sig2 = Signature::default();
    /// let p = sig2.new_op(2, Some(".".to_string()));
    /// let s = sig2.new_op(0, Some("S".to_string()));
    /// let k = sig2.new_op(0, Some("K".to_string()));
    ///
    /// assert_eq!(sig, sig2);
    ///
    /// let mut sig = Signature::new(vec![]);
    ///
    /// let mut sig2 = Signature::default();
    ///
    /// assert_eq!(sig, sig2);
    ///```
    pub fn new(operator_spec: Vec<(u8, Option<String>)>) -> Self {
        Signature {
            operators: operator_spec,
            variables: vec![],
        }
    }
    /// Returns every [`Operator`] known to the `Signature`, in the order they were created.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature:: new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// let ops: Vec<String> = sig.operators().iter().map(|op| op.display(&sig)).collect();;
    ///
    /// assert_eq!(ops, vec![".", "S", "K"]);
    ///```
    pub fn operators(&self) -> Vec<Operator> {
        (0..self.operators.len()).map(Operator).collect()
    }
    /// Returns every [`Variable`] known to the `Signature`, in the order they were created.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term};
    /// let mut sig = Signature:: new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// parse_term(&mut sig, "A(v0_ v1_)").expect("parse of A(v0_ v1_)");
    ///
    /// let vars: Vec<String> = sig.variables().iter().map(|v| v.display()).collect();
    ///
    /// assert_eq!(vars, vec!["v0_", "v1_"]);
    ///```
    pub fn variables(&self) -> Vec<Variable> {
        (0..self.variables.len()).map(Variable).collect()
    }
    /// Returns every [`Atom`] known to the `Signature`.
    ///
    /// [`Atom`]: enum.Atom.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// parse_term(&mut sig, "A(v0_ B(v1_))").expect("parse of A(v0_ B(v1_))");
    ///
    /// let atoms: Vec<String> = sig.atoms().iter().map(|a| a.display(&sig)).collect();
    ///
    /// assert_eq!(atoms, vec!["v0_", "v1_", "B", "A"]);
    /// ```
    pub fn atoms(&self) -> Vec<Atom> {
        let vars = self.variables().into_iter().map(Atom::Variable);
        let ops = self.operators().into_iter().map(Atom::Operator);
        vars.chain(ops).collect()
    }
    /// Create a new [`Operator`] distinct from all existing [`Operator`]s.
    ///
    /// [`Operator`]: struct.Operator.html ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature};
    /// let mut sig = Signature::default();
    ///
    /// let a = sig.new_op(1, Some(".".to_string()));
    /// let s = sig.new_op(2, Some("S".to_string()));
    /// let s2 = sig.new_op(2, Some("S".to_string()));
    ///
    /// assert_ne!(a, s);
    /// assert_ne!(a, s2);
    /// assert_ne!(s, s2);
    /// ```
    pub fn new_op(&mut self, arity: u8, name: Option<String>) -> Operator {
        let operator = Operator(self.operators.len());
        self.operators.push((arity, name));
        operator
    }
    /// Find an `Operator` in the `Signature`.
    pub fn has_op(&self, arity: u8, name: Option<String>) -> Option<Operator> {
        self.operators
            .iter()
            .position(|(o_arity, o_name)| *o_arity == arity && *o_name == name)
            .map(Operator)
    }
    /// Create a new [`Variable`] distinct from all existing [`Variable`]s.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature};
    /// let mut sig = Signature::default();
    ///
    /// let z = sig.new_var(Some("z".to_string()));
    /// let z2 = sig.new_var(Some("z".to_string()));
    ///
    /// assert_ne!(z, z2);
    /// ```
    pub fn new_var(&mut self, name: Option<String>) -> Variable {
        let variable = Variable(self.variables.len());
        self.variables.push(name);
        variable
    }
    pub fn clear_variables(&mut self) {
        self.variables.clear();
    }
    pub fn contract(&mut self, ids: &[usize]) -> usize {
        match ids.iter().max() {
            Some(n) => {
                self.operators.truncate(n + 1);
                *n
            }
            _ => self.operators.len() - 1,
        }
    }
    /// Merge two `Signature`s. All [`Term`]s, [`Context`]s, [`Rule`]s, and [`TRS`]s associated
    /// with the `other` `Signature` should be `reified` using methods provided
    /// by the returned [`SignatureChange`].
    ///
    /// [`Term`]: struct.Term.html
    /// [`Context`]: struct.Context.html
    /// [`Rule`]: struct.Rule.html
    /// [`TRS`]: struct.TRS.html
    /// [`SignatureChange`]: struct.SignatureChange.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, MergeStrategy};
    /// // Merging 2 signatures by assuming all operators in the second are distinct from the first.
    /// let mut sig1 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// let mut sig2 = Signature::new(vec![
    ///     (2, Some("A".to_string())),
    ///     (1, Some("B".to_string())),
    ///     (0, Some("C".to_string())),
    /// ]);
    ///
    /// sig1.merge(&sig2, MergeStrategy::DistinctOperators);
    ///
    /// let ops: Vec<String> = sig1.operators().iter().map(|op| op.display(&sig1)).collect();
    ///
    /// assert_eq!(ops, vec![".", "S", "K", "A", "B", "C"]);
    ///
    /// // Merging 2 signatures by assuming all operators in the second are the same from the first.
    /// let mut sig1 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// let mut sig2 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// sig1.merge(&sig2, MergeStrategy::SameOperators);
    ///
    /// let ops: Vec<String> = sig1.operators().iter().map(|op| op.display(&sig1)).collect();
    ///
    /// assert_eq!(ops, vec![".", "S", "K"]);
    ///
    /// // Merging 2 signatures by SameOperators should fail if all operators in both signatures are not the same.
    /// let mut sig1 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// let mut sig2 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (1, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// assert!(sig1.merge(&sig2, MergeStrategy::SameOperators).is_err());
    ///
    /// // Merging 2 signatures assuming any operators with the same name and arity are the same.
    /// let mut sig1 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// let mut sig2 = Signature::new(vec![
    ///     (2, Some("A".to_string())),
    ///     (1, Some("B".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    ///
    /// sig1.merge(&sig2, MergeStrategy::OperatorsByArityAndName);
    ///
    /// let ops: Vec<String> = sig1.operators().iter().map(|op| op.display(&sig1)).collect();
    ///
    /// assert_eq!(ops, vec![".", "S", "K", "A", "B"]);
    /// ```
    pub fn merge(
        &mut self,
        other: &Signature,
        strategy: MergeStrategy,
    ) -> Result<SignatureChange, ()> {
        let op_map =
            match strategy {
                MergeStrategy::SameOperators => {
                    let mut temp_map = HashMap::default();
                    if self.operators.len() == other.operators.len()
                        && self.operators.iter().zip(&other.operators).all(
                            |((arity1, op1), (arity2, op2))| *arity1 == *arity2 && *op1 == *op2,
                        )
                    {
                        for idx in 0..self.operators.len() {
                            temp_map.insert(idx, idx);
                        }
                    } else {
                        return Err(());
                    }
                    temp_map
                }
                MergeStrategy::OperatorsByArityAndName => {
                    let old_len = self.operators.len();
                    let mut new_idx = old_len;
                    let mut temp_map = HashMap::default();
                    for (op, idx) in other.operators.iter().zip(0..other.operators.len()) {
                        if self.operators.contains(&op) {
                            for original_idx in 0..self.operators.len() {
                                if self.operators[original_idx] == *op {
                                    temp_map.insert(idx, original_idx);
                                    break;
                                }
                            }
                        } else {
                            self.operators.push(op.clone());
                            temp_map.insert(idx, new_idx);
                            new_idx += 1;
                        }
                    }
                    temp_map
                }
                MergeStrategy::DistinctOperators => {
                    let mut new_idx = self.operators.len();
                    let mut temp_map = HashMap::default();
                    for idx in 0..other.operators.len() {
                        temp_map.insert(idx, new_idx);
                        new_idx += 1;
                    }
                    self.operators.extend_from_slice(&other.operators);
                    temp_map
                }
            };
        let delta_var = self.variables.len();
        self.variables.extend_from_slice(&other.variables);
        Ok(SignatureChange { op_map, delta_var })
    }
}
impl Default for Signature {
    fn default() -> Signature {
        Signature {
            operators: vec![],
            variables: vec![],
        }
    }
}
impl Hash for Signature {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.variables.hash(state);
        self.operators.hash(state);
    }
}
impl PartialEq for Signature {
    fn eq(&self, other: &Self) -> bool {
        self.variables.len() == other.variables.len()
            && self.operators.len() == other.operators.len()
            && self
                .operators
                .iter()
                .zip(&other.operators)
                .all(|(&(arity1, _), &(arity2, _))| arity1 == arity2)
    }
}
impl Eq for Signature {}

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

/// Allows [`Term`]s/[`Rule`]s/[`TRS`]s to be reified for use with another [`Signature`].
/// See [`Signature::merge`].
///
/// [`Signature::merge`]: struct.Signature.html#method.merge
/// [`Term`]: struct.Term.html
/// [`Rule`]: struct.Rule.html
/// [`TRS`]: struct.TRS.html
/// [`Signature`]: struct.Signature.html
///
/// # Examples
///
/// ```
/// # use term_rewriting::{MergeStrategy, Signature, parse_term, parse_trs};
/// let mut sig1 = Signature::new(vec![
///     (2, Some(".".to_string())),
///     (0, Some("S".to_string())),
///     (0, Some("K".to_string())),
/// ]);
/// let mut sig2 = Signature::default();
///
/// let term = parse_term(&mut sig2, "A B").unwrap();
///
/// assert_eq!(term.pretty(&sig2), "A B");
///
/// let sigchange = sig1.merge(&sig2, MergeStrategy::OperatorsByArityAndName).unwrap();
///
/// let ops: Vec<String> = sig1.operators().iter().map(|op| op.display(&sig1)).collect();
///
/// assert_eq!(ops, vec![".", "S", "K", "A", "B"]);
///
/// let term = sigchange.reify_term(&sig1, term);
///
/// assert_eq!(term.pretty(&sig1), "A B");
/// ```
pub struct SignatureChange {
    pub op_map: HashMap<usize, usize>,
    pub delta_var: usize,
}
impl SignatureChange {
    /// Reifies [`Term`] for use with another [`Signature`].
    ///
    /// [`Term`]: struct.Term.html
    /// [`Signature`]: struct.Signature.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{MergeStrategy, Signature, parse_term, parse_trs};
    /// let mut sig1 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// let mut sig2 = Signature::default();
    ///
    /// let term = parse_term(&mut sig2, "A B").unwrap();
    ///
    /// let sigchange = sig1.merge(&sig2, MergeStrategy::DistinctOperators).unwrap();
    ///
    /// let term = sigchange.reify_term(&sig1, term);
    ///
    /// assert_eq!(term.pretty(&sig1), "A B");
    /// ```
    pub fn reify_term(&self, sig: &Signature, term: Term) -> Term {
        match term {
            Term::Variable(Variable(id)) => {
                let id = id + self.delta_var;
                Term::Variable(Variable(id))
            }
            Term::Application {
                op: Operator(id),
                args,
            } => {
                let id = self.op_map[&id];
                Term::Application {
                    op: Operator(id),
                    args: args.into_iter().map(|t| self.reify_term(sig, t)).collect(),
                }
            }
        }
    }
    /// Reifies [`Context`] for use with another [`Signature`].
    ///
    /// [`Context`]: struct.Context.html
    /// [`Signature`]: struct.Signature.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{MergeStrategy, Signature, Context, parse_context};
    /// let mut sig1 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// let mut sig2 = Signature::default();
    ///
    /// let context = parse_context(&mut sig2, "A([!] B)").expect("parse of A([!] B)");
    ///
    /// let sigchange = sig1.merge(&sig2, MergeStrategy::OperatorsByArityAndName).unwrap();
    ///
    /// let context = sigchange.reify_context(&sig1, context);
    ///
    /// assert_eq!(context.pretty(&sig1), "A([!], B)");
    /// ```
    pub fn reify_context(&self, sig: &Signature, context: Context) -> Context {
        match context {
            Context::Hole => Context::Hole,
            Context::Variable(Variable(id)) => {
                let id = id + self.delta_var;
                Context::Variable(Variable(id))
            }
            Context::Application {
                op: Operator(id),
                args,
            } => {
                let id = self.op_map[&id];
                Context::Application {
                    op: Operator(id),
                    args: args
                        .into_iter()
                        .map(|t| self.reify_context(sig, t))
                        .collect(),
                }
            }
        }
    }
    /// Reifies [`Rule`] for use with another [`Signature`].
    ///
    /// [`Rule`]: struct.Rule.html
    /// [`Signature`]: struct.Signature.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{MergeStrategy, Signature, parse_rule, parse_trs};
    /// let mut sig1 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// let mut sig2 = Signature::default();
    ///
    /// let rule = parse_rule(&mut sig2, "A = B | C").unwrap();
    ///
    /// let sigchange = sig1.merge(&sig2, MergeStrategy::OperatorsByArityAndName).unwrap();
    ///
    /// let rule = sigchange.reify_rule(&sig1, rule);
    ///
    /// assert_eq!(rule.pretty(&sig1), "A = B | C");
    /// ```
    pub fn reify_rule(&self, sig: &Signature, rule: Rule) -> Rule {
        let Rule { lhs, rhs } = rule;
        let lhs = self.reify_term(sig, lhs);
        let rhs = rhs.into_iter().map(|t| self.reify_term(sig, t)).collect();
        Rule { lhs, rhs }
    }
    /// Reifies [`TRS`] for use with another [`Signature`].
    ///
    /// [`TRS`]: struct.TRS.html
    /// [`Signature`]: struct.Signature.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{MergeStrategy, Signature, parse_trs};
    /// let mut sig1 = Signature::new(vec![
    ///     (2, Some(".".to_string())),
    ///     (0, Some("S".to_string())),
    ///     (0, Some("K".to_string())),
    /// ]);
    /// let mut sig2 = Signature::default();
    ///
    /// let trs = parse_trs(&mut sig2,
    /// "A = B;
    /// C = B;").unwrap();
    ///
    /// let sigchange = sig1.merge(&sig2, MergeStrategy::OperatorsByArityAndName).unwrap();
    ///
    /// let trs = sigchange.reify_trs(&sig1, trs);
    ///
    /// assert_eq!(trs.pretty(&sig1),
    /// "A = B;
    /// C = B;");
    /// ```
    pub fn reify_trs(&self, sig: &Signature, trs: TRS) -> TRS {
        let rules = trs
            .rules
            .into_iter()
            .map(|r| self.reify_rule(sig, r))
            .collect();
        TRS { rules, ..trs }
    }
}
