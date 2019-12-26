use super::{Atom, Context, Operator, Rule, Term, Variable, TRS};
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, RwLock};

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
#[derive(Clone)]
pub struct Signature {
    pub(crate) sig: Arc<RwLock<Sig>>,
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
    pub fn new(operator_spec: Vec<(u8, Option<String>)>) -> Signature {
        Signature {
            sig: Arc::new(RwLock::new(Sig::new(operator_spec))),
        }
    }
    pub fn deep_copy(&self) -> Signature {
        Signature {
            sig: Arc::new(RwLock::new(
                self.sig.read().expect("poisoned signature").clone(),
            )),
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
        self.sig
            .read()
            .expect("poisoned signature")
            .operators()
            .into_iter()
            .map(|id| Operator {
                id,
                arity: self.sig.read().expect("poisoned signature").operators[id].0,
            })
            .collect()
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
    /// parse_term(&mut sig, "A(x_ y_)").expect("parse of A(x_ y_)");
    ///
    /// let vars: Vec<String> = sig.variables().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(vars, vec!["x_", "y_"]);
    ///```
    pub fn variables(&self) -> Vec<Variable> {
        self.sig
            .read()
            .expect("poisoned signature")
            .variables()
            .into_iter()
            .map(|id| Variable { id })
            .collect()
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
    /// parse_term(&mut sig, "A(x_ B(y_))").expect("parse of A(x_ B(y_))");
    ///
    /// let atoms: Vec<String> = sig.atoms().iter().map(|a| a.display(&sig)).collect();
    ///
    /// assert_eq!(atoms, vec!["x_", "y_", "B", "A"]);
    /// ```
    pub fn atoms(&self) -> Vec<Atom> {
        let vars = self.variables().into_iter().map(Atom::Variable);
        let ops = self.operators().into_iter().map(Atom::Operator);
        vars.chain(ops).collect()
    }
    /// Create a new [`Operator`] distinct from all existing [`Operator`]s.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
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
    pub fn new_op(&self, arity: u8, name: Option<String>) -> Operator {
        let id = self
            .sig
            .write()
            .expect("poisoned signature")
            .new_op(arity, name);
        Operator { id, arity }
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
    pub fn new_var(&self, name: Option<String>) -> Variable {
        let id = self.sig.write().expect("poisoned signature").new_var(name);
        Variable { id }
    }
    pub fn contract(&mut self, ids: &[usize]) -> usize {
        self.sig.write().expect("poisoned signature").contract(ids)
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
    pub fn merge(&self, other: &Signature, strategy: MergeStrategy) -> Result<SignatureChange, ()> {
        self.sig
            .write()
            .expect("poisoned signature")
            .merge(&other, strategy)
    }
}
impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let sig = self.sig.read();
        write!(f, "Signature{{{:?}}}", sig)
    }
}
impl Default for Signature {
    fn default() -> Signature {
        Signature {
            sig: Arc::new(RwLock::new(Sig::default())),
        }
    }
}
impl PartialEq for Signature {
    fn eq(&self, other: &Signature) -> bool {
        self.sig
            .read()
            .expect("poisoned signature")
            .eq(&other.sig.read().expect("poisoned signature"))
    }
}
impl Eq for Signature {}
impl PartialOrd for Signature {
    fn partial_cmp(&self, other: &Signature) -> Option<std::cmp::Ordering> {
        self.sig
            .read()
            .expect("poisoned signature")
            .partial_cmp(&other.sig.read().expect("poisoned signature"))
    }
}
impl Ord for Signature {
    fn cmp(&self, other: &Signature) -> std::cmp::Ordering {
        self.sig
            .read()
            .expect("poisoned signature")
            .cmp(&other.sig.read().expect("poisoned signature"))
    }
}
impl Hash for Signature {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.sig.read().expect("poisoned signature").hash(state);
    }
}

#[derive(Clone, Debug, PartialOrd, Ord)]
pub(crate) struct Sig {
    /// Stores the (arity, name) for every [`Operator`].
    /// [`Operator`]: struct.Operator.html
    pub(crate) operators: Vec<(u8, Option<String>)>,
    /// Stores the name for every [`Variable`].
    /// [`Variable`]: struct.Variable.html
    pub(crate) variables: Vec<Option<String>>,
}
impl Sig {
    pub fn new(operator_spec: Vec<(u8, Option<String>)>) -> Sig {
        Sig {
            operators: operator_spec,
            variables: vec![],
        }
    }
    pub fn operators(&self) -> Vec<usize> {
        (0..self.operators.len()).collect()
    }
    pub fn variables(&self) -> Vec<usize> {
        (0..self.variables.len()).collect()
    }
    pub fn new_op(&mut self, arity: u8, name: Option<String>) -> usize {
        self.operators.push((arity, name));
        self.operators.len() - 1
    }
    pub fn new_var(&mut self, name: Option<String>) -> usize {
        self.variables.push(name);
        self.variables.len() - 1
    }
    /// Shrink the universe of symbols.
    pub fn contract(&mut self, ids: &[usize]) -> usize {
        match ids.iter().max() {
            Some(n) => {
                self.operators.truncate(n + 1);
                *n
            }
            _ => self.operators.len() - 1,
        }
    }
    pub fn merge(
        &mut self,
        other: &Signature,
        strategy: MergeStrategy,
    ) -> Result<SignatureChange, ()> {
        let mut other = other.sig.write().expect("poisoned signature");
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
                    self.operators.append(&mut other.operators);
                    temp_map
                }
            };
        let delta_var = self.variables.len();
        self.variables.append(&mut other.variables);
        Ok(SignatureChange { op_map, delta_var })
    }
}
impl Default for Sig {
    fn default() -> Sig {
        Sig {
            operators: Vec::new(),
            variables: Vec::new(),
        }
    }
}
impl Hash for Sig {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.variables.hash(state);
        self.operators.hash(state);
    }
}
impl PartialEq for Sig {
    fn eq(&self, other: &Sig) -> bool {
        self.variables.len() == other.variables.len()
            && self.operators.len() == other.operators.len()
            && self
                .operators
                .iter()
                .zip(&other.operators)
                .all(|(&(arity1, _), &(arity2, _))| arity1 == arity2)
    }
}
impl Eq for Sig {}

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
    op_map: HashMap<usize, usize>,
    delta_var: usize,
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
            Term::Variable(Variable { id }) => {
                let id = id + self.delta_var;
                Term::Variable(Variable { id })
            }
            Term::Application {
                op: Operator { id, arity },
                args,
            } => {
                let id = self.op_map[&id];
                Term::Application {
                    op: Operator { id, arity },
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
            Context::Variable(Variable { id }) => {
                let id = id + self.delta_var;
                Context::Variable(Variable { id })
            }
            Context::Application {
                op: Operator { id, arity },
                args,
            } => {
                let id = self.op_map[&id];
                Context::Application {
                    op: Operator { id, arity },
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

#[cfg(test)]
mod tests {
    use super::super::super::parser::*;
    use super::super::Signature;
    use super::*;

    #[test]
    fn new_test() {
        let mut sig = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);
        let mut ops = sig.operators();

        let mut op_names: Vec<String> = ops.iter().map(|op| op.display(&sig)).collect();
        assert_eq!(op_names, vec![".", "S", "K"]);

        let mut sig2 = Signature::default();
        sig2.new_op(2, Some(".".to_string()));
        sig2.new_op(0, Some("S".to_string()));
        sig2.new_op(0, Some("K".to_string()));

        ops = sig2.operators();

        op_names = ops.iter().map(|op| op.display(&sig)).collect();
        assert_eq!(op_names, vec![".", "S", "K"]);

        assert_eq!(sig, sig2);

        sig = Signature::new(vec![]);

        sig2 = Signature::default();

        assert_eq!(sig, sig2);
    }

    #[test]
    #[ignore]
    fn operators_test() {
        let sig = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);

        let ops: Vec<String> = sig.operators().iter().map(|op| op.display(&sig)).collect();

        assert_eq!(ops, vec![".", "S", "K"]);
    }

    #[test]
    #[ignore]
    fn variables_test() {
        let mut sig = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);

        parse_term(&mut sig, "A(x_ y_)").expect("parse of A(x_ y_)");

        let vars: Vec<String> = sig.variables().iter().map(|v| v.display(&sig)).collect();

        assert_eq!(vars, vec!["x_", "y_"]);
    }

    #[test]
    fn atoms_test() {
        let mut sig = Signature::default();

        parse_term(&mut sig, "A(x_ B(y_))").expect("parse of A(x_ B(y_))");

        let atoms: Vec<String> = sig.atoms().iter().map(|a| a.display(&sig)).collect();

        assert_eq!(atoms, vec!["x_", "y_", "B", "A"]);
    }

    #[test]
    #[ignore]
    fn new_op_test() {
        let sig = Signature::default();

        let a = sig.new_op(1, Some(".".to_string()));
        let s = sig.new_op(2, Some("S".to_string()));
        let s2 = sig.new_op(2, Some("S".to_string()));

        assert_ne!(a, s);
        assert_ne!(a, s2);
        assert_ne!(s, s2);
    }

    #[test]
    #[ignore]
    fn new_var() {
        let sig = Signature::default();

        let z = sig.new_var(Some("z".to_string()));
        let z2 = sig.new_var(Some("z".to_string()));

        assert_ne!(z, z2);
    }

    #[test]
    fn signature_merge_test() {
        // Merging 2 signatures by assuming all operators in the second are distinct from the first.
        let sig1 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);

        let sig2 = Signature::new(vec![
            (2, Some("A".to_string())),
            (1, Some("B".to_string())),
            (0, Some("C".to_string())),
        ]);

        sig1.merge(&sig2, MergeStrategy::DistinctOperators)
            .expect("merge of distinct operators");

        let ops: Vec<String> = sig1
            .operators()
            .iter()
            .map(|op| op.display(&sig1))
            .collect();

        assert_eq!(ops, vec![".", "S", "K", "A", "B", "C"]);

        // Merging 2 signatures by assuming all operators in the second are the same from the first.
        let sig1 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);

        let sig2 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);

        sig1.merge(&sig2, MergeStrategy::SameOperators)
            .expect("merge of same operators");

        let ops: Vec<String> = sig1
            .operators()
            .iter()
            .map(|op| op.display(&sig1))
            .collect();

        assert_eq!(ops, vec![".", "S", "K"]);

        // Merging 2 signatures by SameOperators should fail if all operators in both signatures are not the same.
        let sig1 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);

        let sig2 = Signature::new(vec![
            (2, Some(".".to_string())),
            (1, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);

        assert!(sig1.merge(&sig2, MergeStrategy::SameOperators).is_err());

        // Merging 2 signatures assuming any operators with the same name and arity are the same.
        let sig1 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);

        let sig2 = Signature::new(vec![
            (2, Some("A".to_string())),
            (1, Some("B".to_string())),
            (0, Some("K".to_string())),
        ]);

        sig1.merge(&sig2, MergeStrategy::OperatorsByArityAndName)
            .expect("merge of same arity and name");

        let ops: Vec<String> = sig1
            .operators()
            .iter()
            .map(|op| op.display(&sig1))
            .collect();

        assert_eq!(ops, vec![".", "S", "K", "A", "B"]);
    }

    #[test]
    fn sig_merge_test() {}

    #[test]
    fn reify_term_test() {
        let sig1 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);
        let mut sig2 = Signature::default();

        let term = parse_term(&mut sig2, "A B").unwrap();

        let sigchange = sig1.merge(&sig2, MergeStrategy::DistinctOperators).unwrap();

        let term = sigchange.reify_term(&sig1, term);

        assert_eq!(term.pretty(&sig1), "A B");
    }

    #[test]
    fn reify_context_test() {
        let sig1 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);
        let mut sig2 = Signature::default();

        let context = parse_context(&mut sig2, "A([!] B)").expect("parse of A([!] B)");

        let sigchange = sig1
            .merge(&sig2, MergeStrategy::OperatorsByArityAndName)
            .unwrap();

        let context = sigchange.reify_context(&sig1, context);

        assert_eq!(context.pretty(&sig1), "A([!], B)");
    }

    #[test]
    fn reify_rule_test() {
        let sig1 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);
        let mut sig2 = Signature::default();

        let rule = parse_rule(&mut sig2, "A = B | C").unwrap();

        let sigchange = sig1
            .merge(&sig2, MergeStrategy::OperatorsByArityAndName)
            .unwrap();

        let rule = sigchange.reify_rule(&sig1, rule);

        assert_eq!(rule.pretty(&sig1), "A = B | C");
    }

    #[test]
    fn reify_trs_test() {
        let sig1 = Signature::new(vec![
            (2, Some(".".to_string())),
            (0, Some("S".to_string())),
            (0, Some("K".to_string())),
        ]);
        let mut sig2 = Signature::default();

        let trs = parse_trs(&mut sig2, "A = B;\nC = B;").unwrap();

        let sigchange = sig1
            .merge(&sig2, MergeStrategy::OperatorsByArityAndName)
            .unwrap();

        let trs = sigchange.reify_trs(&sig1, trs);

        assert_eq!(trs.pretty(&sig1), "A = B;\nC = B;");
    }
}
