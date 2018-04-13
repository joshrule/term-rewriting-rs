use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use super::parser;

/// Represents the human-assigned name of a [`Variable`] or an [`Operator`].
///
/// [`Variable`]: struct.Variable.html
/// [`Operator`]: struct.Operator.html
pub type Name = Option<String>;

/// Represents the unique identity of a [`Variable`] or an [`Operator`].
///
/// [`Variable`]: struct.Variable.html
/// [`Operator`]: struct.Operator.html
pub type DeBruin = usize;

/// Represents the number of arguments an [`Operator`] takes.
///
/// [`Operator`]: struct.Operator.html
pub type Arity = usize;

/// Represents a mapping from [`Variable`s] to [`Term`s].
///
/// [`Variable`s]: struct.Variable.html
/// [`Term`s]: struct.Term.html
pub type Substitution = HashMap<Variable, Term>;

/// Represents a symbol with fixed [`Arity`].
///
/// [`Arity`]: type.Arity.html
#[derive(Debug, Clone, Eq)]
pub struct Operator {
    id: DeBruin,
    arity: Arity,
    name: Name,
}
impl Operator {
    /// Return the human-assigned [`Name`] of `self`.
    ///
    /// [`Name`]: type.Name.html
    pub fn name(&self) -> &Name {
        &self.name
    }
    /// Return the [`Arity`] of `self`.
    ///
    /// [`Arity`]: type.Arity.html
    pub fn arity(&self) -> Arity {
        self.arity
    }
}
impl PartialEq for Operator {
    fn eq(&self, other: &Operator) -> bool {
        self.id == other.id && self.arity == other.arity
    }
}
impl Hash for Operator {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
        self.arity.hash(state);
    }
}

/// Represents a symbol signifying an unspecified [`Term`].
///
/// [`Term`]: enum.Term.html
#[derive(Debug, Clone, Eq)]
pub struct Variable {
    id: DeBruin,
    name: Name,
}
impl Variable {
    /// Return the human-assigned [`Name`] of `self`.
    ///
    /// [`Name`]: type.Name.html
    pub fn name(&self) -> &Name {
        &self.name
    }
}
impl PartialEq for Variable {
    fn eq(&self, other: &Variable) -> bool {
        self.id == other.id
    }
}
impl Hash for Variable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// Represents a first-order term: either a [`Variable`] or an [`Application`]
/// of an [`Operator`] to [`Term`]s
///
/// [`Variable`]: enum.Term.html#variant.Variable
/// [`Operator`]: struct.Operator.html
/// [`Application`]: enum.Term.html#variant.Application
/// [`Term`]: enum.Term.html
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Term {
    /// A concrete but unspecified [`Term`] (e.g. `x`, `y`)
    ///
    /// [`Term`]: enum.Term.html
    Variable(Variable),
    /// some [`Operator`] applied to zero or more [`Term`]s (e.g. (`f(x, y)`, `g()`)
    ///
    /// [`Operator`]: struct.Operator.html
    /// [`Term`]: enum.Term.html
    Application { head: Operator, args: Vec<Term> },
}
impl Term {
    /// Return a [`Vec<Variable>`] containing every [`Variable`] that occurs in `self`.
    ///
    /// [`Vec<Variable>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Variable`]: struct.Variable.html
    pub fn variables(&self) -> Vec<&Variable> {
        match *self {
            Term::Variable(ref v) => vec![v],
            Term::Application { args: ref a, .. } => a.iter().flat_map(|x| x.variables()).collect(),
        }
    }
    /// Return a [`Vec<Variable>`] containing every unbound [`Variable`] that occurs in `self`.
    ///
    /// [`Vec<Variable>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Variable`]: struct.Variable.html
    pub fn free_vars(&self) -> Vec<&Variable> {
        self.variables()
    }
    /// Given a mapping from [`Variable`s] to [`Term`s], perform a substitution on a [`Term`].
    ///
    /// [`Variable`s]: struct.Variable.html
    /// [`Term`s]: enum.Term.html
    /// [`Term`]: enum.Term.html
    pub fn substitute(&self, sub: &Substitution) -> Term {
        match *self {
            Term::Variable(ref v) => sub.get(v).unwrap_or(self).clone(),
            Term::Application { ref head, ref args } => Term::Application {
                head: head.clone(),
                args: args.iter().map(|x| x.substitute(sub)).collect(),
            },
        }
    }
    /// Take a vector of pairs of terms and perform a substitution on each term.
    fn constraint_substitute(cs: &[(Term, Term)], sub: &Substitution) -> Vec<(Term, Term)> {
        cs.iter()
            .map(|&(ref s, ref t)| (s.substitute(sub), t.substitute(sub)))
            .collect()
    }
    /// Compose two substitutions.
    fn compose(sub1: Option<Substitution>, sub2: Option<Substitution>) -> Option<Substitution> {
        match (sub1, sub2) {
            (Some(ref s1), Some(ref s2)) => {
                let mut sub = s1.clone();
                for (k, v) in s2 {
                    sub.insert(k.clone(), v.substitute(s1));
                }
                Some(sub)
            }
            _ => None,
        }
    }
    /// Given a vector of contraints, return [`Some(sigma)`] if the constraints
    /// can be satisfied, where `sigma` is a substitution, otherwise [`None`].
    ///
    /// [`Some(sigma)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn unify(mut cs: Vec<(Term, Term)>) -> Option<Substitution> {
        let c = cs.pop();
        match c {
            None => Some(HashMap::new()),
            Some((ref s, ref t)) if s == t => Term::unify(cs),
            Some((
                Term::Application {
                    head: ref h1,
                    args: ref a1,
                },
                Term::Application {
                    head: ref h2,
                    args: ref a2,
                },
            )) if h1 == h2 =>
            {
                cs.append(&mut a1.clone().into_iter().zip(a2.clone().into_iter()).collect());
                Term::unify(cs)
            }
            Some((Term::Variable(ref var), ref t)) if !Term::free_vars(t).contains(&var) => {
                let mut st = HashMap::new();
                st.insert(var.clone(), t.clone());
                let mut cs = Term::constraint_substitute(&cs, &st);
                Term::compose(Term::unify(cs), Some(st))
            }
            Some((ref s, Term::Variable(ref var))) if !Term::free_vars(s).contains(&var) => {
                let mut ts = HashMap::new();
                ts.insert(var.clone(), s.clone());
                let mut cs = Term::constraint_substitute(&cs, &ts);
                Term::compose(Term::unify(cs), Some(ts))
            }
            _ => None,
        }
    }
}

/// Represents a rewrite rule equating a left-hand-side [`Term`] with one or
/// more right-hand-side [`Term`]s.
///
/// [`Term`]: enum.Term.html
#[derive(Debug, PartialEq)]
pub struct Rule {
    lhs: Term,
    rhs: Vec<Term>,
}
impl Rule {
    /// logic ensuring that the `lhs` and `rhs` are compatible.
    fn is_valid(lhs: &Term, rhs: &[Term]) -> bool {
        // the lhs must be an application
        if let Term::Application { .. } = *lhs {
            // variables(rhs) must be a subset of variables(lhs)
            let lhs_vars: HashSet<&Variable> = lhs.variables().into_iter().collect();
            let rhs_vars: HashSet<&Variable> = rhs.iter().flat_map(|r| r.variables()).collect();
            rhs_vars.is_subset(&lhs_vars)
        } else {
            false
        }
    }
    /// Construct a rewrite rule from a left-hand-side (LHS) [`Term`] with one
    /// or more right-hand-side (RHS) [`Term`]s. Returns [`Some(Rule{lhs, rhs})`]
    /// if `Rule{lhs, rhs}` is valid, and [`None`] otherwise.
    ///
    /// Valid rules meet two conditions:
    ///
    /// 1. `lhs` is an [`Application`]. This prevents a single rule from
    /// matching all possible terms
    /// 2. A [`Term`] in `rhs` can only use a [`Variable`] if it appears in
    /// `lhs`. This prevents rewrites from inventing arbitrary terms.
    ///
    /// [`Term`]: enum.Term.html
    /// [`Application`]: enum.Term.html#variant.Application
    /// [`Variable`]: struct.Variable.html
    /// [`Some(Rule{lhs, rhs})`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn new(lhs: Term, rhs: Vec<Term>) -> Option<Rule> {
        if Rule::is_valid(&lhs, &rhs) {
            Some(Rule { lhs, rhs })
        } else {
            None
        }
    }
}

/// Represents a universe of [`Operator`] and [`Variable`] symbols.
///
/// [`Operator`]: struct.Operator.html
/// [`Variable`]: struct.Variable.html
#[derive(Debug)]
pub struct Signature {
    operators: Vec<Operator>,
    variables: Vec<Variable>,
    operator_count: DeBruin,
    variable_count: DeBruin,
}
impl Signature {
    /// Construct a fresh [`Operator`] and add it to `self`. Returns the newly
    /// constructed [`Operator`]. Because this operation always creates a fresh
    /// [`Operator`], it is possible for `self` to track multiple [`Operator`]s
    /// with the same `name` and `arity` but different `id`s.
    ///
    /// [`Operator`]: struct.Operator.html
    pub fn new_operator(&mut self, name: Name, arity: Arity) -> Operator {
        self.operator_count += 1;
        let o = Operator {
            id: self.operator_count - 1,
            name,
            arity,
        };
        self.operators.push(o.clone());
        o
    }
    /// Construct a fresh [`Variable`] and add it to `self`. Returns the newly
    /// constructed [`Variable`]. Because this operation always creates a fresh
    /// [`Variable`], it is possible for `self` to track multiple [`Variable`]s
    /// with the same `name` but different `id`s.
    ///
    /// [`Variable`]: struct.Variable.html
    pub fn new_variable(&mut self, name: Name) -> Variable {
        self.variable_count += 1;
        let id = self.variable_count - 1;
        let v = Variable { id, name };
        self.variables.push(v.clone());
        v
    }
    /// Returns [`Some(v)`] where `v` has the lowest `id` of any [`Variable`] in
    /// `self` named `name` if such a [`Variable`] exists, otherwise [`None`].
    ///
    /// [`Some(v)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Variable`]: struct.Variable.html
    pub fn has_var(&self, name: &str) -> Option<Variable> {
        let res = self.variables.iter().find(|&v| match *v.name() {
            Some(ref n) if n == name => true,
            _ => false,
        });
        if let Some(v) = res {
            Some(v.clone())
        } else {
            None
        }
    }
    /// Returns a [`Variable`] `v` where `v` has the lowest `id` of any [`Variable`] in
    /// `self` named `name`, creating this [`Variable`] if necessary.
    ///
    /// [`Variable`]: struct.Variable.html
    pub fn get_var(&mut self, name: &str) -> Variable {
        match self.has_var(name) {
            Some(v) => v,
            None => self.new_variable(Some(name.to_string())),
        }
    }
    /// Returns [`Some(o)`] where `o` has the lowest `id` of any [`Operator`] in
    /// `self` named `name` with arity `arity` if such an [`Operator`] exists,
    /// otherwise [`None`].
    ///
    /// [`Some(v)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Operator`]: struct.Operator.html
    pub fn has_op(&mut self, name: &str, arity: Arity) -> Option<Operator> {
        let res = self.operators.iter().find(|&o| match *o.name() {
            Some(ref n) if n == name && arity == o.arity() => true,
            _ => false,
        });
        if let Some(o) = res {
            Some(o.clone())
        } else {
            None
        }
    }
    /// Returns an [`Operator`] `v` where `v` has the lowest `id` of any [`Operator`] in
    /// `self` named `name` with arity `arity`, creating this [`Operator`] if necessary.
    ///
    /// [`Operator`]: struct.Operator.html
    pub fn get_op(&mut self, name: &str, arity: Arity) -> Operator {
        match self.has_op(name, arity) {
            Some(o) => o,
            None => self.new_operator(Some(name.to_string()), arity),
        }
    }
    /// `self` forgets every currently tracked [`Variable`].
    ///
    /// [`Variable`]: struct.Variable.html
    pub fn clear_variables(&mut self) {
        self.variables.clear();
    }
    /// Parse a string as a [`TRS`], `trs`, and a [`Term`] list, `terms`, to be
    /// evaluated. Returns [`Ok((trs, terms))`] if parsing succeeds and an
    /// [`Err`] otherwise.
    ///
    /// # TRS syntax
    ///
    /// `input` is parsed as a `<program>`, defined as follows:
    ///
    /// ```text
    /// <program> ::= ( <comment>* <statement> ";" <comment>* )*
    ///
    /// <comment> ::= "#" <any-char-but-newline> "\n"
    ///
    /// <statement> ::= <rule> | <top-level-term>
    ///
    /// <rule> ::= <top-level-term> "=" <top-level-term> ( "|" <top-level-term> )
    ///
    /// <top-level-term) ::= ( <term> | ( "(" <top-level-term> ")" ) ) (" "  ( <term> | ( "(" <top-level-term> ")" ) ) )*
    ///
    /// <term> ::= <variable> | <application>
    ///
    /// <variable> ::= <identifier>"_"
    ///
    /// <application> ::= <constant> | <binary-application> | <standard-application>
    ///
    /// <constant> ::= <identifier>
    ///
    /// <binary-application> ::= "(" <term> " " <term> ")"
    ///
    /// <standard-application> ::= <identifier> "(" <term>* ")"
    ///
    /// <identifier> ::= <alphanumeric>+
    /// ```
    ///
    /// [`TRS`]: struct.TRS.html
    /// [`Term`]: enum.Term.html
    /// [`Ok((trs, terms))`]:  https://doc.rust-lang.org/std/result/enum.Result.html#variant.Ok
    /// [`Err`]:  https://doc.rust-lang.org/std/result/enum.Result.html#variant.Err
    pub fn parse<'a>(&mut self, input: &'a str) -> Result<(TRS, Vec<Term>), &'a str> {
        parser::parse(input, self)
    }
}
impl Default for Signature {
    fn default() -> Self {
        Signature {
            operators: vec![],
            variables: vec![],
            operator_count: 0,
            variable_count: 0,
        }
    }
}

/// Represents a first-order term rewriting system.
#[derive(Debug, PartialEq)]
pub struct TRS {
    rules: Vec<Rule>,
}
impl TRS {
    /// Constructs a term rewriting system from a list of rules.
    pub fn new(rules: Vec<Rule>) -> TRS {
        TRS { rules }
    }
}

#[cfg(test)]
mod tests;
