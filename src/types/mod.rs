use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::iter;

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

/// Represents a place in a [`Term`]
///
/// [`Term`]: struct.Term.html
pub type Place = Vec<usize>;

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

/// What type of unification is being performed?
#[derive(PartialEq, Eq)]
enum Unification {
    Match,
    Unify,
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
    /// Return a [`Vec<&Variable>`] referencing every [`Variable`] in `self`.
    ///
    /// [`Vec<&Variable>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Variable`]: struct.Variable.html
    pub fn variables(&self) -> Vec<&Variable> {
        match *self {
            Term::Variable(ref v) => vec![v],
            Term::Application { ref args, .. } => {
                args.iter().flat_map(|x| x.variables()).unique().collect()
            }
        }
    }
    /// Return a [`Vec<&Operator>`] referencing every [`Operator`] in `self`.
    ///
    /// [`Vec<&Operator>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Operator`]: struct.Operator.html
    pub fn operators(&self) -> Vec<&Operator> {
        match *self {
            Term::Variable(_) => vec![],
            Term::Application { ref head, ref args } => args.iter()
                .flat_map(|x| x.operators())
                .chain(iter::once(head))
                .unique()
                .collect(),
        }
    }
    /// Return a [`Vec<Place>`] containing every [`Place`] in `self`.
    ///
    /// [`Vec<Place>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Place`]: type.Place.html
    pub fn places(&self) -> Vec<Place> {
        match *self {
            Term::Variable(_) => vec![vec![]],
            Term::Application { ref args, .. } => {
                let here = iter::once(vec![]);
                let subplaces = args.iter().enumerate().flat_map(|(i, arg)| {
                    arg.places()
                        .into_iter()
                        .zip(iter::repeat(i))
                        .map(|(p, ii)| {
                            let mut a = vec![ii];
                            a.extend(p);
                            a
                        })
                });
                here.chain(subplaces).collect()
            }
        }
    }
    /// Return a [`Vec<&Term>`] referencing every [`Term`] in `self`.
    ///
    /// [`Vec<&Term>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Term`]: enum.Term.html
    pub fn subterms(&self) -> Vec<&Term> {
        match *self {
            Term::Variable(_) => vec![self],
            Term::Application { ref args, .. } => {
                let here = iter::once(self);
                let subterms = args.iter().flat_map(|a| a.subterms());
                here.chain(subterms).collect()
            }
        }
    }
    /// Return [`Some(t)`] if `t` is the subterm at [`Place`] `place`, else [`None`].
    ///
    /// [`Some(t)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`Place`]: type.Place.html
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn at(&self, place: &[usize]) -> Option<&Term> {
        if place.is_empty() {
            Some(self)
        } else {
            match *self {
                Term::Variable(_) => None,
                Term::Application { ref args, .. } => if place[0] <= args.len() {
                    args[place[0]].at(&place[1..].to_vec())
                } else {
                    None
                },
            }
        }
    }
    /// Return a [`some(term)`], where is a copy of `self` where the [`Term`] at [`Place`] `place` has been replaced with `subterm`, otherwise [`None`].
    ///
    /// [`Some(term)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`Place`]: type.Place.html
    /// [`Term`]: enum.Term.html
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn replace(&self, place: &[usize], subterm: Term) -> Option<Term> {
        if place.is_empty() {
            Some(subterm)
        } else {
            match *self {
                Term::Variable(_) => None,
                Term::Application { ref head, ref args } => if place[0] <= args.len() {
                    if let Some(term) = args[place[0]].replace(&place[1..].to_vec(), subterm) {
                        let mut new_args = args.clone();
                        new_args.remove(place[0]);
                        new_args.insert(place[0], term);
                        Some(Term::Application {
                            head: head.clone(),
                            args: new_args,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                },
            }
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
    /// Given two terms, return `true` if they are [alpha equivalent], else `false`.
    ///
    /// [alpha equivalent]: https://en.wikipedia.org/wiki/Lambda_calculus#Alpha_equivalence
    pub fn alpha_equivalent(t1: &Term, t2: &Term) -> bool {
        Term::pmatch(vec![(t1.clone(), t2.clone())]).is_some()
            && Term::pmatch(vec![(t2.clone(), t1.clone())]).is_some()
    }
    pub fn shape_equivalent(t1: &Term, t2: &Term) -> bool {
        let mut vmap = HashMap::new();
        let mut omap = HashMap::new();
        Term::se_helper(t1, t2, &mut vmap, &mut omap)
    }
    pub fn se_helper(
        t1: &Term,
        t2: &Term,
        vmap: &mut HashMap<Variable, Variable>,
        omap: &mut HashMap<Operator, Operator>,
    ) -> bool {
        match (t1, t2) {
            (&Term::Variable(ref v1), &Term::Variable(ref v2)) => {
                v2 == vmap.entry(v1.clone()).or_insert_with(|| v2.clone())
            }
            (
                &Term::Application {
                    head: ref h1,
                    args: ref as1,
                },
                &Term::Application {
                    head: ref h2,
                    args: ref as2,
                },
            ) => {
                h2 == omap.entry(h1.clone()).or_insert_with(|| h2.clone())
                    && as1.iter()
                        .zip(as2.iter())
                        .all(|(a1, a2)| Term::se_helper(a1, a2, vmap, omap))
            }
            _ => false,
        }
    }
    /// Given a vector of contraints, return [`Some(sigma)`] if the constraints
    /// can be satisfied, where `sigma` is a substitution, otherwise [`None`].
    ///
    /// [`Some(sigma)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn pmatch(cs: Vec<(Term, Term)>) -> Option<Substitution> {
        Term::unify_internal(cs, Unification::Match)
    }
    /// Given a vector of contraints, return [`Some(sigma)`] if the constraints
    /// can be satisfied, where `sigma` is a substitution, otherwise [`None`].
    ///
    /// [`Some(sigma)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn unify(cs: Vec<(Term, Term)>) -> Option<Substitution> {
        Term::unify_internal(cs, Unification::Unify)
    }
    /// the internal implementation of unify and match.
    fn unify_internal(mut cs: Vec<(Term, Term)>, utype: Unification) -> Option<Substitution> {
        let c = cs.pop();
        match c {
            None => Some(HashMap::new()),
            Some((ref s, ref t)) if s == t => Term::unify_internal(cs, utype),
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
                Term::unify_internal(cs, utype)
            }
            Some((Term::Variable(ref var), ref t)) if !Term::free_vars(t).contains(&var) => {
                let mut st = HashMap::new();
                st.insert(var.clone(), t.clone());
                let mut cs = Term::constraint_substitute(&cs, &st);
                Term::compose(Term::unify_internal(cs, utype), Some(st))
            }
            Some((ref s, Term::Variable(ref var)))
                if !Term::free_vars(s).contains(&var) && utype != Unification::Match =>
            {
                let mut ts = HashMap::new();
                ts.insert(var.clone(), s.clone());
                let mut cs = Term::constraint_substitute(&cs, &ts);
                Term::compose(Term::unify_internal(cs, utype), Some(ts))
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
    pub fn parse(&mut self, input: &str) -> Result<(TRS, Vec<Term>), parser::ParseError> {
        parser::parse(input, self)
    }
    /// Similar to `parse`, but produces only a [`TRS`].
    ///
    /// [`TRS`]: struct.TRS.html
    pub fn parse_trs(&mut self, input: &str) -> Result<TRS, parser::ParseError> {
        parser::parse_trs(input, self)
    }
    /// Similar to `parse`, but produces only a [`Term`].
    ///
    /// [`Term`]: struct.Term.html
    pub fn parse_term(&mut self, input: &str) -> Result<Term, parser::ParseError> {
        parser::parse_term(input, self)
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
        if let Term::Application { ref head, ref args } = *term {
            for (i, arg) in args.iter().enumerate() {
                if let Some(v) = self.rewrite(arg) {
                    let res = v.iter()
                        .map(|x| {
                            let head = head.clone();
                            let mut args = args.clone();
                            args[i] = x.clone();
                            Term::Application { head, args }
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
    pub fn rewrite(&self, term: &Term) -> Option<Vec<Term>> {
        match term {
            &Term::Variable(_) => None,
            app => self.rewrite_head(app).or_else(|| self.rewrite_args(app)),
        }
    }
}

#[cfg(test)]
mod tests;
