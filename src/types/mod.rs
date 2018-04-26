use itertools::Itertools;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::iter;

use super::parser;

/// Represents a unique identity, a [DeBruijn Index].
///
/// [DeBruijn Index]: https://en.wikipedia.org/wiki/De_Bruijn_index
pub type DeBruijn = usize;

/// Represents a place in a [`Term`]
///
/// [`Term`]: struct.Term.html
pub type Place = Vec<usize>;

/// An ADT for Variables.
pub trait Variable: Eq + Ord + Hash + Clone {
    /// Construct a new `Variable` that has not been used.
    fn new_distinct<'a, T>(existing: T, name: Option<String>) -> Self
    where
        T: IntoIterator<Item = &'a Self>,
        Self: 'a;
    /// A human-readable representation of the variable.
    fn show(&self) -> String {
        "<variable>".to_string()
    }
}

/// An ADT for Operators.
pub trait Operator: Eq + Hash + Clone {
    /// Construct a new `Operator` that has not been used.
    fn new_distinct<'a, T>(operators: T, arity: usize, name: Option<String>) -> Self
    where
        T: IntoIterator<Item = &'a Self>,
        Self: 'a;
    /// The number of arguments a particular operator takes.
    fn arity(&self) -> usize;
    /// A human-readable representation of the operator.
    fn show(&self) -> String {
        "<operator>".to_string()
    }
}

/// Represents a symbol with fixed [`Arity`].
///
/// [`Arity`]: type.Arity_.html
#[derive(Debug, Clone, Eq)]
pub struct Op {
    id: DeBruijn,
    arity: usize,
    name: Option<String>,
}
impl Op {
    pub fn new(id: DeBruijn, arity: usize, name: Option<String>) -> Op {
        Op { id, arity, name }
    }
    pub fn name(&self) -> Option<&str> {
        self.name.as_ref().map(|s| s.as_str())
    }
}
impl Hash for Op {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
        self.arity.hash(state);
    }
}
impl PartialEq for Op {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.arity == other.arity
    }
}
impl Operator for Op {
    fn new_distinct<'a, T>(ops: T, arity: usize, name: Option<String>) -> Op
    where
        T: IntoIterator<Item = &'a Op>,
    {
        let id = match ops.into_iter().map(|o| o.id).max() {
            Some(n) => n + 1,
            _ => 0,
        };
        Op { id, arity, name }
    }
    fn arity(&self) -> usize {
        self.arity
    }
    fn show(&self) -> String {
        if let Some(ref s) = self.name {
            s.clone()
        } else {
            format!("<op {}/{}>", self.id, self.arity)
        }
    }
}

/// Represents a symbol signifying an unspecified [`Term`].
///
/// [`Term`]: enum.Term.html
#[derive(Debug, Clone, Eq)]
pub struct Var {
    id: DeBruijn,
    name: Option<String>,
}
impl Var {
    pub fn new(id: DeBruijn, name: Option<String>) -> Self {
        Var { id, name }
    }
    pub fn name(&self) -> Option<&str> {
        self.name.as_ref().map(|s| s.as_str())
    }
}
impl Hash for Var {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Ord for Var {
    fn cmp(&self, other: &Var) -> Ordering {
        self.id.cmp(&other.id)
    }
}
impl PartialOrd for Var {
    fn partial_cmp(&self, other: &Var) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Variable for Var {
    fn new_distinct<'a, T>(existing: T, name: Option<String>) -> Var
    where
        T: IntoIterator<Item = &'a Var>,
    {
        let id = match existing.into_iter().map(|o| o.id).max() {
            Some(n) => n + 1,
            _ => 0,
        };
        Var { id, name }
    }
    fn show(&self) -> String {
        if let Some(ref s) = self.name {
            s.clone()
        } else {
            format!("<var {}>", self.id)
        }
    }
}

/// A way of signifying what type of unification is being performed
#[derive(PartialEq, Eq)]
enum Unification {
    Match,
    Unify,
}

/// Represents a first-order term: either a [`Variable`] or an [`Application`]
/// of an [`Operator`] to [`Term`]s
///
/// [`Variable`]: trait.Variable.html
/// [`Application`]: enum.Term.html#variant.Application
/// [`Operator`]: trait.Operator.html
/// [`Term`]: enum.Term.html
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Term<V: Variable, O: Operator> {
    /// A concrete but unspecified [`Term<V,O>`] (e.g. `x`, `y`)
    ///
    /// [`Term<V,O>`]: enum.Term.html
    Variable(V),
    /// some [`Operator`] applied to zero or more [`Term<V,O>`s] (e.g. (`f(x, y)`, `g()`)
    ///
    /// [`Operator`]: trait.Operator.html
    /// [`Term<V,O>`s]: enum.Term.html
    Application { head: O, args: Vec<Term<V, O>> },
}
impl<V: Variable, O: Operator> Term<V, O> {
    /// Return a [`Vec`] referencing every [`Variable`] in `self`.
    ///
    /// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Variable`]: trait.Variable.html
    pub fn variables(&self) -> Vec<&V> {
        match *self {
            Term::Variable(ref v) => vec![v],
            Term::Application { ref args, .. } => {
                args.iter().flat_map(|x| x.variables()).unique().collect()
            }
        }
    }
    /// Return a [`Vec`] referencing every [`Operator`] in `self`.
    ///
    /// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Operator`]: struct.Operator.html
    pub fn operators(&self) -> Vec<&O> {
        match *self {
            Term::Variable(_) => vec![],
            Term::Application { ref head, ref args } => args.iter()
                .flat_map(|x| x.operators())
                .chain(iter::once(head))
                .unique()
                .collect(),
        }
    }
    /// Return a [`Vec`] containing every [`Place`] in `self`.
    ///
    /// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
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
    /// Return a [`Vec`] referencing every [`Term`] in `self`.
    ///
    /// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Term`]: enum.Term.html
    pub fn subterms(&self) -> Vec<&Term<V, O>> {
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
    pub fn at(&self, place: &[usize]) -> Option<&Term<V, O>> {
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
    /// Return a [`some(term)`], where is a copy of `self` where the [`Term`]
    /// at [`Place`] `place` has been replaced with `subterm`, otherwise
    /// [`None`].
    ///
    /// [`Some(term)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`Place`]: type.Place.html
    /// [`Term`]: enum.Term.html
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn replace(&self, place: &[usize], subterm: Term<V, O>) -> Option<Term<V, O>> {
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
    /// Return a [`Vec`] referencing every unbound [`Variable`] that occurs in `self`.
    ///
    /// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    /// [`Variable`]: trait.Variable.html
    pub fn free_vars(&self) -> Vec<&V> {
        self.variables()
    }
    /// Given a mapping from [`Variable`s] to [`Term`s], perform a substitution on a [`Term`].
    ///
    /// [`Variable`s]: trait.Variable.html
    /// [`Term`s]: enum.Term.html
    /// [`Term`]: enum.Term.html
    pub fn substitute(&self, sub: &HashMap<V, Term<V, O>>) -> Term<V, O> {
        match *self {
            Term::Variable(ref v) => sub.get(v).unwrap_or(self).clone(),
            Term::Application { ref head, ref args } => Term::Application {
                head: head.clone(),
                args: args.iter().map(|x| x.substitute(sub)).collect(),
            },
        }
    }
    /// Take a vector of pairs of terms and perform a substitution on each term.
    fn constraint_substitute(
        cs: &[(Term<V, O>, Term<V, O>)],
        sub: &HashMap<V, Term<V, O>>,
    ) -> Vec<(Term<V, O>, Term<V, O>)> {
        cs.iter()
            .map(|&(ref s, ref t)| (s.substitute(sub), t.substitute(sub)))
            .collect()
    }
    /// Compose two substitutions.
    fn compose(
        sub1: Option<HashMap<V, Term<V, O>>>,
        sub2: Option<HashMap<V, Term<V, O>>>,
    ) -> Option<HashMap<V, Term<V, O>>> {
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
    pub fn alpha_equivalent(t1: &Term<V, O>, t2: &Term<V, O>) -> bool {
        Term::pmatch(vec![(t1.clone(), t2.clone())]).is_some()
            && Term::pmatch(vec![(t2.clone(), t1.clone())]).is_some()
    }
    pub fn shape_equivalent(t1: &Term<V, O>, t2: &Term<V, O>) -> bool {
        let mut vmap = HashMap::new();
        let mut omap = HashMap::new();
        Term::se_helper(t1, t2, &mut vmap, &mut omap)
    }
    pub fn se_helper(
        t1: &Term<V, O>,
        t2: &Term<V, O>,
        vmap: &mut HashMap<V, V>,
        omap: &mut HashMap<O, O>,
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
    pub fn pmatch(cs: Vec<(Term<V, O>, Term<V, O>)>) -> Option<HashMap<V, Term<V, O>>> {
        Term::unify_internal(cs, Unification::Match)
    }
    /// Given a vector of contraints, return [`Some(sigma)`] if the constraints
    /// can be satisfied, where `sigma` is a substitution, otherwise [`None`].
    ///
    /// [`Some(sigma)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn unify(cs: Vec<(Term<V, O>, Term<V, O>)>) -> Option<HashMap<V, Term<V, O>>> {
        Term::unify_internal(cs, Unification::Unify)
    }
    /// the internal implementation of unify and match.
    fn unify_internal(
        mut cs: Vec<(Term<V, O>, Term<V, O>)>,
        utype: Unification,
    ) -> Option<HashMap<V, Term<V, O>>> {
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
pub struct Rule<V: Variable, O: Operator> {
    lhs: Term<V, O>,
    rhs: Vec<Term<V, O>>,
}
impl<V: Variable, O: Operator> Rule<V, O> {
    /// logic ensuring that the `lhs` and `rhs` are compatible.
    fn is_valid(lhs: &Term<V, O>, rhs: &[Term<V, O>]) -> bool {
        // the lhs must be an application
        if let Term::Application { .. } = *lhs {
            // variables(rhs) must be a subset of variables(lhs)
            let lhs_vars: HashSet<&V> = lhs.variables().into_iter().collect();
            let rhs_vars: HashSet<&V> = rhs.iter().flat_map(|r| r.variables()).collect();
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
    /// [`Variable`]: trait.Variable.html
    /// [`Some(Rule{lhs, rhs})`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn new(lhs: Term<V, O>, rhs: Vec<Term<V, O>>) -> Option<Rule<V, O>> {
        if Rule::is_valid(&lhs, &rhs) {
            Some(Rule { lhs, rhs })
        } else {
            None
        }
    }
}

/// Represents a first-order term rewriting system.
#[derive(Debug, PartialEq)]
pub struct TRS<V: Variable, O: Operator> {
    rules: Vec<Rule<V, O>>,
}
impl<V: Variable, O: Operator> TRS<V, O> {
    /// Constructs a term rewriting system from a list of rules.
    pub fn new(rules: Vec<Rule<V, O>>) -> TRS<V, O> {
        TRS { rules }
    }
    // Return rewrites modifying the entire term, if possible, else None.
    fn rewrite_head(&self, term: &Term<V, O>) -> Option<Vec<Term<V, O>>> {
        for rule in &self.rules {
            if let Some(ref sub) = Term::pmatch(vec![(rule.lhs.clone(), term.clone())]) {
                return Some(rule.rhs.iter().map(|x| x.substitute(sub)).collect());
            }
        }
        None
    }
    // Return rewrites modifying subterms, if possible, else None.
    fn rewrite_args(&self, term: &Term<V, O>) -> Option<Vec<Term<V, O>>> {
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
    pub fn rewrite(&self, term: &Term<V, O>) -> Option<Vec<Term<V, O>>> {
        match term {
            &Term::Variable(_) => None,
            app => self.rewrite_head(app).or_else(|| self.rewrite_args(app)),
        }
    }
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
pub fn parse(
    operators: &[Op],
    input: &str,
) -> Result<(TRS<Var, Op>, Vec<Term<Var, Op>>), parser::ParseError> {
    parser::parse(input, operators)
}
/// Similar to `parse`, but produces only a [`TRS`].
///
/// [`TRS`]: struct.TRS.html
pub fn parse_trs(operators: &[Op], input: &str) -> Result<TRS<Var, Op>, parser::ParseError> {
    parser::parse_trs(input, operators)
}
/// Similar to `parse`, but produces only a [`Term`].
///
/// [`Term`]: struct.Term.html
pub fn parse_term(operators: &[Op], input: &str) -> Result<Term<Var, Op>, parser::ParseError> {
    parser::parse_term(input, operators)
}

#[cfg(test)]
mod tests;
