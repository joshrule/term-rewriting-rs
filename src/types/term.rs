use super::super::pretty::Pretty;
use super::{Atom, Operator, Place, Signature, Unification, Variable};
use itertools::Itertools;
use std::collections::HashMap;
use std::iter;

/// A first-order `Context`: a [`Term`] that may have [`Hole`]s; a sort of [`Term`] template.
///
/// [`Term`]: enum.Term.html
/// [`Hole`]: enum.Context.html#variant.Hole
///
/// Examples
///
/// ```
/// # use term_rewriting::{Signature, Context, parse_context};
/// let mut sig = Signature::default();
///
/// // Constructing a Context manually.
/// let a = sig.new_op(3, Some("A".to_string()));
/// let b = sig.new_op(0, Some("B".to_string()));
/// let x = sig.new_var(Some("x".to_string()));
///
/// let b_context = Context::Application { op: b, args: vec![] };
/// let x_context = Context::Variable(x);
///
/// let context = Context::Application { op: a, args: vec![ b_context, x_context, Context::Hole ] };
///
/// // Constructing a Context using the Parser.
/// let context2 = parse_context(&mut sig, "A(B x_ [!])").expect("parse of A(B x_ [!])");
///
/// assert_eq!(context.display(&sig), context2.display(&sig));
/// ```
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Context {
    /// An empty place in the `Context`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context, Context};
    /// // Constructing a hole manually.
    /// let h = Context::Hole;
    ///
    /// // Constructing a hole using the parser.
    /// let mut sig = Signature::default();
    /// let h2 = parse_context(&mut sig, "[!]").expect("parse of [!]");
    ///
    /// assert_eq!(h.display(&sig), h2.display(&sig));
    /// ```
    Hole,
    /// A concrete but unspecified `Context` (e.g. `x`, `y`)
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context, Context};
    /// let mut sig = Signature::default();
    ///
    /// // Constructing a Context Variable manually.
    /// let v = sig.new_var(Some("x".to_string()));
    /// let var = Context::Variable(v);
    ///
    /// //Contstructing a Context Variable using the parser.
    /// let var2 = parse_context(&mut sig, "x_").expect("parse of x_");
    ///
    /// assert_eq!(var.display(&sig), var2.display(&sig));
    /// ```
    Variable(Variable),
    /// An [`Operator`] applied to zero or more `Context`s (e.g. (`f(x, y)`, `g()`)
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context, Context};
    /// let mut sig = Signature::default();
    ///
    /// // Constructing a Context Application manually.
    /// let a = sig.new_op(0, Some("A".to_string()));
    /// let app = Context::Application { op: a, args: vec![] };
    ///
    /// // Constructing a Context Application using the parser.
    /// let app2 = parse_context(&mut sig, "A").expect("parse of A");
    ///
    /// assert_eq!(app, app2);
    /// ```
    Application { op: Operator, args: Vec<Context> },
}
impl Context {
    /// Serialize a `Context`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, Context, Variable, Operator, parse_context};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "x_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
    ///     .expect("parse of x_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)") ;
    ///
    /// assert_eq!(context.display(&sig), ".(.(.(.(x_ [!]) A) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5))");
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
                    let args_str = args.iter().map(|c| c.display(sig)).join(" ");
                    format!("{}({})", op_str, args_str)
                }
            }
        }
    }
    /// A human-readable serialization of the `Context`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "x_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
    ///     .expect("parse of x_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)") ;
    ///
    /// assert_eq!(context.pretty(&sig), "x_ [!] A [2, 1, 0] 105");
    /// ```
    pub fn pretty(&self, sig: &Signature) -> String {
        Pretty::pretty(self, sig)
    }
    /// Every [`Atom`] used in the `Context`.
    ///
    /// [`Atom`]: enum.Atom.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "A(B x_ [!])").expect("parse of A(B x_ [!])");
    ///
    /// let atoms: Vec<String> = context.atoms().iter().map(|a| a.display(&sig)).collect();
    ///
    /// assert_eq!(atoms, vec!["x_", "B", "A"]);
    /// ```
    pub fn atoms(&self) -> Vec<Atom> {
        let vars = self.variables().into_iter().map(Atom::Variable);
        let ops = self.operators().into_iter().map(Atom::Operator);
        vars.chain(ops).collect()
    }
    /// Every [`Variable`] used in the `Context`.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context, Context};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "A([!]) B y_ z_").expect("parse of A([!]) B y_ z_");
    ///
    /// let var_names: Vec<String> = context.variables().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(var_names, vec!["y_".to_string(), "z_".to_string()]);
    /// ```
    pub fn variables(&self) -> Vec<Variable> {
        match *self {
            Context::Hole => vec![],
            Context::Variable(v) => vec![v],
            Context::Application { ref args, .. } => {
                let mut vars = args.iter().flat_map(Context::variables).collect_vec();
                vars.sort();
                vars.dedup();
                vars
            }
        }
    }
    /// Every [`Operator`] used in the `Context`.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context, Context};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "A([!]) B y_ z_").expect("parse of A([!]) B y_ z_");
    ///
    /// let op_names: Vec<String> = context.operators().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(op_names, vec!["A".to_string(), "B".to_string(), ".".to_string()]);
    /// ```
    pub fn operators(&self) -> Vec<Operator> {
        if let Context::Application { op, ref args } = *self {
            let mut ops = args
                .iter()
                .flat_map(Context::operators)
                .chain(iter::once(op))
                .collect_vec();
            ops.sort();
            ops.dedup();
            ops
        } else {
            vec![]
        }
    }
    /// A list of the [`Place`]s in the `Context` that are `Hole`s.
    ///
    /// [`Place`]: type.Place.html
    /// [`Hole`]: enum.Context.html#variant.Hole
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context, Place};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "A([!] B([!]) y_ z_)").expect("parse of A([!] B([!]) y_ z_)");
    ///
    /// let p: &[usize] = &[0];
    /// let p2: &[usize] = &[1, 0];
    ///
    /// assert_eq!(context.holes(), vec![p, p2]);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context, Atom};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "A(B([!]) z_)").expect("parse of A(B([!]) z_)");
    ///
    /// assert_eq!(context.head().unwrap().display(&sig), "A");
    /// ```
    pub fn head(&self) -> Option<Atom> {
        match *self {
            Context::Hole => None,
            Context::Variable(v) => Some(Atom::Variable(v)),
            Context::Application { op, .. } => Some(Atom::Operator(op)),
        }
    }
    /// The args of the `Context`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context, Atom};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "A B").expect("parse of A B");
    /// let args: Vec<String> = context.args().iter().map(|arg| arg.display(&sig)).collect();
    ///
    /// assert_eq!(args, vec!["A", "B"]);
    ///
    /// let context = parse_context(&mut sig, "A(y_)").expect("parse of A(y_)");
    /// let args: Vec<String> = context.args().iter().map(|arg| arg.display(&sig)).collect();
    ///
    /// assert_eq!(args, vec!["y_"]);
    /// ```
    pub fn args(&self) -> Vec<Context> {
        if let Context::Application { args, .. } = self {
            args.clone()
        } else {
            vec![]
        }
    }
    /// Every `subcontext` and its [`Place`], starting with the original `Context` itself.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context, Context};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "A(B [!])").expect("parse of A(B [!])");
    ///
    /// let p: Vec<usize> = vec![];
    /// let subcontext0 = parse_context(&mut sig, "A(B [!])").expect("parse of A(B [!])");
    ///
    /// let p1: Vec<usize> = vec![0];
    /// let subcontext1 = parse_context(&mut sig, "B").expect("parse of B");
    ///
    /// let p2: Vec<usize> = vec![1];
    /// let subcontext2 = Context::Hole;
    ///
    /// assert_eq!(context.subcontexts(), vec![(&subcontext0, p), (&subcontext1, p1), (&subcontext2, p2)]);
    /// ```
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
    /// The number of distinct [`Place`]s in the `Context`.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context};
    /// let mut sig = Signature::default();
    /// let context = parse_context(&mut sig, "A B").expect("parse of A B");
    ///
    /// assert_eq!(context.size(), 3);
    ///
    /// let context = parse_context(&mut sig, "A(B)").expect("parse of A(B)");
    ///
    /// assert_eq!(context.size(), 2);
    /// ```
    pub fn size(&self) -> usize {
        self.subcontexts().len()
    }
    /// Get the `subcontext` at the given [`Place`], or `None` if the [`Place`] does not exist.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context};
    /// let mut sig = Signature::default();
    /// let context = parse_context(&mut sig, "B(A)").expect("parse of B(A)");
    ///
    /// let p: &[usize] = &[7];
    ///
    /// assert_eq!(context.at(p), None);
    ///
    /// let p: &[usize] = &[0];
    ///
    /// assert_eq!(context.at(p).unwrap().display(&sig), "A");
    /// ```
    #[cfg_attr(feature = "cargo-clippy", allow(clippy::ptr_arg))]
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
    /// Create a copy of the `Context` where the subcontext at the given [`Place`] has been replaced with
    /// `subcontext`.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "B(A)").expect("parse of B(A)");
    /// let context2 = parse_context(&mut sig, "C [!]").expect("parse of C [!]");
    ///
    /// let p: &[usize] = &[0];
    /// let new_context = context.replace(p, context2);
    ///
    /// assert_eq!(new_context.unwrap().pretty(&sig), "B(C [!])");
    /// ```
    pub fn replace(&self, place: &[usize], subcontext: Context) -> Option<Context> {
        self.replace_helper(&*place, subcontext)
    }
    pub fn fill(&self, fillers: &[Context]) -> Option<Context> {
        let mut context = self.clone();
        for (i, hole) in self.holes().iter().enumerate().take(fillers.len()) {
            context = context.replace(hole, fillers[i].clone())?;
        }
        Some(context)
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
    /// Translate the `Context` into a [`Term`], if possible.
    ///
    /// [`Term`]: enum.Term.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_context};
    /// let mut sig = Signature::default();
    ///
    /// let context = parse_context(&mut sig, "A(B [!])").expect("parse of A(B [!])");
    ///
    /// assert!(context.to_term().is_err());
    ///
    /// let context = parse_context(&mut sig, "A(B C)").expect("parse of A(B C)");
    ///
    /// let term = context.to_term().expect("converting context to term");
    ///
    /// assert_eq!(term.display(&sig), "A(B C)");
    /// ```
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
    /// `true` if `self` is a more general instance of some `Term`.
    pub fn generalize<'a>(
        cs: Vec<(&'a Context, &'a Context)>,
    ) -> Option<HashMap<&'a Variable, &'a Context>> {
        Context::unify_internal(cs, Unification::Generalize)
    }
    /// Compute the [alpha equivalence] for two `Context`s.
    ///
    /// [alpha equivalence]: https://en.wikipedia.org/wiki/Lambda_calculus#Alpha_equivalence
    pub fn alpha<'a>(
        cs: Vec<(&'a Context, &'a Context)>,
    ) -> Option<HashMap<&'a Variable, &'a Context>> {
        Context::unify_internal(cs, Unification::Alpha)
    }
    /// Given a vector of constraints, return a substitution which satisfies the
    /// constraints. If the constraints are not satisfiable, return `None`.
    /// Constraints are in the form of patterns, where substitutions are only
    /// considered for variables in the first `Context` of each pair.
    ///
    /// For more information see [`Pattern Matching`].
    ///
    /// [`Pattern Matching`]: https://en.wikipedia.org/wiki/Pattern_matching
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context};
    /// # use std::collections::{HashMap, HashSet};
    /// let mut sig = Signature::default();
    ///
    /// let t1 = parse_context(&mut sig, "C(A)").expect("parse of C(A)");
    /// let t2 = parse_context(&mut sig, "C([!])").expect("parse of C([!])");
    /// let t3 = parse_context(&mut sig, "C([!])").expect("parse of C(x_)");
    /// let t4 = parse_context(&mut sig, "C(x_)").expect("parse of C(x_)");
    ///
    /// assert_eq!(Context::pmatch(vec![(&t1, &t2)]), None);
    /// assert_eq!(Context::pmatch(vec![(&t2, &t1)]), None);
    /// assert_eq!(Context::pmatch(vec![(&t2, &t3)]), Some(HashMap::new()));
    ///
    /// // Map variable x in term t4 to hole [!] in term t3.
    /// let t_k = &t4.variables()[0];
    /// let t_v = Context::Hole;
    /// let mut expected_sub = HashMap::new();
    /// expected_sub.insert(t_k, &t_v);
    ///
    /// assert_eq!(Context::pmatch(vec![(&t4, &t3)]), Some(expected_sub));
    /// ```
    pub fn pmatch<'a>(
        cs: Vec<(&'a Context, &'a Context)>,
    ) -> Option<HashMap<&'a Variable, &'a Context>> {
        Context::unify_internal(cs, Unification::Match)
    }
    /// Given a vector of constraints, return a substitution which satisfies the
    /// constraints. If the constraints are not satisfiable, return `None`.
    ///
    /// For more information see [`Unification`].
    ///
    /// [`Unification`]: https://en.wikipedia.org/wiki/Unification_(computer_science)
    ///
    /// # Examples
    ///
    /// Given
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_term};
    /// # use std::collections::{HashMap, HashSet};
    /// let mut sig = Signature::default();
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context};
    /// # use std::collections::{HashMap, HashSet};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_context(&mut sig, "C(A)").expect("parse of C(A)");
    /// let t2 = parse_context(&mut sig, "C([!])").expect("parse of C([!])");
    ///
    /// assert_eq!(Context::unify(vec![(&t1, &t2)]), None);
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context};
    /// # use std::collections::{HashMap, HashSet};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_context(&mut sig, "C(x_)").expect("parse of C(x_)");
    /// let t2 = parse_context(&mut sig, "C([!])").expect("parse of C([!])");
    ///
    /// // Map variable x in term t2 to variable y in term t2.
    /// let mut expected_sub = HashMap::new();
    /// let t_k = &t1.variables()[0];
    /// let t_v = Context::Hole;
    /// expected_sub.insert(t_k, &t_v);
    ///
    /// assert_eq!(Context::unify(vec![(&t1, &t2)]), Some(expected_sub));
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_context};
    /// # use std::collections::{HashMap, HashSet};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_context(&mut sig, "C([!])").expect("parse of C([!])");
    /// let t2 = parse_context(&mut sig, "C([!])").expect("parse of C([!])");
    ///
    /// assert_eq!(Context::unify(vec![(&t1, &t2)]), Some(HashMap::new()));
    /// ```
    pub fn unify<'a>(
        cs: Vec<(&'a Context, &'a Context)>,
    ) -> Option<HashMap<&'a Variable, &'a Context>> {
        Context::unify_internal(cs, Unification::Unify)
    }
    /// the internal implementation of unify and match.
    fn unify_internal<'a>(
        mut cs: Vec<(&'a Context, &'a Context)>,
        utype: Unification,
    ) -> Option<HashMap<&'a Variable, &'a Context>> {
        let mut subs: HashMap<&Variable, &Context> = HashMap::new();
        while !cs.is_empty() {
            let (mut s, mut t) = cs.pop().unwrap();

            while let Context::Variable(ref v) = *s {
                if subs.contains_key(v) {
                    s = &subs[v];
                } else {
                    break;
                }
            }

            while let Context::Variable(ref v) = *t {
                if subs.contains_key(v) {
                    t = &subs[v];
                } else {
                    break;
                }
            }

            // if they are equal, you're all done with them.
            if s != t {
                match (s, t) {
                    (Context::Hole, Context::Hole) => (),
                    (Context::Hole, _) if utype == Unification::Generalize => (),
                    (Context::Variable(ref var), Context::Variable(_)) => {
                        subs.insert(var, t);
                    }
                    (Context::Variable(ref var), t)
                        if utype != Unification::Alpha && utype != Unification::Generalize =>
                    {
                        if !(*t).variables().contains(&&var) {
                            subs.insert(var, t);
                        } else {
                            return None;
                        }
                    }
                    (s, Context::Variable(ref var)) if utype == Unification::Unify => {
                        if !(*s).variables().contains(&&var) {
                            subs.insert(var, s);
                        } else {
                            return None;
                        }
                    }
                    (
                        Context::Application {
                            op: ref h1,
                            args: ref a1,
                        },
                        Context::Application {
                            op: ref h2,
                            args: ref a2,
                        },
                    ) if h1 == h2 => {
                        cs.append(&mut a1.iter().zip(a2.iter()).collect());
                    }
                    _ => {
                        return None;
                    }
                }
            }
        }
        Some(subs)
    }
}
impl From<&Term> for Context {
    fn from(t: &Term) -> Context {
        match *t {
            Term::Variable(v) => Context::Variable(v),
            Term::Application { op, ref args } => {
                let args = args.iter().map(Context::from).collect();
                Context::Application { op, args }
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
impl From<Atom> for Context {
    fn from(a: Atom) -> Context {
        match a {
            Atom::Variable(v) => Context::Variable(v),
            Atom::Operator(op) => {
                let args = iter::repeat(Context::Hole)
                    .take(op.arity() as usize)
                    .collect_vec();
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
    /// Serialize a `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let term = parse_term(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
    ///     .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)");
    ///
    /// assert_eq!(term.display(&sig), ".(.(.(A B(x_)) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5))");
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        match self {
            Term::Variable(ref v) => v.display(sig),
            Term::Application { ref op, ref args } => {
                let op_str = op.display(sig);
                if args.is_empty() {
                    op_str
                } else {
                    let args_str = args.iter().map(|t| t.display(sig)).join(" ");
                    format!("{}({})", op_str, args_str)
                }
            }
        }
    }
    /// A human-readable serialization of the `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let term = parse_term(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
    ///     .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)");
    ///
    /// assert_eq!(term.pretty(&sig), "A B(x_) [2, 1, 0] 105");
    /// ```
    pub fn pretty(&self, sig: &Signature) -> String {
        Pretty::pretty(self, sig)
    }
    /// A short-cut for creating `Application`s.
    pub fn apply(op: Operator, args: Vec<Term>) -> Option<Term> {
        if op.arity() == (args.len() as u32) {
            Some(Term::Application { op, args })
        } else {
            None
        }
    }
    pub fn as_application(&self) -> Option<(&Operator, &[Term])> {
        match self {
            Term::Variable(_) => None,
            Term::Application { ref op, ref args } => Some((op, args)),
        }
    }
    pub fn as_guarded_application(
        &self,
        sig: &Signature,
        name: &str,
        arity: u32,
    ) -> Option<(&Operator, &[Term])> {
        match self {
            Term::Variable(_) => None,
            Term::Application { ref op, ref args } => match (op.name(sig), op.arity()) {
                (Some(ref s), a) if s.as_str() == name && a == arity => Some((op, args)),
                _ => None,
            },
        }
    }
    /// Every [`Atom`] used in the `Term`.
    ///
    /// [`Atom`]: enum.Atom.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let example_term = parse_term(&mut sig, "A(B x_)").expect("parse of A(B x_)");
    /// let atoms: Vec<String> = example_term.atoms().iter().map(|a| a.display(&sig)).collect();
    ///
    /// assert_eq!(atoms, vec!["x_", "B", "A"]);
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
    /// let var_names: Vec<String> = t.variables().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(var_names, vec!["y_", "z_"]);
    /// ```
    pub fn variables(&self) -> Vec<Variable> {
        match *self {
            Term::Variable(v) => vec![v],
            Term::Application { ref args, .. } => {
                let mut vars = args.iter().flat_map(Term::variables).collect_vec();
                vars.sort();
                vars.dedup();
                vars
            }
        }
    }
    /// Every [`Operator`] used in the `Term`.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "A B y_ z_").expect("parse of A B y_ z_");
    /// let op_names: Vec<String> = t.operators().iter().map(|v| v.display(&sig)).collect();
    ///
    /// assert_eq!(op_names, vec!["A", "B", "."]);
    /// ```
    pub fn operators(&self) -> Vec<Operator> {
        match *self {
            Term::Variable(_) => vec![],
            Term::Application { op, ref args } => {
                let mut ops = args
                    .iter()
                    .flat_map(Term::operators)
                    .chain(iter::once(op))
                    .collect_vec();
                ops.sort();
                ops.dedup();
                ops
            }
        }
    }
    /// The head of the `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term, Atom};
    /// let mut sig = Signature::default();
    ///
    /// let op = sig.new_op(2, Some("A".to_string()));
    /// let t = parse_term(&mut sig, "A(B z_)").expect("parse of A(B z_)");
    ///
    /// assert_eq!(t.atoms().len(), 3);
    /// assert_eq!(t.head(), Atom::Operator(op));
    /// ```
    pub fn head(&self) -> Atom {
        match *self {
            Term::Variable(v) => Atom::Variable(v),
            Term::Application { op, .. } => Atom::Operator(op),
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
    /// let t = parse_term(&mut sig, "C(A B)").expect("parse of C(A B)");
    /// let arg0 = parse_term(&mut sig, "A").expect("parse of A");
    /// let arg1 = parse_term(&mut sig, "B").expect("parse of B");
    ///
    /// assert_eq!(t.args(), vec![arg0, arg1]);
    ///
    /// let t2 = parse_term(&mut sig, "A").expect("parse of A");
    ///
    /// assert_eq!(t2.args(), vec![]);
    /// ```
    pub fn args(&self) -> Vec<Term> {
        match self {
            Term::Variable(_) => vec![],
            Term::Application { args, .. } => args.clone(),
        }
    }
    /// Every `subterm` and its [`Place`], starting with the `Term` and the empty [`Place`].
    ///
    /// [`Place`]: struct.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// let mut sig = Signature::default();
    ///
    /// let b = sig.new_op(0, Some("B".to_string()));
    /// let a = sig.new_op(1, Some("A".to_string()));
    ///
    /// let p: Vec<usize> = vec![];
    /// let p1: Vec<usize> = vec![0];
    /// let t = parse_term(&mut sig, "A(B)").expect("parse of A(B)");
    /// let subterm0 = Term::Application {
    ///     op: a.clone(),
    ///     args: vec![Term::Application {
    ///         op: b.clone(),
    ///         args: vec![],
    ///     }],
    /// };
    /// let subterm1 = Term::Application {
    ///     op: b.clone(),
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
    /// Every slice (i.e. subcontext) of the `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// let mut sig = Signature::default();
    ///
    /// let t1 = parse_term(&mut sig, "x_").expect("parse of x_");
    /// assert_eq!(t1.slices().len(), 2);
    ///
    /// let t2 = parse_term(&mut sig, "B").expect("parse of B");
    /// assert_eq!(t2.slices().len(), 2);
    ///
    /// let t3 = parse_term(&mut sig, "A(C(x_ A(B)))").expect("parse of A(C(x_ A(B)))");
    ///
    /// let slices = t3.slices();
    /// for slice in &slices {
    ///     println!("{}", slice.pretty(&sig));
    /// }
    ///
    /// assert_eq!(slices.len(), 22);
    ///
    /// // 1. [!]
    /// // 2. A([!])
    /// // 3. A(C([!] [!]))
    /// // 4. A(C(x_ [!]))
    /// // 5. A(C(x_ A([!])))
    /// // 6. A(C([!] A(B)))
    /// // 7. A(C([!] A([!])))
    /// // 8. A(C(x_ A(B)))
    /// // 9. [!]
    /// // 10. C([!] [!])
    /// // 11. C(x_ [!])
    /// // 12. C(x_ A([!]))
    /// // 13. C([!] A(B))
    /// // 14. C([!] A([!]))
    /// // 15. C(x_ A(B))
    /// // 16. [!]
    /// // 17. x_
    /// // 18. [!]
    /// // 19. A([!])
    /// // 20. A(B)
    /// // 21. [!]
    /// // 22. B
    /// ```
    pub fn slices(&self) -> Vec<Context> {
        // TODO: use a HashMap to make me more efficient.
        self.subterms()
            .iter()
            .flat_map(|(t, _)| t.slices_at())
            .collect_vec()
    }
    /// Compute one-hole `Context`s for a `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// let mut sig = Signature::default();
    /// let t = parse_term(&mut sig, "A (B C) B").expect("parse of A (B C) B");
    ///
    /// let contexts = t.contexts(1);
    /// for context in &contexts {
    ///     println!("{}", context.pretty(&sig));
    /// }
    /// assert_eq!(contexts.len(), 8);
    ///
    /// println!("");
    /// let contexts = t.contexts(2);
    /// for context in &contexts {
    ///     println!("{}", context.pretty(&sig));
    /// }
    /// assert_eq!(contexts.len(), 17);
    pub fn contexts(&self, max_holes: usize) -> Vec<Context> {
        let (_, places): (Vec<_>, Vec<Place>) = self.subterms().into_iter().unzip();
        let master = Context::from(self);
        let mut contexts = vec![];
        for n_holes in 0..=max_holes {
            for holes in Term::select_holes(vec![], &places, n_holes) {
                let mut context = master.clone();
                for hole in holes {
                    context = context.replace(&hole, Context::Hole).unwrap();
                }
                contexts.push(context);
            }
        }
        contexts
    }
    fn select_holes(selected: Vec<Place>, places: &[Place], n: usize) -> Vec<Vec<Place>> {
        if n == 0 {
            vec![selected]
        } else if places.is_empty() {
            vec![]
        } else {
            let mut holess = vec![];
            for i in 0..places.len() {
                if !selected.iter().any(|s| places[i].starts_with(s)) {
                    let mut new_selected = selected.clone();
                    new_selected.push(places[i].clone());
                    holess.append(&mut Term::select_holes(
                        new_selected,
                        &places[(i + 1)..],
                        n - 1,
                    ))
                }
            }
            holess
        }
    }
    /// Compute slices rooted at some point.
    fn slices_at(&self) -> Vec<Context> {
        match *self {
            Term::Application { op, ref args } if !args.is_empty() => {
                let arg_slices = args.iter().map(Term::slices_at).collect_vec();
                let slices = arg_slices
                    .iter()
                    .cloned()
                    .multi_cartesian_product()
                    .map(|slice_args| Context::Application {
                        op,
                        args: slice_args,
                    })
                    .collect_vec();
                iter::once(Context::Hole).chain(slices).collect_vec()
            }
            _ => vec![Context::Hole, Context::from(self)],
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
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_term(&mut sig, "A B").expect("parse of A B");
    ///
    /// assert_eq!(t.size(), 3);
    ///
    /// let t = parse_term(&mut sig, "A(B)").expect("parse of A(B)");
    ///
    /// assert_eq!(t.size(), 2);
    /// ```
    pub fn size(&self) -> usize {
        match *self {
            Term::Variable(_) => 1,
            Term::Application { ref args, .. } => args.iter().map(Term::size).sum::<usize>() + 1,
        }
    }
    /// Get the `subterm` at the given [`Place`] if possible.  Otherwise, return `None`.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(0, Some("A".to_string()));
    /// let t = parse_term(&mut sig, "B(A)").expect("parse of B(A)");
    ///
    /// assert_eq!(t.size(), 2);
    /// let p: &[usize] = &[7];
    ///
    /// assert_eq!(t.at(p), None);
    ///
    /// let p: &[usize] = &[0];
    /// let args = vec![];
    ///
    /// assert_eq!(t.at(p), Some(&Term::Application { op, args }));
    /// ```
    #[cfg_attr(feature = "cargo-clippy", allow(clippy::ptr_arg))]
    pub fn at(&self, place: &[usize]) -> Option<&Term> {
        self.at_helper(place)
    }
    fn at_helper(&self, place: &[usize]) -> Option<&Term> {
        if place.is_empty() {
            Some(self)
        } else {
            match *self {
                Term::Variable(_) => None,
                Term::Application { ref args, .. } => {
                    if place[0] < args.len() {
                        args[place[0]].at_helper(&place[1..].to_vec())
                    } else {
                        None
                    }
                }
            }
        }
    }
    /// Create a copy of the `Term` where the `Term` at the given [`Place`] has been replaced with
    /// `subterm`.
    ///
    /// [`Place`]: type.Place.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
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
    #[cfg_attr(feature = "cargo-clippy", allow(clippy::ptr_arg))]
    pub fn replace(&self, place: &[usize], subterm: Term) -> Option<Term> {
        if place.is_empty() {
            Some(subterm)
        } else {
            match *self {
                Term::Application { op, ref args } if place[0] <= args.len() => {
                    args[place[0]].replace(&place[1..], subterm).map(|term| {
                        let mut new_args = args.clone();
                        new_args[place[0]] = term;
                        Term::Application { op, args: new_args }
                    })
                }
                _ => None,
            }
        }
    }
    /// Replace all occurrences of `old_term` with `new_term`
    pub fn replace_all(&self, old_term: &Term, new_term: &Term) -> Term {
        match *self {
            ref x if x == old_term => new_term.clone(),
            Term::Variable(_) => self.clone(),
            Term::Application { op, ref args } => {
                let new_args = args
                    .iter()
                    .map(|arg| arg.replace_all(old_term, new_term))
                    .collect_vec();
                Term::Application { op, args: new_args }
            }
        }
    }
    /// Compute the percentage of shared subterms between two `Term`s.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term};
    /// let mut sig = Signature::default();
    ///
    /// let t1 = parse_term(&mut sig, "S (K y_ z_)").expect("parse of S K y_ z_");
    /// let t2 = parse_term(&mut sig, "S (K w_ x_)").expect("parse of S K w_ x_");
    /// let t3 = parse_term(&mut sig, "K (K w_ x_) S").expect("parse of S K w_ x_");
    ///
    /// // Identical Terms
    /// assert_eq!(Term::shared_score(&t1, &t1), 1.0);
    ///
    /// // Alpha-equivalent Terms
    /// assert_eq!(Term::shared_score(&t1, &t2), 1.0);
    ///
    /// // Distinct Terms
    /// assert_eq!(Term::shared_score(&t1, &t3), 0.5);
    /// ```
    pub fn shared_score(t1: &Term, t2: &Term) -> f64 {
        let t1s = t1.subterms().iter().map(|x| x.0).collect_vec();
        let mut t2s = t2.subterms().iter().map(|x| x.0).collect_vec();
        let t1_total: usize = t1s.iter().map(|&x| x.size()).sum();
        let t2_total: usize = t2s.iter().map(|&x| x.size()).sum();
        let total: f64 = (t1_total + t2_total) as f64;
        let mut count = 0.0;
        for o in t1s {
            if let Some((idx, _)) = t2s
                .iter()
                .find_position(|t| Term::alpha(vec![(o, t)]).is_some())
            {
                count += 2.0 * (o.size() as f64);
                t2s.swap_remove(idx);
            }
        }
        count / total
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
    /// let y = &vars[0];
    /// let z = &vars[1];
    ///
    /// let mut sub = HashMap::new();
    /// sub.insert(y, &s_term);
    /// sub.insert(z, &k_term);
    ///
    /// let expected_term = parse_term(&mut sig, "S K S K").expect("parse of S K S K");
    /// let subbed_term = term_before.substitute(&sub);
    ///
    /// assert_eq!(subbed_term, expected_term);
    /// ```
    pub fn substitute(&self, sub: &HashMap<&Variable, &Term>) -> Term {
        match *self {
            Term::Variable(v) => (*(sub.get(&v).unwrap_or(&self))).clone(),
            Term::Application { op, ref args } => Term::Application {
                op,
                args: args.iter().map(|t| t.substitute(sub)).collect(),
            },
        }
    }
    /// Compute the [alpha equivalence] for two `Term`s.
    ///
    /// [alpha equivalence]: https://en.wikipedia.org/wiki/Lambda_calculus#Alpha_equivalence
    ///
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
    /// let (y, z, a, b) = (&vars[0], &vars[1], &vars[2], &vars[3]);
    ///
    /// let ta = Term::Variable(a.clone());
    /// let tb = Term::Variable(b.clone());
    /// let mut expected_alpha: HashMap<&Variable, &Term> = HashMap::new();
    /// expected_alpha.insert(y, &ta);
    /// expected_alpha.insert(z, &tb);
    ///
    /// assert_eq!(Term::alpha(vec![(&t, &t2)]), Some(expected_alpha));
    ///
    /// assert_eq!(Term::alpha(vec![(&t, &t3)]), None);
    /// ```
    pub fn alpha<'a>(cs: Vec<(&'a Term, &'a Term)>) -> Option<HashMap<&'a Variable, &'a Term>> {
        Term::unify_internal(cs, Unification::Alpha)
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
    ///
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
            (&Term::Variable(v1), &Term::Variable(v2)) => {
                v2 == *vmap.entry(v1).or_insert_with(|| v2)
            }
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
                op2 == *omap.entry(op1).or_insert_with(|| op2)
                    && args1
                        .iter()
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
    /// let mut sig = Signature::default();
    ///
    /// let t1 = parse_term(&mut sig, "C(A)").expect("parse of C(A)");
    ///
    /// let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    ///
    /// assert_eq!(Term::pmatch(vec![(&t1, &t2)]), None);
    ///
    /// // maps variable x in term t2 to constant A in term t1
    /// let t_k = &t2.variables()[0];
    /// let t_v = parse_term(&mut sig, "A").expect("parse of A");
    /// let mut expected_sub = HashMap::new();
    /// expected_sub.insert(t_k, &t_v);
    ///
    /// assert_eq!(Term::pmatch(vec![(&t2, &t1)]), Some(expected_sub));
    ///
    /// let t3 = parse_term(&mut sig, "A(x_)").expect("parse of A(x_)");
    ///
    /// assert_eq!(Term::pmatch(vec![(&t2, &t3)]), None);
    /// ```
    pub fn pmatch<'a>(cs: Vec<(&'a Term, &'a Term)>) -> Option<HashMap<&'a Variable, &'a Term>> {
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
    /// Given
    ///
    /// ```
    /// # use term_rewriting::{Signature, Context, parse_term};
    /// # use std::collections::{HashMap, HashSet};
    /// let mut sig = Signature::default();
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// # use std::collections::{HashMap, HashSet};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_term(&mut sig, "C(A)").expect("parse of C(A)");
    /// let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    ///
    /// // Map variable x in term t2 to constant A in term t1.
    /// let mut expected_sub = HashMap::new();
    /// let t_k = &t2.variables()[0];
    /// let t_v = parse_term(&mut sig, "A").expect("parse of A");
    /// expected_sub.insert(t_k, &t_v);
    ///
    /// assert_eq!(Term::unify(vec![(&t1, &t2)]), Some(expected_sub));
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// # use std::collections::{HashMap, HashSet};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    /// let t2 = parse_term(&mut sig, "C(y_)").expect("parse of C(y_)");
    ///
    /// // Map variable x in term t2 to variable y in term t2.
    /// let mut expected_sub = HashMap::new();
    /// let t_k = &t1.variables()[0];
    /// let t_v = Term::Variable(t2.variables()[0].clone());
    /// expected_sub.insert(t_k, &t_v);
    ///
    /// assert_eq!(Term::unify(vec![(&t1, &t2)]), Some(expected_sub));
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// # use std::collections::{HashMap, HashSet};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    /// let t2 = parse_term(&mut sig, "B(x_)").expect("parse of B(x_)");
    ///
    /// assert_eq!(Term::unify(vec![(&t1, &t2)]), None);
    /// ```
    pub fn unify<'a>(cs: Vec<(&'a Term, &'a Term)>) -> Option<HashMap<&'a Variable, &'a Term>> {
        Term::unify_internal(cs, Unification::Unify)
    }
    /// the internal implementation of unify and match.
    fn unify_internal<'a>(
        mut cs: Vec<(&'a Term, &'a Term)>,
        utype: Unification,
    ) -> Option<HashMap<&'a Variable, &'a Term>> {
        let mut subs: HashMap<&Variable, &Term> = HashMap::new();
        while !cs.is_empty() {
            let (mut s, mut t) = cs.pop().unwrap();

            while let Term::Variable(ref v) = *s {
                if subs.contains_key(v) {
                    s = &subs[v];
                } else {
                    break;
                }
            }

            while let Term::Variable(ref v) = *t {
                if subs.contains_key(v) {
                    t = &subs[v];
                } else {
                    break;
                }
            }

            // if they are equal, you're all done with them.
            if s != t {
                match (s, t) {
                    (Term::Variable(ref var), Term::Variable(_)) => {
                        subs.insert(var, t);
                    }
                    (Term::Variable(ref var), t) if utype != Unification::Alpha => {
                        if !(*t).variables().contains(&&var) {
                            subs.insert(var, t);
                        } else {
                            return None;
                        }
                    }
                    (s, Term::Variable(ref var)) if utype == Unification::Unify => {
                        if !(*s).variables().contains(&&var) {
                            subs.insert(var, s);
                        } else {
                            return None;
                        }
                    }
                    (
                        Term::Application {
                            op: ref h1,
                            args: ref a1,
                        },
                        Term::Application {
                            op: ref h2,
                            args: ref a2,
                        },
                    ) if h1 == h2 => {
                        cs.append(&mut a1.iter().zip(a2.iter()).collect());
                    }
                    _ => return None,
                }
            }
        }
        Some(subs)
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::parser::*;
    use super::super::{Atom, Context, Signature, Term};
    use std::collections::HashMap;

    #[test]
    fn context_display_test() {
        let mut sig = Signature::default();

        let context = parse_context(&mut sig,
            "x_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
            .expect("parse of x_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)") ;

        assert_eq!(context.display(&sig),
            ".(.(.(.(x_ [!]) A) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5))");
    }

    #[test]
    fn context_pretty_test() {
        let mut sig = Signature::default();

        let context = parse_context(&mut sig, "x_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
            .expect("parse of x_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)") ;

        assert_eq!(context.pretty(&sig), "x_ [!] A [2, 1, 0] 105");
    }

    #[test]
    fn context_atoms_test() {
        let mut sig = Signature::default();

        let context = parse_context(&mut sig, "A(B x_ [!])").expect("parse of A(B x_ [!])");

        let atoms: Vec<String> = context.atoms().iter().map(|a| a.display(&sig)).collect();

        assert_eq!(atoms, vec!["x_", "B", "A"]);
    }

    #[test]
    fn context_variables_test() {
        let mut sig = Signature::default();

        let context = parse_context(&mut sig, "A([!]) B y_ z_").expect("parse of A([!]) B y_ z_");

        let var_names: Vec<String> = context
            .variables()
            .iter()
            .map(|v| v.display(&sig))
            .collect();

        assert_eq!(var_names, vec!["y_".to_string(), "z_".to_string()]);
    }

    #[test]
    fn context_operators_test() {
        let mut sig = Signature::default();

        let context = parse_context(&mut sig, "A([!]) B y_ z_").expect("parse of A([!]) B y_ z_");

        let op_names: Vec<String> = context
            .operators()
            .iter()
            .map(|v| v.display(&sig))
            .collect();

        assert_eq!(
            op_names,
            vec!["A".to_string(), "B".to_string(), ".".to_string()]
        );
    }

    #[test]
    fn hole_test() {
        let mut sig = Signature::default();

        let context =
            parse_context(&mut sig, "A([!] B([!]) y_ z_)").expect("parse of A([!] B([!]) y_ z_)");

        let p: &[usize] = &[0];
        let p2: &[usize] = &[1, 0];

        assert_eq!(context.holes(), vec![p, p2]);
    }

    #[test]
    fn context_head_test() {
        let mut sig = Signature::default();

        let mut context = parse_context(&mut sig, "A(B([!]) z_)").expect("parse of A(B([!]) z_)");

        assert_eq!(context.head().unwrap().display(&sig), "A");

        sig = Signature::default();

        context = parse_context(&mut sig, "z_").expect("parse of z_");

        assert_eq!(context.head().unwrap().display(&sig), "z_");
    }

    #[test]
    fn context_args_test() {
        let mut sig = Signature::default();

        let mut context = parse_context(&mut sig, "A B").expect("parse of A B");
        let mut args: Vec<String> = context.args().iter().map(|arg| arg.display(&sig)).collect();

        assert_eq!(args, vec!["A", "B"]);

        context = parse_context(&mut sig, "A(y_)").expect("parse of A(y_)");
        args = context.args().iter().map(|arg| arg.display(&sig)).collect();

        assert_eq!(args, vec!["y_"]);

        context = parse_context(&mut sig, "y_").expect("parse of y_");
        args = context.args().iter().map(|arg| arg.display(&sig)).collect();

        let vec: Vec<String> = Vec::new();

        assert_eq!(args, vec);
    }

    #[test]
    fn subcontexts_test() {
        let mut sig = Signature::default();

        let context = parse_context(&mut sig, "A(B [!])").expect("parse of A(B [!])");

        let p: Vec<usize> = vec![];
        let subcontext0 = parse_context(&mut sig, "A(B [!])").expect("parse of A(B [!])");

        let p1: Vec<usize> = vec![0];
        let subcontext1 = parse_context(&mut sig, "B").expect("parse of B");

        let p2: Vec<usize> = vec![1];
        let subcontext2 = Context::Hole;

        assert_eq!(
            context.subcontexts(),
            vec![(&subcontext0, p), (&subcontext1, p1), (&subcontext2, p2)]
        );
    }

    #[test]
    fn context_size_test() {
        let mut sig = Signature::default();
        let context = parse_context(&mut sig, "A B").expect("parse of A B");

        assert_eq!(context.size(), 3);

        let context = parse_context(&mut sig, "A(B)").expect("parse of A(B)");

        assert_eq!(context.size(), 2);
    }

    #[test]
    fn context_at_test() {
        let mut sig = Signature::default();
        let context = parse_context(&mut sig, "B(A)").expect("parse of B(A)");

        let p: &[usize] = &[7];

        assert_eq!(context.at(p), None);

        let p: &[usize] = &[0];

        assert_eq!(context.at(p).unwrap().display(&sig), "A");
    }

    #[test]
    fn context_replace_test() {
        let mut sig = Signature::default();

        let context = parse_context(&mut sig, "B(A)").expect("parse of B(A)");
        let context2 = parse_context(&mut sig, "C [!]").expect("parse of C [!]");

        let p: &[usize] = &[0];
        let new_context = context.replace(p, context2);

        assert_eq!(new_context.unwrap().pretty(&sig), "B(C [!])");
    }

    #[test]
    fn to_term_test() {
        let mut sig = Signature::default();

        let context = parse_context(&mut sig, "A(B [!])").expect("parse of A(B [!])");

        assert!(context.to_term().is_err());

        let context = parse_context(&mut sig, "A(B C)").expect("parse of A(B C)");

        let term = context.to_term().expect("converting context to term");

        assert_eq!(term.display(&sig), "A(B C)");
    }

    #[test]
    fn term_display_test() {
        let mut sig = Signature::default();

        let term = parse_term(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
            .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)");

        assert_eq!(term.display(&sig), ".(.(.(A B(x_)) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5))");
    }

    #[test]
    fn term_pretty_test() {
        let mut sig = Signature::default();

        let term = parse_term(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
             .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)");

        assert_eq!(term.pretty(&sig), "A B(x_) [2, 1, 0] 105");
    }

    #[test]
    fn term_atoms_test() {
        let mut sig = Signature::default();

        let example_term = parse_term(&mut sig, "A(B x_)").expect("parse of A(B x_)");
        let atoms: Vec<String> = example_term
            .atoms()
            .iter()
            .map(|a| a.display(&sig))
            .collect();

        assert_eq!(atoms, vec!["x_", "B", "A"]);
    }

    #[test]
    fn term_variables_test() {
        let mut sig = Signature::default();

        let t = parse_term(&mut sig, "A B y_ z_").expect("parse of A B y_ z_");
        let var_names: Vec<String> = t.variables().iter().map(|v| v.display(&sig)).collect();

        assert_eq!(var_names, vec!["y_", "z_"]);
    }

    #[test]
    fn term_operators_test() {
        let mut sig = Signature::default();

        let t = parse_term(&mut sig, "A B y_ z_").expect("parse of A B y_ z_");
        let op_names: Vec<String> = t.operators().iter().map(|v| v.display(&sig)).collect();

        assert_eq!(op_names, vec!["A", "B", "."]);
    }

    #[test]
    fn term_head_test() {
        let mut sig = Signature::default();

        let op = sig.new_op(2, Some("A".to_string()));
        let t = parse_term(&mut sig, "A(B z_)").expect("parse of A(B z_)");

        assert_eq!(t.atoms().len(), 3);
        assert_eq!(t.head(), Atom::Operator(op));
    }

    #[test]
    fn term_args_test() {
        let mut sig = Signature::default();

        let t = parse_term(&mut sig, "C(A B)").expect("parse of C(A B)");
        let arg0 = parse_term(&mut sig, "A").expect("parse of A");
        let arg1 = parse_term(&mut sig, "B").expect("parse of B");

        assert_eq!(t.args(), vec![arg0, arg1]);

        let t2 = parse_term(&mut sig, "A").expect("parse of A");

        assert_eq!(t2.args(), vec![]);
    }

    #[test]
    fn subterms_test() {
        let mut sig = Signature::default();

        let b = sig.new_op(0, Some("B".to_string()));
        let a = sig.new_op(1, Some("A".to_string()));

        let p: Vec<usize> = vec![];
        let p1: Vec<usize> = vec![0];
        let t = parse_term(&mut sig, "A(B)").expect("parse of A(B)");
        let subterm0 = Term::Application {
            op: a.clone(),
            args: vec![Term::Application {
                op: b.clone(),
                args: vec![],
            }],
        };

        let subterm1 = Term::Application {
            op: b.clone(),
            args: vec![],
        };

        assert_eq!(t.subterms(), vec![(&subterm0, p), (&subterm1, p1)]);
    }

    #[test]
    fn term_size_test() {
        let mut sig = Signature::default();

        let t = parse_term(&mut sig, "A B").expect("parse of A B");

        assert_eq!(t.size(), 3);

        let t = parse_term(&mut sig, "A(B)").expect("parse of A(B)");

        assert_eq!(t.size(), 2);
    }

    #[test]
    fn term_at_test() {
        let mut sig = Signature::default();
        let op = sig.new_op(0, Some("A".to_string()));
        let t = parse_term(&mut sig, "B(A)").expect("parse of B(A)");

        assert_eq!(t.size(), 2);
        let p: &[usize] = &[7];

        assert_eq!(t.at(p), None);

        let p: &[usize] = &[0];
        let args = vec![];

        assert_eq!(t.at(p), Some(&Term::Application { op, args }));
    }

    #[test]
    fn term_replace() {
        let mut sig = Signature::default();

        let t = parse_term(&mut sig, "B(A)").expect("parse of B(A)");
        let t2 = parse_term(&mut sig, "C").expect("parse of C");
        let expected_term = parse_term(&mut sig, "B(C)").expect("parse of B(C)");

        let p: &[usize] = &[0];
        let new_term = t.replace(p, t2);

        assert_eq!(new_term, Some(expected_term));
    }

    #[test]
    fn term_substitute_test() {
        let mut sig = Signature::default();

        let term_before = parse_term(&mut sig, "S K y_ z_").expect("parse of S K y_ z_");
        let s_term = parse_term(&mut sig, "S").expect("parse of S");
        let k_term = parse_term(&mut sig, "K").expect("parse of K");

        let vars = sig.variables();
        let y = &vars[0];
        let z = &vars[1];

        let mut sub = HashMap::new();
        sub.insert(y, &s_term);
        sub.insert(z, &k_term);

        let expected_term = parse_term(&mut sig, "S K S K").expect("parse of S K S K");
        let subbed_term = term_before.substitute(&sub);

        assert_eq!(subbed_term, expected_term);
    }

    #[test]
    fn alpha_test() {
        let mut sig = Signature::default();
        let _s = sig.new_op(0, Some("S".to_string()));

        let t = parse_term(&mut sig, "S K y_ z_").expect("parse of S K y_ z_");
        let t2 = parse_term(&mut sig, "S K a_ b_").expect("parse of S K a_ b_");
        let t3 = parse_term(&mut sig, "S K y_").expect("parse of S K y_");

        let vars = sig.variables();
        let (y, z, a, b) = (
            vars[0].clone(),
            vars[1].clone(),
            vars[2].clone(),
            vars[3].clone(),
        );

        assert_eq!(y.display(&sig), "y_".to_string());
        assert_eq!(z.display(&sig), "z_".to_string());
        assert_eq!(a.display(&sig), "a_".to_string());
        assert_eq!(b.display(&sig), "b_".to_string());

        {
            let ta = Term::Variable(a);
            let tb = Term::Variable(b);
            let mut expected_alpha = HashMap::new();
            expected_alpha.insert(&y, &ta);
            expected_alpha.insert(&z, &tb);

            assert_eq!(Term::alpha(vec![(&t, &t2)]), Some(expected_alpha));
        }

        assert_eq!(Term::alpha(vec![(&t, &t3)]), None);
    }

    #[test]
    fn shape_equivalent_test() {
        let mut sig = Signature::default();

        let t = parse_term(&mut sig, "S K y_ z_").expect("parse of S K y_ z_");
        let t2 = parse_term(&mut sig, "A B x_ w_").expect("parse of A B x_ w_");
        let t3 = parse_term(&mut sig, "S K y_").expect("parse of S K y_");

        assert!(Term::shape_equivalent(&t, &t2));

        assert!(!Term::shape_equivalent(&t, &t3));
    }

    #[test]
    fn pmatch_test() {
        let mut sig = Signature::default();

        let t = parse_term(&mut sig, "C(A)").expect("parse of C(A)");

        let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");

        let t3 = parse_term(&mut sig, "C(y_)").expect("parse of C(y_)");

        let t4 = parse_term(&mut sig, "A(x_)").expect("parse of A(x_)");

        assert_eq!(Term::pmatch(vec![(&t, &t2)]), None);

        // maps variable x in term t2 to variable y in term t3
        {
            let subbee = &t2.variables()[0];
            let subbed = Term::Variable(t3.variables()[0].clone());
            let mut expected_sub = HashMap::new();
            expected_sub.insert(subbee, &subbed);

            assert_eq!(Term::pmatch(vec![(&t2, &t3)]), Some(expected_sub));
        }

        assert_eq!(Term::pmatch(vec![(&t3, &t4)]), None);
    }

    #[test]
    fn unify_test() {
        let mut sig = Signature::default();

        let t = parse_term(&mut sig, "C(A)").expect("parse of C(A)");

        let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");

        let t3 = parse_term(&mut sig, "C(y_)").expect("parse of C(y_)");

        let t4 = parse_term(&mut sig, "B(x_)").expect("parse of B(x_)");

        {
            // maps variable x in term t2 to constant A in term t
            let subbee = &t2.variables()[0];
            let subbed = Term::Application {
                op: t.operators()[0].clone(),
                args: vec![],
            };
            let mut expected_sub = HashMap::new();
            expected_sub.insert(subbee, &subbed);

            assert_eq!(Term::unify(vec![(&t, &t2)]), Some(expected_sub));
        }

        {
            // maps variable x in term t2 to variable y in term t3
            let subbee = &t2.variables()[0];
            let subbed = Term::Variable(t3.variables()[0].clone());
            let mut expected_sub = HashMap::new();
            expected_sub.insert(subbee, &subbed);

            assert_eq!(Term::unify(vec![(&t2, &t3)]), Some(expected_sub));
        }

        assert_eq!(Term::unify(vec![(&t3, &t4)]), None);
    }
}
