use super::super::pretty::Pretty;
use super::{Atom, Operator, Place, Signature, SituatedAtom, Unification, Variable};
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};
use std::{collections::HashMap, convert::TryFrom, iter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Substitution<'a>(pub Vec<(&'a Variable, &'a Term)>);

pub struct Variables<'a> {
    stack: SmallVec<[&'a Term; 32]>,
}

impl<'a> Variables<'a> {
    pub(crate) fn new(term: &'a Term) -> Self {
        Variables {
            stack: smallvec![term],
        }
    }
}

impl<'a> Iterator for Variables<'a> {
    type Item = Variable;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(term) = self.stack.pop() {
            match term {
                Term::Variable(v) => return Some(*v),
                Term::Application { ref args, .. } => {
                    for arg in args.iter().rev() {
                        self.stack.push(arg);
                    }
                }
            }
        }
        None
    }
}

pub struct Preorder<'a> {
    stack: SmallVec<[(&'a Term, usize); 32]>,
}

impl<'a> Preorder<'a> {
    pub(crate) fn new(term: &'a Term) -> Self {
        let mut stack = SmallVec::with_capacity(term.height());
        stack.push((term, 0));
        Preorder { stack }
    }
}

impl<'a> Iterator for Preorder<'a> {
    type Item = &'a Term;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((term, arg)) = self.stack.pop() {
            match term {
                Term::Variable(_) => return Some(term),
                Term::Application { ref args, .. } => {
                    if arg < args.len() {
                        self.stack.push((term, arg + 1));
                        self.stack.push((&args[arg], 0));
                    }
                    if arg == 0 {
                        return Some(term);
                    }
                }
            }
        }
        None
    }
}

pub struct Postorder<'a> {
    stack: SmallVec<[(&'a Term, usize); 32]>,
}

impl<'a> Postorder<'a> {
    pub(crate) fn new(term: &'a Term) -> Self {
        let mut stack = SmallVec::with_capacity(term.height());
        stack.push((term, 0));
        Postorder { stack }
    }
}

impl<'a> Iterator for Postorder<'a> {
    type Item = &'a Term;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((term, arg)) = self.stack.pop() {
            match term {
                Term::Variable(_) => return Some(term),
                Term::Application { ref args, .. } => {
                    if arg == args.len() {
                        return Some(term);
                    } else {
                        self.stack.push((term, arg + 1));
                        self.stack.push((&args[arg], 0));
                    }
                }
            }
        }
        None
    }
}

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
/// let context = parse_context(&mut sig, "A(B v0_ [!])").expect("parsed context");
///
/// assert_eq!(context.pretty(&sig), "A(B, v0_, [!])");
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
    /// let var = parse_context(&mut sig, "v0_").expect("parse of v0_");
    ///
    /// assert_eq!(var.pretty(&sig), "v0_");
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
    /// let context = parse_context(&mut sig, "v0_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
    ///     .expect("parsed context") ;
    ///
    /// assert_eq!(context.display(&sig), ".(.(.(.(v0_ [!]) A) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5))");
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        match self {
            Context::Hole => "[!]".to_string(),
            Context::Variable(v) => v.display(),
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
    /// let context = parse_context(&mut sig, "v0_ [!] A CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
    ///     .expect("parsed context") ;
    ///
    /// assert_eq!(context.pretty(&sig), "v0_ [!] A [2, 1, 0] 105");
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
    /// let context = parse_context(&mut sig, "A(B v0_ [!])").expect("parsed context");
    /// let atoms: Vec<String> = context.atoms().iter().map(|a| a.display(&sig)).collect();
    ///
    /// assert_eq!(atoms, vec!["v0_", "B", "A"]);
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
    /// let context = parse_context(&mut sig, "A([!]) B v0_ v1_").expect("parse of A([!]) B v0_ v1_");
    /// let var_names: Vec<String> = context.variables().iter().map(|v| v.display()).collect();
    ///
    /// assert_eq!(var_names, vec!["v0_".to_string(), "v1_".to_string()]);
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
    pub fn is_hole(&self) -> bool {
        match self {
            Context::Hole => true,
            _ => false,
        }
    }
    /// The leftmost [`Place`] in the `Context` that is a `Hole`.
    ///
    /// [`Place`]: type.Place.html
    /// [`Hole`]: enum.Context.html#variant.Hole
    pub fn leftmost_hole(&self) -> Option<Place> {
        match *self {
            Context::Hole => Some(vec![]),
            Context::Variable(_) => None,
            Context::Application { ref args, .. } => {
                for (i, arg) in args.iter().enumerate() {
                    if let Some(mut place) = arg.leftmost_hole() {
                        let mut full_place = vec![i];
                        full_place.append(&mut place);
                        return Some(full_place);
                    }
                }
                None
            }
        }
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
    /// let context = parse_context(&mut sig, "A(v0_)").expect("parse of A(v0_)");
    /// let args: Vec<String> = context.args().iter().map(|arg| arg.display(&sig)).collect();
    ///
    /// assert_eq!(args, vec!["v0_"]);
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
        match *self {
            Context::Hole | Context::Variable(_) => 1,
            Context::Application { ref args, .. } => {
                args.iter().map(Context::size).sum::<usize>() + 1
            }
        }
    }
    /// The height of the `Context`.
    pub fn height(&self) -> usize {
        match *self {
            Context::Hole | Context::Variable(_) => 1,
            Context::Application { ref args, .. } => {
                args.iter().map(|a| 1 + a.height()).max().unwrap_or(1)
            }
        }
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
        if place.is_empty() {
            Some(subcontext)
        } else {
            match *self {
                Context::Application { op, ref args } if place[0] < args.len() => args[place[0]]
                    .replace(&place[1..], subcontext)
                    .map(|context| {
                        let mut new_args = Vec::with_capacity(args.len());
                        new_args.extend_from_slice(&args[..place[0]]);
                        new_args.push(context);
                        new_args.extend_from_slice(&args[place[0] + 1..]);
                        Context::Application { op, args: new_args }
                    }),
                _ => None,
            }
        }
    }
    pub fn fill(&self, fillers: &[Context]) -> Option<Context> {
        let mut context = self.clone();
        for (i, hole) in self.holes().iter().enumerate().take(fillers.len()) {
            context = context.replace(hole, fillers[i].clone())?;
        }
        Some(context)
    }
    /// `true` if `self` is a more general instance of some `Term`.
    pub fn generalize<'a>(
        cs: Vec<(&'a Context, &'a Context)>,
    ) -> Option<HashMap<&'a Variable, &'a Context>> {
        Context::unify_internal(cs, Unification::Generalize)
    }
    pub fn canonicalize(&mut self, map: &mut HashMap<usize, usize>) {
        match self {
            Context::Hole => (),
            Context::Variable(v) => {
                let new_id = map.len();
                let id = map.entry(v.0).or_insert_with(|| new_id);
                v.0 = *id;
            }
            Context::Application { ref mut args, .. } => {
                args.iter_mut().for_each(|arg| arg.canonicalize(map))
            }
        }
    }
    pub fn offset(&mut self, n: usize) {
        match self {
            Context::Hole => (),
            Context::Variable(v) => v.0 += n,
            Context::Application { ref mut args, .. } => {
                args.iter_mut().for_each(|arg| arg.offset(n))
            }
        }
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
impl TryFrom<&Context> for Term {
    type Error = Place;
    fn try_from(context: &Context) -> Result<Self, Self::Error> {
        match *context {
            Context::Hole => Err(vec![]),
            Context::Variable(v) => Ok(Term::Variable(v)),
            Context::Application { op, ref args } => {
                let mut mapped_args = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    match Term::try_from(arg) {
                        Ok(arg_term) => mapped_args.push(arg_term),
                        Err(mut place) => {
                            place.reverse();
                            place.push(i);
                            place.reverse();
                            return Err(place);
                        }
                    }
                }
                Ok(Term::Application {
                    op,
                    args: mapped_args,
                })
            }
        }
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
impl<'a> From<SituatedAtom<'a>> for Context {
    fn from(a: SituatedAtom<'a>) -> Context {
        match a.atom {
            Atom::Variable(v) => Context::Variable(v),
            Atom::Operator(op) => {
                let args = iter::repeat(Context::Hole)
                    .take(op.arity(a.sig) as usize)
                    .collect_vec();
                Context::Application { op, args }
            }
        }
    }
}
impl From<Variable> for Context {
    fn from(v: Variable) -> Context {
        Context::Variable(v)
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
    /// let term = parse_term(&mut sig, "A B(v0_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
    ///     .expect("parsed term");
    ///
    /// assert_eq!(term.display(&sig), ".(.(.(A B(v0_)) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5))");
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        match self {
            Term::Variable(ref v) => v.display(),
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
    /// let term = parse_term(&mut sig, "A B(v0_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5)")
    ///     .expect("parsed term");
    ///
    /// assert_eq!(term.pretty(&sig), "A B(v0_) [2, 1, 0] 105");
    /// ```
    pub fn pretty(&self, sig: &Signature) -> String {
        Pretty::pretty(self, sig)
    }
    pub fn apply(op: Operator, args: Vec<Term>, sig: &Signature) -> Option<Term> {
        if op.arity(sig) == (args.len() as u8) {
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
        arity: u8,
    ) -> Option<(&Operator, &[Term])> {
        match self {
            Term::Variable(_) => None,
            Term::Application { ref op, ref args } => match (op.name(sig), op.arity(sig)) {
                (Some(s), a) if s == name && a == arity => Some((op, args)),
                _ => None,
            },
        }
    }
    /// Returns an iterator performing a preorder traversal of the `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term};
    /// let mut sig = Signature::default();
    /// let term = parse_term(&mut sig, "A(B(A(C v0_)) B(A(v1_ v0_)))")
    ///     .expect("parsed term");
    ///
    /// let preorder: Vec<_> = term.preorder().map(|t| t.display(&sig)).collect();
    /// assert_eq!(preorder, vec!["A(B(A(C v0_)) B(A(v1_ v0_)))", "B(A(C v0_))", "A(C v0_)", "C", "v0_", "B(A(v1_ v0_))", "A(v1_ v0_)", "v1_", "v0_"]);
    /// ```
    pub fn preorder(&self) -> Preorder {
        Preorder::new(self)
    }
    /// Returns an iterator performing a postorder traversal of the `Term`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term};
    /// let mut sig = Signature::default();
    /// let term = parse_term(&mut sig, "A(B(A(C v0_)) B(A(v1_ v0_)))")
    ///     .expect("parsed term");
    ///
    /// let postorder: Vec<_> = term.postorder().map(|t| t.display(&sig)).collect();
    /// assert_eq!(postorder, vec!["C", "v0_", "A(C v0_)", "B(A(C v0_))", "v1_", "v0_", "A(v1_ v0_)", "B(A(v1_ v0_))", "A(B(A(C v0_)) B(A(v1_ v0_)))"]);
    /// ```
    pub fn postorder(&self) -> Postorder {
        Postorder::new(self)
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
    /// let term = parse_term(&mut sig, "A(B v0_)").expect("parsed term");
    /// let atoms: Vec<String> = term.atoms().iter().map(|a| a.display(&sig)).collect();
    ///
    /// assert_eq!(atoms, vec!["v0_", "B", "A"]);
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
    /// let t = parse_term(&mut sig, "A B v0_ v1_").expect("parsed term");
    /// let var_names: Vec<String> = t.variables().iter().map(|v| v.display()).collect();
    ///
    /// assert_eq!(var_names, vec!["v0_", "v1_"]);
    /// ```
    pub fn variables(&self) -> Vec<Variable> {
        let mut vars = self.all_variables().collect_vec();
        vars.sort();
        vars.dedup();
        vars
    }
    pub fn all_variables(&self) -> Variables {
        Variables::new(self)
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
    /// let t = parse_term(&mut sig, "A B v0_ v1_").expect("parsed term");
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
    /// The height of the `Term`.
    pub fn height(&self) -> usize {
        match *self {
            Term::Variable(_) => 1,
            Term::Application { ref args, .. } => {
                args.iter().map(|a| 1 + a.height()).max().unwrap_or(1)
            }
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
    pub fn at(&self, place: &[usize]) -> Option<&Term> {
        if place.is_empty() {
            Some(self)
        } else {
            match *self {
                Term::Variable(_) => None,
                Term::Application { ref args, .. } => {
                    if place[0] < args.len() {
                        args[place[0]].at(&place[1..].to_vec())
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
                Term::Application { op, ref args } if place[0] < args.len() => {
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
                .find_position(|t| Term::alpha(&[(o, t)]).is_some())
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
    /// # use term_rewriting::{Signature, Substitution, parse_term, Term};
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
    /// let mut sub = Substitution(vec![(y, &s_term), (z, &k_term)]);
    ///
    /// let expected_term = parse_term(&mut sig, "S K S K").expect("parse of S K S K");
    /// let subbed_term = term_before.substitute(&sub);
    ///
    /// assert_eq!(subbed_term, expected_term);
    /// ```
    pub fn substitute(&self, sub: &Substitution) -> Term {
        match *self {
            Term::Variable(v) => sub
                .0
                .iter()
                .find(|(k_var, _)| **k_var == v)
                .map(|x| (x.1).clone())
                .unwrap_or(Term::Variable(v)),
            Term::Application { op, ref args } => Term::Application {
                op,
                args: args.iter().map(|t| t.substitute(sub)).collect(),
            },
        }
    }
    /// Only use this if you know what you're doing. Otherwise, you might wreak
    /// havoc on your `Signature`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_rule, Term};
    /// # use std::collections::HashMap;
    /// let mut sig = Signature::default();
    /// let rule = parse_rule(&mut sig, "(x_ y_) z_ = (z_ y_) x_").expect("parsed rule");
    /// let mut t1 = rule.lhs.clone();
    /// let mut t2 = rule.rhs[0].clone();
    ///
    /// assert_ne!(t1, t2);
    ///
    /// t1.canonicalize(&mut HashMap::new());
    /// t2.canonicalize(&mut HashMap::new());
    ///
    /// assert_eq!(t1, t2);
    pub fn canonicalize(&mut self, map: &mut HashMap<usize, usize>) {
        match self {
            Term::Variable(v) => {
                let new_id = map.len();
                let id = map.entry(v.0).or_insert_with(|| new_id);
                v.0 = *id;
            }
            Term::Application { ref mut args, .. } => {
                args.iter_mut().for_each(|arg| arg.canonicalize(map))
            }
        }
    }
    pub fn offset(&mut self, n: usize) {
        match self {
            Term::Variable(v) => v.0 += n,
            Term::Application { ref mut args, .. } => args.iter_mut().for_each(|arg| arg.offset(n)),
        }
    }
    /// Compute the [alpha equivalence] for two `Term`s.
    ///
    /// [alpha equivalence]: https://en.wikipedia.org/wiki/Lambda_calculus#Alpha_equivalence
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_term, Term, Substitution, Variable};
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
    /// let expected_alpha = Substitution(vec![(z, &tb), (y, &ta)]);
    ///
    /// assert_eq!(Term::alpha(&[(&t, &t2)]), Some(expected_alpha));
    ///
    /// assert_eq!(Term::alpha(&[(&t, &t3)]), None);
    /// ```
    pub fn alpha<'a>(cs: &[(&'a Term, &'a Term)]) -> Option<Substitution<'a>> {
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
    /// assert!(Term::same_shape(&t, &t2));
    ///
    /// assert!(!Term::same_shape(&t, &t3));
    /// ```
    pub fn same_shape(t1: &Term, t2: &Term) -> bool {
        let mut omap = HashMap::new();
        let mut vmap = HashMap::new();
        Term::same_shape_given(t1, t2, &mut omap, &mut vmap)
    }
    pub fn same_shape_given(
        t1: &Term,
        t2: &Term,
        omap: &mut HashMap<Operator, Operator>,
        vmap: &mut HashMap<Variable, Variable>,
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
                args1.len() == args2.len()
                    && op2 == *omap.entry(op1).or_insert(op2)
                    && args1
                        .iter()
                        .zip(args2)
                        .all(|(a1, a2)| Term::same_shape_given(a1, a2, omap, vmap))
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
    /// # use term_rewriting::{Signature, Term, Substitution, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let t1 = parse_term(&mut sig, "C(A)").expect("parse of C(A)");
    ///
    /// let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    ///
    /// assert_eq!(Term::pmatch(&[(&t1, &t2)]), None);
    ///
    /// // maps variable x in term t2 to constant A in term t1
    /// let t_k = &t2.variables()[0];
    /// let t_v = parse_term(&mut sig, "A").expect("parse of A");
    /// let expected_sub = Substitution(vec![(t_k, &t_v)]);
    ///
    /// assert_eq!(Term::pmatch(&[(&t2, &t1)]), Some(expected_sub));
    ///
    /// let t3 = parse_term(&mut sig, "A(x_)").expect("parse of A(x_)");
    ///
    /// assert_eq!(Term::pmatch(&[(&t2, &t3)]), None);
    /// ```
    pub fn pmatch<'a>(cs: &[(&'a Term, &'a Term)]) -> Option<Substitution<'a>> {
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
    /// # use term_rewriting::{Signature, Term, Substitution, parse_term};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_term(&mut sig, "C(A)").expect("parse of C(A)");
    /// let t2 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    ///
    /// // Map variable x in term t2 to constant A in term t1.
    /// let t_k = &t2.variables()[0];
    /// let t_v = parse_term(&mut sig, "A").expect("parse of A");
    /// let expected_sub = Substitution(vec![(t_k, &t_v)]);
    ///
    /// assert_eq!(Term::unify(&[(&t1, &t2)]), Some(expected_sub));
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{Signature, Substitution, Term, parse_term};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    /// let t2 = parse_term(&mut sig, "C(y_)").expect("parse of C(y_)");
    ///
    /// // Map variable x in term t2 to variable y in term t2.
    /// let t_k = &t1.variables()[0];
    /// let t_v = Term::Variable(t2.variables()[0].clone());
    /// let expected_sub = Substitution(vec![(t_k, &t_v)]);
    ///
    /// assert_eq!(Term::unify(&[(&t1, &t2)]), Some(expected_sub));
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{Signature, Term, parse_term};
    /// # use std::collections::{HashMap, HashSet};
    /// # let mut sig = Signature::default();
    /// let t1 = parse_term(&mut sig, "C(x_)").expect("parse of C(x_)");
    /// let t2 = parse_term(&mut sig, "B(x_)").expect("parse of B(x_)");
    ///
    /// assert_eq!(Term::unify(&[(&t1, &t2)]), None);
    /// ```
    pub fn unify<'a>(cs: &[(&'a Term, &'a Term)]) -> Option<Substitution<'a>> {
        Term::unify_internal(cs, Unification::Unify)
    }
    /// the internal implementation of a single unification.
    #[inline]
    fn unify_one<'a>(
        mut s: &'a Term,
        mut t: &'a Term,
        cs: &mut SmallVec<[(&'a Term, &'a Term); 32]>,
        subs: &mut SmallVec<[(&'a Variable, &'a Term); 32]>,
        utype: &Unification,
    ) -> Option<()> {
        while let Term::Variable(v) = *s {
            match subs.iter().find(|(k_var, _)| **k_var == v) {
                Some((_, v_term)) => s = v_term,
                None => break,
            }
        }

        while let Term::Variable(v) = *t {
            match subs.iter().find(|(k_var, _)| **k_var == v) {
                Some((_, v_term)) => t = v_term,
                None => break,
            }
        }

        // if they are equal, you're all done with them.
        if s != t {
            match (s, t) {
                (Term::Variable(ref var), Term::Variable(_)) => {
                    subs.push((var, t));
                }
                (Term::Variable(ref var), t) if *utype != Unification::Alpha => {
                    if t.all_variables().any(|v| v == *var) {
                        return None;
                    } else {
                        subs.push((var, t));
                    }
                }
                (s, Term::Variable(ref var)) if *utype == Unification::Unify => {
                    if s.all_variables().any(|v| v == *var) {
                        return None;
                    } else {
                        subs.push((var, s));
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
                    for pair in a1.iter().zip(a2.iter()) {
                        cs.push(pair);
                    }
                }
                _ => return None,
            }
        }
        Some(())
    }
    /// the internal implementation of unification.
    fn unify_internal<'a>(
        initial_cs: &[(&'a Term, &'a Term)],
        utype: Unification,
    ) -> Option<Substitution<'a>> {
        let mut cs: SmallVec<[(&Term, &Term); 32]> = smallvec![];
        let mut subs: SmallVec<[(&Variable, &Term); 32]> = smallvec![];
        for &(s, t) in initial_cs {
            Term::unify_one(s, t, &mut cs, &mut subs, &utype)?;
        }
        while let Some((s, t)) = cs.pop() {
            Term::unify_one(s, t, &mut cs, &mut subs, &utype)?;
        }
        Some(Substitution(subs.to_vec()))
    }
}
