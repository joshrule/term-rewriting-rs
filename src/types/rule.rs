use super::{Context, Operator, Place, Signature, Term, Variable};
use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    convert::TryFrom,
    iter,
};

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
    /// The `RuleContext` must abide by the same restrictions as a [`Rule`] being created with [`Rule::new`].
    ///
    /// [`Rule`]: struct.Rule.html
    /// [`Rule::new`]: struct.Rule.html#method.new
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
    ///
    /// let left = parse_context(&mut sig, "A(B C [!])").expect("parse of A(B C [!])");
    /// let b = parse_context(&mut sig, "B [!] x_").expect("parse of B [!] x_");
    /// let c = parse_context(&mut sig, "C").expect("parse of C");
    ///
    /// assert_eq!(RuleContext::new(left, vec![b, c]), None);
    ///
    /// let left = parse_context(&mut sig, "x_").expect("parse of x_");
    /// let b = parse_context(&mut sig, "B [!]").expect("parse of B [!]");
    ///
    /// assert_eq!(RuleContext::new(left, vec![b]), None);
    /// ```
    pub fn new(lhs: Context, rhs: Vec<Context>) -> Option<RuleContext> {
        if RuleContext::is_valid(&lhs, &rhs) {
            Some(RuleContext { lhs, rhs })
        } else {
            None
        }
    }
    /// Could `lhs` and `rhs` form a valid `RuleContext`?
    pub fn is_valid(lhs: &Context, rhs: &[Context]) -> bool {
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
    /// Serialize a `RuleContext`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let rule = parse_rulecontext(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = [!] CONS(A CONS(B(x_) CONS(SUCC(SUCC(ZERO)) NIL)))")
    ///     .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = [!] CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))");
    ///
    /// assert_eq!(rule.display(&sig), ".(.(.(A B(x_)) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5)) = .([!] CONS(A CONS(B(x_) CONS(SUCC(SUCC(ZERO)) NIL))))");
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        let lhs_str = self.lhs.display(sig);
        let rhs_str = self.rhs.iter().map(|c| c.display(sig)).join(" | ");
        format!("{} = {}", lhs_str, rhs_str)
    }
    /// A human-readable serialization of the `RuleContext`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let rule = parse_rulecontext(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = [!] CONS(A CONS(B(x_) CONS(SUCC(SUCC(ZERO)) NIL)))")
    ///     .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = [!] CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))");
    ///
    /// assert_eq!(rule.pretty(&sig), "A B(x_) [2, 1, 0] 105 = [!] [A, B(x_), 2]");
    /// ```
    pub fn pretty(&self, sig: &Signature) -> String {
        let lhs_str = self.lhs.pretty(sig);
        let rhs_str = self.rhs.iter().map(|c| c.pretty(sig)).join(" | ");
        format!("{} = {}", lhs_str, rhs_str)
    }
    /// The total number of subcontexts across all [`Context`]s in the `RuleContext`.
    ///
    /// [`Context`]: enum.Context.html
    pub fn size(&self) -> usize {
        self.lhs.size() + self.rhs.iter().map(Context::size).sum::<usize>()
    }
    /// `true` if `self == [!] = [!]`, else `false`.
    pub fn is_empty(&self) -> bool {
        self.lhs == Context::Hole && self.rhs.len() == 1 && self.rhs[0] == Context::Hole
    }
    /// The leftmost [`Place`] in the `RuleContext` that is a [`Hole`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_rulecontext};
    /// let mut sig = Signature::default();
    ///
    /// let rule = parse_rulecontext(&mut sig, "[!] = [!]").expect("parsed rule");
    /// assert_eq!(rule.leftmost_hole(), Some(vec![0]));
    ///
    /// let rule = parse_rulecontext(&mut sig, "A = [!]").expect("parsed rule");
    /// assert_eq!(rule.leftmost_hole(), Some(vec![1]));
    ///
    /// let rule = parse_rulecontext(&mut sig, "(B [!]) A = [!]").expect("parsed rule");
    /// assert_eq!(rule.leftmost_hole(), Some(vec![0, 0, 1]));
    ///
    /// let rule = parse_rulecontext(&mut sig, "(B A) A = B [!]").expect("parsed rule");
    /// assert_eq!(rule.leftmost_hole(), Some(vec![1, 1]));
    /// ```
    ///
    /// [`Place`]: type.Place.html
    /// [`Hole`]: enum.Context.html#variant.Hole
    pub fn leftmost_hole(&self) -> Option<Place> {
        self.lhs
            .leftmost_hole()
            .map(|mut place| {
                let mut full_place = vec![0];
                full_place.append(&mut place);
                full_place
            })
            .or_else(|| {
                self.rhs.iter().enumerate().find_map(|(i, rhs)| {
                    rhs.leftmost_hole().map(|mut place| {
                        let mut full_place = vec![i + 1];
                        full_place.append(&mut place);
                        full_place
                    })
                })
            })
    }
    /// Get all the [`subcontexts`] and [`Place`]s in a `RuleContext`.
    ///
    /// [`subcontexts`]: struct.Context.html
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
    ///     .map(|(c, p)| format!("({}, {:?})", c.display(&sig), p))
    ///     .collect();
    ///
    /// assert_eq!(
    ///     subcontexts,
    ///     vec![
    ///         "(A(x_ [!]), [0])",
    ///         "(x_, [0, 0])",
    ///         "([!], [0, 1])",
    ///         "(C(x_), [1])",
    ///         "(x_, [1, 0])",
    ///         "(D([!]), [2])",
    ///         "([!], [2, 0])",
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
    /// let r_variables: Vec<String> = r.variables().iter().map(|v| v.display()).collect();
    ///
    /// assert_eq!(r_variables, vec!["x_"]);
    ///
    /// let r = parse_rulecontext(&mut sig, "B(y_ z_) = C [!]").expect("parse of B(y_ z_) = C [!]");
    /// let r_variables: Vec<String> = r.variables().iter().map(|v| v.display()).collect();
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
            self.lhs.replace(&place[1..], subcontext).map(|lhs| {
                let rhs = self.rhs.clone();
                RuleContext { lhs, rhs }
            })
        } else {
            self.rhs[place[0] - 1]
                .replace(&place[1..], subcontext)
                .map(|an_rhs| {
                    let lhs = self.lhs.clone();
                    let mut rhs = self.rhs.clone();
                    rhs[place[0] - 1] = an_rhs;
                    RuleContext { lhs, rhs }
                })
        }
    }
    pub fn replace_all(&self, places: &[Place], subcontext: Context) -> Option<RuleContext> {
        let mut lhs = self.lhs.clone();
        let mut rhs = self.rhs.clone();
        for place in places {
            if place[0] == 0 {
                lhs = lhs.replace(&place[1..], subcontext.clone())?;
            } else {
                rhs[place[0] - 1] = rhs[place[0] - 1].replace(&place[1..], subcontext.clone())?;
            }
        }
        RuleContext::new(lhs, rhs)
    }
    pub fn canonicalize(&mut self, map: &mut HashMap<usize, usize>) {
        self.lhs.canonicalize(map);
        self.rhs.iter_mut().for_each(|r| r.canonicalize(map));
    }
    pub fn offset(&mut self, n: usize) {
        self.lhs.offset(n);
        self.rhs.iter_mut().for_each(|r| r.offset(n));
    }
}
impl From<&Rule> for RuleContext {
    fn from(r: &Rule) -> RuleContext {
        let new_lhs = Context::from(&r.lhs);
        let new_rhs = r.rhs.iter().map(Context::from).collect();
        RuleContext::new(new_lhs, new_rhs).unwrap()
    }
}
impl From<Rule> for RuleContext {
    fn from(r: Rule) -> RuleContext {
        let new_lhs = Context::from(r.lhs);
        let new_rhs = r.rhs.into_iter().map(Context::from).collect();
        RuleContext::new(new_lhs, new_rhs).unwrap()
    }
}
impl TryFrom<&RuleContext> for Rule {
    type Error = Place;
    fn try_from(context: &RuleContext) -> Result<Self, Self::Error> {
        let lhs = Term::try_from(&context.lhs).map_err(|mut lhs_place| {
            let mut place = vec![0];
            place.append(&mut lhs_place);
            place
        })?;
        let mut rhss = Vec::with_capacity(context.rhs.len());
        for (i, rhs) in context.rhs.iter().enumerate() {
            let new_rhs = Term::try_from(rhs).map_err(|mut rhs_place| {
                let mut place = vec![i + 1];
                place.append(&mut rhs_place);
                place
            })?;
            rhss.push(new_rhs);
        }
        Rule::new(lhs, rhss).ok_or_else(Vec::new)
    }
}
impl Default for RuleContext {
    fn default() -> Self {
        RuleContext {
            lhs: Context::Hole,
            rhs: vec![Context::Hole],
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
    /// Serialize a `Rule`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Rule, Term, parse_term, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let rule = parse_rule(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))")
    ///     .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))");
    ///
    /// assert_eq!(rule.display(&sig), ".(.(.(A B(x_)) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5)) = CONS(A CONS(B(x_) CONS(SUCC(SUCC(ZERO)) NIL)))");
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        let lhs_str = self.lhs.display(sig);
        let rhs_str = self.rhs.iter().map(|t| t.display(sig)).join(" | ");
        format!("{} = {}", lhs_str, rhs_str)
    }
    /// A human-readable serialization of the `Rule`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let rule = parse_rule(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))")
    ///     .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))");
    ///
    /// assert_eq!(rule.pretty(&sig), "A B(x_) [2, 1, 0] 105 = [A, B(x_), 2]");
    /// ```
    pub fn pretty(&self, sig: &Signature) -> String {
        let lhs_str = self.lhs.pretty(sig);
        let rhs_str = self.rhs.iter().map(|t| t.pretty(sig)).join(" | ");
        format!("{} = {}", lhs_str, rhs_str)
    }
    /// The total number of subterms across all [`Term`]s in the `Rule`.
    ///
    /// [`Term`]: struct.Term.html
    ///
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
    ///
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
            let lhs_vars = lhs.variables().into_iter().collect_vec();
            let mut rhs_vars = rhs.iter().flat_map(Term::variables);
            rhs_vars.all(|v| lhs_vars.contains(&v))
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
    /// let mut r = parse_rule(&mut sig, "A(x_) = B").expect("parse A(x_) = B");
    /// let r2 = parse_rule(&mut sig, "A(y_) = C(y_)").expect("parse A(y_) = C(y_)");
    /// r.merge(&r2);
    ///
    /// assert_eq!(r.display(&sig), "A(x_) = B | C(x_)");
    /// ```
    pub fn merge(&mut self, r: &Rule) {
        if let Some(s) = Term::alpha(vec![(&r.lhs, &self.lhs)]) {
            for rhs in r.rhs.clone() {
                let new_rhs = rhs.substitute(&s);
                if !self.rhs.contains(&new_rhs) {
                    self.rhs.push(new_rhs);
                }
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
        if let Some(sub) = Term::alpha(vec![(&r.lhs, &self.lhs)]) {
            let terms = r
                .rhs
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
    /// let x = Term::Variable(r.variables()[0].clone());
    /// let y = &r2.variables()[0];
    /// let mut sub = HashMap::default();
    /// sub.insert(y, &x);
    ///
    /// assert_eq!(r.contains(&r2).unwrap(), sub);
    /// ```
    pub fn contains<'a>(&'a self, r: &'a Rule) -> Option<HashMap<&'a Variable, &'a Term>> {
        if let Some(sub) = Term::alpha(vec![(&r.lhs, &self.lhs)]) {
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
    ///     .map(|(t, p)| format!("{}, {:?}", t.display(&sig), p))
    ///     .collect();
    ///
    /// assert_eq!(
    ///     subterms,
    ///     vec![
    ///         "A(x_ B), [0]",
    ///         "x_, [0, 0]",
    ///         "B, [0, 1]",
    ///         "C(x_), [1]",
    ///         "x_, [1, 0]",
    ///         "D(B), [2]",
    ///         "B, [2, 0]",
    ///     ]
    /// );
    /// ```
    pub fn subterms(&self) -> Vec<(&Term, Place)> {
        let lhs = self.lhs.subterms().into_iter().map(|(t, mut p)| {
            p.insert(0, 0);
            (t, p)
        });
        let rhs = self.rhs.iter().enumerate().flat_map(|(i, rhs)| {
            iter::repeat(i + 1)
                .zip(rhs.subterms())
                .map(|(i, (t, mut p))| {
                    p.insert(0, i);
                    (t, p)
                })
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
            self.lhs
                .replace(&place[1..], subterm)
                .and_then(|lhs| Rule::new(lhs, self.rhs.clone()))
        } else {
            self.rhs[place[0] - 1]
                .replace(&place[1..], subterm)
                .and_then(|an_rhs| {
                    let mut rhs = self.rhs.clone();
                    rhs[place[0] - 1] = an_rhs;
                    Rule::new(self.lhs.clone(), rhs)
                })
        }
    }
    pub fn replace_all(&self, places: &[Place], subterm: Term) -> Option<Rule> {
        let mut lhs = self.lhs.clone();
        let mut rhs = self.rhs.clone();
        for place in places {
            if place[0] == 0 {
                lhs = lhs.replace(&place[1..], subterm.clone())?;
            } else {
                rhs[place[0] - 1] = rhs[place[0] - 1].replace(&place[1..], subterm.clone())?;
            }
        }
        Rule::new(lhs, rhs)
    }
    pub fn canonicalize(&mut self, map: &mut HashMap<usize, usize>) {
        self.lhs.canonicalize(map);
        self.rhs.iter_mut().for_each(|r| r.canonicalize(map));
    }
    pub fn offset(&mut self, n: usize) {
        self.lhs.offset(n);
        self.rhs.iter_mut().for_each(|r| r.offset(n));
    }
    /// Compute the least general generalization of two `Rule`s.
    ///
    /// # Example
    /// ```
    /// # use term_rewriting::{Signature, parse_rule, Rule};
    /// let mut sig = Signature::default();
    ///
    /// let r1 = parse_rule(&mut sig, "C(CONS(2 NIL)) = 2 ").expect("parsed rule");
    /// let r2 = parse_rule(&mut sig, "C(CONS(3 NIL)) = 3 ").expect("parsed rule");
    /// let r3 = Rule::least_general_generalization(&r1, &r2).expect("generalization");
    ///
    /// assert_eq!(r3.display(&sig), "C(CONS(v0_ NIL)) = v0_");
    ///
    /// let r1 = parse_rule(&mut sig, "C(CONS(2 NIL)) = 3 ").expect("parsed rule");
    /// let r2 = parse_rule(&mut sig, "C(CONS(3 NIL)) = 2 ").expect("parsed rule");
    /// let none = Rule::least_general_generalization(&r1, &r2);
    ///
    /// assert!(none.is_none());
    /// ```
    pub fn least_general_generalization(r1: &Rule, r2: &Rule) -> Option<Rule> {
        // Make a variable generator
        let mut id = 0;
        // Match on the structure of the term
        let mut stack = vec![(&r1.lhs, &r2.lhs)];
        let mut map = HashMap::new();
        while let Some(terms) = stack.pop() {
            match terms {
                (
                    &Term::Application {
                        op: ref op1,
                        args: ref args1,
                    },
                    &Term::Application {
                        op: ref op2,
                        args: ref args2,
                    },
                ) if op1 == op2 => {
                    for pair in args1.iter().zip(args2) {
                        stack.push(pair);
                    }
                }
                other => {
                    if map.get(&other).is_none() {
                        map.insert(other, id);
                        id += 1;
                    }
                }
            }
        }
        let new_rhs = r1
            .rhs
            .iter()
            .zip(&r2.rhs)
            .map(|rhss| Rule::lgg_helper(rhss, &map))
            .collect::<Option<Vec<Term>>>();
        if let Some(new_rhs) = new_rhs {
            if let Some(new_lhs) = Rule::lgg_helper((&r1.lhs, &r2.lhs), &map) {
                return Rule::new(new_lhs, new_rhs);
            }
        }
        None
    }
    fn lgg_helper(terms: (&Term, &Term), map: &HashMap<(&Term, &Term), usize>) -> Option<Term> {
        if let Some(&id) = map.get(&terms) {
            Some(Term::Variable(Variable { id }))
        } else {
            match terms {
                (
                    &Term::Application {
                        op: ref op1,
                        args: ref args1,
                    },
                    &Term::Application {
                        op: ref op2,
                        args: ref args2,
                    },
                ) if op1 == op2 => {
                    let mut mapped_args = Vec::with_capacity(args1.len());
                    for pair in args1.iter().zip(args2) {
                        if let Some(subterm) = Rule::lgg_helper(pair, map) {
                            mapped_args.push(subterm)
                        } else {
                            return None;
                        }
                    }
                    Some(Term::Application {
                        op: *op1,
                        args: mapped_args,
                    })
                }
                _ => None,
            }
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
    /// assert_eq!(Rule::pmatch(&r, &r2), None);
    /// assert_eq!(Rule::pmatch(&r, &r3), None);
    /// assert_eq!(Rule::pmatch(&r, &r4), None);
    ///
    /// let t_k = &r.variables()[0];
    /// let t_v = Term::Variable(r5.variables()[0].clone());
    /// let mut expected_map = HashMap::default();
    /// expected_map.insert(t_k, &t_v);
    ///
    /// assert_eq!(Rule::pmatch(&r, &r5), Some(expected_map));
    /// ```
    pub fn pmatch<'a>(r1: &'a Rule, r2: &'a Rule) -> Option<HashMap<&'a Variable, &'a Term>> {
        let cs = iter::once((&r1.lhs, &r2.lhs)).chain(r1.rhs.iter().zip(r2.rhs.iter()));
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
    /// let t_k0 = &r.variables()[0];
    /// let t_k1 = &r2.variables()[0];
    /// let b = parse_term(&mut sig, "B").expect("parse of B");
    /// let mut expected_map = HashMap::default();
    /// expected_map.insert(t_k0, &b);
    /// expected_map.insert(t_k1, &b);
    ///
    /// assert_eq!(Rule::unify(&r, &r2), Some(expected_map));
    ///
    /// assert_eq!(Rule::unify(&r, &r3), None);
    /// assert_eq!(Rule::unify(&r, &r4), None);
    ///
    /// let t_k = &r.variables()[0];
    /// let t_v = Term::Variable(r5.variables()[0].clone());
    /// let mut expected_map = HashMap::default();
    /// expected_map.insert(t_k, &t_v);
    ///
    /// assert_eq!(Rule::unify(&r, &r5), Some(expected_map));
    /// ```
    pub fn unify<'a>(r1: &'a Rule, r2: &'a Rule) -> Option<HashMap<&'a Variable, &'a Term>> {
        let cs = iter::once((&r1.lhs, &r2.lhs)).chain(r1.rhs.iter().zip(r2.rhs.iter()));
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
    /// let t_k = &r.variables()[0];
    /// let t_v = Term::Variable(r5.variables()[0].clone());
    /// let mut expected_map = HashMap::default();
    /// expected_map.insert(t_k, &t_v);
    ///
    /// assert_eq!(Rule::alpha(&r, &r5), Some(expected_map));
    /// ```
    pub fn alpha<'a>(r1: &'a Rule, r2: &'a Rule) -> Option<HashMap<&'a Variable, &'a Term>> {
        let cs = iter::once((&r1.lhs, &r2.lhs)).chain(r1.rhs.iter().zip(r2.rhs.iter()));
        Term::alpha(cs.collect())
    }
    /// Do two rules share the same shape?
    pub fn same_shape(r1: &Rule, r2: &Rule) -> bool {
        let mut omap = HashMap::new();
        let mut vmap = HashMap::new();
        Rule::same_shape_given(r1, r2, &mut omap, &mut vmap)
    }
    /// Do two rules share the same shape given some initial constraints?
    pub fn same_shape_given(
        r1: &Rule,
        r2: &Rule,
        ops: &mut HashMap<Operator, Operator>,
        vars: &mut HashMap<Variable, Variable>,
    ) -> bool {
        if r1.rhs.len() == r2.rhs.len() {
            Term::same_shape_given(&r1.lhs, &r2.lhs, ops, vars)
                && r1
                    .rhs
                    .iter()
                    .zip(&r2.rhs)
                    .all(|(r1_rhs, r2_rhs)| Term::same_shape_given(r1_rhs, r2_rhs, ops, vars))
        } else {
            false
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
    /// let x = &vars[0];
    ///
    /// let mut substitution = HashMap::default();
    /// substitution.insert(x, &c);
    ///
    /// let r2 = r.substitute(&substitution);
    ///
    /// assert_eq!(r2.display(&sig), "A(C y_) = A(C) | B(y_)");
    /// ```
    pub fn substitute(&self, sub: &HashMap<&Variable, &Term>) -> Rule {
        Rule::new(
            self.lhs.substitute(sub),
            self.rhs.iter().map(|rhs| rhs.substitute(sub)).collect(),
        )
        .unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::parser::*;
    use super::super::{Signature, Term};
    use super::*;
    use std::{collections::HashMap, convert::TryFrom};

    #[test]
    fn rulecontext_new_test() {
        let mut sig = Signature::default();

        let left = parse_context(&mut sig, "A(B C [!])").expect("parse of A(B C [!])");
        let b = parse_context(&mut sig, "B [!]").expect("parse of B [!]");
        let c = parse_context(&mut sig, "C").expect("parse of C");

        let r = RuleContext::new(left, vec![b, c]).unwrap();

        assert_eq!(r.pretty(&sig), "A(B, C, [!]) = B [!] | C");

        let left = parse_context(&mut sig, "A(B C [!])").expect("parse of A(B C [!])");
        let b = parse_context(&mut sig, "B [!] x_").expect("parse of B [!] x_");
        let c = parse_context(&mut sig, "C").expect("parse of C");

        assert_eq!(RuleContext::new(left, vec![b, c]), None);

        let left = parse_context(&mut sig, "x_").expect("parse of x_");
        let b = parse_context(&mut sig, "B [!]").expect("parse of B [!]");

        assert_eq!(RuleContext::new(left, vec![b]), None);
    }

    #[test]
    fn rulecontext_display_test() {
        let mut sig = Signature::default();

        let rule = parse_rulecontext(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = [!] CONS(A CONS(B(x_) CONS(SUCC(SUCC(ZERO)) NIL)))")
            .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = [!] CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))");

        assert_eq!(rule.display(&sig), ".(.(.(A B(x_)) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5)) = .([!] CONS(A CONS(B(x_) CONS(SUCC(SUCC(ZERO)) NIL))))");
    }

    #[test]
    fn rule_context_pretty_test() {
        let mut sig = Signature::default();

        let rule = parse_rulecontext(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = [!] CONS(A CONS(B(x_) CONS(SUCC(SUCC(ZERO)) NIL)))")
            .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = [!] CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))");

        assert_eq!(
            rule.pretty(&sig),
            "A B(x_) [2, 1, 0] 105 = [!] [A, B(x_), 2]"
        );
    }

    #[test]
    fn subcontexts_test() {
        let mut sig = Signature::default();

        let r = parse_rulecontext(&mut sig, "A(x_ [!]) = C(x_) | D([!])")
            .expect("parse of A(x_ B[!]) = C(x_) | D([!])");

        let subcontexts: Vec<String> = r
            .subcontexts()
            .iter()
            .map(|(c, p)| format!("({}, {:?})", c.display(&sig), p))
            .collect();

        assert_eq!(
            subcontexts,
            vec![
                "(A(x_ [!]), [0])",
                "(x_, [0, 0])",
                "([!], [0, 1])",
                "(C(x_), [1])",
                "(x_, [1, 0])",
                "(D([!]), [2])",
                "([!], [2, 0])",
            ]
        );
    }

    #[test]
    fn holes_test() {
        let mut sig = Signature::default();

        let r = parse_rulecontext(&mut sig, "A(x_ [!]) = C(x_) | D([!])")
            .expect("parse of A(x_ B[!]) = C(x_) | D([!])");

        let p: &[usize] = &[0, 1];
        let p2: &[usize] = &[2, 0];

        assert_eq!(r.holes(), vec![p, p2]);
    }

    #[test]
    fn rulecontext_variables_test() {
        let mut sig = Signature::default();

        let r =
            parse_rulecontext(&mut sig, "A(x_ [!]) = C(x_)").expect("parse of A(x_ [!]) = C(x_)");
        let r_variables: Vec<String> = r.variables().iter().map(|v| v.display()).collect();

        assert_eq!(r_variables, vec!["x_"]);

        let r = parse_rulecontext(&mut sig, "B(y_ z_) = C [!]").expect("parse of B(y_ z_) = C [!]");
        let r_variables: Vec<String> = r.variables().iter().map(|v| v.display()).collect();

        assert_eq!(r_variables, vec!["y_", "z_"]);
    }

    #[test]
    fn rulecontext_operators_test() {
        let mut sig = Signature::default();

        let r = parse_rulecontext(&mut sig, "A(D E) = C([!])").expect("parse of A(D E) = C([!])");
        let r_ops: Vec<String> = r.operators().iter().map(|o| o.display(&sig)).collect();

        assert_eq!(r_ops, vec!["D", "E", "A", "C"]);

        let r = parse_rulecontext(&mut sig, "B(F x_) = C [!]").expect("parse of B(F x_) = C [!]");
        let r_ops: Vec<String> = r.operators().iter().map(|o| o.display(&sig)).collect();

        assert_eq!(r_ops, vec!["F", "B", "C", "."]);
    }

    #[test]
    fn rulecontext_at_test() {
        let mut sig = Signature::default();

        let r = parse_rulecontext(&mut sig, "A(x_ [!]) = B | C(x_ [!])")
            .expect("parse of A(x_ [!]) = B | C(x_ [!])");

        assert_eq!(r.at(&[0]).unwrap().display(&sig), "A(x_ [!])");
        assert_eq!(r.at(&[0, 1]).unwrap().display(&sig), "[!]");
        assert_eq!(r.at(&[0, 0]).unwrap().display(&sig), "x_");
        assert_eq!(r.at(&[1]).unwrap().display(&sig), "B");
        assert_eq!(r.at(&[2]).unwrap().display(&sig), "C(x_ [!])");
    }

    #[test]
    fn rulecontext_replace_test() {
        let mut sig = Signature::default();

        let r = parse_rulecontext(&mut sig, "A(x_) = B | C(x_) | [!]")
            .expect("parse of A(x_) = B| C(x_) | [!]");
        let new_context = parse_context(&mut sig, "E [!]").expect("parse of E [!]");
        let new_r = r.replace(&[1], new_context);

        assert_ne!(r, new_r.clone().unwrap());
        assert_eq!(new_r.unwrap().pretty(&sig), "A(x_) = E [!] | C(x_) | [!]");
    }

    #[test]
    fn try_from_test() {
        let mut sig = Signature::default();

        let r = parse_rulecontext(&mut sig, "A(x_ [!]) = B | C(x_ [!])")
            .expect("parse of A(x_ [!]) = B | C(x_ [!])");

        assert!(Rule::try_from(&r).is_err());

        let r =
            parse_rulecontext(&mut sig, "A(x_) = B | C(x_)").expect("parse of A(x_) = B | C(x_)");
        let rule = Rule::try_from(&r).expect("converting RuleContext to Rule");

        assert_eq!(rule.pretty(&sig), "A(x_) = B | C(x_)");
    }

    #[test]
    fn rule_display_test() {
        let mut sig = Signature::default();

        let rule = parse_rule(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))")
            .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))");

        assert_eq!(rule.display(&sig), ".(.(.(A B(x_)) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL)))) DECC(DECC(DIGIT(1) 0) 5)) = CONS(A CONS(B(x_) CONS(SUCC(SUCC(ZERO)) NIL)))");
    }

    #[test]
    fn rule_pretty_test() {
        let mut sig = Signature::default();

        let rule = parse_rule(&mut sig, "A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))")
            .expect("parse of A B(x_) CONS(SUCC(SUCC(ZERO)) CONS(SUCC(ZERO) CONS(ZERO NIL))) DECC(DECC(DIGIT(1) 0) 5) = CONS(A CONS(B(x_) CONS( SUCC(SUCC(ZERO)) NIL)))");

        assert_eq!(rule.pretty(&sig), "A B(x_) [2, 1, 0] 105 = [A, B(x_), 2]");
    }

    #[test]
    fn size_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");

        assert_eq!(r.size(), 5);
    }

    #[test]
    fn len_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");

        assert_eq!(r.size(), 5);
    }

    #[test]
    fn is_empty_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");

        assert!(!r.is_empty());

        let lhs = parse_term(&mut sig, "A").expect("parse of A");
        let rhs: Vec<Term> = vec![];
        let r = Rule::new(lhs, rhs).unwrap();

        assert!(r.is_empty());
    }

    #[test]
    fn rhs_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A = B").expect("parse of A = B");
        let b = parse_term(&mut sig, "B").expect("parse of B");

        assert_eq!(r.rhs().unwrap(), b);

        let r = parse_rule(&mut sig, "A = B | C").expect("parse of A = B | C");

        assert_eq!(r.rhs(), Option::None);
    }

    #[test]
    fn clauses_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A = B").expect("parse of A = B");

        assert_eq!(r.clauses(), vec![r]);

        let r = parse_rule(&mut sig, "A = B | C").expect("parse of A = B | C");
        let r1 = parse_rule(&mut sig, "A = B").expect("parse of A = B");
        let r2 = parse_rule(&mut sig, "A = C").expect("parse of A = C");

        assert_eq!(r.clauses(), vec![r1, r2]);
    }

    #[test]
    fn is_valid_test() {}

    #[test]
    #[ignore]
    fn rule_new_test() {
        let mut sig = Signature::default();

        let lhs = parse_term(&mut sig, "A").expect("parse of A");
        let rhs = vec![parse_term(&mut sig, "B").expect("parse of B")];
        let r = Rule::new(lhs, rhs).unwrap();

        let r2 = parse_rule(&mut sig, "A = B").expect("parse of A = B");

        assert_eq!(r, r2);

        let left = parse_term(&mut sig, "A").expect("parse of A");
        let right = vec![parse_term(&mut sig, "B").expect("parse of B")];
        let r2 = Rule {
            lhs: left,
            rhs: right,
        };

        assert_eq!(r, r2);
    }

    #[test]
    fn add_test() {
        let mut sig = Signature::default();

        let c = parse_term(&mut sig, "C").expect("parse of C");
        let mut r = parse_rule(&mut sig, "A = B").expect("parse of A = B");

        assert_eq!(r.display(&sig), "A = B");

        r.add(c);

        assert_eq!(r.display(&sig), "A = B | C");
    }

    #[test]
    fn merge_test() {
        let mut sig = Signature::default();

        let mut r = parse_rule(&mut sig, "A = B").expect("parse A = B");
        let r2 = parse_rule(&mut sig, "A = C").expect("parse A = C");
        r.merge(&r2);

        assert_eq!(r.display(&sig), "A = B | C");
    }

    #[test]
    fn discard_test() {
        let mut sig = Signature::default();

        let mut r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");
        let r2 = parse_rule(&mut sig, "A(y_) = B(y_)").expect("parse of A(y_) = B(y_)");
        r.discard(&r2);

        assert_eq!(r.display(&sig), "A(x_) = C");
    }

    #[test]
    fn contains_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B(x_) | C").expect("parse of A(x_) = B(x_) | C");
        let r2 = parse_rule(&mut sig, "A(y_) = B(y_)").expect("parse of A(y_) = B(y_)");

        assert_eq!(r2.contains(&r), None);

        {
            let x = Term::Variable(r.variables()[0].clone());
            let y = &r2.variables()[0];
            let mut sub = HashMap::new();
            sub.insert(y, &x);

            assert_eq!(r.contains(&r2).unwrap(), sub);
        }
    }

    #[test]
    fn rule_variables_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = C(x_)").expect("parse of A(x_) = C(x_)");
        let r_variables: Vec<String> = r.variables().iter().map(|v| v.display()).collect();

        assert_eq!(r_variables, vec!["x_"]);

        let r = parse_rule(&mut sig, "B(y_ z_) = C").expect("parse of B(y_ z_) = C");
        let r_variables: Vec<String> = r.variables().iter().map(|v| v.display()).collect();

        assert_eq!(r_variables, vec!["y_", "z_"]);
    }

    #[test]
    fn rule_operators_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(D E) = C").expect("parse of A(D E) = C");
        let r_ops: Vec<String> = r.operators().iter().map(|o| o.display(&sig)).collect();

        assert_eq!(r_ops, vec!["D", "E", "A", "C"]);

        let r = parse_rule(&mut sig, "B(F x_) = C").expect("parse of B(F x_) = C");
        let r_ops: Vec<String> = r.operators().iter().map(|o| o.display(&sig)).collect();

        assert_eq!(r_ops, vec!["F", "B", "C"]);
    }

    #[test]
    fn subterms_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_ B) = C(x_) | D(B)")
            .expect("parse of A(x_ B) = C(x_) | D(B)");

        let subterms: Vec<String> = r
            .subterms()
            .iter()
            .map(|(t, p)| format!("{}, {:?}", t.display(&sig), p))
            .collect();

        assert_eq!(
            subterms,
            vec![
                "A(x_ B), [0]",
                "x_, [0, 0]",
                "B, [0, 1]",
                "C(x_), [1]",
                "x_, [1, 0]",
                "D(B), [2]",
                "B, [2, 0]",
            ]
        );
    }

    #[test]
    fn rule_at_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B | C(x_)").expect("parse of A(x_) = B | C(x_)");

        assert_eq!(r.at(&[0]).unwrap().display(&sig), "A(x_)");
        assert_eq!(r.at(&[0, 0]).unwrap().display(&sig), "x_");
        assert_eq!(r.at(&[1]).unwrap().display(&sig), "B");
        assert_eq!(r.at(&[2]).unwrap().display(&sig), "C(x_)");
    }

    #[test]
    fn rule_replace_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B | C(x_)").expect("parse of A(x_) = B| C(x_)");
        let new_term = parse_term(&mut sig, "E").expect("parse of E");
        let new_rule = r.replace(&[1], new_term);

        assert_ne!(r, new_rule.clone().unwrap());

        assert_eq!(new_rule.unwrap().display(&sig), "A(x_) = E | C(x_)");
    }

    #[test]
    fn pmatch_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B").expect("parse of A(x_) = B");
        let r2 = parse_rule(&mut sig, "A(y_) = y_").expect("parse of A(y_) = y_");
        let r3 = parse_rule(&mut sig, "A(z_) = C").expect("parse of A(z_) = C");
        let r4 = parse_rule(&mut sig, "D(w_) = B").expect("parse of D(w_) = B");
        let r5 = parse_rule(&mut sig, "A(t_) = B").expect("parse of A(t_) = B");

        assert_eq!(Rule::pmatch(&r, &r2), None);
        assert_eq!(Rule::pmatch(&r, &r3), None);
        assert_eq!(Rule::pmatch(&r, &r4), None);

        {
            let subbee = &r.variables()[0];
            let subbed = Term::Variable(r5.variables()[0].clone());
            let mut expected_map = HashMap::default();
            expected_map.insert(subbee, &subbed);

            assert_eq!(Rule::pmatch(&r, &r5), Some(expected_map));
        }
    }

    #[test]
    fn unify_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B").expect("parse of A(x_) = B");
        let r2 = parse_rule(&mut sig, "A(y_) = y_").expect("parse of A(y_) = y_");
        let r3 = parse_rule(&mut sig, "A(z_) = C").expect("parse of A(z_) = C");
        let r4 = parse_rule(&mut sig, "D(w_) = B").expect("parse of D(w_) = B");
        let r5 = parse_rule(&mut sig, "A(t_) = B").expect("parse of A(t_) = B");

        {
            let subbee1 = &r.variables()[0];
            let subbee2 = &r2.variables()[0];
            let b = parse_term(&mut sig, "B").expect("parse of B");
            let mut expected_map = HashMap::default();
            expected_map.insert(subbee1, &b);
            expected_map.insert(subbee2, &b);

            assert_eq!(Rule::unify(&r, &r2), Some(expected_map));
        }

        assert_eq!(Rule::unify(&r, &r3), None);
        assert_eq!(Rule::unify(&r, &r4), None);

        {
            let subbee = &r.variables()[0];
            let subbed = Term::Variable(r5.variables()[0].clone());
            let mut expected_map = HashMap::default();
            expected_map.insert(subbee, &subbed);

            assert_eq!(Rule::unify(&r, &r5), Some(expected_map));
        }
    }

    #[test]
    fn alpha_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_) = B").expect("parse of A(x_) = B");
        let r2 = parse_rule(&mut sig, "A(y_) = y_").expect("parse of A(y_) = y_");
        let r3 = parse_rule(&mut sig, "A(z_) = C").expect("parse of A(z_) = C");
        let r4 = parse_rule(&mut sig, "D(w_) = B").expect("parse of D(w_) = B");
        let r5 = parse_rule(&mut sig, "A(t_) = B").expect("parse of A(t_) = B");

        assert_eq!(Rule::alpha(&r, &r2), None);
        assert_eq!(Rule::alpha(&r, &r3), None);
        assert_eq!(Rule::alpha(&r, &r4), None);

        {
            let subbee = &r.variables()[0];
            let subbed = Term::Variable(r5.variables()[0].clone());
            let mut expected_map = HashMap::default();
            expected_map.insert(subbee, &subbed);

            assert_eq!(Rule::alpha(&r, &r5), Some(expected_map));
        }
    }

    #[test]
    fn substitute_test() {
        let mut sig = Signature::default();

        let r = parse_rule(&mut sig, "A(x_ y_) = A(x_) | B(y_)")
            .expect("parse of A(x_ y_) = A(x_) | B(y_)");
        let c = parse_term(&mut sig, "C").expect("parse of C");
        let vars = r.variables();
        let x = &vars[0];

        let mut substitution = HashMap::default();
        substitution.insert(x, &c);

        let r2 = r.substitute(&substitution);

        assert_eq!(r2.display(&sig), "A(C y_) = A(C) | B(y_)");
    }
}
