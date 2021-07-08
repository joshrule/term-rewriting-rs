use super::{
    Applicativeness, Atom, NumberLogic, NumberRepresentation, Operator, Rewrites, Rule, Signature,
    Term, Variable,
};
use itertools::Itertools;
use serde_derive::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::collections::HashMap;
use std::fmt;

pub fn logplusexp(x: f64, y: f64) -> f64 {
    let largest = x.max(y);
    if largest == f64::NEG_INFINITY {
        f64::NEG_INFINITY
    } else {
        ((x - largest).exp() + (y - largest).exp()).ln() + largest
    }
}

fn try_forms_mut(
    term: &mut Term,
    sig: &Signature,
    patterns: &Patterns,
    lo: usize,
    hi: usize,
) -> bool {
    addition_form_mut(term, sig, patterns, lo, hi)
        .or_else(|| subtraction_form_mut(term, sig, patterns, lo, hi))
        .or_else(|| greater_form_mut(term, sig, patterns, lo, hi))
        .unwrap_or(false)
}

fn addition_form_mut(
    term: &mut Term,
    sig: &Signature,
    patterns: &Patterns,
    lo: usize,
    hi: usize,
) -> Option<bool> {
    let pattern = patterns.add_napp.as_ref()?;
    let sub = Term::pmatch(&[(&pattern, &term)])?;
    let x = sub.get(Variable(0))?.to_usize(sig)?;
    let y = sub.get(Variable(1))?.to_usize(sig)?;
    match term {
        Term::Variable(_) => unreachable!(),
        Term::Application { op, args } => {
            let n = x.saturating_add(y);
            if n < lo || n > hi {
                *op = sig.has_op(0, Some("NAN"))?;
            } else {
                *op = sig.has_n(n)?;
            }
            args.clear();
        }
    }
    Some(true)
}

fn subtraction_form_mut(
    term: &mut Term,
    sig: &Signature,
    patterns: &Patterns,
    lo: usize,
    hi: usize,
) -> Option<bool> {
    let pattern = patterns.sub_napp.as_ref()?;
    let sub = Term::pmatch(&[(&pattern, &term)])?;
    let x = sub.get(Variable(0))?.to_usize(sig)?;
    let y = sub.get(Variable(1))?.to_usize(sig)?;
    match term {
        Term::Variable(_) => unreachable!(),
        Term::Application { op, args } => {
            let n = x.saturating_sub(y);
            if n < lo || n > hi {
                *op = sig.has_op(0, Some("NAN"))?;
            } else {
                *op = sig.has_n(n)?;
            }
            args.clear();
        }
    }
    Some(true)
}

fn greater_form_mut(
    term: &mut Term,
    sig: &Signature,
    patterns: &Patterns,
    lo: usize,
    hi: usize,
) -> Option<bool> {
    let pattern = patterns.gt_napp.as_ref()?;
    let sub = Term::pmatch(&[(&pattern, &term)])?;
    let x = sub.get(Variable(0))?.to_usize(sig)?;
    let y = sub.get(Variable(1))?.to_usize(sig)?;
    if !(x < lo || x > hi || y < lo || y > hi) {
        match term {
            Term::Variable(_) => unreachable!(),
            Term::Application { op, args } => {
                if x > y {
                    *op = sig.has_op(0, Some("TRUE"))?;
                } else {
                    *op = sig.has_op(0, Some("FALSE"))?;
                }
                args.clear();
            }
        }
        return Some(true);
    }
    None
}

// Based on code from Steven Piantadosi's fleet library.
fn p_prefix(
    x: &[Option<usize>],
    y: &[Option<usize>],
    p_add: f64,
    p_del: f64,
    n_chars: usize,
) -> f64 {
    let ln_p_add = p_add.ln();
    let ln_p_del = p_del.ln();
    let ln_chars = (n_chars as f64).ln();
    let ln_1m_p_add = (1.0 - p_add).ln();
    let ln_1m_p_del = (1.0 - p_del).ln();

    // We can always delete all of x and add on all of y.
    // We don't add log_1mdel_p here since we can't delete past the beginning.
    let mut lp =
        ln_p_del * (x.len() as f64) + (ln_p_add - ln_chars) * (y.len() as f64) + ln_1m_p_add;

    // We can keep as little or as much of the shared prefix as we want.
    // i_prefix represents possible options of the length of the shared prefix to keep.
    for i_prefix in 1..=x.len().min(y.len()) {
        if x[i_prefix - 1] == y[i_prefix - 1] {
            lp = logplusexp(
                lp,
                ln_p_del * ((x.len() - i_prefix) as f64)
                    + ln_1m_p_del
                    + (ln_p_add - ln_chars) * ((y.len() - i_prefix) as f64)
                    + ln_1m_p_add,
            );
        } else {
            break;
        }
    }
    lp
}

/// A first-order term rewriting system.
///
/// # Examples
///
/// ```
/// # use term_rewriting::{Signature, Rule, parse_rule, TRS, parse_trs};
/// let mut sig = Signature::default();
///
/// // Construct a TRS manually.
/// let r0 = parse_rule(&mut sig, "A(v0_) = A(B)").expect("parsed rule");
/// let r1 = parse_rule(&mut sig, "B = C | D").expect("parsed rule");
/// let r2 = parse_rule(&mut sig, "E(F) = G").expect("parsed rule");
///
/// let t = TRS::new(vec![r0, r1, r2]);
///
/// // Or, parse an entire TRS.
/// let t = parse_trs(
///     &mut sig,
///     "A(v0_) = A(B);
///      B = C | D;
///      E(F) = G;").expect("parsed TRS");
/// ```
#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct TRS {
    pub(crate) is_deterministic: bool,
    pub lo: usize,
    pub hi: usize,
    pub rules: Vec<Rule>,
}

pub struct Patterns {
    add_napp: Option<Term>,
    add_app: Option<Term>,
    sub_napp: Option<Term>,
    sub_app: Option<Term>,
    gt_napp: Option<Term>,
    gt_app: Option<Term>,
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
    /// # use term_rewriting::{Signature, Rule, parse_trs, TRS};
    /// let mut sig = Signature::default();
    /// let trs = parse_trs(&mut sig, "A = B; C(v0_) = v0_; D(v1_) = D(E);").expect("parsed TRS");
    ///
    /// assert_eq!(trs.display(&sig), "A = B;\nC(v0_) = v0_;\nD(v1_) = D(E);");
    /// ```
    pub fn new(rules: Vec<Rule>) -> TRS {
        let mut trs = TRS {
            rules: vec![],
            is_deterministic: false,
            lo: usize::MIN,
            hi: usize::MAX,
        };
        trs.pushes(rules).ok();
        trs
    }
    /// Make the `TRS` [`deterministic`] and restrict it to be so until further notice.
    ///
    /// Return `true` if the `TRS` was changed, otherwise `false`.
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
    /// assert!(t.make_deterministic());
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
    pub fn make_deterministic(&mut self) -> bool {
        if !self.is_deterministic {
            for rule in self.rules.iter_mut() {
                rule.rhs.truncate(1);
            }
            self.is_deterministic = true;
            true
        } else {
            false
        }
    }
    /// Remove any [`determinism`] restriction the `TRS` might be under.
    ///
    /// Return `true` if the `TRS` was changed, otherwise `false`.
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
    /// t.make_deterministic();
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
    /// Report whether the `TRS` is currently deterministic.
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
    /// t.make_deterministic();
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
    /// Serialize a `TRS`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    ///     "A = B;
    ///      C = D | E;
    ///      F(v0_) = G;").expect("parsed TRS");
    ///
    /// assert_eq!(t.display(&sig), "A = B;\nC = D | E;\nF(v0_) = G;");
    ///
    /// let trs = parse_trs(&mut sig,
    /// "A(v1_ v2_ v3_) = A(v1_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    /// CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    /// B C D E = B C | D E;")
    ///     .expect("parsed trs");
    ///
    /// assert_eq!(trs.display(&sig),
    /// "A(v1_ v2_ v3_) = A(v1_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    /// CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    /// .(.(.(B C) D) E) = .(B C) | .(D E);");
    /// ```
    pub fn display(&self, sig: &Signature) -> String {
        self.rules
            .iter()
            .map(|r| format!("{};", r.display(sig)))
            .join("\n")
    }
    /// A human-readable serialization of the `TRS`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, parse_trs};
    /// let mut sig = Signature::default();
    ///
    /// let trs = parse_trs(&mut sig,
    /// "A(v0_ v1_ v2_) = A(v0_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    /// CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    /// B C D E = B C | D E;")
    ///     .expect("parsed TRS");
    ///
    /// assert_eq!(trs.pretty(&sig), "A(v0_, v1_, v2_) = A(v0_, 105, 2);\n[B, C, D] = [C, D];\nB C D E = B C | D E;");
    /// ```
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
    pub fn canonicalize(&mut self, map: &mut HashMap<usize, usize>) {
        self.rules
            .iter_mut()
            .for_each(|rule| rule.canonicalize(map));
    }
    pub fn patterns(&self, sig: &Signature) -> Patterns {
        Patterns {
            add_napp: TRS::addition_pattern_nonapplicative(sig),
            add_app: TRS::addition_pattern_applicative(sig),
            sub_napp: TRS::subtraction_pattern_nonapplicative(sig),
            sub_app: TRS::subtraction_pattern_applicative(sig),
            gt_napp: TRS::greater_pattern_nonapplicative(sig),
            gt_app: TRS::greater_pattern_applicative(sig),
        }
    }
    /// Do two TRSs [`unify`]?
    ///
    /// [`unify`]: https://en.wikipedia.org/wiki/Unification_(computer_science)
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
            && trs1
                .rules
                .iter()
                .zip(trs2.rules.iter())
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
            && trs1
                .rules
                .iter()
                .zip(trs2.rules.iter())
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
        trs1.len() == trs2.len()
            && trs1
                .rules
                .iter()
                .zip(&trs2.rules[..])
                .all(|(r1, r2)| Rule::alpha(r1, r2).is_some())
    }
    /// Do two TRSs share the same shape?
    pub fn same_shape(t1: &TRS, t2: &TRS) -> bool {
        let mut omap = HashMap::new();
        let mut vmap = HashMap::new();
        TRS::same_shape_given(t1, t2, &mut omap, &mut vmap)
    }
    /// Do two rules share the same shape given some initial constraints?
    pub fn same_shape_given(
        t1: &TRS,
        t2: &TRS,
        ops: &mut HashMap<Operator, Operator>,
        vars: &mut HashMap<Variable, Variable>,
    ) -> bool {
        t1.len() == t2.len()
            && t1
                .rules
                .iter()
                .zip(&t2.rules)
                .all(|(r1, r2)| Rule::same_shape_given(r1, r2, ops, vars))
    }
    fn addition_form(
        term: &Term,
        sig: &Signature,
        patterns: &Patterns,
        lo: usize,
        hi: usize,
        rep: NumberRepresentation,
    ) -> Option<Term> {
        let pattern = match rep.app {
            Applicativeness::Applicative => patterns.add_app.as_ref(),
            Applicativeness::NonApplicative => patterns.add_napp.as_ref(),
        }?;
        let sub = Term::pmatch(&[(&pattern, &term)])?;
        let x = sub.get(Variable(0))?.to_usize(sig)?;
        let y = sub.get(Variable(1))?.to_usize(sig)?;
        Term::from_usize_with_bound(x.saturating_add(y), sig, lo, hi, rep)
    }
    fn addition_pattern_nonapplicative(sig: &Signature) -> Option<Term> {
        let pattern = Term::Application {
            op: sig.has_op(2, Some("+"))?,
            args: vec![Term::Variable(Variable(0)), Term::Variable(Variable(1))],
        };
        Some(pattern)
    }
    fn addition_pattern_applicative(sig: &Signature) -> Option<Term> {
        let plus = sig.has_op(0, Some("+"))?;
        let app = sig.has_op(2, Some("."))?;
        let pattern = Term::Application {
            op: app,
            args: vec![
                Term::Application {
                    op: app,
                    args: vec![
                        Term::Application {
                            op: plus,
                            args: vec![],
                        },
                        Term::Variable(Variable(0)),
                    ],
                },
                Term::Variable(Variable(1)),
            ],
        };
        Some(pattern)
    }
    fn subtraction_form(
        term: &Term,
        sig: &Signature,
        patterns: &Patterns,
        lo: usize,
        hi: usize,
        rep: NumberRepresentation,
    ) -> Option<Term> {
        let pattern = match rep.app {
            Applicativeness::Applicative => patterns.sub_app.as_ref(),
            Applicativeness::NonApplicative => patterns.sub_napp.as_ref(),
        }?;
        let sub = Term::pmatch(&[(&pattern, &term)])?;
        let x = sub.get(Variable(0))?.to_usize(sig)?;
        let y = sub.get(Variable(1))?.to_usize(sig)?;
        Term::from_usize_with_bound(x.saturating_sub(y), sig, lo, hi, rep)
    }
    fn subtraction_pattern_nonapplicative(sig: &Signature) -> Option<Term> {
        let pattern = Term::Application {
            op: sig.has_op(2, Some("-"))?,
            args: vec![Term::Variable(Variable(0)), Term::Variable(Variable(1))],
        };
        Some(pattern)
    }
    fn subtraction_pattern_applicative(sig: &Signature) -> Option<Term> {
        let minus = sig.has_op(0, Some("-"))?;
        let app = sig.has_op(2, Some("."))?;
        let pattern = Term::Application {
            op: app,
            args: vec![
                Term::Application {
                    op: app,
                    args: vec![
                        Term::Application {
                            op: minus,
                            args: vec![],
                        },
                        Term::Variable(Variable(0)),
                    ],
                },
                Term::Variable(Variable(1)),
            ],
        };
        Some(pattern)
    }
    fn greater_form(
        term: &Term,
        sig: &Signature,
        patterns: &Patterns,
        lo: usize,
        hi: usize,
        rep: NumberRepresentation,
    ) -> Option<Term> {
        let t = sig.has_op(0, Some("TRUE"))?;
        let f = sig.has_op(0, Some("FALSE"))?;
        let pattern = match rep.app {
            Applicativeness::Applicative => patterns.gt_app.as_ref(),
            Applicativeness::NonApplicative => patterns.gt_napp.as_ref(),
        }?;
        let sub = Term::pmatch(&[(&pattern, &term)])?;
        let x = sub.get(Variable(0))?.to_usize(sig)?;
        let y = sub.get(Variable(1))?.to_usize(sig)?;
        TRS::check_bounds(x, sig, lo, hi)
            .or_else(|| TRS::check_bounds(y, sig, lo, hi))
            .or_else(|| {
                let term = Term::Application {
                    op: if x > y { t } else { f },
                    args: vec![],
                };
                Some(term)
            })
    }
    fn greater_pattern_nonapplicative(sig: &Signature) -> Option<Term> {
        let pattern = Term::Application {
            op: sig.has_op(2, Some(">"))?,
            args: vec![Term::Variable(Variable(0)), Term::Variable(Variable(1))],
        };
        Some(pattern)
    }
    fn greater_pattern_applicative(sig: &Signature) -> Option<Term> {
        let greater = sig.has_op(0, Some(">"))?;
        let app = sig.has_op(2, Some("."))?;
        let pattern = Term::Application {
            op: app,
            args: vec![
                Term::Application {
                    op: app,
                    args: vec![
                        Term::Application {
                            op: greater,
                            args: vec![],
                        },
                        Term::Variable(Variable(0)),
                    ],
                },
                Term::Variable(Variable(1)),
            ],
        };
        Some(pattern)
    }
    fn check_bounds(n: usize, sig: &Signature, lo: usize, hi: usize) -> Option<Term> {
        if n < lo || n > hi {
            Some(Term::Application {
                op: sig.has_op(0, Some("NAN"))?,
                args: vec![],
            })
        } else {
            None
        }
    }
    // Return rewrites modifying the entire term, if possible, else None.
    fn rewrite_head(&self, term: &Term) -> Option<Vec<Term>> {
        for rule in &self.rules {
            if let Some(ref sub) = Term::pmatch(&[(&rule.lhs, &term)]) {
                let items = rule.rhs.iter().map(|x| x.substitute(sub)).collect_vec();
                if !items.is_empty() {
                    return Some(items);
                }
            }
        }
        None
    }
    // Return rewrites modifying subterms, if possible, else None.
    fn rewrite_args(
        &self,
        term: &Term,
        patterns: &Patterns,
        strategy: Strategy,
        rep: NumberRepresentation,
        sig: &Signature,
    ) -> Option<Vec<Term>> {
        if let Term::Application { op, ref args } = *term {
            for (i, arg) in args.iter().enumerate() {
                let mut it = self.rewrite(arg, patterns, strategy, rep, sig).peekable();
                if it.peek().is_some() {
                    let res = it
                        .map(|x| {
                            let mut args = args.clone();
                            args[i] = x;
                            Term::Application { op, args }
                        })
                        .collect();
                    return Some(res);
                }
            }
        }
        None
    }
    // performs all possible rewrites, else None.
    fn rewrite_all(&self, term: &Term) -> Option<Vec<Term>> {
        match term {
            Term::Variable(_) => None,
            Term::Application { ref args, .. } => {
                // rewrite head
                let mut rewrites = self.rewrite_head(term).unwrap_or_else(Vec::new);
                // rewrite subterms
                for (i, arg) in args.iter().enumerate() {
                    for rewrite in self.rewrite_all(arg).unwrap_or_else(Vec::new) {
                        rewrites.push(term.replace(&[i], rewrite).unwrap());
                    }
                }
                Some(rewrites)
            }
        }
    }
    // performs all possible rewrites, interpreting the term as a string
    fn rewrite_as_string(&self, term: &Term, sig: &Signature) -> Option<Vec<Term>> {
        let string = TRS::convert_term_to_string(term, sig)?;
        let mut rewrites = vec![];
        for rule in &self.rules {
            let pattern = TRS::convert_rule_to_strings(rule, sig)?;
            for breaks in TRS::gen_breaks(&pattern.0, string.len()).iter() {
                if let Some(matches) = TRS::match_pattern(&pattern.0, &breaks[..], &string) {
                    for rhs in &pattern.1 {
                        let new_string = TRS::substitute_pattern(&rhs[..], &matches)?;
                        let new_term = TRS::convert_to_term(&new_string, sig)?;
                        rewrites.push(new_term)
                    }
                }
            }
        }
        Some(rewrites)
    }
    pub fn convert_list_to_string_fast(term: &Term, sig: &Signature) -> Option<Vec<Option<usize>>> {
        let mut string = vec![];
        let mut t = term;
        loop {
            if t.as_guarded_application(sig, "NIL", 0).is_some() {
                return Some(string);
            } else {
                let (_, args) = t.as_guarded_application(sig, "CONS", 2)?;
                string.push(args[0].to_usize(sig));
                t = &args[1];
            }
        }
    }
    pub fn convert_list_to_string(term: &Term, sig: &mut Signature) -> Option<Vec<Atom>> {
        if term.as_guarded_application(sig, "NIL", 0).is_some() {
            Some(vec![])
        } else {
            let (_, args) = term.as_guarded_application(sig, ".", 2)?;
            let (_, inner_args) = args[0].as_guarded_application(sig, ".", 2)?;
            inner_args[0].as_guarded_application(sig, "CONS", 0)?;
            let mut string = vec![TRS::num_to_atom(&inner_args[1], sig)?];
            string.append(&mut TRS::convert_list_to_string(&args[1], sig)?);
            Some(string)
        }
    }
    fn num_to_atom(term: &Term, sig: &mut Signature) -> Option<Atom> {
        let n = term.to_usize(sig)?;
        if n < 100 {
            sig.operators()
                .iter()
                .find(|op| op.name(sig) == Some(&n.to_string()) && op.arity(sig) == 0)
                .map(|&op| Atom::from(op))
                .or_else(|| Some(Atom::from(sig.new_op(0, Some(n.to_string())))))
        } else {
            None
        }
    }
    fn convert_term_to_string(term: &Term, sig: &Signature) -> Option<Vec<Atom>> {
        match *term {
            Term::Variable(v) => Some(vec![Atom::Variable(v)]),
            Term::Application { op, ref args } => match (op.name(sig), op.arity(sig)) {
                (_, 0) => Some(vec![Atom::Operator(op)]),
                (Some(s), 2) if s == "." => {
                    let results = args
                        .iter()
                        .map(|a| TRS::convert_term_to_string(a, sig))
                        .collect_vec();
                    let mut string = vec![];
                    for result in results {
                        if let Some(mut chars) = result {
                            string.append(&mut chars);
                        } else {
                            return None;
                        }
                    }
                    Some(string)
                }
                _ => None,
            },
        }
    }
    fn convert_rule_to_strings(
        rule: &Rule,
        sig: &Signature,
    ) -> Option<(Vec<Atom>, Vec<Vec<Atom>>)> {
        let lhs = TRS::convert_term_to_string(&rule.lhs, sig)?;
        let rhs = rule
            .rhs
            .iter()
            .map(|r| TRS::convert_term_to_string(r, sig))
            .collect::<Option<Vec<_>>>()?;
        Some((lhs, rhs))
    }
    fn gen_breaks(pattern: &[Atom], n: usize) -> Vec<Vec<usize>> {
        (0..=n)
            .combinations(pattern.len() - 1)
            .map(|mut x| {
                x.insert(0, 0);
                x.push(n);
                x
            })
            .filter(|x| TRS::valid_option(&pattern, &x))
            .collect_vec()
    }
    fn valid_option(pattern: &[Atom], breaks: &[usize]) -> bool {
        for (i, atom) in pattern.iter().enumerate() {
            if let Atom::Operator(_) = atom {
                if breaks[i + 1] - breaks[i] != 1 {
                    return false;
                }
            }
        }
        true
    }
    fn match_pattern(
        pattern: &[Atom],
        breaks: &[usize],
        string: &[Atom],
    ) -> Option<HashMap<Variable, Vec<Atom>>> {
        let mut matches: HashMap<Variable, Vec<Atom>> = HashMap::new();

        for (i, &atom) in pattern.iter().enumerate() {
            match atom {
                Atom::Variable(v)
                    if matches.contains_key(&v)
                        && matches[&v] != string[breaks[i]..breaks[i + 1]].to_vec() =>
                {
                    return None
                }
                Atom::Operator(_) if string[breaks[i]..breaks[i + 1]] != [atom] => return None,
                _ => (),
            }

            if let Atom::Variable(v) = atom {
                matches
                    .entry(v)
                    .or_insert_with(|| string[breaks[i]..breaks[i + 1]].to_vec());
            }
        }
        Some(matches)
    }
    fn substitute_pattern(
        pattern: &[Atom],
        matches: &HashMap<Variable, Vec<Atom>>,
    ) -> Option<Vec<Atom>> {
        let mut string = vec![];
        for &atom in pattern.iter() {
            match atom {
                Atom::Variable(v) if matches.contains_key(&v) => {
                    string.append(&mut matches[&v].clone())
                }
                Atom::Operator(_) => string.push(atom),
                _ => return None,
            }
        }
        Some(string)
    }
    fn convert_to_term(string: &[Atom], sig: &Signature) -> Option<Term> {
        if string.is_empty() {
            return None;
        }
        let (mut term, bin_op_op) = match string[0] {
            Atom::Variable(v) => (
                Term::Variable(v),
                sig.operators()
                    .into_iter()
                    .find(|x| x.arity(sig) == 2 && x.name(sig) == Some(".")),
            ),
            Atom::Operator(op) => (
                Term::Application { op, args: vec![] },
                sig.operators()
                    .into_iter()
                    .find(|x| x.arity(sig) == 2 && x.name(sig) == Some(".")),
            ),
        };
        if let Some(bin_op) = bin_op_op {
            for character in string[1..].iter() {
                let subterm = match *character {
                    Atom::Variable(v) => Term::Variable(v),
                    Atom::Operator(op) => Term::Application { op, args: vec![] },
                };
                term = Term::Application {
                    op: bin_op,
                    args: vec![term, subterm],
                }
            }
            Some(term)
        } else {
            None
        }
    }
    /// madness: `p_string` treats two `Term`s as strings and computes a
    /// probabilistic edit distance between them.
    pub fn p_string(
        x: &Term,
        y: &Term,
        dist: PStringDist,
        t_max: usize,
        d_max: usize,
        sig: &Signature,
    ) -> Option<f64> {
        let sig = sig.clone();
        let x_string = TRS::convert_term_to_string(x, &sig)?;
        let y_string = TRS::convert_term_to_string(y, &sig)?;
        let p = PString::new(x_string, y_string, dist, &sig).compute(t_max, d_max);
        Some(p.ln())
    }
    /// madness: `p_list` treats two list `Term`s as strings and computes a
    /// probabilistic edit distance between them.
    pub fn p_list(
        x: &Term,
        y: &Term,
        dist: PStringDist,
        t_max: usize,
        d_max: usize,
        sig: &Signature,
    ) -> f64 {
        let mut sig = sig.clone();
        let x_string = TRS::convert_list_to_string(x, &mut sig);
        let y_string = TRS::convert_list_to_string(y, &mut sig);
        match (x_string, y_string) {
            (Some(x_string), Some(y_string)) => {
                let p = PString::new(x_string, y_string, dist, &sig).compute(t_max, d_max);
                p.ln()
            }
            _ => std::f64::NEG_INFINITY,
        }
    }
    /// madness: `p_list` treats two list `Term`s as strings and computes a
    /// probabilistic edit distance between them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, logplusexp};
    /// let mut sig = Signature::default();
    ///
    /// let x = parse_term(&mut sig, "CONS(1 CONS(2 CONS(3 CONS(4 CONS(5 NIL)))))")
    ///     .expect("parsed [1, 2, 3, 4, 5]");
    /// let p_add: f64 = 0.1;
    /// let p_del: f64 = 0.01;
    /// let n_chars = 10;
    ///
    /// // We might have no shared prefix.
    /// let y = parse_term(&mut sig, "CONS(5 CONS(4 CONS(3 CONS(2 CONS(1 NIL)))))")
    ///     .expect("parsed [5, 4, 3, 2, 1]");
    /// let expected = (p_add.ln()-(n_chars as f64).ln())*5.0+p_del.ln()*5.0+(1.0-p_add).ln();
    /// let actual = TRS::p_list_prefix(&x, &y, p_add, p_del, n_chars, &sig);
    /// assert_eq!(expected, actual);
    ///
    /// // We might have some shared prefix.
    /// let y = parse_term(&mut sig, "CONS(1 CONS(2 CONS(6 CONS(7 CONS(8 NIL)))))")
    ///     .expect("parsed [1, 2, 6, 7, 8]");
    /// let expected = logplusexp(
    ///     logplusexp(p_del.ln()*5.0+(p_add.ln()-(n_chars as f64).ln())*5.0+(1.0-p_add).ln(),
    ///                p_del.ln()*4.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*4.0+(1.0-p_add).ln()),
    ///     p_del.ln()*3.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*3.0+(1.0-p_add).ln());
    /// let actual = TRS::p_list_prefix(&x, &y, p_add, p_del, n_chars, &sig);
    /// assert_eq!(expected, actual);
    ///
    /// // Maybe y is shorter than x.
    /// let y = parse_term(&mut sig, "CONS(1 CONS(2 NIL))")
    ///     .expect("parsed [1, 2]");
    /// let expected = logplusexp(
    ///     logplusexp(p_del.ln()*5.0+(p_add.ln()-(n_chars as f64).ln())*2.0+(1.0-p_add).ln(),
    ///                p_del.ln()*4.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*1.0+(1.0-p_add).ln()),
    ///     p_del.ln()*3.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*0.0+(1.0-p_add).ln());
    /// let actual = TRS::p_list_prefix(&x, &y, p_add, p_del, n_chars, &sig);
    /// assert_eq!(expected, actual);
    ///
    /// // Maybe y is longer than x.
    /// let y = parse_term(
    ///    &mut sig,
    ///    "CONS(1 CONS(2 CONS(3 CONS(4 CONS(5 CONS(6 CONS(7 NIL)))))))")
    ///     .expect("parsed [1, 2, 3, 4, 5, 6, 7]");
    /// let expected = logplusexp(
    ///     logplusexp(
    ///         logplusexp(
    ///             logplusexp(
    ///                 logplusexp(
    ///                     p_del.ln()*5.0+(p_add.ln()-(n_chars as f64).ln())*7.0+(1.0-p_add).ln(),
    ///                     p_del.ln()*4.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*6.0+(1.0-p_add).ln()),
    ///                 p_del.ln()*3.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*5.0+(1.0-p_add).ln()),
    ///             p_del.ln()*2.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*4.0+(1.0-p_add).ln()),
    ///         p_del.ln()*1.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*3.0+(1.0-p_add).ln()),
    ///     p_del.ln()*0.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*2.0+(1.0-p_add).ln());
    /// let actual = TRS::p_list_prefix(&x, &y, p_add, p_del, n_chars, &sig);
    /// assert_eq!(expected, actual);
    ///
    /// // Maybe y == x.
    /// let y = parse_term(
    ///    &mut sig,
    ///    "CONS(1 CONS(2 CONS(3 CONS(4 CONS(5 NIL)))))")
    ///     .expect("parsed [1, 2, 3, 4, 5]");
    /// let expected = logplusexp(
    ///     logplusexp(
    ///         logplusexp(
    ///             logplusexp(
    ///                 logplusexp(
    ///                     p_del.ln()*5.0+(p_add.ln()-(n_chars as f64).ln())*5.0+(1.0-p_add).ln(),
    ///                     p_del.ln()*4.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*4.0+(1.0-p_add).ln()),
    ///                 p_del.ln()*3.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*3.0+(1.0-p_add).ln()),
    ///             p_del.ln()*2.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*2.0+(1.0-p_add).ln()),
    ///         p_del.ln()*1.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*1.0+(1.0-p_add).ln()),
    ///     p_del.ln()*0.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*0.0+(1.0-p_add).ln());
    /// let actual = TRS::p_list_prefix(&x, &y, p_add, p_del, n_chars, &sig);
    /// assert_eq!(expected, actual);
    ///
    /// // And, double-check on those NANs.
    /// let y = parse_term(
    ///    &mut sig,
    ///    "CONS(1 CONS(2 CONS(NAN CONS(NAN CONS(NAN NIL)))))")
    ///     .expect("parsed [1, 2, NAN, NAN, NAN]");
    /// let expected = logplusexp(
    ///     logplusexp(p_del.ln()*5.0+(p_add.ln()-(n_chars as f64).ln())*5.0+(1.0-p_add).ln(),
    ///                p_del.ln()*4.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*4.0+(1.0-p_add).ln()),
    ///     p_del.ln()*3.0+(1.0-p_del).ln()+(p_add.ln()-(n_chars as f64).ln())*3.0+(1.0-p_add).ln());
    /// let actual = TRS::p_list_prefix(&x, &y, p_add, p_del, n_chars, &sig);
    /// assert_eq!(expected, actual);
    /// ```
    pub fn p_list_prefix(
        x: &Term,
        y: &Term,
        p_add: f64,
        p_del: f64,
        n_chars: usize,
        sig: &Signature,
    ) -> f64 {
        let x_string = TRS::convert_list_to_string_fast(x, sig);
        let y_string = TRS::convert_list_to_string_fast(y, sig);
        match (x_string, y_string) {
            (Some(x_string), Some(y_string)) => {
                p_prefix(&x_string, &y_string, p_add, p_del, n_chars)
            }
            _ => std::f64::NEG_INFINITY,
        }
    }
    /// Perform a single rewrite step.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{NumberRepresentation, Signature, Strategy, TRS, parse_trs, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let term = parse_term(&mut sig, "J(F(C) K(C A))").expect("parse of J(F(C) K(C A))");
    /// let patterns = t.patterns(&sig);
    ///
    /// let rewritten_terms: Vec<_> = t.rewrite(&term, &patterns, Strategy::Normal, NumberRepresentation::default(), &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "J(G K(C A))");
    ///
    /// let rewritten_terms: Vec<_> = t.rewrite(&term, &patterns, Strategy::Eager, NumberRepresentation::default(), &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 2);
    /// assert_eq!(rewritten_terms[0].display(&sig), "J(F(D) K(C A))");
    /// assert_eq!(rewritten_terms[1].display(&sig), "J(F(E) K(C A))");
    ///
    /// let rewritten_terms: Vec<_> = t.rewrite(&term, &patterns, Strategy::All, NumberRepresentation::default(), &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 6);
    /// assert_eq!(rewritten_terms[0].display(&sig), "J(G K(C A))");
    /// assert_eq!(rewritten_terms[1].display(&sig), "J(F(D) K(C A))");
    /// assert_eq!(rewritten_terms[2].display(&sig), "J(F(E) K(C A))");
    /// assert_eq!(rewritten_terms[3].display(&sig), "J(F(C) K(D A))");
    /// assert_eq!(rewritten_terms[4].display(&sig), "J(F(C) K(E A))");
    /// assert_eq!(rewritten_terms[5].display(&sig), "J(F(C) K(C B))");
    /// ```
    ///
    /// Also, addition (`+`), subtraction (`-`), and greater-than (`>`) have
    /// built-in behavior for normal-order rewriting if they are defined.
    ///
    /// ```
    /// # use term_rewriting::{NumberRepresentation, Applicativeness, NumberLogic, Signature, Strategy, TRS, parse_trs, Term, parse_term};
    /// let mut sig = Signature::default();
    /// sig.new_op(2, Some(".".to_string()));
    /// sig.new_op(0, Some("TRUE".to_string()));
    /// sig.new_op(0, Some("FALSE".to_string()));
    /// sig.new_op(0, Some("+".to_string()));
    /// sig.new_op(0, Some("-".to_string()));
    /// sig.new_op(0, Some(">".to_string()));
    /// sig.new_op(0, Some("F".to_string()));
    /// (0..99).for_each(|x| {sig.new_op(0, Some(x.to_string()));});
    /// let mut trs = parse_trs(&mut sig, "").expect("trs");
    /// trs.lo = 0; trs.hi = 99;
    /// let rep = NumberRepresentation {
    ///     logic: NumberLogic::Symbolic,
    ///     app: Applicativeness::Applicative,
    /// };
    /// let patterns = trs.patterns(&sig);
    ///
    /// let t1 = parse_term(&mut sig, "(+ 7 3)").expect("t1");
    /// let rewritten_terms: Vec<_> = trs.rewrite(&t1, &patterns, Strategy::Normal, rep, &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "10");
    ///
    /// let t2 = parse_term(&mut sig, "(- 7 3)").expect("t2");
    /// let rewritten_terms: Vec<_> = trs.rewrite(&t2, &patterns, Strategy::Normal, rep, &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "4");
    ///
    /// let t3 = parse_term(&mut sig, "(> 7 3)").expect("t3");
    /// let rewritten_terms: Vec<_> = trs.rewrite(&t3, &patterns, Strategy::Normal, rep, &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "TRUE");
    ///
    /// let t4 = parse_term(&mut sig, "(F (+ 7 3))").expect("t3");
    /// let rewritten_terms: Vec<_> = trs.rewrite(&t4, &patterns, Strategy::Normal, rep, &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), ".(F 10)");
    /// ```
    ///
    /// ```
    /// # use term_rewriting::{NumberRepresentation, Signature, Strategy, TRS, parse_trs, Term, parse_term};
    /// let mut sig = Signature::default();
    /// sig.new_op(0, Some("TRUE".to_string()));
    /// sig.new_op(0, Some("FALSE".to_string()));
    /// sig.new_op(1, Some("F".to_string()));
    /// sig.new_op(2, Some("+".to_string()));
    /// sig.new_op(2, Some("-".to_string()));
    /// sig.new_op(2, Some(">".to_string()));
    /// (0..99).for_each(|x| {sig.new_op(0, Some(x.to_string()));});
    /// let mut trs = parse_trs(&mut sig, "").expect("trs");
    /// trs.lo = 0; trs.hi = 99;
    /// let patterns = trs.patterns(&sig);
    ///
    /// let t1 = parse_term(&mut sig, "+(7 3)").expect("t1");
    /// let rewritten_terms: Vec<_> = trs.rewrite(&t1, &patterns, Strategy::Normal, NumberRepresentation::default(), &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "10");
    ///
    /// let t2 = parse_term(&mut sig, "-(7 3)").expect("t2");
    /// let rewritten_terms: Vec<_> = trs.rewrite(&t2, &patterns, Strategy::Normal, NumberRepresentation::default(), &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "4");
    ///
    /// let t3 = parse_term(&mut sig, ">(7 3)").expect("t3");
    /// let rewritten_terms: Vec<_> = trs.rewrite(&t3, &patterns, Strategy::Normal, NumberRepresentation::default(), &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "TRUE");
    ///
    /// let t4 = parse_term(&mut sig, "F(+(7 3))").expect("t3");
    /// let rewritten_terms: Vec<_> = trs.rewrite(&t4, &patterns, Strategy::Normal, NumberRepresentation::default(), &sig).collect();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "F(10)");
    /// ```
    pub fn rewrite<'a>(
        &'a self,
        term: &'a Term,
        patterns: &'a Patterns,
        strategy: Strategy,
        rep: NumberRepresentation,
        sig: &'a Signature,
    ) -> TRSRewrites<'a> {
        TRSRewrites::new(self, term, patterns, strategy, rep, sig)
    }
    /// This is a highly specialized rewriter that mutably rewrites terms using
    /// normal-order evaluation. It requires that the TRS is deterministic.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{NumberRepresentation, Signature, Strategy, TRS, parse_trs, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D;
    /// F(x_) = G;").expect("trs");
    /// t.make_deterministic();
    /// let patterns = t.patterns(&sig);
    ///
    /// let mut term = parse_term(&mut sig, "J(F(C) K(C A))").expect("J(F(C) K(C A))");
    ///
    /// assert_eq!(term.display(&sig), "J(F(C) K(C A))");
    /// assert!(t.rewrite_mut(&mut term, &patterns, NumberRepresentation::default(), &sig));
    /// assert_eq!(term.display(&sig), "J(G K(C A))");
    /// ```
    ///
    /// Also, addition (`+`), subtraction (`-`), and greater-than (`>`) have
    /// built-in behavior if they are defined.
    ///
    /// ```
    /// # use term_rewriting::{NumberRepresentation, Signature, Strategy, TRS, parse_trs, Term, parse_term};
    /// let mut sig = Signature::default();
    /// sig.new_op(0, Some("TRUE".to_string()));
    /// sig.new_op(0, Some("FALSE".to_string()));
    /// sig.new_op(0, Some("NAN".to_string()));
    /// sig.new_op(2, Some("+".to_string()));
    /// sig.new_op(2, Some("-".to_string()));
    /// sig.new_op(2, Some(">".to_string()));
    /// sig.new_op(1, Some("F".to_string()));
    /// (0..99).for_each(|x| {sig.new_op(0, Some(x.to_string()));});
    /// let mut trs = parse_trs(&mut sig, "").expect("trs");
    /// let rep = NumberRepresentation::default();
    /// trs.lo = 0; trs.hi = 99;
    /// trs.make_deterministic();
    /// let patterns = trs.patterns(&sig);
    ///
    /// let mut term = parse_term(&mut sig, "+(7 3)").expect("t1");
    /// trs.rewrite_mut(&mut term, &patterns, rep, &sig);
    /// assert_eq!(term.display(&sig), "10");
    ///
    /// term = parse_term(&mut sig, "-(7 3)").expect("t2");
    /// trs.rewrite_mut(&mut term, &patterns, rep, &sig);
    /// assert_eq!(term.display(&sig), "4");
    ///
    /// term = parse_term(&mut sig, ">(7 3)").expect("t3");
    /// trs.rewrite_mut(&mut term, &patterns, rep, &sig);
    /// assert_eq!(term.display(&sig), "TRUE");
    ///
    /// term = parse_term(&mut sig, "F(+(7 3))").expect("t3");
    /// trs.rewrite_mut(&mut term, &patterns, rep, &sig);
    /// assert_eq!(term.display(&sig), "F(10)");
    /// ```
    pub fn rewrite_mut(
        &self,
        term: &mut Term,
        patterns: &Patterns,
        rep: NumberRepresentation,
        sig: &Signature,
    ) -> bool {
        let default_rep = NumberRepresentation {
            logic: NumberLogic::Symbolic,
            app: Applicativeness::NonApplicative,
        };
        if !self.is_deterministic() || rep != default_rep {
            return false;
        }
        let mut place: SmallVec<[usize; 32]> = SmallVec::with_capacity(32);
        let mut stack: SmallVec<[(usize, bool); 128]> = SmallVec::with_capacity(128);
        loop {
            match term.at_mut(&place) {
                None => panic!("FAIL: {} {:?}", term.pretty(sig), place),
                Some(subterm) => {
                    if std::iter::once(try_forms_mut(subterm, sig, patterns, self.lo, self.hi))
                        .chain(self.rules.iter().map(|rule| rule.rewrite_mut(subterm)))
                        .any(|x| x)
                    {
                        return true;
                    }
                    match subterm {
                        Term::Application { args, .. } if !args.is_empty() => {
                            for arg_idx in (1..args.len()).rev() {
                                stack.push((arg_idx, false))
                            }
                            stack.push((0, true));
                            place.push(0);
                        }
                        _ => {
                            while let Some((_, true)) = stack.last() {
                                stack.pop();
                                place.pop();
                            }
                            if let Some((idx, seen)) = stack.last_mut() {
                                *seen = true;
                                place.push(*idx);
                            } else {
                                return false;
                            }
                        }
                    }
                }
            }
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
        let mut lhs = lhs.clone();
        lhs.canonicalize(&mut HashMap::new());
        let n_vars = lhs.variables().len();
        for (idx, rule) in self.rules.iter().enumerate() {
            let mut new_lhs = rule.lhs.clone();
            new_lhs.offset(n_vars);
            if Term::alpha(&[(&lhs, &new_lhs)]).is_some() {
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
    /// "A(v0_ v1_) = B(v0_ v0_);
    /// D(v2_ v3_) = D(E F);").expect("parsed TRS");
    ///
    /// let r = parse_rule(&mut sig, "A(v4_ v5_) = B(v4_ v4_)").expect("parsed rule");
    ///
    /// assert_eq!(t.get_clause(&r).unwrap().1.display(&sig), "A(v0_ v1_) = B(v0_ v0_)");
    ///
    /// let r = parse_rule(&mut sig, "D(E E) = D(E F)").expect("parsed rule");
    ///
    /// assert!(t.get_clause(&r).is_none());
    /// ```
    pub fn get_clause(&self, rule: &Rule) -> Option<(usize, Rule)> {
        let mut inner_rule = rule.clone();
        for (i, r) in self.rules.iter().enumerate() {
            if let Some(n) = r.lhs.all_variables().map(|Variable(x)| x).max() {
                inner_rule.offset(n);
            }
            if let Some(sub) = r.contains(&inner_rule) {
                return Some((i, inner_rule.substitute(&sub)));
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
    /// F(v0_) = G;").expect("parsed TRS");
    ///
    /// let a = parse_term(&mut sig, "A").expect("parse of A");
    /// let c = parse_term(&mut sig, "C").expect("parse of C");
    ///
    /// assert_eq!(t.remove(&a).expect("removed A = B").display(&sig), "A = B");
    /// assert_eq!(t.remove(&c).expect("removed C = D").display(&sig), "C = D | E");
    /// assert_eq!(t.display(&sig), "F(v0_) = G;");
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
    /// F(v0_) = G;").expect("parsed TRS");
    ///
    /// assert_eq!(t.remove_idx(0).expect("removing A = B").display(&sig), "A = B");
    /// assert_eq!(t.remove_idx(0).expect("removing C = D").display(&sig), "C = D | E");
    /// assert_eq!(t.display(&sig), "F(v0_) = G;");
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
    /// F(v0_) = G;").expect("parsed TRS");
    ///
    /// let r = parse_rule(&mut sig, "C = D").expect("parsed rule");
    ///
    /// assert_eq!(t.remove_clauses(&r).expect("removing C = D").display(&sig), "C = D");
    /// assert_eq!(t.display(&sig), "A = B;\nC = E;\nF(v0_) = G;");
    /// ```
    pub fn remove_clauses(&mut self, rule: &Rule) -> Result<Rule, TRSError> {
        self.rules
            .iter_mut()
            .find_map(|r| r.discard(&rule))
            .ok_or(TRSError::NotInTRS)
            .map(|discarded| {
                self.rules.retain(|rule| !rule.is_empty());
                discarded
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
    /// F(v0_) = G;").expect("parsed TRS");
    ///
    /// let r = parse_rule(&mut sig, "D = G").expect("parsed rule");
    ///
    /// t.insert(1, r).expect("inserting");
    ///
    /// assert_eq!(t.display(&sig), "A = B;\nD = G;\nC = D | E;\nF(v0_) = G;");
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
    /// F(v0_) = G;").expect("parsed TRS");
    ///
    /// let r = parse_rule(&mut sig, "D = G").expect("parsed rule");
    ///
    /// t.insert_idx(1, r).expect("inserting");
    ///
    /// assert_eq!(t.display(&sig), "A = B;\nD = G;\nC = D | E;\nF(v0_) = G;");
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
    /// Inserts a series of [`Rule`]s into the `TRS` at the index provided if possible.
    ///
    /// [`Rule`]: struct.Rule.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, TRS, parse_trs, Term, parse_term, Rule, parse_rule};
    /// let mut sig = Signature::default();
    ///
    /// let mut t = parse_trs(&mut sig, "A = B; C = D | E; F(v0_) = H;").expect("parsed TRS");
    ///
    /// let r0 = parse_rule(&mut sig, "G(v1_) = v1_").expect("parsed r0");
    /// let r1 = parse_rule(&mut sig, "B = C").expect("parsed r1");
    /// let r2 = parse_rule(&mut sig, "E = F | B").expect("parsed r2");
    ///
    /// t.inserts_idx(2, vec![r0, r1, r2]).expect("inserting");
    ///
    /// assert_eq!(t.display(&sig), "A = B;\nC = D | E;\nG(v1_) = v1_;\nB = C;\nE = F | B;\nF(v0_) = H;");
    /// ```
    pub fn inserts_idx(&mut self, idx: usize, rules: Vec<Rule>) -> Result<&mut TRS, TRSError> {
        for rule in rules.into_iter().rev() {
            self.insert_idx(idx, rule)?;
        }
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
    /// F(v0_) = G;").expect("parsed TRS");
    ///
    /// let r = parse_rule(&mut sig, "A = H").expect("parsed rule");
    ///
    /// let t = t.insert_clauses(&r).expect("inserting");
    ///
    /// assert_eq!(t.display(&sig), "A = B | H;\nC = D | E;\nF(v0_) = G;");
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
    /// F(v0_) = G;").expect("parsed TRS");
    ///
    /// let r = parse_rule(&mut sig, "G(v1_) = v1_").expect("parsed rule");
    ///
    /// t.push(r).expect("inserting");
    ///
    /// assert_eq!(t.display(&sig), "G(v1_) = v1_;\nA = B;\nC = D | E;\nF(v0_) = G;");
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
    /// F(v0_) = H;").expect("parsed TRS");
    ///
    /// let r0 = parse_rule(&mut sig, "G(v1_) = v1_").expect("parsed r0");
    /// let r1 = parse_rule(&mut sig, "B = C").expect("parsed r1");
    /// let r2 = parse_rule(&mut sig, "E = F | B").expect("parsed r2");
    ///
    /// t.pushes(vec![r0, r1, r2]).expect("inserting");
    ///
    /// assert_eq!(t.display(&sig),
    /// "G(v1_) = v1_;
    /// B = C;
    /// E = F | B;
    /// A = B;
    /// C = D | E;
    /// F(v0_) = H;");
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
    /// let mut t = parse_trs(&mut sig, "A = B; C = D | E; F(v0_) = G; H = I;").expect("parsed TRS");
    ///
    /// t.move_rule(0, 2).expect("moving rule from index 0 to index 2");
    ///
    /// assert_eq!(t.display(&sig), "C = D | E;\nF(v0_) = G;\nA = B;\nH = I;");
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
    /// F(v0_) = G;").expect("parsed TRS");
    ///
    /// let r = parse_rule(&mut sig, "C = D").expect("parse of C = D");
    /// let r_new = parse_rule(&mut sig, "C = A").expect("parse of C = A");
    /// t.replace(0, &r, r_new).expect("replaceing C = D with C = A");
    ///
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// C = E | A;
    /// F(v0_) = G;");
    /// ```
    pub fn replace(&mut self, idx: usize, rule1: &Rule, rule2: Rule) -> Result<&mut TRS, TRSError> {
        self.remove_clauses(rule1)?;
        self.insert(idx, rule2)
    }
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum Strategy {
    /// Perform only the leftmost-innermost rewrite
    Normal,
    /// Perform only the leftmost-innermost rewrite
    Eager,
    /// Perform all possible rewrites
    All,
    /// Rewrite term as a string (i.e. leaves only)
    String,
}
impl fmt::Display for Strategy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Strategy::Normal => write!(f, "Normal"),
            Strategy::Eager => write!(f, "Eager"),
            Strategy::All => write!(f, "All"),
            Strategy::String => write!(f, "String"),
        }
    }
}

#[derive(Debug, Clone)]
/// The error type for [`TRS`] manipulations.
///
/// [`TRS`]: struct.TRS.html
pub enum TRSError {
    /// Returned when requesting to edit a rule that is not in the TRS.
    ///
    /// See [`TRS::get`] for more information.
    ///
    /// [`TRS::get`]: struct.TRS.html#method.get
    NotInTRS,
    /// Returned when attempting to insert a rule into a TRS that already exists.
    ///
    /// See [`TRS::insert`] for more information.
    ///
    /// [`TRS::insert`]: struct.TRS.html#method.insert
    AlreadyInTRS,
    /// Returned when attempting to insert a rule with multiple RHSs into a deterministic TRS.
    ///
    /// See [`TRS::insert`] and [`TRS::make_deterministic`] for more information.
    ///
    /// [`TRS::insert`]: struct.TRS.html#method.insert
    /// [`TRS::make_deterministic`]: struct.TRS.html#method.make_deterministic
    NondeterministicRule,
    /// Returned when requesting the rule at an index that is out of the range of indicies for the TRS.
    ///
    /// See [`TRS::get_idx`] for more information.
    ///
    /// [`TRS::get_idx`]: struct.TRS.html#method.get_idx
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

#[derive(Debug, Copy, Clone, PartialEq, Serialize, Deserialize)]
/// Note: p_deletion + p_correct_sub + sum(all values of p_incorrect_sub) must equal 1.0.
pub struct PStringDist {
    /// The probability of a single insertion, used to compute the probability of `t` insertions as `(1-beta)(beta^t)`.
    pub beta: f64,
    /// The probability of any given symbol being the particular symbol inserted.
    pub p_insertion: f64,
    /// The probability of deleting a character.
    pub p_deletion: f64,
    /// The probability of substituting correctly.
    pub p_correct_sub: f64,
    /// A distribution over incorrect substitutions.
    pub p_incorrect_sub: PStringIncorrect,
}
#[derive(Debug, Copy, Clone, PartialEq, Serialize, Deserialize)]
pub enum PStringIncorrect {
    Constant(f64),
    Bounded {
        low: usize,
        high: usize,
        weight: f64,
    },
}

struct PString<'a> {
    cache: HashMap<(usize, usize, usize), f64>,
    m: usize,
    n: usize,
    x: Vec<Atom>,
    y: Vec<Atom>,
    dist: PStringDist,
    sig: &'a Signature,
}
impl<'a> PString<'a> {
    fn new(x: Vec<Atom>, y: Vec<Atom>, dist: PStringDist, sig: &'a Signature) -> PString<'a> {
        let cache = HashMap::new();
        let m = x.len();
        let n = y.len();
        PString {
            cache,
            m,
            n,
            x,
            y,
            dist,
            sig,
        }
    }
    pub fn compute(&mut self, t_max: usize, d_max: usize) -> f64 {
        // How few insertions can you do? n-m
        let t_start = self.n.saturating_sub(self.m);
        // How many insertions can you do? d_max-(m-n)
        let t_end = t_max.min((d_max + self.n).saturating_sub(self.m));
        (t_start..=t_end)
            .filter_map(|t| {
                // Insertions can't be deleted, so t must be smaller than n
                if t > self.n || self.n > self.m + t {
                    None
                } else {
                    let d = self.m + t - self.n;
                    let s = self.n - t;
                    Some(self.rho_t(t) * self.query((t, d, s)) * self.normalizer(t))
                }
            })
            .sum()
    }
    /// The probability of t insertions = (1-beta)*(beta^t)
    fn rho_t(&self, t: usize) -> f64 {
        (1.0 - self.dist.beta) * self.dist.beta.powi(t as i32)
    }
    fn normalizer(&self, t: usize) -> f64 {
        // m!t!/(m+t)! = min(m,t)!/(\prod_{i = max(m,t)..m+t} i)
        if self.m == 0 && t == 0 {
            1.0
        } else {
            let min_mt = t.min(self.m);
            let max_mt = t.max(self.m);
            let numerator: f64 = (1..=min_mt).product::<usize>() as f64;
            let denominator: f64 = (max_mt + 1..=(self.m + t)).product::<usize>() as f64;
            numerator / denominator
        }
    }
    fn p_sub(&self, x: &Atom, y: &Atom) -> f64 {
        if x == y {
            self.dist.p_correct_sub
        } else {
            match self.dist.p_incorrect_sub {
                PStringIncorrect::Constant(p) => p,
                PStringIncorrect::Bounded { low, high, weight } => {
                    let n_x = x.display(self.sig).parse::<usize>(); // 75
                    let n_y = y.display(self.sig).parse::<usize>(); // 81
                    match (n_x, n_y) {
                        (Ok(n_x), Ok(n_y)) => {
                            let range = high + 1 - low; // 100
                            let d_xy = if n_x > n_y { n_x - n_y } else { n_y - n_x }; // 6
                            let peak = if n_x == low || n_x == high {
                                range
                            } else {
                                (high + 1 - n_x).max(n_x + 1 - low)
                            }; // 76
                            let mass_y = peak - d_xy; // 70
                            let z = (1..peak).sum::<usize>()
                                + (1..peak).rev().take(high - n_x).sum::<usize>();
                            weight * (mass_y as f64) / (z as f64)
                        }
                        _ => 0.0,
                    }
                }
            }
        }
    }
    fn query(&mut self, key: (usize, usize, usize)) -> f64 {
        if self.cache.contains_key(&key) {
            return self.cache[&key];
        }
        let new_val = match key {
            (0, 0, 0) => 1.0,
            (t, 0, 0) if t > 0 => self.query((t - 1, 0, 0)) * self.dist.p_insertion,
            (0, d, 0) if d > 0 => self.query((0, d - 1, 0)) * self.dist.p_deletion,
            (0, 0, s) if s > 0 => {
                self.query((0, 0, s - 1)) * self.p_sub(&self.x[s - 1], &self.y[s - 1])
            }
            (t, d, 0) if t > 0 && d > 0 => {
                self.query((t - 1, d, 0)) * self.dist.p_insertion
                    + self.query((t, d - 1, 0)) * self.dist.p_deletion
            }
            (t, 0, s) if t > 0 && s > 0 => {
                self.query((t - 1, 0, s)) * self.dist.p_insertion
                    + self.query((t, 0, s - 1)) * self.p_sub(&self.x[s - 1], &self.y[s + t - 1])
            }
            (0, d, s) if d > 0 && s > 0 => {
                self.query((0, d - 1, s)) * self.dist.p_deletion
                    + self.query((0, d, s - 1)) * self.p_sub(&self.x[s + d - 1], &self.y[s - 1])
            }
            (t, d, s) if t > 0 && d > 0 && s > 0 => {
                self.query((t - 1, d, s)) * self.dist.p_insertion
                    + self.query((t, d - 1, s)) * self.dist.p_deletion
                    + self.query((t, d, s - 1)) * self.p_sub(&self.x[s + d - 1], &self.y[s + t - 1])
            }
            _ => 0.0,
        };
        self.cache.insert(key, new_val);
        new_val
    }
}

pub struct Normal<'a> {
    rewrites: NormalKind<'a>,
}

enum NormalKind<'a> {
    None,
    HeadForm(Option<Term>),
    Head(Box<std::iter::Peekable<Rewrites<'a>>>),
    SubtermForm(Vec<(Operator, usize, &'a [Term], bool)>, Option<Term>),
    Subterm(
        Vec<(Operator, usize, &'a [Term], bool)>,
        Box<std::iter::Peekable<Rewrites<'a>>>,
    ),
}

impl<'a> Normal<'a> {
    fn try_forms(
        term: &'a Term,
        sig: &'a Signature,
        patterns: &'a Patterns,
        lo: usize,
        hi: usize,
        rep: NumberRepresentation,
    ) -> Option<Term> {
        TRS::addition_form(term, sig, patterns, lo, hi, rep)
            .or_else(|| TRS::subtraction_form(term, sig, patterns, lo, hi, rep))
            .or_else(|| TRS::greater_form(term, sig, patterns, lo, hi, rep))
    }
    pub(crate) fn new(
        trs: &'a TRS,
        sig: &'a Signature,
        patterns: &'a Patterns,
        term: &'a Term,
        rep: NumberRepresentation,
    ) -> Normal<'a> {
        let mut it: std::iter::Peekable<Rewrites>;
        if let Term::Application { op, args } = term {
            // Try the head.
            let head_forms = Normal::try_forms(term, sig, patterns, trs.lo, trs.hi, rep);
            if head_forms.is_some() {
                return Normal {
                    rewrites: NormalKind::HeadForm(head_forms),
                };
            }
            if !trs.rules.is_empty() {
                it = trs.rules[0].rewrite(term).peekable();
                if it.peek().is_some() {
                    return Normal {
                        rewrites: NormalKind::Head(Box::new(it)),
                    };
                }
                for rule in trs.rules.iter().skip(1) {
                    it = rule.rewrite(term).peekable();
                    if it.peek().is_some() {
                        return Normal {
                            rewrites: NormalKind::Head(Box::new(it)),
                        };
                    }
                }
            }
            // Try each arg.
            let mut stack: Vec<(Operator, usize, &[Term], bool)> = Vec::with_capacity(32);
            if !args.is_empty() {
                stack.push((*op, 0, args.as_slice(), false));
            }
            while let Some(x) = stack.last_mut() {
                match (&x.2[x.1], x.3) {
                    (_, true) if x.1 + 1 < x.2.len() => {
                        x.1 += 1;
                        x.3 = false;
                    }
                    (Term::Application { op, args }, false) => {
                        let forms =
                            Normal::try_forms(&x.2[x.1], sig, patterns, trs.lo, trs.hi, rep);
                        if forms.is_some() {
                            return Normal {
                                rewrites: NormalKind::SubtermForm(stack, forms),
                            };
                        }
                        for rule in &trs.rules {
                            it = rule.rewrite(&x.2[x.1]).peekable();
                            if it.peek().is_some() {
                                return Normal {
                                    rewrites: NormalKind::Subterm(stack, Box::new(it)),
                                };
                            }
                        }
                        x.3 = true;
                        if !args.is_empty() {
                            stack.push((*op, 0, args, false));
                        }
                    }
                    _ => {
                        stack.pop();
                    }
                }
            }
        }
        Normal {
            rewrites: NormalKind::None,
        }
    }
}

impl<'a> Iterator for Normal<'a> {
    type Item = Term;
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.rewrites {
            NormalKind::None => None,
            NormalKind::HeadForm(forms) => forms.take(),
            NormalKind::Head(it) => it.next(),
            NormalKind::SubtermForm(stack, forms) => forms.take().map(|subterm| {
                stack
                    .iter()
                    .rev()
                    .fold(subterm, |subterm, &(op, arg, args, _)| {
                        let mut new_args = Vec::with_capacity(args.len());
                        new_args.extend_from_slice(&args[..arg]);
                        new_args.push(subterm);
                        new_args.extend_from_slice(&args[arg + 1..]);
                        Term::Application { op, args: new_args }
                    })
            }),
            NormalKind::Subterm(stack, it) => it.next().map(|subterm| {
                stack
                    .iter()
                    .rev()
                    .fold(subterm, |subterm, &(op, arg, args, _)| {
                        let mut new_args = Vec::with_capacity(args.len());
                        new_args.extend_from_slice(&args[..arg]);
                        new_args.push(subterm);
                        new_args.extend_from_slice(&args[arg + 1..]);
                        Term::Application { op, args: new_args }
                    })
            }),
        }
    }
}

pub struct TRSRewrites<'a>(TRSRewriteKind<'a>);

enum TRSRewriteKind<'a> {
    Normal(Normal<'a>),
    Eager(std::vec::IntoIter<Term>),
    All(std::vec::IntoIter<Term>),
    String(std::vec::IntoIter<Term>),
}

impl<'a> TRSRewrites<'a> {
    pub(crate) fn new(
        trs: &'a TRS,
        term: &'a Term,
        patterns: &'a Patterns,
        strategy: Strategy,
        rep: NumberRepresentation,
        sig: &'a Signature,
    ) -> Self {
        match strategy {
            Strategy::Normal => TRSRewrites(TRSRewriteKind::Normal(Normal::new(
                trs, sig, patterns, term, rep,
            ))),
            Strategy::Eager => TRSRewrites(TRSRewriteKind::Eager(
                trs.rewrite_args(term, patterns, strategy, rep, sig)
                    .or_else(|| trs.rewrite_head(term))
                    .unwrap_or_else(Vec::new)
                    .into_iter(),
            )),
            Strategy::All => TRSRewrites(TRSRewriteKind::All(
                trs.rewrite_all(term).unwrap_or_else(Vec::new).into_iter(),
            )),
            Strategy::String => TRSRewrites(TRSRewriteKind::String(
                trs.rewrite_as_string(term, sig)
                    .unwrap_or_else(Vec::new)
                    .into_iter(),
            )),
        }
    }
}

impl<'a> Iterator for TRSRewrites<'a> {
    type Item = Term;
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            TRSRewriteKind::Normal(it) => it.next(),
            TRSRewriteKind::Eager(it) => it.next(),
            TRSRewriteKind::All(it) => it.next(),
            TRSRewriteKind::String(it) => it.next(),
        }
    }
}
