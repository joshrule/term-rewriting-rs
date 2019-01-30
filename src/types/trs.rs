use super::{Operator, Rule, Term};
use itertools::Itertools;
use rand::seq::sample_iter;
use rand::Rng;
use std::fmt;

/// A first-order term rewriting system.
///
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
    pub(crate) is_deterministic: bool,
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
    /// assert_eq!(new_trs.display(),
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
    /// let str_before = t.display();
    ///
    /// assert!(t.make_deterministic(& mut r));
    ///
    /// assert_ne!(t.display(), str_before);
    ///
    /// let str_before = t.display();
    /// let r = parse_rule(&mut sig, "C = B | D").expect("parse of C = B | D");
    ///
    /// if t.insert_idx(1, r.clone()).is_err() {
    ///     assert!(true);
    /// }
    ///
    /// assert_eq!(str_before, t.display());
    ///
    /// assert!((t.display() ==
    /// "A = B;
    /// D = E;") ||
    ///     (t.display() ==
    /// "A = C;
    /// D = E;"));
    /// # }
    /// ```
    pub fn make_deterministic<R: Rng>(&mut self, rng: &mut R) -> bool {
        if !self.is_deterministic {
            self.rules = self
                .rules
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
    /// t.make_deterministic(& mut r);
    ///
    /// let str_before = t.display();
    /// let r = parse_rule(&mut sig, "C = B | D").expect("parse of C = B | D");
    /// assert!(t.insert_idx(1, r.clone()).is_err());
    /// assert_eq!(str_before, t.display());
    ///
    /// assert!(t.make_nondeterministic());
    ///
    /// t.insert_idx(1, r).expect("inserting C = B | D");
    ///
    /// assert!((t.display() ==
    /// "A = B;
    /// C = B | D;
    /// D = E;") ||
    ///     (t.display() ==
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
    /// Serialize a `TRS`.
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
    /// assert_eq!(t.display(),
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;");
    ///
    /// let trs = parse_trs(&mut sig,
    /// "A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    /// CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    /// B C D E = B C | D E;")
    ///     .expect("parse of A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    ///     CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    ///     B C D E = B C | D E;");
    ///
    /// assert_eq!(trs.display(),
    /// "A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    /// CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    /// .(.(.(B C) D) E) = .(B C) | .(D E);");
    /// ```
    pub fn display(&self) -> String {
        self.rules
            .iter()
            .map(|r| format!("{};", r.display()))
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
    /// "A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    /// CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    /// B C D E = B C | D E;")
    ///     .expect("parse of A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    ///     CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    ///     B C D E = B C | D E;");
    ///
    /// assert_eq!(trs.pretty(),
    /// "A(x_, y_, z_) = A(x_, 105, 2);
    /// [B, C, D] = [C, D];
    /// B C D E = B C | D E;");
    /// ```
    pub fn pretty(&self) -> String {
        self.rules
            .iter()
            .map(|r| format!("{};", r.pretty()))
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
    /// let ops: Vec<String> = t.operators().iter().map(|o| o.display()).collect();
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
            && trs1
                .rules
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
    fn rewrite_args(&self, term: &Term, strategy: Strategy) -> Option<Vec<Term>> {
        if let Term::Application { ref op, ref args } = *term {
            for (i, arg) in args.iter().enumerate() {
                if let Some(v) = self.rewrite(arg, strategy) {
                    let res = v
                        .iter()
                        .map(|x| {
                            let mut args = args.clone();
                            args[i] = x.clone();
                            Term::Application {
                                op: op.clone(),
                                args,
                            }
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
    // performs all possible rewrites, else None.
    fn rewrite_all(&self, term: &Term) -> Option<Vec<Term>> {
        match term {
            Term::Variable(_) => None,
            Term::Application { ref args, .. } => {
                // rewrite head
                let mut rewrites = self.rewrite_head(term).unwrap_or_else(|| vec![]);
                // rewrite subterms
                for (i, arg) in args.iter().enumerate() {
                    for rewrite in self.rewrite_all(arg).unwrap_or_else(|| vec![]) {
                        rewrites.push(term.replace(&[i], rewrite).unwrap());
                    }
                }
                Some(rewrites)
            }
        }
    }
    /// Perform a single rewrite step.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Strategy, TRS, parse_trs, Term, parse_term};
    /// let mut sig = Signature::default();
    ///
    /// let t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let term = parse_term(&mut sig, "J(F(C) K(C A))").expect("parse of J(F(C) K(C A))");
    ///
    /// let rewritten_terms = &t.rewrite(&term, Strategy::Normal).unwrap();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(), "J(G K(C A))");
    ///
    /// let rewritten_terms = &t.rewrite(&term, Strategy::Eager).unwrap();
    /// assert_eq!(rewritten_terms.len(), 2);
    /// assert_eq!(rewritten_terms[0].display(), "J(F(D) K(C A))");
    /// assert_eq!(rewritten_terms[1].display(), "J(F(E) K(C A))");
    ///
    /// let rewritten_terms = &t.rewrite(&term, Strategy::All).unwrap();
    /// assert_eq!(rewritten_terms.len(), 6);
    /// assert_eq!(rewritten_terms[0].display(), "J(G K(C A))");
    /// assert_eq!(rewritten_terms[1].display(), "J(F(D) K(C A))");
    /// assert_eq!(rewritten_terms[2].display(), "J(F(E) K(C A))");
    /// assert_eq!(rewritten_terms[3].display(), "J(F(C) K(D A))");
    /// assert_eq!(rewritten_terms[4].display(), "J(F(C) K(E A))");
    /// assert_eq!(rewritten_terms[5].display(), "J(F(C) K(C B))");
    /// ```
    pub fn rewrite(&self, term: &Term, strategy: Strategy) -> Option<Vec<Term>> {
        match *term {
            Term::Variable(_) => None,
            ref app => match strategy {
                Strategy::Normal => self
                    .rewrite_head(app)
                    .or_else(|| self.rewrite_args(app, strategy)),
                Strategy::Eager => self
                    .rewrite_args(app, strategy)
                    .or_else(|| self.rewrite_head(app)),
                Strategy::All => self.rewrite_all(app),
            },
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
    /// assert_eq!(t.get(&a).unwrap().1.display(), "A = B");
    ///
    /// let c = parse_term(&mut sig, "C").expect("parse of C");
    ///
    /// assert_eq!(t.get(&c).unwrap().1.display(), "C = D | E");
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
    /// assert_eq!(t.get_idx(0).unwrap().display(), "A = B");
    ///
    /// assert_eq!(t.get_idx(1).unwrap().display(), "C = D | E");
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
    /// assert_eq!(t.get_clause(&r).unwrap().1.display(), "A(a_ b_) = B(b_ b_)");
    ///
    /// let r = parse_rule(&mut sig, "D(w_ q_) = D(E F)").expect("parse of D(w_ q_) = D(E F)");
    ///
    /// assert_eq!(t.get_clause(&r).unwrap().1.display(), "D(c_ e_) = D(E F)");
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
    /// assert_eq!(t.remove(&a).expect("removing A = B").display(), "A = B");
    ///
    /// assert_eq!(t.remove(&c).expect("removing C = D").display(), "C = D | E");
    ///
    /// assert_eq!(t.display(), "F(x_) = G;");
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
    /// assert_eq!(t.remove_idx(0).expect("removing A = B").display(), "A = B");
    ///
    /// assert_eq!(t.remove_idx(0).expect("removing C = D").display(), "C = D | E");
    ///
    /// assert_eq!(t.display(), "F(x_) = G;");
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
    /// assert_eq!(t.remove_clauses(&r).expect("removing C = D").display(), "C = D");
    ///
    /// assert_eq!(t.display(),
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
    /// assert_eq!(t.display(),
    /// "A = B;
    /// D = G;
    /// C = D | E;
    /// F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "D = A").expect("parse of D = A");
    ///
    /// t.insert(0, r).expect("inserting D = A with D = G");
    ///
    /// assert_eq!(t.display(),
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
    /// assert_eq!(t.display(),
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
    /// let mut t = parse_trs(&mut sig,
    /// "A = B;
    /// C = D | E;
    /// F(x_) = H;").expect("parse of A = B; C = D | E; F(x_) = H;");
    ///
    /// let r0 = parse_rule(&mut sig, "G(y_) = y_").expect("parse of G(y_) = y_");
    /// let r1 = parse_rule(&mut sig, "B = C").expect("parse of B = C");
    /// let r2 = parse_rule(&mut sig, "E = F | B").expect("parse of E = F | B");
    ///
    /// t.inserts_idx(2, vec![r0, r1, r2]).expect("inserting 3 rules at index 2");
    ///
    /// assert_eq!(t.display(),
    /// "A = B;
    /// C = D | E;
    /// G(y_) = y_;
    /// B = C;
    /// E = F | B;
    /// F(x_) = H;");
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
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "A = H").expect("parse of A = H");
    ///
    /// let t = t.insert_clauses(&r).expect("inserting A = H with A = B");
    ///
    /// assert_eq!(t.display(),
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
    /// assert_eq!(t.display(),
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
    /// assert_eq!(t.display(),
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
    /// assert_eq!(t.display(),
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
    /// assert_eq!(t.display(),
    /// "A = B;
    /// C = E | A;
    /// F(x_) = G;");
    /// ```
    pub fn replace(&mut self, idx: usize, rule1: &Rule, rule2: Rule) -> Result<&mut TRS, TRSError> {
        self.remove_clauses(rule1)?;
        self.insert(idx, rule2)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Strategy {
    /// Perform only the leftmost-innermost rewrite
    Normal,
    /// Perform only the leftmost-innermost rewrite
    Eager,
    /// Perform all possible rewrites
    All,
}
impl fmt::Display for Strategy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Strategy::Normal => write!(f, "Normal"),
            Strategy::Eager => write!(f, "Eager"),
            Strategy::All => write!(f, "All"),
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
