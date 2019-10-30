use super::{Atom, Operator, Rule, Signature, Term, Variable};
use itertools::Itertools;
use serde_derive::{Deserialize, Serialize};
use std::collections::HashMap;
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
    /// assert_eq!(new_trs.display(&sig),
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
    /// "A = B;
    /// C = D | E;
    /// F(x_) = G;").expect("parse of A = B; C = D | E; F(x_) = G;");
    ///
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(trs.display(&sig),
    /// "A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
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
    /// "A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    /// CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    /// B C D E = B C | D E;")
    ///     .expect("parse of A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
    ///     CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
    ///     B C D E = B C | D E;");
    ///
    /// assert_eq!(trs.pretty(&sig),
    /// "A(x_, y_, z_) = A(x_, 105, 2);
    /// [B, C, D] = [C, D];
    /// B C D E = B C | D E;");
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
    // Return rewrites modifying the entire term, if possible, else None.
    fn rewrite_head(&self, term: &Term) -> Option<Vec<Term>> {
        let mut rewrites = vec![];
        for rule in &self.rules {
            if let Some(ref sub) = Term::pmatch(vec![(&rule.lhs, &term)]) {
                let mut items = rule.rhs.iter().map(|x| x.substitute(sub)).collect_vec();
                if self.is_deterministic && !items.is_empty() {
                    return Some(vec![items.remove(0)]);
                } else {
                    rewrites.append(&mut items);
                }
            }
        }
        if rewrites.is_empty() {
            None
        } else {
            Some(rewrites)
        }
    }
    // Return rewrites modifying subterms, if possible, else None.
    fn rewrite_args(&self, term: &Term, strategy: Strategy, sig: &Signature) -> Option<Vec<Term>> {
        if let Term::Application { op, ref args } = *term {
            for (i, arg) in args.iter().enumerate() {
                if let Some(v) = self.rewrite(arg, strategy, sig) {
                    let res = v
                        .iter()
                        .map(|x| {
                            let mut args = args.clone();
                            args[i] = x.clone();
                            Term::Application { op, args }
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
    // performs all possible rewrites, interpreting the term as a string
    fn rewrite_as_string(&self, term: &Term, sig: &Signature) -> Option<Vec<Term>> {
        let string = TRS::convert_term_to_string(term, sig)?;
        let mut rewrites = vec![];
        for rule in &self.rules {
            let pattern = TRS::convert_rule_to_strings(rule, sig)?;
            for breaks in TRS::gen_breaks(&pattern.0, string.len())?.iter() {
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
    pub fn convert_list_to_string(term: &Term, sig: &Signature) -> Option<Vec<Atom>> {
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
    fn digit_to_usize(term: &Term, sig: &Signature) -> Option<usize> {
        let (op, _) = term.as_application()?;
        match (op.name(sig), op.arity()) {
            (Some(ref s), 0) if s.as_str() == "0" => Some(0),
            (Some(ref s), 0) if s.as_str() == "1" => Some(1),
            (Some(ref s), 0) if s.as_str() == "2" => Some(2),
            (Some(ref s), 0) if s.as_str() == "3" => Some(3),
            (Some(ref s), 0) if s.as_str() == "4" => Some(4),
            (Some(ref s), 0) if s.as_str() == "5" => Some(5),
            (Some(ref s), 0) if s.as_str() == "6" => Some(6),
            (Some(ref s), 0) if s.as_str() == "7" => Some(7),
            (Some(ref s), 0) if s.as_str() == "8" => Some(8),
            (Some(ref s), 0) if s.as_str() == "9" => Some(9),
            _ => None,
        }
    }
    fn num_to_usize(term: &Term, sig: &Signature) -> Option<usize> {
        let (_, args) = term.as_guarded_application(sig, ".", 2)?;
        if args[0].as_guarded_application(sig, "DIGIT", 0).is_some() {
            TRS::digit_to_usize(&args[1], sig)
        } else {
            let (_, inner_args) = args[0].as_guarded_application(sig, ".", 2)?;
            inner_args[0].as_guarded_application(sig, "DECC", 0)?;
            let sigs = TRS::num_to_usize(&inner_args[1], sig)?;
            let digit = TRS::digit_to_usize(&args[1], sig)?;
            Some(sigs * 10 + digit)
        }
    }
    fn num_to_atom(term: &Term, sig: &Signature) -> Option<Atom> {
        let n = TRS::num_to_usize(term, sig)?;
        if n < 100 {
            sig.operators()
                .iter()
                .find(|op| op.name(sig) == Some(n.to_string()) && op.arity() == 0)
                .map(|&op| Atom::from(op))
                .or_else(|| Some(Atom::from(sig.new_op(0, Some(n.to_string())))))
        } else {
            None
        }
    }
    fn convert_term_to_string(term: &Term, sig: &Signature) -> Option<Vec<Atom>> {
        match *term {
            Term::Variable(v) => Some(vec![Atom::Variable(v)]),
            Term::Application { op, ref args } => match (op.name(sig), op.arity()) {
                (_, 0) => Some(vec![Atom::Operator(op)]),
                (Some(ref s), 2) if s.as_str() == "." => {
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
    fn gen_breaks(pattern: &[Atom], n: usize) -> Option<Vec<Vec<usize>>> {
        let breaks = (0..=n)
            .combinations(pattern.len() - 1)
            .map(|mut x| {
                x.insert(0, 0);
                x.push(n);
                x
            })
            .filter(|x| TRS::valid_option(&pattern, &x))
            .collect_vec();
        Some(breaks)
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
                    .find(|x| x.arity() == 2 && x.name(sig) == Some(".".to_string())),
            ),
            Atom::Operator(op) => (
                Term::Application { op, args: vec![] },
                sig.operators()
                    .into_iter()
                    .find(|x| x.arity() == 2 && x.name(sig) == Some(".".to_string())),
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
        let x_string = TRS::convert_term_to_string(x, sig)?;
        let y_string = TRS::convert_term_to_string(y, sig)?;
        let p = PString::new(x_string, y_string, dist, sig).compute(t_max, d_max);
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
        let x_string = TRS::convert_list_to_string(x, sig);
        let y_string = TRS::convert_list_to_string(y, sig);
        match (x_string, y_string) {
            (Some(x_string), Some(y_string)) => {
                let p = PString::new(x_string, y_string, dist, &sig).compute(t_max, d_max);
                p.ln()
            }
            _ => std::f64::NEG_INFINITY,
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
    /// let rewritten_terms = &t.rewrite(&term, Strategy::Normal, &sig).unwrap();
    /// assert_eq!(rewritten_terms.len(), 1);
    /// assert_eq!(rewritten_terms[0].display(&sig), "J(G K(C A))");
    ///
    /// let rewritten_terms = &t.rewrite(&term, Strategy::Eager, &sig).unwrap();
    /// assert_eq!(rewritten_terms.len(), 2);
    /// assert_eq!(rewritten_terms[0].display(&sig), "J(F(D) K(C A))");
    /// assert_eq!(rewritten_terms[1].display(&sig), "J(F(E) K(C A))");
    ///
    /// let rewritten_terms = &t.rewrite(&term, Strategy::All, &sig).unwrap();
    /// assert_eq!(rewritten_terms.len(), 6);
    /// assert_eq!(rewritten_terms[0].display(&sig), "J(G K(C A))");
    /// assert_eq!(rewritten_terms[1].display(&sig), "J(F(D) K(C A))");
    /// assert_eq!(rewritten_terms[2].display(&sig), "J(F(E) K(C A))");
    /// assert_eq!(rewritten_terms[3].display(&sig), "J(F(C) K(D A))");
    /// assert_eq!(rewritten_terms[4].display(&sig), "J(F(C) K(E A))");
    /// assert_eq!(rewritten_terms[5].display(&sig), "J(F(C) K(C B))");
    /// ```
    pub fn rewrite(&self, term: &Term, strategy: Strategy, sig: &Signature) -> Option<Vec<Term>> {
        match *term {
            Term::Variable(_) => None,
            ref app => match strategy {
                Strategy::Normal => self
                    .rewrite_head(app)
                    .or_else(|| self.rewrite_args(app, strategy, sig)),
                Strategy::Eager => self
                    .rewrite_args(app, strategy, sig)
                    .or_else(|| self.rewrite_head(app)),
                Strategy::All => self.rewrite_all(app),
                Strategy::String => self.rewrite_as_string(app, sig),
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
    /// assert_eq!(t.get(&a).unwrap().1.display(&sig), "A = B");
    ///
    /// let c = parse_term(&mut sig, "C").expect("parse of C");
    ///
    /// assert_eq!(t.get(&c).unwrap().1.display(&sig), "C = D | E");
    /// ```
    pub fn get(&self, lhs: &Term) -> Option<(usize, Rule)> {
        for (idx, rule) in self.rules.iter().enumerate() {
            if Term::alpha(vec![(lhs, &rule.lhs)]).is_some() {
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
    /// "A(a_ b_) = B(b_ b_);
    /// D(c_ e_) = D(E F);").expect("parse of A(a_ b_) = B(b_ b_); D(c_ e_) = D(E F);");
    ///
    /// let r = parse_rule(&mut sig, "A(x_ y_) = B(y_ y_)").expect("parse of A(x_ y_) = B(y_ y_)");
    ///
    /// assert_eq!(t.get_clause(&r).unwrap().1.display(&sig), "A(a_ b_) = B(b_ b_)");
    ///
    /// let r = parse_rule(&mut sig, "D(w_ q_) = D(E F)").expect("parse of D(w_ q_) = D(E F)");
    ///
    /// assert_eq!(t.get_clause(&r).unwrap().1.display(&sig), "D(c_ e_) = D(E F)");
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
    /// assert_eq!(t.remove(&a).expect("removing A = B").display(&sig), "A = B");
    ///
    /// assert_eq!(t.remove(&c).expect("removing C = D").display(&sig), "C = D | E");
    ///
    /// assert_eq!(t.display(&sig), "F(x_) = G;");
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
    /// assert_eq!(t.remove_idx(0).expect("removing A = B").display(&sig), "A = B");
    ///
    /// assert_eq!(t.remove_idx(0).expect("removing C = D").display(&sig), "C = D | E");
    ///
    /// assert_eq!(t.display(&sig), "F(x_) = G;");
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
    /// assert_eq!(t.remove_clauses(&r).expect("removing C = D").display(&sig), "C = D");
    ///
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// D = G;
    /// C = D | E;
    /// F(x_) = G;");
    ///
    /// let r = parse_rule(&mut sig, "D = A").expect("parse of D = A");
    ///
    /// t.insert(0, r).expect("inserting D = A with D = G");
    ///
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(t.display(&sig),
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
    /// assert_eq!(t.display(&sig),
    /// "A = B;
    /// C = E | A;
    /// F(x_) = G;");
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
pub struct PStringDist {
    pub beta: f64,
    pub p_insertion: f64,
    pub p_deletion: f64,
    pub p_correct_sub: f64,
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
        let t_start = if self.n > self.m { self.n - self.m } else { 0 };
        let t_end = if self.m > d_max + self.n {
            0
        } else {
            t_max.min(d_max + self.n - self.m)
        };
        (t_start..=t_end)
            .filter_map(|t| {
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
            let denominator: f64 = (max_mt..=(self.m + t)).product::<usize>() as f64;
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
                                                                    // println!("n_x: {:?}, n_y: {:?}", n_x, n_y);
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

#[cfg(test)]
mod tests {
    use super::super::super::parser::*;
    use super::super::Signature;
    use super::*;

    #[test]
    fn new_test() {
        let mut sig = Signature::default();

        let r0 = parse_rule(&mut sig, "A = B").expect("parse of A = B");
        let r1 = parse_rule(&mut sig, "C(x_) = x_").expect("parse of C(x_) = x_");
        let r2 = parse_rule(&mut sig, "D(y_) = D(E)").expect("parse of D(y_) = D(E)");
        let new_trs = TRS::new(vec![r0, r1, r2]);

        assert_eq!(new_trs.display(&sig), "A = B;\nC(x_) = x_;\nD(y_) = D(E);");
    }

    #[test]
    fn make_deterministic_test() {
        let mut sig = Signature::default();
        let mut t = parse_trs(
            &mut sig,
            "A = B | C;
            D = E;",
        )
        .expect("parse of A = B | C; D = E");

        let str_before = t.display(&sig);

        assert!(t.make_deterministic());

        assert_ne!(t.display(&sig), str_before);

        let str_before = t.display(&sig);
        let r = parse_rule(&mut sig, "C = B | D").expect("parse of C = B | D");

        if t.insert_idx(1, r.clone()).is_err() {
            assert!(true);
        }

        assert_eq!(str_before, t.display(&sig));

        assert!((t.display(&sig) == "A = B;\nD = E;") || (t.display(&sig) == "A = C;\nD = E;"));
    }

    #[test]
    fn make_nondeterministic_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(&mut sig, "A = B | C; D = E;").expect("parse of A = B | C; D = E");

        t.make_deterministic();

        let str_before = t.display(&sig);
        let r = parse_rule(&mut sig, "C = B | D").expect("parse of C = B | D");
        assert!(t.insert_idx(1, r.clone()).is_err());
        assert_eq!(str_before, t.display(&sig));

        assert!(t.make_nondeterministic());

        t.insert_idx(1, r).expect("inserting C = B | D");

        assert!(
            (t.display(&sig) == "A = B;\nC = B | D;\nD = E;")
                || (t.display(&sig) == "A = C;\nC = B | D;\nD = E;")
        );
    }

    #[test]
    fn is_deterministic_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B | C;
            D = E;",
        )
        .expect("parse of A = B | C; D = E");

        assert!(!t.is_deterministic());

        t.make_deterministic();

        assert!(t.is_deterministic());
    }

    #[test]
    fn len_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        assert_eq!(t.len(), 3);
    }

    #[test]
    fn is_empty_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        assert!(!t.is_empty());

        let t = parse_trs(&mut sig, "").expect("parse of blank string");

        assert!(t.is_empty());
    }

    #[test]
    fn size_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        assert_eq!(t.size(), 8);
    }

    #[test]
    fn display_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        assert_eq!(t.display(&sig), "A = B;\nC = D | E;\nF(x_) = G;");

        let trs = parse_trs(&mut sig,
        "A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO))); CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL)); B C D E = B C | D E;")
            .expect("parse of A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
            CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
            B C D E = B C | D E;");

        assert_eq!(trs.display(&sig),
        "A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));\nCONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));\n.(.(.(B C) D) E) = .(B C) | .(D E);");
    }

    #[test]
    fn pretty_test() {
        let mut sig = Signature::default();

        let trs = parse_trs(
            &mut sig,
            "A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
        CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
        B C D E = B C | D E;",
        )
        .expect(
            "parse of A(x_ y_ z_) = A(x_ DECC(DECC(DIGIT(1) 0) 5) SUCC(SUCC(ZERO)));
             CONS(B CONS(C CONS(D NIL))) = CONS(C CONS(D NIL));
             B C D E = B C | D E;",
        );

        assert_eq!(
            trs.pretty(&sig),
            "A(x_, y_, z_) = A(x_, 105, 2);\n[B, C, D] = [C, D];\nB C D E = B C | D E;"
        );
    }

    #[test]
    fn clauses_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F = G;",
        )
        .expect("parse of A = B; C = D | E; F = G;");

        let r0 = parse_rule(&mut sig, "A = B").expect("parse of A = B");
        let r1 = parse_rule(&mut sig, "C = D").expect("parse of C = D");
        let r2 = parse_rule(&mut sig, "C = E").expect("parse of C = E");
        let r3 = parse_rule(&mut sig, "F = G").expect("parse of F = G");

        assert_eq!(t.clauses(), vec![r0, r1, r2, r3]);
    }

    #[test]
    fn operators_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let ops: Vec<String> = t.operators().iter().map(|o| o.display(&sig)).collect();

        assert_eq!(ops, vec!["A", "B", "C", "D", "E", "F", "G"]);
    }

    #[test]
    fn unifies_test() {
        let mut sig = Signature::default();

        let t0 = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let t1 = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(H) = G;",
        )
        .expect("parse of A = B; C = D | E; F(H) = G;");

        assert!(TRS::unifies(t0.clone(), t1));

        let t2 = parse_trs(
            &mut sig,
            "B = A;
            C = D | E;
            F(y_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(y_) = G;");

        assert!(!TRS::unifies(t0, t2));
    }

    #[test]
    fn pmatches() {
        let mut sig = Signature::default();

        let t0 = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let t1 = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(H) = G;",
        )
        .expect("parse of A = B; C = D | E; F(H) = G;");

        assert!(TRS::pmatches(t0.clone(), t1));

        let t2 = parse_trs(
            &mut sig,
            "B = A;
            C = D | E;
            F(y_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(y_) = G;");

        assert!(!TRS::pmatches(t0.clone(), t2));

        let t3 = parse_trs(
            &mut sig,
            "A = B | C;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B | C; C = D | E; F(x_) = G");

        assert!(TRS::pmatches(t0.clone(), t3));

        let t4 = parse_trs(
            &mut sig,
            "A = B;
            C = D;
            D = E;",
        )
        .expect("parse of A = B; C = D; D = E;");

        assert!(!TRS::pmatches(t0, t4));
    }

    #[test]
    fn alphas_test() {
        let mut sig = Signature::default();

        let t0 = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let t1 = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(H) = G;",
        )
        .expect("parse of A = B; C = D | E; F(H) = G;");

        assert!(!TRS::alphas(&t0, &t1));

        let t2 = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(y_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(y_) = G;");

        assert!(TRS::alphas(&t0, &t2));
    }

    #[test]
    fn rewrite_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let term = parse_term(&mut sig, "J(F(C) K(C A))").expect("parse of J(F(C) K(C A))");

        let rewritten_terms = &t.rewrite(&term, Strategy::Normal, &sig).unwrap();
        assert_eq!(rewritten_terms.len(), 1);
        assert_eq!(rewritten_terms[0].display(&sig), "J(G K(C A))");

        let rewritten_terms = &t.rewrite(&term, Strategy::Eager, &sig).unwrap();
        assert_eq!(rewritten_terms.len(), 2);
        assert_eq!(rewritten_terms[0].display(&sig), "J(F(D) K(C A))");
        assert_eq!(rewritten_terms[1].display(&sig), "J(F(E) K(C A))");

        let rewritten_terms = &t.rewrite(&term, Strategy::All, &sig).unwrap();
        assert_eq!(rewritten_terms.len(), 6);
        assert_eq!(rewritten_terms[0].display(&sig), "J(G K(C A))");
        assert_eq!(rewritten_terms[1].display(&sig), "J(F(D) K(C A))");
        assert_eq!(rewritten_terms[2].display(&sig), "J(F(E) K(C A))");
        assert_eq!(rewritten_terms[3].display(&sig), "J(F(C) K(D A))");
        assert_eq!(rewritten_terms[4].display(&sig), "J(F(C) K(E A))");
        assert_eq!(rewritten_terms[5].display(&sig), "J(F(C) K(C B))");
    }

    #[test]
    fn get_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let a = parse_term(&mut sig, "A").expect("parse of A");

        assert_eq!(t.get(&a).unwrap().1.display(&sig), "A = B");

        let c = parse_term(&mut sig, "C").expect("parse of C");

        assert_eq!(t.get(&c).unwrap().1.display(&sig), "C = D | E");
    }

    #[test]
    fn get_idx_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        assert_eq!(t.get_idx(0).unwrap().display(&sig), "A = B");

        assert_eq!(t.get_idx(1).unwrap().display(&sig), "C = D | E");
    }

    #[test]
    fn get_clause_test() {
        let mut sig = Signature::default();

        let t = parse_trs(
            &mut sig,
            "A(a_ b_) = B(b_ b_);
            D(c_ e_) = D(E F);",
        )
        .expect("parse of A(a_ b_) = B(b_ b_); D(c_ e_) = D(E F);");

        let r = parse_rule(&mut sig, "A(x_ y_) = B(y_ y_)").expect("parse of A(x_ y_) = B(y_ y_)");

        assert_eq!(
            t.get_clause(&r).unwrap().1.display(&sig),
            "A(a_ b_) = B(b_ b_)"
        );

        let r = parse_rule(&mut sig, "D(w_ q_) = D(E F)").expect("parse of D(w_ q_) = D(E F)");

        assert_eq!(
            t.get_clause(&r).unwrap().1.display(&sig),
            "D(c_ e_) = D(E F)"
        );
    }

    #[test]
    fn remove_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let a = parse_term(&mut sig, "A").expect("parse of A");
        let c = parse_term(&mut sig, "C").expect("parse of C");

        assert_eq!(t.remove(&a).expect("removing A = B").display(&sig), "A = B");

        assert_eq!(
            t.remove(&c).expect("removing C = D").display(&sig),
            "C = D | E"
        );

        assert_eq!(t.display(&sig), "F(x_) = G;");
    }

    #[test]
    fn remove_idx_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
        C = D | E;
        F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        assert_eq!(
            t.remove_idx(0).expect("removing A = B").display(&sig),
            "A = B"
        );

        assert_eq!(
            t.remove_idx(0).expect("removing C = D").display(&sig),
            "C = D | E"
        );

        assert_eq!(t.display(&sig), "F(x_) = G;");
    }

    #[test]
    fn remove_clauses_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let r = parse_rule(&mut sig, "C = D").expect("parse of C = D");

        assert_eq!(
            t.remove_clauses(&r).expect("removing C = D").display(&sig),
            "C = D"
        );

        assert_eq!(t.display(&sig), "A = B;\nC = E;\nF(x_) = G;");
    }

    #[test]
    fn insert_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let r = parse_rule(&mut sig, "D = G").expect("parse of D = G");

        t.insert(1, r).expect("inserting D = G at index 1");

        assert_eq!(t.display(&sig), "A = B;\nD = G;\nC = D | E;\nF(x_) = G;");

        let r = parse_rule(&mut sig, "D = A").expect("parse of D = A");

        t.insert(0, r).expect("inserting D = A with D = G");

        assert_eq!(
            t.display(&sig),
            "A = B;\nD = G | A;\nC = D | E;\nF(x_) = G;"
        );
    }

    #[test]
    fn insert_idx_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let r = parse_rule(&mut sig, "D = G").expect("parse of D = G");

        t.insert_idx(1, r).expect("inserting D = G at index 1");

        assert_eq!(t.display(&sig), "A = B;\nD = G;\nC = D | E;\nF(x_) = G;");
    }

    #[test]
    fn inserts_idx_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = H;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = H;");

        let r0 = parse_rule(&mut sig, "G(y_) = y_").expect("parse of G(y_) = y_");
        let r1 = parse_rule(&mut sig, "B = C").expect("parse of B = C");
        let r2 = parse_rule(&mut sig, "E = F | B").expect("parse of E = F | B");

        t.inserts_idx(2, vec![r0, r1, r2])
            .expect("inserting 3 rules at index 2");

        assert_eq!(
            t.display(&sig),
            "A = B;\nC = D | E;\nG(y_) = y_;\nB = C;\nE = F | B;\nF(x_) = H;"
        );
    }

    #[test]
    fn insert_clauses_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let r = parse_rule(&mut sig, "A = H").expect("parse of A = H");

        let t = t.insert_clauses(&r).expect("inserting A = H with A = B");

        assert_eq!(t.display(&sig), "A = B | H;\nC = D | E;\nF(x_) = G;");
    }

    #[test]
    fn push_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let r = parse_rule(&mut sig, "G(y_) = y_").expect("parse of G(y_) = y_");

        t.push(r).expect("inserting G(y_) = y_ at index 0");

        assert_eq!(
            t.display(&sig),
            "G(y_) = y_;\nA = B;\nC = D | E;\nF(x_) = G;"
        );
    }

    #[test]
    fn pushes_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = H;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = H;");

        let r0 = parse_rule(&mut sig, "G(y_) = y_").expect("parse of G(y_) = y_");
        let r1 = parse_rule(&mut sig, "B = C").expect("parse of B = C");
        let r2 = parse_rule(&mut sig, "E = F | B").expect("parse of E = F | B");

        t.pushes(vec![r0, r1, r2])
            .expect("inserting 3 rules at index 0");

        assert_eq!(
            t.display(&sig),
            "G(y_) = y_;\nB = C;\nE = F | B;\nA = B;\nC = D | E;\nF(x_) = H;"
        );
    }

    #[test]
    fn move_rule_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;
            H = I;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G; H = I;");

        t.move_rule(0, 2)
            .expect("moving rule from index 0 to index 2");

        assert_eq!(t.display(&sig), "C = D | E;\nF(x_) = G;\nA = B;\nH = I;");
    }

    #[test]
    fn replace_test() {
        let mut sig = Signature::default();

        let mut t = parse_trs(
            &mut sig,
            "A = B;
            C = D | E;
            F(x_) = G;",
        )
        .expect("parse of A = B; C = D | E; F(x_) = G;");

        let r = parse_rule(&mut sig, "C = D").expect("parse of C = D");
        let r_new = parse_rule(&mut sig, "C = A").expect("parse of C = A");

        t.replace(0, &r, r_new)
            .expect("replaceing C = D with C = A");

        assert_eq!(t.display(&sig), "A = B;\nC = E | A;\nF(x_) = G;");
    }
}
