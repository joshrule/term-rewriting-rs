extern crate term_rewriting;

use std::collections::HashMap;

use term_rewriting::*;

#[test]
fn term_substitute_test() {
    let mut sig = Signature::new(vec![
        (2, Some(".".to_string())),
        (0, Some("S".to_string())),
        (0, Some("K".to_string())),
    ]);

    // build some terms
    let term_before = parse_term(&mut sig, "S K y_ z_").expect("parse of S K y_ z_");
    let s_term = parse_term(&mut sig, "S").expect("parse of S");
    let k_term = parse_term(&mut sig, "K").expect("parse of K");

    // build a substitution
    let vars = sig.variables();
    let y = &vars[0];
    let z = &vars[1];
    let mut sub = HashMap::new();
    sub.insert(y.clone(), s_term);
    sub.insert(z.clone(), k_term);

    // build the term after substitution
    let term_after = parse_term(&mut sig, "S K S K").expect("parse of S K S K");

    // check for equality
    assert_eq!(term_before.substitute(&sub), term_after);
    assert_ne!(term_before, term_before.substitute(&sub));
    assert_ne!(term_before, term_after);
    assert_eq!(term_before.substitute(&HashMap::new()), term_before);
    assert_ne!(
        term_before.substitute(&HashMap::new()),
        term_before.substitute(&sub)
    );
}

#[test]
fn signature_parse() {
    let mut sig = Signature::new(vec![
        (2, Some(".".to_string())),
        (0, Some("S".to_string())),
        (0, Some("K".to_string())),
    ]);
    let ops = sig.operators();
    let a = &ops[0];
    let s = &ops[1];
    let k = &ops[2];

    let sk = "S x_ y_ z_ = x_ z_ (y_ z_); K x_ y_ = x_;";
    let (trs1, _) = parse(&mut sig, sk).expect("parse of SK");

    let vars = sig.variables();
    let x = &vars[0];
    let y = &vars[1];
    let z = &vars[2];
    let x2 = &vars[3];
    let y2 = &vars[4];

    let s_lhs = Term::Application {
        op: a.clone(),
        args: vec![
            Term::Application {
                op: a.clone(),
                args: vec![
                    Term::Application {
                        op: a.clone(),
                        args: vec![
                            Term::Application {
                                op: s.clone(),
                                args: vec![],
                            },
                            Term::Variable(x.clone()),
                        ],
                    },
                    Term::Variable(y.clone()),
                ],
            },
            Term::Variable(z.clone()),
        ],
    };
    let s_rhs = vec![Term::Application {
        op: a.clone(),
        args: vec![
            Term::Application {
                op: a.clone(),
                args: vec![Term::Variable(x.clone()), Term::Variable(z.clone())],
            },
            Term::Application {
                op: a.clone(),
                args: vec![Term::Variable(y.clone()), Term::Variable(z.clone())],
            },
        ],
    }];
    let s_rule = Rule::new(s_lhs, s_rhs).expect("new S rule");

    let k_lhs = Term::Application {
        op: a.clone(),
        args: vec![
            Term::Application {
                op: a.clone(),
                args: vec![
                    Term::Application {
                        op: k.clone(),
                        args: vec![],
                    },
                    Term::Variable(x2.clone()),
                ],
            },
            Term::Variable(y2.clone()),
        ],
    };
    let k_rhs = vec![Term::Variable(x2.clone())];
    let k_rule = Rule::new(k_lhs, k_rhs).expect("new K rule");

    let trs2 = TRS::new(vec![s_rule, k_rule]);

    assert_eq!(trs1, trs2);
}

#[test]
fn unify_test() {
    let mut sig = Signature::default();
    let a = sig.new_op(2, Some(".".to_string()));
    let s = sig.new_op(0, Some("S".to_string()));
    let k = sig.new_op(0, Some("K".to_string()));

    // build some terms
    let t1 = parse_term(&mut sig, "S K y_ z_").expect("parse of S K y_ z_");
    let t2 = parse_term(&mut sig, "S K S K").expect("parse of S K S K");
    let t3 = parse_term(&mut sig, "K K K K").expect("parse of K K K K");
    let t4 = parse_term(&mut sig, "y_ K").expect("parse of y_ K");
    let vars = sig.variables();
    let y = &vars[0];
    let z = &vars[1];
    let y2 = &vars[2];

    let mut hm1 = HashMap::new();
    hm1.insert(
        y.clone(),
        Term::Application {
            op: s.clone(),
            args: vec![],
        },
    );
    hm1.insert(
        z.clone(),
        Term::Application {
            op: k.clone(),
            args: vec![],
        },
    );
    assert_eq!(Some(hm1), Term::unify(vec![(t1.clone(), t2.clone())]));
    assert_eq!(None, Term::unify(vec![(t1.clone(), t3.clone())]));
    assert_eq!(None, Term::unify(vec![(t2.clone(), t3.clone())]));
    let mut hm2 = HashMap::new();
    hm2.insert(
        y2.clone(),
        Term::Application {
            op: a.clone(),
            args: vec![
                Term::Application {
                    op: a.clone(),
                    args: vec![
                        Term::Application {
                            op: k.clone(),
                            args: vec![],
                        },
                        Term::Application {
                            op: k.clone(),
                            args: vec![],
                        },
                    ],
                },
                Term::Application {
                    op: k.clone(),
                    args: vec![],
                },
            ],
        },
    );
    assert_eq!(Some(hm2), Term::unify(vec![(t3.clone(), t4.clone())]));
}

#[test]
fn rewrite_test() {
    // build a term
    let s_str = "S x_ y_ z_ = x_ z_ (y_ z_);";
    let k_str = "K x_ y_ = x_;";
    let l_str = "K S K;";
    let r_str = "S;";

    let mut sig = Signature::default();
    let s = s_str.to_owned() + k_str + l_str + r_str;
    let (trs, terms) = parse(&mut sig, &s).expect("parse TRS + terms");
    let l_term = &terms[0];
    let r_term = terms[1].clone();

    assert_eq!(trs.rewrite(&l_term, Strategy::Normal), Some(vec![r_term]));
}

#[test]
fn display_variable() {
    let mut sig = Signature::default();

    let v1 = sig.new_var(None);
    let v2 = sig.new_var(Some("blah".to_string()));

    assert_eq!(v1.display(), "var0_".to_string());
    assert_eq!(v1.name(), None);
    assert_eq!(v2.display(), "blah_".to_string());
    assert_eq!(v2.name(), Some("blah".to_string()));
}

#[test]
fn operator_methods() {
    let mut sig = Signature::default();

    let o = sig.new_op(0, None);

    assert_eq!(o.display(), "op0");
    assert_eq!(o.arity(), 0);
    assert_eq!(o.name(), None);
}

#[test]
fn atom_methods() {
    let mut sig = Signature::default();

    let o0 = sig.new_op(0, None);
    let o1 = sig.new_op(1, Some("A".to_string()));
    let v0 = sig.new_var(None);
    let v1 = sig.new_var(Some("X".to_string()));

    // use from
    let a0 = Atom::from(o0);
    let a1 = Atom::from(o1);
    let a2 = Atom::from(v0);
    let a3 = Atom::from(v1);
    // test derives
    assert_eq!(a0, a0.clone());
    assert_eq!(a0, a0);
    assert_eq!(a1, a1);
    assert_ne!(a0, a1);
    assert_eq!(a2, a2);
    assert_eq!(a3, a3);
    assert_ne!(a2, a3);
    assert_ne!(a1, a2);
    // test display
    assert_eq!(a0.display(), "op0");
    assert_eq!(a1.display(), "A");
    assert_eq!(a2.display(), "var0_");
    assert_eq!(a3.display(), "X_");
}

#[test]
fn rule_new_valid() {
    let mut sig = Signature::default();
    let lhs: Term = Term::Application {
        op: sig.new_op(0, None),
        args: vec![],
    };

    let rhs: Vec<Term> = vec![Term::Application {
        op: sig.new_op(0, None),
        args: vec![],
    }];

    assert!(Rule::new(lhs, rhs).is_some());
}

#[test]
fn rule_new_valid_lhs_var() {
    let mut sig = Signature::default();

    let lhs = Term::Application {
        op: sig.new_op(0, None),
        args: vec![Term::Variable(sig.new_var(None))],
    };
    let rhs = vec![Term::Application {
        op: sig.new_op(1, None),
        args: vec![],
    }];

    assert!(Rule::new(lhs, rhs).is_some());
}

#[test]
fn rule_new_invalid_lhs_var() {
    let mut sig = Signature::default();

    let lhs = Term::Variable(sig.new_var(None));
    let rhs = vec![Term::Application {
        op: sig.new_op(0, None),
        args: vec![],
    }];

    assert!(Rule::new(lhs, rhs).is_none());
}

#[test]
fn rule_new_invalid_rhs_var() {
    let mut sig = Signature::default();

    let lhs = Term::Application {
        op: sig.new_op(0, None),
        args: vec![],
    };
    let rhs = vec![Term::Variable(sig.new_var(None))];

    assert!(Rule::new(lhs, rhs).is_none());
}

#[test]
fn parse_display_roundtrip_term() {
    let mut sig = Signature::default();
    let s = "foo(bar(x_) y_ baz)";
    let term = parse_term(&mut sig, s).unwrap_or_else(|_| panic!("parse of {}", s));
    let ns = term.display();
    assert_eq!(s, ns);
}

#[test]
fn parse_display_roundtrip_rule() {
    let mut sig = Signature::default();
    let s = "foo(bar(x_) y_ baz) = bar(y_) | buzz";
    let rule = parse_rule(&mut sig, s).unwrap_or_else(|_| panic!("parse of {}", s));
    let ns = rule.display();
    assert_eq!(s, ns);
}

#[test]
fn parse_display_roundtrip_trs() {
    let mut sig = Signature::default();
    let s = "foo(bar(x_) y_ baz) = bar(y_) | buzz;\nbar(baz) = foo(bar(baz) bar(baz) baz);";
    let trs = parse_trs(&mut sig, s).unwrap_or_else(|_| panic!("parse of {}", s));
    let ns = trs.display();
    assert_eq!(s, ns);
}

#[test]
fn pretty_term_application() {
    let mut sig = Signature::new(vec![
        (2, Some(".".to_string())),
        (0, Some("S".to_string())),
        (0, Some("K".to_string())),
    ]);
    let t = parse_term(&mut sig, "S K S K").expect("parse of S K S K");
    assert_eq!(t.display(), ".(.(.(S K) S) K)");
    assert_eq!(t.pretty(), "S K S K");
}

#[test]
fn pretty_term_list() {
    let mut sig = Signature::new(vec![
        (2, Some("CONS".to_string())),
        (0, Some("NIL".to_string())),
        (0, Some("A".to_string())),
    ]);
    let t = parse_term(&mut sig, "CONS(A CONS(A CONS(A NIL)))")
        .expect("parse of CONS(A CONS(A CONS(A NIL)))");
    assert_eq!(t.display(), "CONS(A CONS(A CONS(A NIL)))");
    assert_eq!(t.pretty(), "[A, A, A]");
}

#[test]
fn pretty_term_number() {
    let mut sig = Signature::new(vec![
        (1, Some("SUCC".to_string())),
        (0, Some("ZERO".to_string())),
        (2, Some("FOO".to_string())),
    ]);
    let t = parse_term(&mut sig, "FOO(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO))")
        .expect("parse of FOO(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO))");
    assert_eq!(t.display(), "FOO(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO))");
    assert_eq!(t.pretty(), "FOO(3, 1)");
}

#[test]
fn pretty_term_nonspecial() {
    let mut sig = Signature::new(vec![
        (0, Some("FOO".to_string())),
        (1, Some("BAR".to_string())),
        (2, Some("BAZ".to_string())),
    ]);
    let t = parse_term(&mut sig, "BAZ(BAZ(BAR(BAR(FOO)) FOO) FOO)")
        .expect("parse of BAZ(BAZ(BAR(BAR(FOO)) FOO) FOO)");
    assert_eq!(t.display(), "BAZ(BAZ(BAR(BAR(FOO)) FOO) FOO)");
    assert_eq!(t.pretty(), "BAZ(BAZ(BAR(BAR(FOO)), FOO), FOO)");
}

#[test]
fn pretty_trs() {
    let mut sig = Signature::new(vec![
        (2, Some(".".to_string())),
        (0, Some("S".to_string())),
        (0, Some("K".to_string())),
        (2, Some("CONS".to_string())),
        (0, Some("NIL".to_string())),
        (1, Some("SUCC".to_string())),
        (0, Some("ZERO".to_string())),
        (0, Some("FOO".to_string())),
        (1, Some("BAR".to_string())),
        (2, Some("BAz".to_string())),
    ]);
    let s = "S x_ y_ z_ = x_ z_ (y_ z_); \
        K x_ y_ = x_; \
        CONS(FOO CONS(FOO NIL)) = SUCC(SUCC(ZERO));
        BAZ(FOO BAR(x_)) = BAZ(x_ FOO) | SUCC(x_);";
    let (trs, _) = parse(&mut sig, s).expect("parse of pretty_trs");
    assert_eq!(
        trs.display(),
        "\
.(.(.(S x_) y_) z_) = .(.(x_ z_) .(y_ z_));
.(.(K x_) y_) = x_;
CONS(FOO CONS(FOO NIL)) = SUCC(SUCC(ZERO));
BAZ(FOO BAR(x_)) = BAZ(x_ FOO) | SUCC(x_);"
    );
    assert_eq!(
        trs.pretty(),
        "\
S x_ y_ z_ = x_ z_ (y_ z_);
K x_ y_ = x_;
[FOO, FOO] = 2;
BAZ(FOO, BAR(x_)) = BAZ(x_, FOO) | SUCC(x_);"
    );
}
