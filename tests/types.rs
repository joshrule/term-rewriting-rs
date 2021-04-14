extern crate term_rewriting;

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
    let sub = Substitution(vec![(y, &s_term), (z, &k_term)]);

    // build the term after substitution
    let term_after = parse_term(&mut sig, "S K S K").expect("parse of S K S K");

    // check for equality
    assert_eq!(term_before.substitute(&sub), term_after);
    assert_ne!(term_before, term_before.substitute(&sub));
    assert_ne!(term_before, term_after);
    assert_eq!(term_before.substitute(&Substitution(vec![])), term_before);
    assert_ne!(
        term_before.substitute(&Substitution(vec![])),
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

    let t1_0 = Term::Application {
        op: s.clone(),
        args: vec![],
    };
    let t1_1 = Term::Application {
        op: k.clone(),
        args: vec![],
    };
    let sub1 = Substitution(vec![(y, &t1_0), (z, &t1_1)]);
    assert_eq!(Some(sub1), Term::unify(&[(&t1, &t2)]));
    assert_eq!(None, Term::unify(&[(&t1, &t3)]));
    assert_eq!(None, Term::unify(&[(&t2, &t3)]));
    let t2 = Term::Application {
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
    };
    let sub2 = Substitution(vec![(y2, &t2)]);
    assert_eq!(Some(sub2), Term::unify(&[(&t3, &t4)]));
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

    assert_eq!(
        trs.rewrite(
            &l_term,
            Strategy::Normal,
            NumberRepresentation::default(),
            &sig
        )
        .collect::<Vec<_>>(),
        vec![r_term]
    );
}

#[test]
fn display_variable() {
    let mut sig = Signature::default();

    let v1 = sig.new_var(None);
    let v2 = sig.new_var(Some("blah".to_string()));

    assert_eq!(v1.display(), "v0_".to_string());
    assert_eq!(v1.name(&sig), None);
    assert_eq!(v2.display(), "v1_".to_string());
    assert_eq!(v2.name(&sig), Some("blah"));
}

#[test]
fn operator_methods() {
    let mut sig = Signature::default();

    let o = sig.new_op(0, None);

    assert_eq!(o.display(&sig), "op0");
    assert_eq!(o.arity(&sig), 0);
    assert_eq!(o.name(&sig), None);
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
    assert_eq!(a0.display(&sig), "op0");
    assert_eq!(a1.display(&sig), "A");
    assert_eq!(a2.display(&sig), "v0_");
    assert_eq!(a3.display(&sig), "v1_");
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
    let s = "foo(bar(v0_) v1_ baz)";
    let term = parse_term(&mut sig, s).unwrap_or_else(|_| panic!("parse of {}", s));
    let ns = term.display(&sig);
    assert_eq!(s, ns);
}

#[test]
fn parse_display_roundtrip_rule() {
    let mut sig = Signature::default();
    let s = "foo(bar(v0_) v1_ baz) = bar(v1_) | buzz";
    let rule = parse_rule(&mut sig, s).unwrap_or_else(|_| panic!("parse of {}", s));
    let ns = rule.display(&sig);
    assert_eq!(s, ns);
}

#[test]
fn parse_display_roundtrip_trs() {
    let mut sig = Signature::default();
    let s = "foo(bar(v0_) v1_ baz) = bar(v1_) | buzz;\nbar(baz) = foo(bar(baz) bar(baz) baz);";
    let trs = parse_trs(&mut sig, s).unwrap_or_else(|_| panic!("parse of {}", s));
    let ns = trs.display(&sig);
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
    assert_eq!(t.display(&sig), ".(.(.(S K) S) K)");
    assert_eq!(t.pretty(&sig), "S K S K");
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
    assert_eq!(t.display(&sig), "CONS(A CONS(A CONS(A NIL)))");
    assert_eq!(t.pretty(&sig), "[A, A, A]");

    let t = parse_term(&mut sig, "CONS(A A)").expect("parse of term");
    assert_eq!(t.display(&sig), "CONS(A A)");
    assert_eq!(t.pretty(&sig), "CONS(A, A)");
}

#[test]
fn pretty_term_number() {
    let mut sig = Signature::new(vec![
        (1, Some("SUCC".to_string())),
        (0, Some("ZERO".to_string())),
        (2, Some("FOO".to_string())),
        (1, Some("DIGIT".to_string())),
        (2, Some("DECC".to_string())),
        (0, Some("ONE".to_string())),
        (0, Some("TWO".to_string())),
        (0, Some("THREE".to_string())),
        (0, Some("FOUR".to_string())),
        (0, Some("FIVE".to_string())),
        (0, Some("SIX".to_string())),
        (0, Some("SEVEN".to_string())),
        (0, Some("EIGHT".to_string())),
        (0, Some("NINE".to_string())),
    ]);

    // test normal unary
    let t = parse_term(&mut sig, "FOO(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO))")
        .expect("parse of FOO(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO))");
    assert_eq!(t.display(&sig), "FOO(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO))");
    assert_eq!(t.pretty(&sig), "FOO(3, 1)");

    // test broken unary
    let t = parse_term(&mut sig, "SUCC(SUCC(ONE))").expect("parse of term");
    assert_eq!(t.display(&sig), "SUCC(SUCC(ONE))");
    assert_eq!(t.pretty(&sig), "SUCC(SUCC(ONE))");

    // test normal decimal
    let t = parse_term(&mut sig, "FOO(DIGIT(ZERO) DECC(DECC(DECC(DECC(DECC(DECC(DECC(DECC(DIGIT(NINE) EIGHT) SEVEN) SIX) FIVE) FOUR) THREE) TWO) ONE))")
        .expect("parse of term");
    assert_eq!(t.display(&sig), "FOO(DIGIT(ZERO) DECC(DECC(DECC(DECC(DECC(DECC(DECC(DECC(DIGIT(NINE) EIGHT) SEVEN) SIX) FIVE) FOUR) THREE) TWO) ONE))");
    assert_eq!(t.pretty(&sig), "FOO(0, 987654321)");

    // test broken decimal
    let t = parse_term(&mut sig, "DIGIT(FOO(ONE NINE))").expect("parse of term");
    assert_eq!(t.display(&sig), "DIGIT(FOO(ONE NINE))");
    assert_eq!(t.pretty(&sig), "DIGIT(FOO(ONE, NINE))");
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
    assert_eq!(t.display(&sig), "BAZ(BAZ(BAR(BAR(FOO)) FOO) FOO)");
    assert_eq!(t.pretty(&sig), "BAZ(BAZ(BAR(BAR(FOO)), FOO), FOO)");
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
        trs.display(&sig),
        "\
.(.(.(S v0_) v1_) v2_) = .(.(v0_ v2_) .(v1_ v2_));
.(.(K v3_) v4_) = v3_;
CONS(FOO CONS(FOO NIL)) = SUCC(SUCC(ZERO));
BAZ(FOO BAR(v5_)) = BAZ(v5_ FOO) | SUCC(v5_);"
    );
    assert_eq!(
        trs.pretty(&sig),
        "\
S v0_ v1_ v2_ = v0_ v2_ (v1_ v2_);
K v3_ v4_ = v3_;
[FOO, FOO] = 2;
BAZ(FOO, BAR(v5_)) = BAZ(v5_, FOO) | SUCC(v5_);"
    );
}
