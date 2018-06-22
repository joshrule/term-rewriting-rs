extern crate term_rewriting;

use std::collections::HashMap;

use term_rewriting::*;

#[test]
fn term_substitute_test() {
    let (mut sig, _) = Signature::new(vec![
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
    let y = vars[0];
    let z = vars[1];
    let mut sub = HashMap::new();
    sub.insert(y, s_term);
    sub.insert(z, k_term);

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
    let (mut sig, ops) = Signature::new(vec![
        (2, Some(".".to_string())),
        (0, Some("S".to_string())),
        (0, Some("K".to_string())),
    ]);
    let a = ops[0];
    let s = ops[1];
    let k = ops[2];

    let sk = "S x_ y_ z_ = x_ z_ (y_ z_); K x_ y_ = x_;";
    let (trs1, _) = parse(&mut sig, sk).expect("parse of SK");

    let vars = sig.variables();
    let x = vars[0];
    let y = vars[1];
    let z = vars[2];
    let x2 = vars[3];
    let y2 = vars[4];

    let s_lhs = Term::Application {
        op: a,
        args: vec![
            Term::Application {
                op: a,
                args: vec![
                    Term::Application {
                        op: a,
                        args: vec![
                            Term::Application {
                                op: s,
                                args: vec![],
                            },
                            Term::Variable(x),
                        ],
                    },
                    Term::Variable(y),
                ],
            },
            Term::Variable(z),
        ],
    };
    let s_rhs = vec![Term::Application {
        op: a,
        args: vec![
            Term::Application {
                op: a,
                args: vec![Term::Variable(x), Term::Variable(z)],
            },
            Term::Application {
                op: a,
                args: vec![Term::Variable(y), Term::Variable(z)],
            },
        ],
    }];
    let s_rule = Rule::new(s_lhs, s_rhs).expect("new S rule");

    let k_lhs = Term::Application {
        op: a,
        args: vec![
            Term::Application {
                op: a,
                args: vec![
                    Term::Application {
                        op: k,
                        args: vec![],
                    },
                    Term::Variable(x2),
                ],
            },
            Term::Variable(y2),
        ],
    };
    let k_rhs = vec![Term::Variable(x2)];
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
    let y = vars[0];
    let z = vars[1];
    let y2 = vars[2];

    let mut hm1 = HashMap::new();
    hm1.insert(
        y,
        Term::Application {
            op: s,
            args: vec![],
        },
    );
    hm1.insert(
        z,
        Term::Application {
            op: k,
            args: vec![],
        },
    );
    assert_eq!(Some(hm1), Term::unify(vec![(t1.clone(), t2.clone())]));
    assert_eq!(None, Term::unify(vec![(t1.clone(), t3.clone())]));
    assert_eq!(None, Term::unify(vec![(t2.clone(), t3.clone())]));
    let mut hm2 = HashMap::new();
    hm2.insert(
        y2,
        Term::Application {
            op: a,
            args: vec![
                Term::Application {
                    op: a,
                    args: vec![
                        Term::Application {
                            op: k,
                            args: vec![],
                        },
                        Term::Application {
                            op: k,
                            args: vec![],
                        },
                    ],
                },
                Term::Application {
                    op: k,
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

    assert_eq!(trs.rewrite(&l_term), Some(vec![r_term]));
}

#[test]
fn display_variable() {
    let mut sig = Signature::default();

    let v1 = sig.new_var(None);
    let v2 = sig.new_var(Some("blah".to_string()));

    assert_eq!(v1.display(&sig), "var0_".to_string());
    assert_eq!(v1.name(&sig), None);
    assert_eq!(v2.display(&sig), "blah_".to_string());
    assert_eq!(v2.name(&sig), Some("blah"));
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
    let ns = term.display(&sig);
    assert_eq!(s, ns);
}

#[test]
fn parse_display_roundtrip_rule() {
    let mut sig = Signature::default();
    let s = "foo(bar(x_) y_ baz) = bar(y_) | buzz";
    let rule = parse_rule(&mut sig, s).unwrap_or_else(|_| panic!("parse of {}", s));
    let ns = rule.display(&sig);
    assert_eq!(s, ns);
}

#[test]
fn parse_display_roundtrip_trs() {
    let mut sig = Signature::default();
    let s = "foo(bar(x_) y_ baz) = bar(y_) | buzz;\nbar(baz) = foo(bar(baz) bar(baz) baz);";
    let trs = parse_trs(&mut sig, s).unwrap_or_else(|_| panic!("parse of {}", s));
    let ns = trs.display(&sig);
    assert_eq!(s, ns);
}
