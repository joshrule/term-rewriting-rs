use super::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hash;

#[test]
fn term_substitute_test() {
    // build some variables
    let y = Var::new(0, Some("y".to_string()));
    let z = Var::new(1, Some("z".to_string()));

    // build some operators
    let a = Op::new(0, 2, Some(".".to_string()));
    let s = Op::new(1, 0, Some("S".to_string()));
    let k = Op::new(2, 0, Some("K".to_string()));

    // build some terms
    let os = vec![a.clone(), s.clone(), k.clone()];
    let term_before = parse_term(&os, "S K y_ z_").expect("parse of S K y_ z_");
    let s_term = parse_term(&os, "S").expect("parse of S");
    let k_term = parse_term(&os, "K").expect("parse of K");

    // build a substitution
    let mut sub = HashMap::new();
    sub.insert(y, s_term);
    sub.insert(z, k_term);

    // build the term after substitution
    let term_after = parse_term(&os, "S K S K").expect("parse of 'S K S K'");

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
fn variable_show() {
    let v1 = Var { id: 7, name: None };
    let v2 = Var {
        id: 8,
        name: Some("blah".to_string()),
    };

    assert_eq!(v1.show(), "".to_string());
    assert_ne!(v1.show(), "blah".to_string());
    assert_ne!(v2.show(), "".to_string());
    assert_eq!(v2.show(), "blah".to_string());
}
#[test]
fn variable_eq() {
    let v1 = Var { id: 7, name: None };
    let v2 = Var { id: 8, name: None };
    let v3 = Var {
        id: 7,
        name: Some("blah".to_string()),
    };
    let v4 = Var { id: 7, name: None };

    assert_eq!(v1, v1);
    assert_ne!(v1, v2);
    assert_eq!(v1, v3);
    assert_eq!(v1, v4);
}
#[test]
fn variable_hash_eq() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();
    let v = Var { id: 7, name: None };
    7_usize.hash(&mut hasher1);
    v.hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}
#[test]
fn variable_hash_ne() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();
    let v = Var { id: 7, name: None };
    8_usize.hash(&mut hasher1);
    v.hash(&mut hasher2);

    assert_ne!(hasher1.finish(), hasher2.finish());
}

#[test]
fn rule_is_valid_yes() {
    let lhs: Term<Var, Op> = Term::Application {
        head: Op {
            arity: 0,
            id: 0,
            name: None,
        },
        args: vec![],
    };

    let rhs: Vec<Term<Var, Op>> = vec![Term::Application {
        head: Op {
            arity: 0,
            id: 1,
            name: None,
        },
        args: vec![],
    }];

    assert!(Rule::is_valid(&lhs, &rhs));
}
#[test]
fn rule_is_valid_lhs_var() {
    let lhs = Term::Variable(Var { name: None, id: 0 });

    let rhs = vec![Term::Application {
        head: Op {
            arity: 0,
            id: 1,
            name: None,
        },
        args: vec![],
    }];

    assert!(!Rule::is_valid(&lhs, &rhs));
}
#[test]
fn rule_is_valid_rhs_var() {
    let lhs = Term::Application {
        head: Op {
            arity: 0,
            id: 0,
            name: None,
        },
        args: vec![],
    };

    let rhs = vec![Term::Variable(Var { name: None, id: 0 })];

    assert!(!Rule::is_valid(&lhs, &rhs));
}
#[test]
fn rule_new_some() {
    let lhs: Term<Var, Op> = Term::Application {
        head: Op {
            arity: 0,
            id: 0,
            name: None,
        },
        args: vec![],
    };

    let rhs = vec![Term::Application {
        head: Op {
            arity: 0,
            id: 1,
            name: None,
        },
        args: vec![],
    }];

    let rule = Rule {
        lhs: lhs.clone(),
        rhs: rhs.clone(),
    };

    assert_eq!(Rule::new(lhs, rhs), Some(rule));
}
#[test]
fn rule_is_valid_none() {
    let lhs = Term::Application {
        head: Op {
            arity: 0,
            id: 0,
            name: None,
        },
        args: vec![],
    };

    let rhs = vec![Term::Variable(Var { name: None, id: 0 })];

    assert_eq!(Rule::new(lhs, rhs), None);
}

#[test]
fn signature_parse() {
    let sk = "S x_ y_ z_ = x_ z_ (y_ z_); K x_ y_ = x_;";

    let a = Op {
        id: 0,
        name: Some(".".to_string()),
        arity: 2,
    };
    let s = Op {
        id: 1,
        name: Some("S".to_string()),
        arity: 0,
    };
    let k = Op {
        id: 2,
        name: Some("K".to_string()),
        arity: 0,
    };
    let x = Var {
        id: 0,
        name: Some("x".to_string()),
    };
    let y = Var {
        id: 1,
        name: Some("y".to_string()),
    };
    let z = Var {
        id: 2,
        name: Some("z".to_string()),
    };
    let x2 = Var {
        id: 0,
        name: Some("x".to_string()),
    };
    let y2 = Var {
        id: 1,
        name: Some("y".to_string()),
    };

    let (trs1, _) = parse(&vec![a.clone(), s.clone(), k.clone()], sk).expect("parse of SK");

    let s_lhs = Term::Application {
        head: a.clone(),
        args: vec![
            Term::Application {
                head: a.clone(),
                args: vec![
                    Term::Application {
                        head: a.clone(),
                        args: vec![
                            Term::Application {
                                head: s.clone(),
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
        head: a.clone(),
        args: vec![
            Term::Application {
                head: a.clone(),
                args: vec![Term::Variable(x.clone()), Term::Variable(z.clone())],
            },
            Term::Application {
                head: a.clone(),
                args: vec![Term::Variable(y.clone()), Term::Variable(z.clone())],
            },
        ],
    }];
    let s_rule = Rule::new(s_lhs, s_rhs).expect("new S rule");

    let k_lhs = Term::Application {
        head: a.clone(),
        args: vec![
            Term::Application {
                head: a.clone(),
                args: vec![
                    Term::Application {
                        head: k.clone(),
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

    let trs2 = TRS {
        rules: vec![s_rule, k_rule],
    };

    assert_eq!(trs1, trs2);
}

#[test]
fn trs_new() {
    let trs1: TRS<Var, Op> = TRS::new(vec![]);
    let trs2 = TRS { rules: vec![] };
    assert_eq!(trs1, trs2);
}
#[test]
fn trs_debug() {
    let trs: TRS<Var, Op> = TRS::new(vec![]);
    assert_eq!(format!("{:?}", trs), "TRS { rules: [] }");
}

#[test]
fn unify_test() {
    // build some variables
    let y = Var::new(0, Some("y".to_string()));
    let z = Var::new(1, Some("z".to_string()));

    // build some operators
    let a = Op::new(0, 2, Some(".".to_string()));
    let s = Op::new(1, 0, Some("S".to_string()));
    let k = Op::new(2, 0, Some("K".to_string()));

    // build some terms
    let os = vec![a.clone(), s.clone(), k.clone()];
    let t1 = parse_term(&os, "S K y_ z_").expect("parse of S K y_ z_");
    let t2 = parse_term(&os, "S K S K").expect("parse of S K S K");
    let t3 = parse_term(&os, "K K K K").expect("parse of K K K K");
    let t4 = parse_term(&os, "y_ K").expect("parse of y_ K");

    let mut hm1 = HashMap::new();
    hm1.insert(
        y.clone(),
        Term::Application {
            head: s.clone(),
            args: vec![],
        },
    );
    hm1.insert(
        z.clone(),
        Term::Application {
            head: k.clone(),
            args: vec![],
        },
    );
    assert_eq!(Some(hm1), Term::unify(vec![(t1.clone(), t2.clone())]));
    assert_eq!(None, Term::unify(vec![(t1.clone(), t3.clone())]));
    assert_eq!(None, Term::unify(vec![(t2.clone(), t3.clone())]));
    let mut hm2 = HashMap::new();
    hm2.insert(
        y.clone(),
        Term::Application {
            head: a.clone(),
            args: vec![
                Term::Application {
                    head: a.clone(),
                    args: vec![
                        Term::Application {
                            head: k.clone(),
                            args: vec![],
                        },
                        Term::Application {
                            head: k.clone(),
                            args: vec![],
                        },
                    ],
                },
                Term::Application {
                    head: k.clone(),
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

    let (trs, terms) = parse(&vec![], &(s_str.to_owned() + k_str + l_str + r_str)).expect("parse");
    let l_term = &terms[0];
    let r_term = terms[1].clone();

    assert_eq!(trs.rewrite(&l_term), Some(vec![r_term]));
}
