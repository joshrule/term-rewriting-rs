use super::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hash;

#[test]
fn term_substitute_test() {
    let mut sig = Signature::default();
    let y = sig.get_var("y");
    let z = sig.get_var("z");

    // build a term
    let s_before = "S K y_ z_;";
    let (_, terms) = sig.parse(s_before).expect("parse of S x_ y_ z_");
    let term_before = terms[0].clone();

    // build a substitution
    let s = sig.get_op("S", 0);
    let s_term = Term::Application {
        head: s,
        args: vec![],
    };
    let k = sig.get_op("K", 0);
    let k_term = Term::Application {
        head: k,
        args: vec![],
    };
    let mut sub = HashMap::new();
    sub.insert(y, s_term);
    sub.insert(z, k_term);

    // build the term after substitution
    let s_after = "S K S K;";
    let (_, terms) = sig.parse(s_after).expect("parse of 'S K S K'");
    let term_after = terms[0].clone();

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
    let v1 = Variable { id: 7, name: None };
    let v2 = Variable {
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
    let v1 = Variable { id: 7, name: None };
    let v2 = Variable { id: 8, name: None };
    let v3 = Variable {
        id: 7,
        name: Some("blah".to_string()),
    };
    let v4 = Variable { id: 7, name: None };

    assert_eq!(v1, v1);
    assert_ne!(v1, v2);
    assert_eq!(v1, v3);
    assert_eq!(v1, v4);
}
#[test]
fn variable_hash_eq() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();
    let v = Variable { id: 7, name: None };
    7_usize.hash(&mut hasher1);
    v.hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}
#[test]
fn variable_hash_ne() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();
    let v = Variable { id: 7, name: None };
    8_usize.hash(&mut hasher1);
    v.hash(&mut hasher2);

    assert_ne!(hasher1.finish(), hasher2.finish());
}

#[test]
fn rule_is_valid_yes() {
    let lhs = Term::Application {
        head: Operator {
            arity: 0,
            id: 0,
            name: None,
        },
        args: vec![],
    };

    let rhs = vec![Term::Application {
        head: Operator {
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
    let lhs = Term::Variable(Variable { name: None, id: 0 });

    let rhs = vec![Term::Application {
        head: Operator {
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
        head: Operator {
            arity: 0,
            id: 0,
            name: None,
        },
        args: vec![],
    };

    let rhs = vec![Term::Variable(Variable { name: None, id: 0 })];

    assert!(!Rule::is_valid(&lhs, &rhs));
}
#[test]
fn rule_new_some() {
    let lhs = Term::Application {
        head: Operator {
            arity: 0,
            id: 0,
            name: None,
        },
        args: vec![],
    };

    let rhs = vec![Term::Application {
        head: Operator {
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
        head: Operator {
            arity: 0,
            id: 0,
            name: None,
        },
        args: vec![],
    };

    let rhs = vec![Term::Variable(Variable { name: None, id: 0 })];

    assert_eq!(Rule::new(lhs, rhs), None);
}

#[test]
fn signature_debug() {
    let sig = Signature::default();
    assert_eq!(
        format!("{:?}", sig),
        "Signature { operators: [], variables: [], operator_count: 0, variable_count: 0 }"
    );
}
#[test]
fn signature_parse() {
    let mut sig = Signature::default();
    let sk = "S x_ y_ z_ = x_ z_ (y_ z_); K x_ y_ = x_;";

    let a = Operator {
        id: 0,
        name: Some(".".to_string()),
        arity: 2,
    };
    let s = Operator {
        id: 1,
        name: Some("S".to_string()),
        arity: 0,
    };
    let k = Operator {
        id: 2,
        name: Some("K".to_string()),
        arity: 0,
    };
    let x = Variable {
        id: 0,
        name: Some("x".to_string()),
    };
    let y = Variable {
        id: 1,
        name: Some("y".to_string()),
    };
    let z = Variable {
        id: 2,
        name: Some("z".to_string()),
    };
    let x2 = Variable {
        id: 3,
        name: Some("x".to_string()),
    };
    let y2 = Variable {
        id: 4,
        name: Some("y".to_string()),
    };

    let (trs1, _) = sig.parse(sk).expect("parse of SK");

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
    let trs1 = TRS::new(vec![]);
    let trs2 = TRS { rules: vec![] };
    assert_eq!(trs1, trs2);
}
#[test]
fn trs_debug() {
    let trs = TRS::new(vec![]);
    assert_eq!(format!("{:?}", trs), "TRS { rules: [] }");
}

#[test]
fn unify_test() {
    let mut sig = Signature::default();

    // build a term
    let s_t1 = "S K y_ z_;";
    let (_, terms) = sig.parse(s_t1).expect("parse of S K y_ z_");
    let t1 = terms[0].clone();

    // build another term
    let s_t2 = "S K S K;";
    let (_, terms) = sig.parse(s_t2).expect("parse of S K S K");
    let t2 = terms[0].clone();

    // build another term
    let s_t3 = "K K K K;";
    let (_, terms) = sig.parse(s_t3).expect("parse of K K K K");
    let t3 = terms[0].clone();

    // build another term
    let mut sig = Signature::default();
    let y = sig.get_var("y");
    let z = sig.get_var("z");
    let a = sig.get_op(".", 2);
    let s = sig.get_op("S", 0);
    let k = sig.get_op("K", 0);
    let s_t4 = "y_ K;";
    let (_, terms) = sig.parse(s_t4).expect("parse of y_ K");
    let t4 = terms[0].clone();

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
    let mut sig = Signature::default();

    // build a term
    let s_str = "S x_ y_ z_ = x_ z_ (y_ z_);";
    let k_str = "K x_ y_ = x_;";
    let l_str = "K S K;";
    let r_str = "S;";

    let (trs, terms) = sig.parse(&(s_str.to_owned() + k_str + l_str + r_str))
        .expect("parse");
    let l_term = &terms[0];
    let r_term = terms[1].clone();

    assert_eq!(trs.rewrite(&l_term), Some(vec![r_term]));
}
