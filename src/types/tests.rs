use std::collections::hash_map::DefaultHasher;
use std::hash::Hash;
use super::*;

#[test]
fn variable_name() {
    let v1 = Variable { id: 7, name: None };
    let v2 = Variable {
        id: 8,
        name: Some("blah".to_string()),
    };

    assert_eq!(v1.name(), &None);
    assert_ne!(v1.name(), &Some("blah".to_string()));
    assert_ne!(v2.name(), &None);
    assert_eq!(v2.name(), &Some("blah".to_string()));
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

    let rhs = vec![
        Term::Application {
            head: Operator {
                arity: 0,
                id: 1,
                name: None,
            },
            args: vec![],
        },
    ];

    assert!(Rule::is_valid(&lhs, &rhs));
}
#[test]
fn rule_is_valid_lhs_var() {
    let lhs = Term::Variable(Variable { name: None, id: 0 });

    let rhs = vec![
        Term::Application {
            head: Operator {
                arity: 0,
                id: 1,
                name: None,
            },
            args: vec![],
        },
    ];

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

    let rhs = vec![
        Term::Application {
            head: Operator {
                arity: 0,
                id: 1,
                name: None,
            },
            args: vec![],
        },
    ];

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
    let s_rhs = vec![
        Term::Application {
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
        },
    ];
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
