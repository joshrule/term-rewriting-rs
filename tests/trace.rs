extern crate term_rewriting;

use term_rewriting::{trace::*, *};

#[test]
fn trace_step() {
    let mut sig = Signature::default();
    let inp = "
        PLUS(SUCC(x_) y_) = PLUS(x_ SUCC(y_));
        PLUS(ZERO x_) = x_;

        PLUS(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO));"
        .trim();
    let (trs, mut terms) = parse(&mut sig, inp).unwrap();
    let mut term = terms.pop().unwrap();
    let mut trace = Trace::new(&trs, &term, 0.2, None);
    let expected = vec!["PLUS(3, 1)", "PLUS(2, 2)", "PLUS(1, 3)", "PLUS(0, 4)", "4"];
    let mut node;
    for x in expected {
        node = trace
            .next()
            .unwrap_or_else(|| panic!("trace step from {} unsuccessful", term.pretty()));
        term = node.term();
        assert_eq!(term.pretty(), x)
    }
    assert!(trace.next().is_none());
}

#[test]
fn trace_rewrite() {
    let mut sig = Signature::default();
    let inp = "
        PLUS(SUCC(x_) y_) = PLUS(x_ SUCC(y_));
        PLUS(ZERO x_) = x_;

        PLUS(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO));"
        .trim();
    let (trs, mut terms) = parse(&mut sig, inp).unwrap();
    let term = terms.pop().unwrap();
    let mut trace = Trace::new(&trs, &term, 0.2, None);
    trace.rewrite(3);

    // leaves
    let leaf_terms_unobserved = trace.root().leaf_terms(&[TraceState::Unobserved]);
    assert_eq!(leaf_terms_unobserved.len(), 1);
    assert_eq!(leaf_terms_unobserved[0].pretty(), "PLUS(0, 4)");
    let leaf_terms_other = trace.root().leaf_terms(&[
        TraceState::Normal,
        TraceState::Rewritten,
        TraceState::TooBig,
    ]);
    assert!(leaf_terms_other.is_empty());

    // all progeny
    assert!(
        trace
            .root()
            .progeny(&[TraceState::Normal, TraceState::TooBig])
            .is_empty()
    );
    let terms_r = trace
        .root()
        .progeny(&[TraceState::Rewritten])
        .into_iter()
        .map(|n| n.term())
        .collect::<Vec<_>>();
    assert_eq!(terms_r.len(), 3);
    assert_eq!(terms_r[0].pretty(), "PLUS(3, 1)");
    assert_eq!(terms_r[1].pretty(), "PLUS(2, 2)");
    assert_eq!(terms_r[2].pretty(), "PLUS(1, 3)");
    let terms_u = trace
        .root()
        .progeny(&[TraceState::Unobserved])
        .into_iter()
        .map(|n| n.term())
        .collect::<Vec<_>>();
    assert_eq!(terms_u.len(), 1);
    assert_eq!(terms_u[0].pretty(), "PLUS(0, 4)");
}
