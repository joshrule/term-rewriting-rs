extern crate criterion;
extern crate term_rewriting;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use term_rewriting::{
    parse_term, parse_trs, trace::Trace, Signature, Strategy, Substitution, Term,
};

pub fn term_rewrite_benchmark(c: &mut Criterion) {
    let mut sig = Signature::default();

    let trs = parse_trs(&mut sig, "A = B; C = D | E; F(x_) = G;").expect("parsed TRS");
    let term = parse_term(&mut sig, "J(I(v0_ G) K(F(C) A))").expect("parse of J(F(C) K(C A))");

    c.bench_function("rewrite_normal", |b| {
        b.iter(|| {
            black_box(&trs)
                .rewrite(
                    black_box(&term),
                    black_box(Strategy::Normal),
                    black_box(&sig),
                )
                .count()
        })
    });
}

pub fn term_unify_benchmark(c: &mut Criterion) {
    let mut sig = Signature::default();
    let t1 =
        parse_term(&mut sig, "A(A(C(A(B v0_)) A(v1_ v2_)) C(A(v3_ C(B))))").expect("parse of t1");
    let t2 = parse_term(
        &mut sig,
        "A(A(C(A(v4_ C(A(v5_ v6_)))) A(C(A(B v7_)) A(B C(B)))) C(A(B v8_)))",
    )
    .expect("parse of t2");

    let ts = vec![(&t1, &t2)];

    c.bench_function("unify", |b| b.iter(|| Term::unify(black_box(&ts))));
}

pub fn term_substitute_benchmark(c: &mut Criterion) {
    let mut sig = Signature::default();
    let term = parse_term(&mut sig, "S (v0_ v1_) (v2_ (v1_ v0_)) v3_").expect("parsed term");
    let s = parse_term(&mut sig, "S").expect("parsed s");
    let k = parse_term(&mut sig, "K").expect("parsed k");
    let sk = parse_term(&mut sig, "S K").expect("parsed sk");
    let kk = parse_term(&mut sig, "S K").expect("parsed kk");

    let vars = term.variables();

    let sub = Substitution(vec![
        (&vars[0], &s),
        (&vars[1], &k),
        (&vars[2], &sk),
        (&vars[3], &kk),
    ]);

    c.bench_function("substitute", |b| {
        b.iter(|| black_box(&term).substitute(black_box(&sub)))
    });
}

pub fn term_trace_benchmark(c: &mut Criterion) {
    let mut sig = Signature::default();
    let trs_str =
        "PLUS(SUCC(v0_) v1_) = PLUS(v0_ SUCC(v1_)) | SUCC(PLUS(v0_ v1_)); PLUS(ZERO v2_) = v2_;";
    let trs = parse_trs(&mut sig, trs_str).expect("parsed trs");
    let input_str = "PLUS(SUCC(SUCC(SUCC(ZERO))) PLUS(SUCC(ZERO) ZERO))";
    let input = parse_term(&mut sig, input_str).expect("parsed input");

    c.bench_function("trace", |b| {
        b.iter_with_large_drop(|| {
            Trace::new(
                black_box(&trs),
                black_box(&sig),
                black_box(&input),
                black_box(0.5),
                black_box(50),
                black_box(None),
                black_box(Strategy::Normal),
            )
        })
    });
}

criterion_group!(
    term,
    term_unify_benchmark,
    term_substitute_benchmark,
    term_rewrite_benchmark,
    term_trace_benchmark,
);
criterion_main!(term);
