extern crate criterion;
extern crate term_rewriting;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use term_rewriting::{parse_context, parse_rulecontext, parse_trs, Rule, Signature, Term};

pub fn rulecontext_replace_benchmark(c: &mut Criterion) {
    let mut sig = Signature::default();

    let rctx = parse_rulecontext(&mut sig, "A(v0_) = C(A([!] [!])) | C(v0_) | [!]").expect("rctx");
    let ctx = parse_context(&mut sig, "E [!]").expect("ctx");

    c.bench_function("rulecontext_replace", |b| {
        b.iter(|| black_box(&rctx).replace(black_box(&[1, 0, 0, 1]), black_box(ctx.clone())))
    });
}

pub fn rulecontext_subcontexts_benchmark(c: &mut Criterion) {
    let mut sig = Signature::default();

    let rctx =
        parse_rulecontext(&mut sig, "A(v0_) = C(A([!] [!])) | C(v0_) | B(v0_ [!])").expect("rctx");

    c.bench_function("rulecontext_subcontexts", |b| {
        b.iter(|| black_box(&rctx).subcontexts())
    });
}

criterion_group!(
    rule,
    rulecontext_replace_benchmark,
    rulecontext_subcontexts_benchmark
);
criterion_main!(rule);
