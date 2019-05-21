# [term-rewriting-rs][0]

[![Travis-CI.org](https://img.shields.io/travis/joshrule/term-rewriting-rs.svg?maxAge=3600)](https://travis-ci.org/joshrule/term-rewriting-rs)
[![Crates.io](https://img.shields.io/crates/v/term_rewriting.svg?maxAge=3600)](https://crates.io/crates/term_rewriting)
[![Codecov](https://img.shields.io/codecov/c/github/joshrule/term-rewriting-rs.svg?maxAge=3600)](https://codecov.io/gh/joshrule/term-rewriting-rs)
[![docs.rs](https://docs.rs/term_rewriting/badge.svg)](https://docs.rs/term_rewriting)

A [Rust][1] library for representing, parsing, and computing with first-order [term rewriting systems][2].

## Usage

To include as a dependency:

```toml
[dependencies]
term_rewriting = "0.7"
```

To actually make use of the library:

```rust
extern crate term_rewriting;
use term_rewriting::{Signature, Term, parse_trs, parse_term};

fn main() {
    // We can parse a string representation of SK combinatory logic,
    let mut sig = Signature::default();
    let sk_rules = "S x_ y_ z_ = (x_ z_) (y_ z_); K x_ y_ = x_;";
    let trs = parse_trs(&mut sig, sk_rules).expect("parsed TRS");

    // and we can also parse an arbitrary term.
    let mut sig = Signature::default();
    let term = "S K K (K S K)";
    let parsed_term = parse_term(&mut sig, term).expect("parsed term");

    // These can also be constructed by hand.
    let mut sig = Signature::default();
    let app = sig.new_op(2, Some(".".to_string()));
    let s = sig.new_op(0, Some("S".to_string()));
    let k = sig.new_op(0, Some("K".to_string()));

    let constructed_term = Term::Application {
        op: app,
        args: vec![
            Term::Application {
                op: app,
                args: vec![
                    Term::Application {
                        op: app,
                        args: vec![
                            Term::Application { op: s, args: vec![] },
                            Term::Application { op: k, args: vec![] },
                        ]
                    },
                    Term::Application { op: k, args: vec![] }
                ]
            },
            Term::Application {
                op: app,
                args: vec![
                    Term::Application {
                        op: app,
                        args: vec![
                            Term::Application { op: k, args: vec![] },
                            Term::Application { op: s, args: vec![] },
                        ]
                    },
                    Term::Application { op: k, args: vec![] }
                ]
            }
        ]
    };

    // This is the same output the parser produces.
    assert_eq!(parsed_term, constructed_term);
}
```

## Term Rewriting Systems

Term Rewriting Systems (TRS) are a simple formalism from theoretical computer science used to model the behavior and evolution of tree-based structures like natural langauge parse trees or abstract syntax trees.

A TRS is defined as a pair _(S, R)_. _S_ is a set of symbols called the signature and together with a disjoint and countably infinite set of variables, defines the set of all possible trees, or terms, which the system can consider. _R_ is a set of rewrite rules. A rewrite rule is an equation, _s = t_, and is interpreted as follows: any term matching the pattern described by _s_ can be rewritten according to the pattern described by _t_. Together _S_ and _R_ define a TRS that describes a system of computation, which can be considered as a sort of programming language. term-rewriting-rs provides a way to describe arbitrary first-order TRSs (i.e. no λ-binding in rules).

### Further Reading

- Baader & Nipkow (1999). [Term rewriting and all that][ref.1]. Cambridge University Press.
- Bezem, Klop, & de Vrijer (Eds.) (2003). [Term Rewriting Systems][ref.2]. Cambridge University Press.
- [Rewriting][ref.3]. (2017). Wikipedia.

[0]: https://github.com/joshrule/term-rewriting-rs
     "term-rewriting-rs"
[1]: https://www.rust-lang.org
     "The Rust Programming Language"
[2]: https://en.wikipedia.org/wiki/Rewriting#Term_rewriting_systems
     "Wikipedia - Term Rewriting Systems"
[ref.1]: http://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/term-rewriting-and-all
     "Term Rewriting and All That"
[ref.2]: http://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/term-rewriting-systems
     "Term Rewriting Systems"
[ref.3]: https://en.wikipedia.org/wiki/Rewriting
     "Wikipedia - Rewriting"
