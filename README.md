[![Build
Status](https://travis-ci.org/joshrule/term-rewriting-rs.svg?branch=develop)](https://travis-ci.org/joshrule/term-rewriting-rs)

# [term-rewriting-rs][0]

A [Rust][1] library for representing and parsing first-order [term rewriting systems][2].

## Usage

To include as a dependency:

```toml
[dependencies]
term-rewriting = "0.1"
```

To actually make use of the library:

```rust
    extern crate term_rewriting;
    use term_rewriting::types::*;

    fn main() {
    // A string representation of SK combinatory logic, including:

    // a rule for the S combinator,
    let s_rule = "S x_ y_ z_ = (x_ z_) (y_ z_);".to_string();

    // the rule for the K combinator,
    let k_rule = "K x_ y_ = x_;";

    // and an arbitrary term,
    let term = "S K K (K S K);";

    // can be parsed to give back the TRS and a term.
    let mut sig = Signature::default();
    let (parsed_trs, parsed_term_vec) = sig.parse(&(s_rule + k_rule + term)).expect("successful parse");

    // These can also be constructed by hand. Let's look at the term:
    let mut sig = Signature::default();
    let app = sig.get_op(".", 2);
    let s = sig.get_op("S", 0);
    let k = sig.get_op("K", 0);

    let term = Term::Application {
        head: app.clone(),
        args: vec![
            Term::Application {
                head: app.clone(),
                args: vec![
                    Term::Application {
                        head: app.clone(),
                        args: vec![
                            Term::Application { head: s.clone(), args: vec![] },
                            Term::Application { head: k.clone(), args: vec![] },
                        ]
                    },
                    Term::Application { head: k.clone(), args: vec![] }
                ]
            },
            Term::Application {
                head: app.clone(),
                args: vec![
                    Term::Application {
                        head: app.clone(),
                        args: vec![
                            Term::Application { head: k.clone(), args: vec![] },
                            Term::Application { head: s.clone(), args: vec![] },
                        ]
                    },
                    Term::Application { head: k.clone(), args: vec![] }
                ]
            }
        ]
    };

    let constructed_term_vec = vec![term];

    // This is the same output the parser produces.
    assert_eq!(parsed_term_vec, constructed_term_vec);
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
