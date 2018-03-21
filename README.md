# term-rewriting-rs

A [Rust][1] library for parsing, representing, and computing with first-order term rewriting systems.

## Usage

```toml
[dependencies]
term-rewriting = { git = "https://github.com/joshrule/term-rewriting-rs" }
```

## Term Rewriting Systems

Term Rewriting Systems (TRS) are a simple formalism from theoretical computer science used to model the behavior and evolution of tree-based structures like natural langauge parse trees or abstract syntax trees.

A TRS is defined as a pair _(S, R)_. _S_ is a set of symbols called the signature and together with a disjoint and countably infinite set of variables, defines the set of all possible trees, or terms, which the system can consider. _R_ is a set of rewrite rules. A rewrite rule is an equation, _s = t_, and is interpreted as follows: any term matching the pattern described by _s_ can be rewritten according to the pattern described by _t_. Together _S_ and _R_ define a TRS that describes a system of computation, which can be considered as a sort of programming language. term-rewriting-rs provides a way to describe arbitrary first-order TRSs (i.e. no lambda-binding in rules).

### Further Reading

- Baader & Nipkow (1999). [Term rewriting and all that][2]. Cambridge University Press.
- Bezem, Klop, & de Vrijer (Eds.) (2003). [Term Rewriting Systems][3]. Cambridge University Press.
- [Rewriting][4]. (2017). Wikipedia.


[1]: https://www.rust-lang.org
     "The Rust Programming Language"
[2]: http://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/term-rewriting-and-all
     "Term Rewriting and All That"
[3]: http://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/term-rewriting-systems
     "Term Rewriting Systems"
[4]: https://en.wikipedia.org/wiki/Rewriting
     "Wikipedia - Rewriting"
