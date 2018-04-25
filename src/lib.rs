//! A [Rust][0] library for representing and parsing first-order [term rewriting systems][1].
//!
//! # Example
//!
//! ```
//! # extern crate term_rewriting;
//! use term_rewriting::types::*;
//!
//! # fn main() {
//! // We can parse a string representation of SK combinatory logic,
//! let sk_rules = "S x_ y_ z_ = (x_ z_) (y_ z_); K x_ y_ = x_;";
//! let parsed_trs = parse_trs(&vec![], sk_rules).expect("parsed TRS");
//!
//! // and we can also parse an arbitrary term.
//! let term = "S K K (K S K)";
//! let parsed_term = parse_term(&vec![], term).expect("parsed term");
//!
//! // These can also be constructed by hand. Let's look at the term:
//! let app = Op::new(0, 2, Some(".".to_string()));
//! let s = Op::new(1, 0, Some("S".to_string()));
//! let k = Op::new(2, 0, Some("K".to_string()));
//!
//! let constructed_term = Term::Application {
//!     head: app.clone(),
//!     args: vec![
//!         Term::Application {
//!             head: app.clone(),
//!             args: vec![
//!                 Term::Application {
//!                     head: app.clone(),
//!                     args: vec![
//!                         Term::Application { head: s.clone(), args: vec![] },
//!                         Term::Application { head: k.clone(), args: vec![] },
//!                     ]
//!                 },
//!                 Term::Application { head: k.clone(), args: vec![] }
//!             ]
//!         },
//!         Term::Application {
//!             head: app.clone(),
//!             args: vec![
//!                 Term::Application {
//!                     head: app.clone(),
//!                     args: vec![
//!                         Term::Application { head: k.clone(), args: vec![] },
//!                         Term::Application { head: s.clone(), args: vec![] },
//!                     ]
//!                 },
//!                 Term::Application { head: k.clone(), args: vec![] }
//!             ]
//!         }
//!     ]
//! };
//!
//! // This is the same output the parser produces.
//! assert_eq!(parsed_term, constructed_term);
//! # }
//! ```
//!
//! # Term Rewriting Systems
//!
//! Term Rewriting Systems (TRS) are a simple formalism from theoretical
//! computer science used to model the behavior and evolution of tree-based
//! structures like natural langauge parse trees or abstract syntax trees.
//!
//! A TRS is defined as a pair _(S, R)_. _S_ is a set of symbols called the
//! signature and together with a disjoint and countably infinite set of
//! variables, defines the set of all possible trees, or terms, which the system
//! can consider. _R_ is a set of rewrite rules. A rewrite rule is an equation,
//! _s = t_, and is interpreted as follows: any term matching the pattern
//! described by _s_ can be rewritten according to the pattern described by _t_.
//! Together _S_ and _R_ define a TRS that describes a system of computation,
//! which can be considered as a sort of programming language.
//! `term_rewriting` provides a way to describe arbitrary first-order TRSs
//! (i.e. no lambda-binding in rules).
//!
//! ### Further Reading
//!
//! - Baader & Nipkow (1999). [Term rewriting and all that][2]. Cambridge University Press.
//! - Bezem, Klop, & de Vrijer (Eds.) (2003). [Term Rewriting Systems][3]. Cambridge University Press.
//! - [Rewriting][4]. (2017). Wikipedia.
//!
//! [0]: https://www.rust-lang.org
//!      "The Rust Programming Language"
//! [1]: https://en.wikipedia.org/wiki/Rewriting#Term_rewriting_systems
//!      "Wikipedia - Term Rewriting Systems"
//! [2]: http://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/term-rewriting-and-all
//!      "Term Rewriting and All That"
//! [3]: http://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/term-rewriting-systems
//!      "Term Rewriting Systems"
//! [4]: https://en.wikipedia.org/wiki/Rewriting
//!      "Wikipedia - Rewriting"

#[macro_use]
extern crate nom;
extern crate itertools;

mod parser;
pub mod types;
