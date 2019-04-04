//! A [Rust][0] library for representing, parsing, and computing with first-order [term rewriting systems][1].
//!
//! # Usage
//!
//! ```toml
//! [dependencies]
//! term_rewriting = "0.5"
//! ```
//!
//! # Example
//!
//! ```
//! use term_rewriting::{Signature, Term, parse_trs, parse_term};
//!
//! // We can parse a string representation of SK combinatory logic,
//! let mut sig = Signature::default();
//! let sk_rules = "S x_ y_ z_ = (x_ z_) (y_ z_); K x_ y_ = x_;";
//! let trs = parse_trs(&mut sig, sk_rules).expect("parsed TRS");
//!
//! // and we can also parse an arbitrary term.
//! let mut sig = Signature::default();
//! let term = "S K K (K S K)";
//! let parsed_term = parse_term(&mut sig, term).expect("parsed term");
//!
//! // These can also be constructed by hand.
//! let mut sig = Signature::default();
//! let s = sig.new_op(0, Some("S".to_string()));
//! let k = sig.new_op(0, Some("K".to_string()));
//! let app = sig.new_op(2, Some(".".to_string()));
//!
//! let constructed_term = Term::Application {
//!     op: app.clone(),
//!     args: vec![
//!         Term::Application {
//!             op: app.clone(),
//!             args: vec![
//!                 Term::Application {
//!                     op: app.clone(),
//!                     args: vec![
//!                         Term::Application { op: s.clone(), args: vec![] },
//!                         Term::Application { op: k.clone(), args: vec![] },
//!                     ]
//!                 },
//!                 Term::Application { op: k.clone(), args: vec![] }
//!             ]
//!         },
//!         Term::Application {
//!             op: app.clone(),
//!             args: vec![
//!                 Term::Application {
//!                     op: app.clone(),
//!                     args: vec![
//!                         Term::Application { op: k.clone(), args: vec![] },
//!                         Term::Application { op: s.clone(), args: vec![] },
//!                     ]
//!                 },
//!                 Term::Application { op: k.clone(), args: vec![] }
//!             ]
//!         }
//!     ]
//! };
//!
//! // This is the same output the parser produces.
//! assert_eq!(parsed_term, constructed_term);
//! ```
//!
//! # TRS syntax
//!
//! Several functions are available which parse TRS-related data structures
//! according to the following grammar (defined in [augmented Backus-Naur form]):
//!
//! - [`parse`]: a [`TRS`] and list of [`Term`s] (`program`)
//! - [`parse_trs`]: a [`TRS`] (`trs`)
//! - [`parse_term`]: a [`Term`] (`top-level-term`)
//! - [`parse_rule`]: a [`Rule`] (`rule`)
//! - [`parse_context`]: a [`Context`] (`top-level-context`)
//! - [`parse_rulecontext`]: a [`RuleContext`] (`rulecontext`)
//!
//! ```text
//! program = *wsp *( *comment statement ";" *comment ) *wsp
//!
//! statement = rule / top-level-term
//!
//! rule = top-level-term *wsp "=" *wsp top-level-term
//! rule /= rule *wsp "|" *wsp top-level-term
//!
//! top-level-term = term
//! top-level-term /= top-level-term 1*wsp top-level-term
//!
//! term = variable
//! term /= application
//! term /= "(" *wsp top-level-term *wsp ")"
//!
//! rulecontext = top-level-term *wsp "=" *wsp top-level-term
//! rulecontext /= rule *wsp "|" *wsp top-level-term
//!
//! top-level-context = context
//! top-level-context /= top-level-context 1*wsp top-level-context
//!
//! context = variable
//! context /= application
//! context /= hole
//! context /= "(" *wsp top-level-context *wsp ")"
//!
//! hole = "[!]"
//!
//! variable = identifier"_"
//!
//! application = identifier "(" [ term *( 1*wsp term ) ] ")"
//! application /= identifier
//! application /= binary-application
//!
//! ; binary application is the '.' operator with arity 2.
//! binary-application = "(" *wsp term *wsp term *wsp ")"
//!
//! identifier = 1*( ALPHA / DIGIT )
//!
//! comment = "#" *any-char-but-newline "\n"
//!
//! wsp = SP / TAB / CR / LF
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
//! [augmented Backus-Naur form]: https://en.wikipedia.org/wiki/Augmented_Backus–Naur_form
//! [`parse`]: fn.parse.html
//! [`parse_trs`]: fn.parse_trs.html
//! [`parse_term`]: fn.parse_term.html
//! [`parse_rule`]: fn.parse_rule.html
//! [`parse_context`]: fn.parse_context.html
//! [`parse_rulecontext`]: fn.parse_rulecontext.html
//! [`TRS`]: struct.TRS.html
//! [`Term`s]: enum.Term.html
//! [`Term`]: enum.Term.html
//! [`Rule`]: struct.Rule.html
//! [`Context`]: enum.Context.html
//! [`RuleContext`]: struct.RuleContext.html

extern crate itertools;
#[macro_use]
extern crate nom;
extern crate rand;

mod parser;
mod pretty;
pub mod trace;
mod types;

pub use parser::{
    parse, parse_context, parse_rule, parse_rulecontext, parse_term, parse_trs, ParseError,
};
pub use types::*;
