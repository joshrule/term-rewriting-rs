use super::types::*;

use nom::types::CompleteStr;
use nom::{multispace0, multispace1};
use std::fmt;

named!(lparen<CompleteStr, CompleteStr>,     tag!("("));
named!(rparen<CompleteStr, CompleteStr>,     tag!(")"));
named!(pipe<CompleteStr, CompleteStr>,       tag!("|"));
named!(semicolon<CompleteStr, CompleteStr>,  tag!(";"));
named!(rule_kw<CompleteStr, CompleteStr>,    tag!("="));
named!(underscore<CompleteStr, CompleteStr>, tag!("_"));
named!(identifier<CompleteStr, CompleteStr>, is_not!("[!]| #_:()=;"));

#[derive(Debug, PartialEq)]
/// The error type for parsing operations.
pub enum ParseError {
    ParseIncomplete,
    ParseFailed,
}
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParseError::ParseIncomplete => write!(f, "incomplete parse"),
            ParseError::ParseFailed => write!(f, "failed parse"),
        }
    }
}
impl ::std::error::Error for ParseError {
    fn description(&self) -> &'static str {
        "parse error"
    }
}

/// Parse a string as a [`TRS`] and a list of [`Term`]s.
///
/// ```
/// # use term_rewriting::{Signature, parse};
/// let inp = "
/// #-- rules:
///     S x_ y_ z_ = x_ z_ (y_ z_);
///     K x_ y_ = x_;
///     PLUS(SUCC(x_) y_) = PLUS(x_ SUCC(y_));
///     PLUS(ZERO y_) = y_;
///
/// #-- terms:
///     S K S K;
///     PLUS(SUCC(SUCC(SUCC(ZERO))) SUCC(ZERO));
/// ";
/// let (trs, terms) = parse(&mut Signature::default(), inp).unwrap();
/// ```
///
/// [`TRS`]: struct.TRS.html
/// [`Term`]: enum.Term.html
pub fn parse(sig: &mut Signature, input: &str) -> Result<(TRS, Vec<Term>), ParseError> {
    let (_parser, result) = Parser::new(sig).program(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), stmts)) => {
            let mut terms = Vec::new();
            let mut rules = Vec::new();
            for stmt in stmts {
                match stmt {
                    Statement::Term(t) => terms.push(t),
                    Statement::Rule(r) => rules.push(r),
                }
            }
            Ok((TRS::new(rules), terms))
        }
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

/// Parse a string as a [`TRS`].
///
/// [`TRS`]: struct.TRS.html
pub fn parse_trs(sig: &mut Signature, input: &str) -> Result<TRS, ParseError> {
    let (_parser, result) = Parser::new(sig).trs(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), trs)) => Ok(trs),
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

/// Parse a string as a [`Rule`].
///
/// [`Rule`]: struct.Rule.html
pub fn parse_rule(sig: &mut Signature, input: &str) -> Result<Rule, ParseError> {
    let (_parser, result) = Parser::new(sig).rule(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), rule)) => Ok(rule),
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

/// Parse a string as a [`Term`].
///
/// [`Term`]: enum.Term.html
pub fn parse_term(sig: &mut Signature, input: &str) -> Result<Term, ParseError> {
    let (_parser, result) = Parser::new(sig).top_term(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), t)) => Ok(t),
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

/// Parse a string as a [`RuleContext`].
///
/// [`RuleContext`]: struct.RuleContext.html
pub fn parse_rulecontext(sig: &mut Signature, input: &str) -> Result<RuleContext, ParseError> {
    let (_parser, result) = Parser::new(sig).rulecontext(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), r)) => Ok(r),
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

/// Parse a string as a [`Context`].
///
/// [`Context`]: enum.Context.html
pub fn parse_context(sig: &mut Signature, input: &str) -> Result<Context, ParseError> {
    let (_parser, result) = Parser::new(sig).top_context(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), c)) => Ok(c),
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Term(Term),
    Rule(Rule),
}

#[derive(Debug)]
pub struct Parser<'a> {
    sig: &'a mut Signature,
    dv: usize,
}
impl<'a> Parser<'a> {
    /// Returns `Some(v)` where `v` has the lowest `id` of any [`Variable`] in
    /// `self` named `name` if such a [`Variable`] exists, otherwise `None`.
    ///
    /// [`Variable`]: trait.Variable.html
    pub fn has_var(&self, name: &str) -> Option<Variable> {
        if name == "" {
            None
        } else {
            self.sig
                .sig
                .read()
                .expect("poisoned signature")
                .variables
                .iter()
                .enumerate()
                .skip(self.dv)
                .find(|&(_, ref var_name)| var_name.as_ref().map(String::as_str) == Some(name))
                .map(|(id, _)| Variable { id })
        }
    }
    /// Returns a [`Variable`] `v` where `v` has the lowest `id` of any [`Variable`] in
    /// `self` named `name`, creating this [`Variable`] if necessary.
    ///
    /// [`Variable`]: trait.Variable.html
    pub fn get_var(&mut self, name: &str) -> Variable {
        match self.has_var(name) {
            Some(var) => var,
            None => self.sig.new_var(Some(name.to_string())),
        }
    }
    /// Returns `Some(o)` where `o` has the lowest `id` of any [`Operator`] in
    /// `self` named `name` with arity `arity` if such an [`Operator`] exists,
    /// otherwise `None`.
    ///
    /// [`Operator`]: struct.Operator.html
    pub fn has_op(&self, name: &str, arity: u32) -> Option<Operator> {
        self.sig
            .sig
            .read()
            .expect("poisoned signature")
            .operators
            .iter()
            .enumerate()
            .find(|&(_, &(op_arity, ref op_name))| {
                op_arity == arity && op_name.as_ref().map(String::as_str) == Some(name)
            })
            .map(|(id, _)| Operator { id, arity })
    }
    /// Returns an [`Operator`] with the given `name` with arity `arity`,
    /// creating it if necessary.
    ///
    /// [`Operator`]: struct.Operator.html
    pub fn get_op(&mut self, name: &str, arity: u32) -> Operator {
        match self.has_op(name, arity) {
            Some(op) => op,
            None => self.sig.new_op(arity, Some(name.to_string())),
        }
    }
    /// Forgets every currently tracked `Variable`.
    pub fn clear_variables(&mut self) {
        self.dv = self.sig.variables().len();
    }
    pub fn new(sig: &'a mut Signature) -> Parser<'a> {
        let dv = sig.variables().len();
        Parser { sig, dv }
    }

    method!(variable<Parser<'a>, CompleteStr, Term>, mut self,
            map!(terminated!(identifier, underscore),
                 |v| Term::Variable(self.get_var(v.0)))
    );

    method!(application<Parser<'a>, CompleteStr, Term>, mut self,
            alt!(call_m!(self.standard_application) |
                 call_m!(self.binary_application))
    );

    // there was a bug in delimited! — see nom#728
    method!(standard_application<Parser<'a>, CompleteStr, Term>, mut self,
            do_parse!(name: identifier >>
                      args: opt!(do_parse!(
                              lparen >>
                              multispace0 >>
                              args: separated_list!(
                                  multispace1,
                                  call_m!(self.term)) >>
                              multispace0 >>
                              rparen >>
                              (args))) >>
                      args: expr_opt!(Some(args.unwrap_or_default())) >>
                      (Term::Application {
                          op: self.get_op(name.0, args.len() as u32),
                          args
                      })
            )
    );

    method!(binary_application<Parser<'a>, CompleteStr, Term>, mut self,
            do_parse!(lparen >>
                      multispace0 >>
                      t1: call_m!(self.term) >>
                      multispace1 >>
                      t2: call_m!(self.term) >>
                      multispace0 >>
                      rparen >>
                      (Term::Application {
                          op: self.get_op(".", 2),
                          args: vec![t1, t2],
                      })
            )
    );

    method!(term<Parser<'a>, CompleteStr, Term>, mut self,
            alt!(call_m!(self.variable) |
                 call_m!(self.application) |
                 do_parse!(lparen >>
                           term: call_m!(self.top_term) >>
                           rparen >>
                           (term))
            )
    );

    method!(top_term<Parser<'a>, CompleteStr, Term>, mut self,
            ws!(map!(
                    separated_nonempty_list!(
                        multispace1,
                        call_m!(self.term)),
                    |a| {
                        let mut it = a.into_iter();
                        let init = it.next().unwrap();
                        it.fold(init, |acc, x| {
                            let args = vec![acc, x];
                            let op = self.get_op(".", 2);
                            Term::Application{ op, args }
                        })
                    }))
    );

    method!(context_variable<Parser<'a>, CompleteStr, Context>, mut self,
            map!(terminated!(identifier, underscore),
                 |v| Context::Variable(self.get_var(v.0)))
    );

    method!(context_application<Parser<'a>, CompleteStr, Context>, mut self,
            alt!(call_m!(self.context_standard_application) |
                 call_m!(self.context_binary_application))
    );

    // there was a bug in delimited! — see nom#728
    method!(context_standard_application<Parser<'a>, CompleteStr, Context>, mut self,
            do_parse!(name: identifier >>
                      args: opt!(do_parse!(
                              lparen >>
                              multispace0 >>
                              args: separated_list!(
                                  multispace1,
                                  call_m!(self.context)) >>
                              multispace0 >>
                              rparen >>
                              (args))) >>
                      args: expr_opt!(Some(args.unwrap_or_default())) >>
                      (Context::Application {
                          op: self.get_op(name.0, args.len() as u32),
                          args,
                      })
            )
    );

    method!(context_binary_application<Parser<'a>, CompleteStr, Context>, mut self,
            do_parse!(lparen >>
                      multispace0 >>
                      t1: call_m!(self.context) >>
                      multispace1 >>
                      t2: ws!(call_m!(self.context)) >>
                      multispace0 >>
                      rparen >>
                      (Context::Application{ op: self.get_op(".", 2), args: vec![t1, t2] }))
    );

    method!(
        context_hole<Parser<'a>, CompleteStr, Context>,
        self,
        do_parse!(tag!("[!]") >> (Context::Hole))
    );

    method!(context<Parser<'a>, CompleteStr, Context>, mut self,
            alt!(call_m!(self.context_variable) |
                 call_m!(self.context_application) |
                 call_m!(self.context_hole))
    );

    method!(top_context<Parser<'a>, CompleteStr, Context>, mut self,
            ws!(map!(
                separated_nonempty_list!(
                    multispace1,
                    alt!(call_m!(self.context) |
                         do_parse!(lparen >>
                                   context: call_m!(self.top_context) >>
                                   rparen >>
                                   (context)))),
                |a| {
                    let mut it = a.into_iter();
                    let init = it.next().unwrap();
                    it.fold(init, |acc, x| {
                        let op = self.get_op(".", 2);
                        let args = vec![acc, x];
                        Context::Application{ op, args }
                    })
                }))
    );

    method!(rule<Parser<'a>, CompleteStr, Rule>, mut self,
            ws!(map_opt!(
                do_parse!(lhs: call_m!(self.top_term) >>
                          ws!(rule_kw) >>
                          rhs: separated_nonempty_list!(
                              ws!(pipe),
                              call_m!(self.top_term)) >>
                          (lhs, rhs)),
                |(lhs, rhs)| Rule::new(lhs, rhs)))
    );

    method!(rule_statement<Parser<'a>, CompleteStr, Statement>, mut self,
            map!(call_m!(self.rule),
                 Statement::Rule)
    );

    method!(rulecontext<Parser<'a>, CompleteStr, RuleContext>, mut self,
            ws!(map_opt!(
                do_parse!(lhs: call_m!(self.top_context) >>
                          ws!(rule_kw) >>
                          rhs: separated_nonempty_list!(
                              ws!(pipe),
                              call_m!(self.top_context)) >>
                          (lhs, rhs)),
                |(lhs, rhs)| RuleContext::new(lhs, rhs)))
    );

    method!(term_statement<Parser<'a>, CompleteStr, Statement>, mut self,
            do_parse!(term: call_m!(self.top_term) >>
                      (Statement::Term(term)))
    );

    method!(
        comment<Parser<'a>, CompleteStr, CompleteStr>,
        self,
        preceded!(tag!("#"), take_until_and_consume!("\n"))
    );

    method!(trs<Parser<'a>, CompleteStr, TRS>, mut self,
            ws!(do_parse!(
                    rules: many0!(
                        do_parse!(
                            many0!(ws!(call_m!(self.comment))) >>
                            rule: call_m!(self.rule) >>
                            ws!(semicolon) >>
                            many0!(ws!(call_m!(self.comment))) >>
                            ({ self.clear_variables(); rule }))) >>
                    (TRS::new(rules))))
    );

    method!(program<Parser<'a>, CompleteStr, Vec<Statement>>, mut self,
            ws!(many0!(do_parse!(many0!(ws!(call_m!(self.comment))) >>
                                 statement: alt!(call_m!(self.rule_statement) |
                                                 call_m!(self.term_statement)) >>
                                 ws!(semicolon) >>
                                 many0!(ws!(call_m!(self.comment))) >>
                                 ({ self.clear_variables(); statement }))))
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lparen_test() {
        assert_eq!(
            lparen(CompleteStr("(")),
            Ok((CompleteStr(""), CompleteStr("(")))
        );
    }

    #[test]
    fn rparen_test() {
        assert_eq!(
            rparen(CompleteStr(")")),
            Ok((CompleteStr(""), CompleteStr(")")))
        );
    }

    #[test]
    fn pipe_test() {
        assert_eq!(
            pipe(CompleteStr("|")),
            Ok((CompleteStr(""), CompleteStr("|")))
        );
    }

    #[test]
    fn semicolon_test() {
        assert_eq!(
            semicolon(CompleteStr(";")),
            Ok((CompleteStr(""), CompleteStr(";")))
        );
    }

    #[test]
    fn rule_kw_test() {
        assert_eq!(
            rule_kw(CompleteStr("=")),
            Ok((CompleteStr(""), CompleteStr("=")))
        );
    }

    #[test]
    fn underscore_test() {
        assert_eq!(
            underscore(CompleteStr("_")),
            Ok((CompleteStr(""), CompleteStr("_")))
        );
    }

    #[test]
    fn has_var_test() {
        let mut sig = Signature::default();
        let p = Parser::new(&mut sig);
        let none = p.has_var("");
        assert_eq!(None, none);
    }

    #[test]
    fn var_test() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let abc = p.get_var("abc");
        let (_, var) = p.variable(CompleteStr("abc_"));
        assert_eq!(var, Ok((CompleteStr(""), Term::Variable(abc))));
    }

    #[test]
    fn app_test_1() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_op("a", 0);
        let (_, app) = p.application(CompleteStr("a()"));
        let term = Term::Application {
            op: a,
            args: vec![],
        };
        assert_eq!(app, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn app_test_2() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let b = p.get_op("b", 0);
        let (_, app) = p.application(CompleteStr("b"));
        let term = Term::Application {
            op: b,
            args: vec![],
        };
        assert_eq!(app, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn app_test_3() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_op(".", 2);
        let b = p.get_op("b", 0);
        let c = p.get_op("c", 0);
        let (_, app) = p.application(CompleteStr("(b c)"));
        let st1 = Term::Application {
            op: b,
            args: vec![],
        };
        let st2 = Term::Application {
            op: c,
            args: vec![],
        };
        let term = Term::Application {
            op: a,
            args: vec![st1, st2],
        };
        assert_eq!(app, Ok((CompleteStr(""), term)));
    }

    #[test]
    fn term_test_1() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_op("a", 0);
        let (_, parsed_term) = p.term(CompleteStr("a()"));
        let term = Term::Application {
            op: a,
            args: vec![],
        };
        assert_eq!(parsed_term, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn term_test_2() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_var("a");
        let (_, parsed_term) = p.term(CompleteStr("a_"));
        let term = Term::Variable(a);
        assert_eq!(parsed_term, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn term_test_3() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a1 = p.get_op("a", 2);
        let x1 = p.get_var("x");
        let y1 = p.get_var("y");
        let (_, parsed_term) = p.term(CompleteStr("a(x_ a(y_ x_))"));
        let a2 = a1.clone();
        let x1 = Term::Variable(x1);
        let x2 = x1.clone();
        let y1 = Term::Variable(y1);
        let term = Term::Application {
            op: a1,
            args: vec![
                x1,
                Term::Application {
                    op: a2,
                    args: vec![y1, x2],
                },
            ],
        };
        assert_eq!(parsed_term, Ok((CompleteStr(""), term)));
    }

    #[test]
    fn top_term_test() {
        let mut sig = Signature::default();
        let (_, parsed_term_vec) = parse(&mut sig, "S K K (K S K);").expect("successful parse");

        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let s = p.get_op("S", 0);
        let k = p.get_op("K", 0);
        let app = p.get_op(".", 2);
        let term = Term::Application {
            op: app.clone(),
            args: vec![
                Term::Application {
                    op: app.clone(),
                    args: vec![
                        Term::Application {
                            op: app.clone(),
                            args: vec![
                                Term::Application {
                                    op: s.clone(),
                                    args: vec![],
                                },
                                Term::Application {
                                    op: k.clone(),
                                    args: vec![],
                                },
                            ],
                        },
                        Term::Application {
                            op: k.clone(),
                            args: vec![],
                        },
                    ],
                },
                Term::Application {
                    op: app.clone(),
                    args: vec![
                        Term::Application {
                            op: app.clone(),
                            args: vec![
                                Term::Application {
                                    op: k.clone(),
                                    args: vec![],
                                },
                                Term::Application {
                                    op: s.clone(),
                                    args: vec![],
                                },
                            ],
                        },
                        Term::Application {
                            op: k.clone(),
                            args: vec![],
                        },
                    ],
                },
            ],
        };

        let term_vec = vec![term];

        assert_eq!(parsed_term_vec, term_vec);
    }

    #[test]
    fn rule_test() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_op("a", 0);
        let b = p.get_op("b", 0);
        let (_, parsed_rule) = p.rule_statement(CompleteStr("a = b()"));

        let lhs = Term::Application {
            op: a,
            args: vec![],
        };
        let rhs = vec![Term::Application {
            op: b,
            args: vec![],
        }];
        let rule = Statement::Rule(Rule::new(lhs, rhs).unwrap());

        assert_eq!(parsed_rule, Ok((CompleteStr(""), rule)));
    }

    #[test]
    fn rulecontext_test() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_op("a", 0);
        let x = p.get_var("x");
        let c = p.get_op("c", 1);
        let d = p.get_op(".", 2);
        let (_, parsed_rule) = p.rulecontext(CompleteStr("a c(x_) = [!]"));
        let lhs = Context::Application {
            op: d,
            args: vec![
                Context::Application {
                    op: a,
                    args: vec![],
                },
                Context::Application {
                    op: c,
                    args: vec![Context::Variable(x)],
                },
            ],
        };
        let rhs = vec![Context::Hole];
        let rule = RuleContext::new(lhs, rhs).unwrap();

        assert_eq!(parsed_rule, Ok((CompleteStr(""), rule)));
    }

    #[test]
    fn statement_test_1() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_op("a", 0);
        let (_, parsed_statement) = p.term_statement(CompleteStr("a()"));
        let statement = Statement::Term(Term::Application {
            op: a,
            args: vec![],
        });
        assert_eq!(parsed_statement, Ok((CompleteStr(""), statement)));
    }
    #[test]
    fn statement_test_2() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_op("a", 0);
        let b = p.get_op("b", 0);
        let dot = p.get_op(".", 2);
        let (_, parsed_statement) = p.term_statement(CompleteStr("a b"));

        let st1 = Term::Application {
            op: a,
            args: vec![],
        };
        let st2 = Term::Application {
            op: b,
            args: vec![],
        };
        let statement = Statement::Term(Term::Application {
            op: dot,
            args: vec![st1, st2],
        });

        assert_eq!(parsed_statement, Ok((CompleteStr(""), statement)));
    }

    #[test]
    fn program_test() {
        let mut sig = Signature::default();
        let mut p = Parser::new(&mut sig);
        let a = p.get_op("a", 0);
        let (_, parsed_program) = p.program(CompleteStr("a();"));
        let program = Statement::Term(Term::Application {
            op: a,
            args: vec![],
        });

        assert_eq!(parsed_program, Ok((CompleteStr(""), vec![program])));
    }

    #[test]
    fn parser_debug() {
        let mut sig = Signature::default();
        let p = Parser::new(&mut sig);
        assert_eq!(
            format!("{:?}", p),
            "Parser { sig: Signature{Ok(RwLockReadGuard { lock: RwLock { data: Sig { operators: [], variables: [] } } })}, dv: 0 }"
        );
    }
    #[test]
    fn parser_incomplete() {
        let mut sig = Signature::default();
        let res = parse(&mut sig, "(a b c");
        assert_eq!(res, Err(ParseError::ParseIncomplete));
    }
}
