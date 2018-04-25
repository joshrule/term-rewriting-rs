use super::types::*;

use nom::types::CompleteStr;
use nom::{alphanumeric, multispace, IResult};

named!(lparen<CompleteStr, CompleteStr>,     tag!("("));
named!(rparen<CompleteStr, CompleteStr>,     tag!(")"));
named!(pipe<CompleteStr, CompleteStr>,       tag!("|"));
named!(semicolon<CompleteStr, CompleteStr>,  tag!(";"));
named!(rule_kw<CompleteStr, CompleteStr>,    tag!("="));
named!(underscore<CompleteStr, CompleteStr>, tag!("_"));
named!(identifier<CompleteStr, CompleteStr>, call!(alphanumeric));

#[derive(Debug, PartialEq)]
pub enum ParseError {
    ParseIncomplete,
    ParseFailed,
}

pub fn parse_trs(input: &str, operators: &[Op]) -> Result<TRS<Var, Op>, ParseError> {
    let (_parser, result) = Parser::new(operators).trs(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), t)) => Ok(t),
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

pub fn parse_term(input: &str, operators: &[Op]) -> Result<Term<Var, Op>, ParseError> {
    let (_parser, result) = Parser::new(operators).top_term(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), t)) => Ok(t),
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

pub fn parse(
    input: &str,
    operators: &[Op],
) -> Result<(TRS<Var, Op>, Vec<Term<Var, Op>>), ParseError> {
    let (_parser, result) = Parser::new(operators).program(CompleteStr(input));
    match result {
        Ok((CompleteStr(""), o)) => {
            let (srs, sts): (Vec<Statement>, Vec<Statement>) =
                o.into_iter().partition(|x| match *x {
                    Statement::Rule(_) => true,
                    _ => false,
                });

            let rs = srs.into_iter()
                .filter_map(|x| match x {
                    Statement::Rule(r) => Some(r),
                    _ => None,
                })
                .collect();

            let ts = sts.into_iter()
                .filter_map(|x| match x {
                    Statement::Term(t) => Some(t),
                    _ => None,
                })
                .collect();

            Ok((TRS::new(rs), ts))
        }
        Ok((CompleteStr(_), _)) => Err(ParseError::ParseIncomplete),
        Err(_) => Err(ParseError::ParseFailed),
    }
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Term(Term<Var, Op>),
    Rule(Rule<Var, Op>),
}

#[derive(Debug)]
pub struct Parser {
    operators: Vec<Op>,
    variables: Vec<Var>,
}
impl Parser {
    /// Returns [`Some(v)`] where `v` has the lowest `id` of any [`Variable`] in
    /// `self` named `name` if such a [`Variable`] exists, otherwise [`None`].
    ///
    /// [`Some(v)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Variable`]: trait.Variable.html
    pub fn has_var(&self, name: &str) -> Option<Var> {
        if name == "" {
            None
        } else {
            self.variables.iter().find(|&v| v.show() == name).cloned()
        }
    }
    /// Returns a [`Variable`] `v` where `v` has the lowest `id` of any [`Variable`] in
    /// `self` named `name`, creating this [`Variable`] if necessary.
    ///
    /// [`Variable`]: trait.Variable.html
    pub fn get_var(&mut self, name: &str) -> Var {
        match self.has_var(name) {
            Some(v) => v,
            None => {
                let v = Var::new(
                    Var::new_id(&self.variables.iter().collect::<Vec<&Var>>()[..]),
                    Some(name.to_string()),
                );
                self.variables.push(v.clone());
                v
            }
        }
    }
    /// Returns [`Some(o)`] where `o` has the lowest `id` of any [`Operator`] in
    /// `self` named `name` with arity `arity` if such an [`Operator`] exists,
    /// otherwise [`None`].
    ///
    /// [`Some(v)`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Operator`]: trait.Operator.html
    pub fn has_op(&mut self, name: &str, arity: Arity_) -> Option<Op> {
        self.operators
            .iter()
            .find(|&o| o.show() == name && o.arity() == arity)
            .cloned()
    }
    /// Returns an [`Operator`] `v` where `v` has the lowest `id` of any [`Operator`] in
    /// `self` named `name` with arity `arity`, creating this [`Operator`] if necessary.
    ///
    /// [`Operator`]: trait.Operator.html
    pub fn get_op(&mut self, name: &str, arity: Arity_) -> Op {
        match self.has_op(name, arity) {
            Some(o) => o,
            None => {
                let o = Op::new(
                    Op::new_id(&self.operators.iter().collect::<Vec<&Op>>()[..]),
                    arity,
                    Some(name.to_string()),
                );
                self.operators.push(o.clone());
                o
            }
        }
    }
    /// `self` forgets every currently tracked [`Variable`].
    ///
    /// [`Variable`]: trait.Variable.html
    pub fn clear_variables(&mut self) {
        self.variables.clear();
    }
    pub fn new(operators: &[Op]) -> Parser {
        Parser {
            operators: operators.to_vec(),
            variables: vec![],
        }
    }
    pub fn get_op_wrapped<'b>(
        mut self: Parser,
        input: CompleteStr<'b>,
        name: &str,
        arity: Arity_,
    ) -> (Self, IResult<CompleteStr<'b>, Op>) {
        let op = self.get_op(name, arity);
        (self, Ok((input, op)))
    }

    method!(variable<Parser, CompleteStr, Term<Var, Op>>, mut self,
            map!(terminated!(identifier, underscore),
                 |v| Term::Variable(self.get_var(v.0)))
    );

    method!(application<Parser, CompleteStr, Term<Var, Op>>, mut self,
            alt!(call_m!(self.standard_application) |
                 call_m!(self.constant) |
                 call_m!(self.binary_application))
    );

    // there was a bug in delimited! (or in tuple_parser! closures)
    method!(standard_application<Parser, CompleteStr, Term<Var, Op>>, mut self,
            do_parse!(name: identifier >>
                      lparen >>
                      args: many0!(ws!(call_m!(self.term))) >>
                      rparen >>
                      head: call_m!(self.get_op_wrapped,
                                    name.0,
                                    args.len()) >>
                      (Term::Application{head, args}))
    );

    method!(constant<Parser, CompleteStr, Term<Var, Op>>, mut self,
            do_parse!(name: identifier >>
                      head: call_m!(self.get_op_wrapped,
                                    name.0,
                                    0) >>
                      (Term::Application{head, args: vec![]}))
    );

    method!(binary_application<Parser, CompleteStr, Term<Var, Op>>, mut self,
            do_parse!(lparen >>
                      t1: ws!(call_m!(self.term)) >>
                      t2: ws!(call_m!(self.term)) >>
                      head: call_m!(self.get_op_wrapped, ".", 2) >>
                      rparen >>
                      (Term::Application{ head, args: vec![t1, t2] }))
    );

    method!(term<Parser, CompleteStr, Term<Var, Op>>, mut self,
            alt!(call_m!(self.variable) | call_m!(self.application))
    );

    method!(top_term<Parser, CompleteStr, Term<Var, Op>>, mut self,
            map!(do_parse!(head: call_m!(self.get_op_wrapped, ".", 2) >>
                           args: separated_nonempty_list!(
                               multispace,
                               alt!(call_m!(self.term) |
                                    do_parse!(lparen >>
                                              term: call_m!(self.top_term) >>
                                              rparen >>
                                              (term)))) >>
                           (head, args)),
                 |(h, a)| { let mut it = a.into_iter();
                            let init = it.next().unwrap();
                            it.fold(init, |acc, x|
                                    Term::Application{
                                        head: h.clone(),
                                        args: vec![acc, x],
                                    })})
    );

    method!(rule<Parser, CompleteStr, Rule<Var, Op>>, mut self,
            map_opt!(
                do_parse!(lhs: call_m!(self.top_term) >>
                          ws!(rule_kw) >>
                          rhs: separated_nonempty_list!(
                              ws!(pipe),
                              call_m!(self.top_term)) >>
                          (lhs, rhs)),
                |(lhs, rhs)| Rule::new(lhs, rhs))
    );

    method!(rule_statement<Parser, CompleteStr, Statement>, mut self,
            map!(call_m!(self.rule),
                 Statement::Rule)
    );

    method!(term_statement<Parser, CompleteStr, Statement>, mut self,
            do_parse!(term: call_m!(self.top_term) >>
                      (Statement::Term(term))));

    method!(
        comment<Parser, CompleteStr, CompleteStr>,
        self,
        preceded!(tag!("#"), take_until_and_consume!("\n"))
    );

    method!(trs<Parser, CompleteStr, TRS<Var, Op>>, mut self,
            add_return_error!(
                ErrorKind::Custom(1),
                do_parse!(
                    rules: many0!(
                        map!(
                            do_parse!(
                                many0!(ws!(call_m!(self.comment))) >>
                                rule: call_m!(self.rule) >>
                                ws!(semicolon) >>
                                many0!(ws!(call_m!(self.comment))) >>
                                (rule)),
                            |r| {self.clear_variables(); r})) >>
                    (TRS::new(rules))))
    );

    method!(program<Parser, CompleteStr, Vec<Statement>>, mut self,
            add_return_error!(
                ErrorKind::Custom(1),
                many0!(map!(do_parse!(many0!(ws!(call_m!(self.comment))) >>
                                      statement: alt!(call_m!(self.rule_statement) |
                                                      call_m!(self.term_statement)) >>
                                      ws!(semicolon) >>
                                      many0!(ws!(call_m!(self.comment))) >>
                                      (statement)),
                            |s| {self.clear_variables(); s})))
    );
}
impl Default for Parser {
    fn default() -> Self {
        Parser {
            operators: vec![],
            variables: vec![],
        }
    }
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
    fn var_test() {
        let mut p = Parser::default();
        let abc = p.get_var("abc");
        let (_, var) = p.variable(CompleteStr("abc_"));
        assert_eq!(var, Ok((CompleteStr(""), Term::Variable(abc))));
    }

    #[test]
    fn app_test_1() {
        let mut p = Parser::default();
        let a = p.get_op("a", 0);
        let (_, app) = p.application(CompleteStr("a()"));
        let term = Term::Application {
            head: a,
            args: vec![],
        };
        assert_eq!(app, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn app_test_2() {
        let mut p = Parser::default();
        let b = p.get_op("b", 0);
        let (_, app) = p.application(CompleteStr("b"));
        let term = Term::Application {
            head: b,
            args: vec![],
        };
        assert_eq!(app, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn app_test_3() {
        let mut p = Parser::default();
        let a = p.get_op(".", 2);
        let b = p.get_op("b", 0);
        let c = p.get_op("c", 0);
        let (_, app) = p.application(CompleteStr("(b c)"));
        let st1 = Term::Application {
            head: b,
            args: vec![],
        };
        let st2 = Term::Application {
            head: c,
            args: vec![],
        };
        let term = Term::Application {
            head: a,
            args: vec![st1, st2],
        };
        assert_eq!(app, Ok((CompleteStr(""), term)));
    }

    #[test]
    fn term_test_1() {
        let mut p = Parser::default();
        let a = p.get_op("a", 0);
        let (_, parsed_term) = p.term(CompleteStr("a()"));
        let term = Term::Application {
            head: a,
            args: vec![],
        };
        assert_eq!(parsed_term, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn term_test_2() {
        let mut p = Parser::default();
        let a = p.get_var("a");
        let (_, parsed_term) = p.term(CompleteStr("a_"));
        let term = Term::Variable(a);
        assert_eq!(parsed_term, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn term_test_3() {
        let mut p = Parser::default();
        let a1 = p.get_op("a", 2);
        let x1 = p.get_var("x");
        let y1 = p.get_var("y");
        let (_, parsed_term) = p.term(CompleteStr("a(x_ a(y_ x_))"));
        let a2 = a1.clone();
        let x1 = Term::Variable(x1);
        let x2 = x1.clone();
        let y1 = Term::Variable(y1);
        let term = Term::Application {
            head: a1,
            args: vec![
                x1,
                Term::Application {
                    head: a2,
                    args: vec![y1, x2],
                },
            ],
        };
        assert_eq!(parsed_term, Ok((CompleteStr(""), term)));
    }

    #[test]
    fn top_term_test() {
        let (_, parsed_term_vec) = parse("S K K (K S K);", &vec![]).expect("successful parse");

        let mut p = Parser::default();
        let app = p.get_op(".", 2);
        let s = p.get_op("S", 0);
        let k = p.get_op("K", 0);
        let term = Term::Application {
            head: app.clone(),
            args: vec![
                Term::Application {
                    head: app.clone(),
                    args: vec![
                        Term::Application {
                            head: app.clone(),
                            args: vec![
                                Term::Application {
                                    head: s.clone(),
                                    args: vec![],
                                },
                                Term::Application {
                                    head: k.clone(),
                                    args: vec![],
                                },
                            ],
                        },
                        Term::Application {
                            head: k.clone(),
                            args: vec![],
                        },
                    ],
                },
                Term::Application {
                    head: app.clone(),
                    args: vec![
                        Term::Application {
                            head: app.clone(),
                            args: vec![
                                Term::Application {
                                    head: k.clone(),
                                    args: vec![],
                                },
                                Term::Application {
                                    head: s.clone(),
                                    args: vec![],
                                },
                            ],
                        },
                        Term::Application {
                            head: k.clone(),
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
        let mut p = Parser::default();
        let a = p.get_op("a", 0);
        let b = p.get_op("b", 0);
        let (_, parsed_rule) = p.rule_statement(CompleteStr("a = b()"));

        let lhs = Term::Application {
            head: a,
            args: vec![],
        };
        let rhs = vec![Term::Application {
            head: b,
            args: vec![],
        }];
        let rule = Statement::Rule(Rule::new(lhs, rhs).unwrap());

        assert_eq!(parsed_rule, Ok((CompleteStr(""), rule)));
    }

    #[test]
    fn statement_test_1() {
        let mut p = Parser::default();
        let a = p.get_op("a", 0);
        let (_, parsed_statement) = p.term_statement(CompleteStr("a()"));
        let statement = Statement::Term(Term::Application {
            head: a,
            args: vec![],
        });
        assert_eq!(parsed_statement, Ok((CompleteStr(""), statement)));
    }
    #[test]
    fn statement_test_2() {
        let mut p = Parser::default();
        let a = p.get_op("a", 0);
        let b = p.get_op("b", 0);
        let dot = p.get_op(".", 2);
        let (_, parsed_statement) = p.term_statement(CompleteStr("a b"));

        let st1 = Term::Application {
            head: a,
            args: vec![],
        };
        let st2 = Term::Application {
            head: b,
            args: vec![],
        };
        let statement = Statement::Term(Term::Application {
            head: dot,
            args: vec![st1, st2],
        });

        assert_eq!(parsed_statement, Ok((CompleteStr(""), statement)));
    }

    #[test]
    fn program_test() {
        let mut p = Parser::default();
        let a = p.get_op("a", 0);
        let (_, parsed_program) = p.program(CompleteStr("a();"));
        let program = Statement::Term(Term::Application {
            head: a,
            args: vec![],
        });

        assert_eq!(parsed_program, Ok((CompleteStr(""), vec![program])));
    }

    #[test]
    fn parser_debug() {
        let p = Parser::default();
        assert_eq!(
            format!("{:?}", p),
            "Parser { operators: [], variables: [] }"
        );
    }
    #[test]
    fn parser_incomplete() {
        let res = parse("(a b c", &vec![]);
        assert_eq!(res, Err(ParseError::ParseIncomplete));
    }
}
