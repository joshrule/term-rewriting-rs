use super::types::*;

use nom::{alphanumeric, multispace, IResult};
use nom::types::CompleteStr;

named!(lparen<CompleteStr, CompleteStr>,     tag!("("));
named!(rparen<CompleteStr, CompleteStr>,     tag!(")"));
named!(pipe<CompleteStr, CompleteStr>,       tag!("|"));
named!(semicolon<CompleteStr, CompleteStr>,  tag!(";"));
named!(rule_kw<CompleteStr, CompleteStr>,    tag!("="));
named!(underscore<CompleteStr, CompleteStr>, tag!("_"));
named!(identifier<CompleteStr, CompleteStr>, call!(alphanumeric));

pub fn parse<'a>(input: &'a str, sig: &mut Signature) -> Result<(TRS, Vec<Term>), &'a str> {
    let (_parser, result) = Parser::new(sig).program(CompleteStr(input));
    println!("{:?}", result);
    match result {
        Ok((CompleteStr(""), o)) => {
            let (srs, sts): (Vec<Statement>, Vec<Statement>) =
                o.into_iter().partition(|x| match *x {
                    Statement::Rule(_) => true,
                    _ => false,
                });

            let rs: Vec<Rule> = srs.into_iter()
                .filter_map(|x| match x {
                    Statement::Rule(r) => Some(r),
                    _ => None,
                })
                .collect();

            let ts: Vec<Term> = sts.into_iter()
                .filter_map(|x| match x {
                    Statement::Term(t) => Some(t),
                    _ => None,
                })
                .collect();

            Ok((TRS::new(rs), ts))
        }
        Ok((CompleteStr(_), _)) => {
            Err("parse incomplete!")
        }
        Err(_) => Err("parse failed!"),
    }
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Term(Term),
    Rule(Rule),
}

#[derive(Debug)]
pub struct Parser<'a> {
    signature: &'a mut Signature,
}
impl<'a> Parser<'a> {
    fn new(s: &'a mut Signature) -> Parser<'a> {
        Parser { signature: s }
    }

    fn get_var(&mut self, name: &str) -> Variable {
        self.signature.get_var(name)
    }

    fn get_op<'b>(
        self: Parser<'a>,
        input: CompleteStr<'b>,
        name: &str,
        arity: Arity,
    ) -> (Self, IResult<CompleteStr<'b>, Operator>) {
        let op = self.signature.get_op(name, arity);
        (self, Ok((input, op)))
    }

    fn clear_variables(&mut self) {
        self.signature.clear_variables();
    }

    method!(variable<Parser<'a>, CompleteStr, Term>, mut self,
            map!(terminated!(identifier, underscore),
                 |v| Term::Variable(self.get_var(v.0)))
    );

    method!(application<Parser<'a>, CompleteStr, Term>, mut self,
            alt!(call_m!(self.standard_application) |
                 call_m!(self.constant) |
                 call_m!(self.binary_application))
    );

    // there was a bug in delimited! (or in tuple_parser! closures)
    method!(standard_application<Parser<'a>, CompleteStr, Term>, mut self,
            do_parse!(name: identifier >>
                      lparen >>
                      args: many0!(ws!(call_m!(self.term))) >>
                      rparen >>
                      head: call_m!(self.get_op,
                                    name.0,
                                    args.len()) >>
                      (Term::Application{head, args}))
    );

    method!(constant<Parser<'a>, CompleteStr, Term>, mut self,
            do_parse!(name: identifier >>
                      head: call_m!(self.get_op,
                                    name.0,
                                    0) >>
                      (Term::Application{head, args: vec![]}))
    );

    method!(binary_application<Parser<'a>, CompleteStr, Term>, mut self,
            do_parse!(lparen >>
                      t1: ws!(call_m!(self.term)) >>
                      t2: ws!(call_m!(self.term)) >>
                      head: call_m!(self.get_op, ".", 2) >>
                      rparen >>
                      (Term::Application{ head, args: vec![t1, t2] }))
    );

    method!(term<Parser<'a>, CompleteStr, Term>, mut self,
            alt!(call_m!(self.variable) | call_m!(self.application))
    );

    method!(top_term<Parser<'a>, CompleteStr, Term>, mut self,
            map!(do_parse!(head: call_m!(self.get_op, ".", 2) >>
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

    method!(rule<Parser<'a>, CompleteStr, Statement>, mut self,
            map!(
                map_opt!(
                    do_parse!(lhs: call_m!(self.top_term) >>
                              ws!(rule_kw) >>
                              rhs: separated_nonempty_list!(
                                  ws!(pipe),
                                  call_m!(self.top_term)) >>
                              (lhs, rhs)),
                    |(lhs, rhs)| Rule::new(lhs, rhs)),
                Statement::Rule)
    );

    method!(statement<Parser<'a>, CompleteStr, Statement>, mut self,
            do_parse!(term: call_m!(self.top_term) >>
                      (Statement::Term(term))));

    method!(comment<Parser<'a>, CompleteStr, CompleteStr>, self,
            preceded!(tag!("#"), take_until_and_consume!("\n"))
    );

    method!(program<Parser<'a>, CompleteStr, Vec<Statement>>, mut self,
            add_return_error!(
                ErrorKind::Custom(1),
                many0!(map!(do_parse!(many0!(ws!(call_m!(self.comment))) >>
                                      statement: alt!(call_m!(self.rule) |
                                                      call_m!(self.statement)) >>
                                      ws!(semicolon) >>
                                      many0!(ws!(call_m!(self.comment))) >>
                                      (statement)),
                            |s| {self.clear_variables(); s})))
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
    fn var_test() {
        let mut s = Signature::default();
        let abc = s.get_var("abc");
        let p = Parser::new(&mut s);
        let (_, var) = p.variable(CompleteStr("abc_"));
        assert_eq!(var, Ok((CompleteStr(""), Term::Variable(abc))));
    }

    #[test]
    fn app_test_1() {
        let mut s = Signature::default();
        let a = s.get_op("a", 0);
        let p = Parser::new(&mut s);
        let (_, app) = p.application(CompleteStr("a()"));
        let term = Term::Application {
            head: a,
            args: vec![],
        };
        assert_eq!(app, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn app_test_2() {
        let mut s = Signature::default();
        let b = s.get_op("b", 0);
        let p = Parser::new(&mut s);
        let (_, app) = p.application(CompleteStr("b"));
        let term = Term::Application {
            head: b,
            args: vec![],
        };
        assert_eq!(app, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn app_test_3() {
        let mut s = Signature::default();
        let a = s.get_op(".", 2);
        let b = s.get_op("b", 0);
        let c = s.get_op("c", 0);
        let p = Parser::new(&mut s);
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
        let mut s = Signature::default();
        let a = s.get_op("a", 0);
        let p = Parser::new(&mut s);
        let (_, parsed_term) = p.term(CompleteStr("a()"));
        let term = Term::Application {
            head: a,
            args: vec![],
        };
        assert_eq!(parsed_term, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn term_test_2() {
        let mut s = Signature::default();
        let a = s.get_var("a");
        let p = Parser::new(&mut s);
        let (_, parsed_term) = p.term(CompleteStr("a_"));
        let term = Term::Variable(a);
        assert_eq!(parsed_term, Ok((CompleteStr(""), term)));
    }
    #[test]
    fn term_test_3() {
        let mut s = Signature::default();
        let a1 = s.get_op("a", 2);
        let x1 = s.get_var("x");
        let y1 = s.get_var("y");
        let p = Parser::new(&mut s);
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
        let mut sig = Signature::default();
        let (_, parsed_term_vec) = sig.parse("S K K (K S K);").expect("successful parse");

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

        let term_vec = vec![term];

        assert_eq!(parsed_term_vec, term_vec);
    }

    #[test]
    fn rule_test() {
        let mut s = Signature::default();
        let a = s.get_op("a", 0);
        let b = s.get_op("b", 0);
        let p = Parser::new(&mut s);
        let (_, parsed_rule) = p.rule(CompleteStr("a = b()"));

        let lhs = Term::Application {
            head: a,
            args: vec![],
        };
        let rhs = vec![
            Term::Application {
                head: b,
                args: vec![],
            },
        ];
        let rule = Statement::Rule(Rule::new(lhs, rhs).unwrap());

        assert_eq!(parsed_rule, Ok((CompleteStr(""), rule)));
    }

    #[test]
    fn statement_test_1() {
        let mut s = Signature::default();
        let a = s.get_op("a", 0);
        let p = Parser::new(&mut s);
        let (_, parsed_statement) = p.statement(CompleteStr("a()"));
        let statement = Statement::Term(Term::Application {
            head: a,
            args: vec![],
        });
        assert_eq!(parsed_statement, Ok((CompleteStr(""), statement)));
    }
    #[test]
    fn statement_test_2() {
        let mut s = Signature::default();
        let a = s.get_op("a", 0);
        let b = s.get_op("b", 0);
        let dot = s.get_op(".", 2);
        let p = Parser::new(&mut s);
        let (_, parsed_statement) = p.statement(CompleteStr("a b"));

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
        let mut s = Signature::default();
        let a = s.get_op("a", 0);
        let p = Parser::new(&mut s);
        let (_, parsed_program) = p.program(CompleteStr("a();"));
        let program = Statement::Term(Term::Application {
            head: a,
            args: vec![],
        });

        assert_eq!(parsed_program, Ok((CompleteStr(""), vec![program])));
    }

    #[test]
    fn parser_debug() {
        let mut sig = Signature::default();
        let p = Parser { signature: &mut sig };
        assert_eq!(format!("{:?}", p),
                   "Parser { signature: Signature { operators: [], variables: [], operator_count: 0, variable_count: 0 } }");
    }
    #[test]
    fn parser_incomplete() {
        let mut sig = Signature::default();
        let res = sig.parse("(a b c");
        assert_eq!(res, Err("parse incomplete!"));
    }
}
