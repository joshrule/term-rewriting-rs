pub mod types {
    /// A `Name` is an optional `String` telling us the name of an atom.
    pub type Name = Option<String>;

    /// A `DeBruin` is a `usize` determining the identity of an atom.
    pub type DeBruin = usize;

    /// An `Arity` is a `usize` determining the number of arguments an
    /// `Operator` takes.
    pub type Arity = usize;

    /// An `Operator` is a symbol with fixed arity.
    #[derive(Debug, Clone)]
    pub struct Operator {
        id: DeBruin,
        arity: Arity,
        name: Name,
    }
    impl Operator {
        pub fn new(name: Name, arity: Arity) -> Operator {
            Operator { id: 0, name, arity }
        }
        pub fn name(&self) -> &Name {
            &self.name
        }
        pub fn arity(&self) -> Arity {
            self.arity
        }
    }
    impl PartialEq for Operator {
        fn eq(&self, other: &Operator) -> bool {
            self.id == other.id && self.arity == other.arity
        }
    }

    /// A `Variable` is a symbol representing an unspecified term.
    #[derive(Debug, Clone)]
    pub struct Variable {
        id: DeBruin,
        name: Name,
    }
    impl Variable {
        pub fn new(name: Name) -> Variable {
            Variable { id: 0, name }
        }
        pub fn name(&self) -> &Name {
            &self.name
        }
    }
    impl PartialEq for Variable {
        fn eq(&self, other: &Variable) -> bool {
            self.id == other.id
        }
    }

    /// A `Rule` equates a LHS `Term` with a RHS `Term`.
    #[derive(Debug, PartialEq)]
    pub struct Rule {
        lhs: Term,
        rhs: Vec<Term>,
    }
    impl Rule {
        pub fn new(lhs: Term, rhs: Vec<Term>) -> Rule {
            Rule { lhs, rhs }
        }
    }

    #[derive(Debug, PartialEq)]
    pub enum Statement {
        Term(Term),
        Rule(Rule),
    }

    /// A `TRS` is a list of `Rule`s.
    #[derive(Debug)]
    pub struct TRS {
        rules: Vec<Rule>,
    }
    impl TRS {
        pub fn new(rules: Vec<Rule>) -> TRS {
            TRS { rules }
        }
    }

    /// a `Term` is either a `Variable` or an `Application
    #[derive(Debug, PartialEq, Clone)]
    pub enum Term {
        Variable(Variable),
        Application { head: Operator, args: Vec<Term> },
    }

    /// an `Atom` is either a `Variable` or an `Operator`
    #[derive(Debug)]
    pub enum Atom {
        Operator(Operator),
        Variable(Variable),
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn new_operator() {
            assert_eq!(
                Operator::new(Some("abc".to_string()), 1),
                Operator {
                    id: 0,
                    name: Some("abc".to_string()),
                    arity: 1,
                }
            )
        }
    }

}

#[macro_use]
extern crate nom;

pub mod parser {
    use super::types::*;
    use nom::alphanumeric;
    use nom::types::CompleteStr;
    use nom::IResult;

    named!(lbracket<CompleteStr, CompleteStr>,   tag!("["));
    named!(rbracket<CompleteStr, CompleteStr>,   tag!("]"));
    named!(lparen<CompleteStr, CompleteStr>,     tag!("("));
    named!(rparen<CompleteStr, CompleteStr>,     tag!(")"));
    named!(pipe<CompleteStr, CompleteStr>,       tag!("|"));
    named!(semicolon<CompleteStr, CompleteStr>,  tag!(";"));
    named!(rule_kw<CompleteStr, CompleteStr>,    tag!("="));
    named!(underscore<CompleteStr, CompleteStr>, tag!("_"));
    named!(octothorpe<CompleteStr, CompleteStr>, tag!("#"));
    named!(identifier<CompleteStr, CompleteStr>, call!(alphanumeric));

    #[derive(Debug)]
    pub struct Parser {
        operators: Vec<Operator>,
        variables: Vec<Variable>,
    }
    impl Parser {
        fn new() -> Parser {
            Parser {
                operators: vec![],
                variables: vec![],
            }
        }

        fn get_or_make_var(&mut self, name: &str) -> Variable {
            for v in &self.variables {
                let vname = v.name();
                match vname {
                    &Some(ref n) if n == name => return v.clone(),
                    _ => (),
                }
            }
            let var = Variable::new(Some(name.to_string()));
            self.variables.push(var.clone());
            var
        }

        fn has_op(&mut self, name: &str, arity: Arity) -> Option<Operator> {
            let res = self.operators.iter().find(
                |&&ref o|
                match o.name() {
                    &Some(ref n) if n == name && arity == o.arity() => true,
                    _ => false
                }
            );
            match res {
                Some(o) => Some(o.clone()),
                _ => None
            }
        }

        fn get_or_make_op2<'a>(
            mut self: Parser, input: CompleteStr<'a>,  name: &str, arity: Arity)
            -> (Self, IResult<CompleteStr<'a>, Operator>) {
            match self.has_op(name, arity) {
                Some(o) => (self, Ok((input, o))),
                None => {let op = Operator::new(Some(name.to_string()), arity);
                         self.operators.push(op.clone());
                         (self, Ok((input, op)))
                }
            }
        }
        
        fn clear_variables(&mut self) {
            self.variables.clear();
        }

        method!(variable<Parser, CompleteStr, Term>, mut self,
                map!(terminated!(identifier, underscore),
                     |v| Term::Variable(self.get_or_make_var(v.0)))
        );

        // there was a bug in delimited! (or in tuple_parser! closures)
        method!(application<Parser, CompleteStr, Term>, mut self,
                do_parse!(name: identifier >>
                          lparen >>
                          args: many0!(ws!(call_m!(self.term))) >>
                          rparen >>
                          head: call_m!(self.get_or_make_op2,
                                        name.0,
                                        args.len()) >>
                          (Term::Application{head, args})) 
        );
        
        method!(term<Parser, CompleteStr, Term>, mut self,
                alt!(call_m!(self.variable) | call_m!(self.application))
        );

        method!(rule<Parser, CompleteStr, Statement>, mut self,
                do_parse!(lhs: call_m!(self.term) >>
                          ws!(rule_kw) >>
                          rhs: separated_nonempty_list!(ws!(pipe),
                                                        call_m!(self.term)) >>
                          (Statement::Rule(Rule::new(lhs, rhs))))
        );
        
        method!(statement<Parser, CompleteStr, Statement>, mut self,
                do_parse!(term: call_m!(self.term) >>
                          (Statement::Term(term))));
        
        method!(program<Parser, CompleteStr, Vec<Statement>>, mut self,
                many0!(map!(terminated!(alt!(call_m!(self.rule) |
                                             call_m!(self.statement)),
                                        ws!(semicolon)),
                            |s| {self.clear_variables(); s}))
        );
    }

    pub fn parse(input: &str) -> Result<(TRS, Vec<Term>), &str> {
        let (_parser, result) = Parser::new().program(CompleteStr(input));
        match result {
            Ok((CompleteStr(""), o)) => {
                let (srs, sts): (Vec<Statement>, Vec<Statement>) =
                    o.into_iter().partition(|x| match x {
                        &Statement::Rule(_) => true,
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
            Ok((CompleteStr(_), _)) => Err("parse incomplete!"),
            Err(_) => Err("parse failed!"),
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn lbracket_test() {
            assert_eq!(
                lbracket(CompleteStr("[")),
                Ok((CompleteStr(""), CompleteStr("[")))
            );
        }

        #[test]
        fn rbracket_test() {
            assert_eq!(
                rbracket(CompleteStr("]")),
                Ok((CompleteStr(""), CompleteStr("]")))
            );
        }

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
        fn octothorpe_test() {
            assert_eq!(
                octothorpe(CompleteStr("#")),
                Ok((CompleteStr(""), CompleteStr("#")))
            );
        }

        #[test]
        fn var_test() {
            let p = Parser::new();
            let (_, var) = p.variable(CompleteStr("abc_"));
            assert_eq!(
                var,
                Ok((
                    CompleteStr(""),
                    Term::Variable(Variable::new(Some("abc".to_string())))
                ))
            );
        }

        #[test]
        fn app_test() {
            let (_, app) = Parser::new().application(CompleteStr("abc()"));
        
            let term = Term::Application {
                head: Operator::new(Some("abc".to_string()), 0),
                args: vec![],
            };
        
            assert_eq!(app, Ok((CompleteStr(""), term)));
        }
        
        #[test]
        fn term_test() {
            let (_, parsed_t1) = Parser::new().term(CompleteStr("a()"));
            let (_, parsed_t2) = Parser::new().term(CompleteStr("a_"));
            let (_, parsed_t3) = Parser::new().term(CompleteStr("A(x_ A(x_ x_))"));
        
            let t1 = Term::Application {
                head: Operator::new(Some("a".to_string()), 0),
                args: vec![],
            };
        
            let t2 = Term::Variable(Variable::new(Some("a".to_string())));
        
            let a1 = Operator::new(Some("A".to_string()), 2);
            let a2 = a1.clone();
            let x1 = Term::Variable(Variable::new(Some("x".to_string())));
            let x2 = x1.clone();
            let x3 = x2.clone();
            let t3 = Term::Application {
                head: a1,
                args: vec![
                    x1,
                    Term::Application {
                        head: a2,
                        args: vec![x2, x3],
                    },
                ],
            };
        
            assert_eq!(parsed_t1, Ok((CompleteStr(""), t1)));
            assert_eq!(parsed_t2, Ok((CompleteStr(""), t2)));
            assert_eq!(parsed_t3, Ok((CompleteStr(""), t3)));
        }
        
        #[test]
        fn rule_test() {
            let lhs = Term::Application {
                head: Operator::new(Some("a".to_string()), 0),
                args: vec![],
            };
        
            let rhs = vec![
                Term::Application {
                    head: Operator::new(Some("b".to_string()), 0),
                    args: vec![],
                },
            ];
        
            let rule = Statement::Rule(Rule::new(lhs, rhs));
        
            let (_, parsed_rule) = Parser::new().rule(CompleteStr("a() = b()"));
            assert_eq!(parsed_rule, Ok((CompleteStr(""), rule)));
        }
        
        #[test]
        fn statement_test() {
            let (_, parsed_statement) = Parser::new()
                .statement(CompleteStr("a()"));
        
            let term = Statement::Term(Term::Application {
                head: Operator::new(Some("a".to_string()), 0),
                args: vec![],
            });
        
            assert_eq!(parsed_statement, Ok((CompleteStr(""), term)));
        }
        
        #[test]
        fn program_test() {
            let (_, parsed_program) = Parser::new()
                .program(CompleteStr("a();"));
            let program = Statement::Term(Term::Application {
                head: Operator::new(Some("a".to_string()), 0),
                args: vec![],
            });
        
            assert_eq!(parsed_program, Ok((CompleteStr(""), vec![program])));
        }

    }
}
