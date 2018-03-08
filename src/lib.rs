pub mod types {
    /// A `Name` is an optional `String` telling us the name of an atom.
    type Name = Option<String>;

    /// A `DeBruin` is a `usize` determining the identity of an atom.
    type DeBruin = usize;

    /// An `Arity` is a `usize` determining the number of arguments an
    /// `Operator` takes.
    type Arity = usize;

    /// An `Operator` is a symbol with fixed arity.
    #[derive(Debug)]
    pub struct Operator {
        id: DeBruin,
        arity: Arity,
        name: Name,
    }
    impl Operator {
        pub fn new(name: Name, arity: Arity) -> Operator {
            Operator { id: 0, name, arity }
        }
    }
    impl PartialEq for Operator {
        fn eq(&self, other: &Operator) -> bool {
            self.id == other.id && self.arity == other.arity
        }
    }

    /// A `Variable` is a symbol representing an unspecified term.
    #[derive(Debug)]
    pub struct Variable {
        id: DeBruin,
        name: Name,
    }
    impl Variable {
        pub fn new(name: Name) -> Variable {
            Variable { id: 0, name }
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
    #[derive(Debug, PartialEq)]
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

    named!(operator<CompleteStr, Operator>,
           do_parse!(name: identifier >>
                     (Operator::new(Some(name.0.to_string()), 1)))
    );

    named!(variable<CompleteStr, Term>,
           do_parse!(name: terminated!(identifier, underscore)  >>
                     (Term::Variable(Variable::new(Some(name.0.to_string())))))
    );

    named!(application<CompleteStr, Term>,
           do_parse!(head: identifier >>
                     args: delimited!(lparen, many0!(ws!(term)), rparen) >>
                     (Term::Application{
                         head: Operator::new(Some(head.0.to_string()),
                                             args.len()),
                         args}))

    );

    named!(term<CompleteStr, Term>,
           alt!(variable | application)
    );

    named!(rule<CompleteStr, Statement>,
           do_parse!(lhs: term >>
                     ws!(rule_kw) >>
                     rhs: separated_nonempty_list!(ws!(pipe), term) >>
                     (Statement::Rule(Rule::new(lhs, rhs))))
    );

    named!(statement<CompleteStr, Statement>,
           do_parse!(term: term >>
                     (Statement::Term(term)))
    );

    named!(program<CompleteStr, Vec<Statement>>,
           many0!(terminated!(alt!(rule | statement), ws!(semicolon)))
    );

    pub fn parse(input: &str) -> Result<(TRS, Vec<Term>), &str> {
        match program(CompleteStr(input)) {
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
            assert_eq!(
                variable(CompleteStr("abc_")),
                Ok((
                    CompleteStr(""),
                    Term::Variable(Variable::new(Some("abc".to_string())))
                ))
            );
        }

        #[test]
        fn app_test() {
            let term = Term::Application {
                head: Operator::new(Some("abc".to_string()), 0),
                args: vec![],
            };

            assert_eq!(
                application(CompleteStr("abc()")),
                Ok((CompleteStr(""), term))
            );
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

            assert_eq!(
                super::rule(CompleteStr("a() = b()")),
                Ok((CompleteStr(""), rule))
            );
        }

        #[test]
        fn statement_test() {
            let term = Statement::Term(Term::Application {
                head: Operator::new(Some("a".to_string()), 0),
                args: vec![],
            });

            assert_eq!(statement(CompleteStr("a()")), Ok((CompleteStr(""), term)));
        }

        #[test]
        fn program_test() {
            let term = Statement::Term(Term::Application {
                head: Operator::new(Some("a".to_string()), 0),
                args: vec![],
            });

            assert_eq!(
                program(CompleteStr("a();")),
                Ok((CompleteStr(""), vec![term]))
            );
        }

    }
}
