
pub mod types {
    type Name = String;
    type DeBruin = usize;
    type Arity = usize;

    /// an `Operator` is a symbol with fixed arity
    pub struct Operator {
        id: DeBruin,
        arity: Arity,
        name: Name,
    }

    /// a `Variable` is a symbol representing an unspecified term
    pub struct Variable {
        id: DeBruin,
        name: Option<Name>,
    }

    /// an `Application` applies an `Operator` to `Term` arguments
    pub struct Application {
        head: Operator,
        args: Vec<Term>,
    }

    /// an `Atom` is either a `Variable` or an `Operator`
    pub enum Atom {
        Var(Variable),
        Op(Operator),
    }

    /// a `Term` is either a `Variable` or an `Application
    pub enum Term {
        Var(Variable),
        App(Application),
    }
}


// #[cfg(test)]
// mod tests {
//     #[test]
//     fn it_works() {
//         assert_eq!(2 + 2, 4);
//     }
// }
