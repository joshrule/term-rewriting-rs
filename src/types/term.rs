use super::{Variable, Operator};

/// a `Term` is either a `Variable` or an `Application
#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    Variable(Variable),
    Application { head: Operator, args: Vec<Term> },
}
impl Term {
    pub fn variables(&self) -> Vec<&Variable> {
        match self {
            &Term::Variable(ref v) => vec![&v],
            &Term::Application { args: ref a, .. } => {
                let res: Vec<&Variable> = a.iter().flat_map(|x| x.variables()).collect();
                res
            }
        }
    }
}
