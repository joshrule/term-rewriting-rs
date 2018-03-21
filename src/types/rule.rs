use super::{Term, Variable};

use std::collections::HashSet;

/// A `Rule` equates a LHS `Term` with a RHS `Term`.
#[derive(Debug, PartialEq)]
pub struct Rule {
    lhs: Term,
    rhs: Vec<Term>,
}
impl Rule {
    pub fn validate(lhs: &Term, rhs: &Vec<Term>) -> bool {
        // the lhs must be an application
        if let &Term::Application{..} = lhs {
            // variables(rhs) must be a subset of variables(lhs)
            let lhs_vars: HashSet<&Variable> = lhs.variables().into_iter().collect();
            let rhs_vars: HashSet<&Variable> =
                rhs.iter().flat_map(|&ref r| r.variables()).collect();
            if rhs_vars.is_subset(&lhs_vars) {
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    pub fn new(lhs: Term, rhs: Vec<Term>) -> Option<Rule> {
        // the lhs must be an application
        if Rule::validate(&lhs, &rhs) {
            Some(Rule { lhs, rhs })
        } else {
            None
        }
    }
}
