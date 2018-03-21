use std::sync::atomic::{AtomicUsize, Ordering};

/// A `Name` is an optional `String` telling us the name of an atom.
pub type Name = Option<String>;

/// A `DeBruin` is a `usize` determining the identity of an atom.
pub type DeBruin = usize;

/// An `Arity` is a `usize` determining the number of arguments an
/// `Operator` takes.
pub type Arity = usize;

lazy_static! {
    static ref OP_ID: AtomicUsize = AtomicUsize::new(0);
}

lazy_static! {
    static ref VAR_ID: AtomicUsize = AtomicUsize::new(0);
}

/// Returns the next internal counter, incrementing it.
fn op_next() -> usize {
    OP_ID.fetch_add(1, Ordering::Relaxed)
}

/// Returns the next internal counter, incrementing it.
fn var_next() -> usize {
    VAR_ID.fetch_add(1, Ordering::Relaxed)
}

/// An `Operator` is a symbol with fixed arity.
#[derive(Debug, Clone)]
pub struct Operator {
    id: DeBruin,
    arity: Arity,
    name: Name,
}
impl Operator {
    pub fn new(name: Name, arity: Arity) -> Operator {
        Operator {
            id: op_next(),
            name,
            arity,
        }
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
#[derive(Debug, Clone, Eq)]
pub struct Variable {
    id: DeBruin,
    name: Name,
}
impl Variable {
    pub fn new(name: Name) -> Variable {
        Variable {
            id: var_next(),
            name,
        }
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
impl Hash for Variable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

use std::hash::{Hash, Hasher};
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
        if lhs.is_application() {
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
impl Term {
    fn variables(&self) -> Vec<&Variable> {
        match self {
            &Term::Variable(ref v) => vec![&v],
            &Term::Application { args: ref a, .. } => {
                let res: Vec<&Variable> = a.iter().flat_map(|x| x.variables()).collect();
                res
            }
        }
    }

    pub fn is_variable(&self) -> bool {
        match self {
            &Term::Variable(_) => true,
            _ => false,
        }
    }

    pub fn is_application(&self) -> bool {
        match self {
            &Term::Application { .. } => true,
            _ => false,
        }
    }
}
