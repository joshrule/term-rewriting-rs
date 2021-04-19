mod atom;
mod rule;
mod signature;
mod term;
mod trs;

pub use self::atom::*;
pub use self::rule::*;
pub use self::signature::*;
pub use self::term::*;
pub use self::trs::*;
use serde_derive::{Deserialize, Serialize};

/// Represents a place in a [`Term`].
///
/// [`Term`]: enum.Term.html
pub type Place = Vec<usize>;

/// A way of signifying what type of unification is being performed
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Unification {
    Match,
    Alpha,
    Unify,
    Generalize,
}

/// A way to signify what kind of numbers a TRS uses.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NumberLogic {
    Symbolic,
    Unary,
    Decimal,
}

/// A way to signify whether a TRS is applicative or non-applicative.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Applicativeness {
    Applicative,
    NonApplicative,
}

/// A way to describe a TRS's number system.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NumberRepresentation {
    pub logic: NumberLogic,
    pub app: Applicativeness,
}

impl Default for NumberRepresentation {
    fn default() -> Self {
        NumberRepresentation {
            logic: NumberLogic::Symbolic,
            app: Applicativeness::NonApplicative,
        }
    }
}
