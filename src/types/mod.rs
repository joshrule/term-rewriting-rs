/// Represents the name of a `Variable` or an `Operator`.
pub type Name = Option<String>;

/// Represents the unique identity of a Variable or an Operator.
pub type DeBruin = u32;

/// Represents the number of arguments an `Operator` takes.
pub type Arity = u32;

pub use self::operator::*;
mod operator;

pub use self::variable::*;
mod variable;

pub use self::term::*;
mod term;

pub use self::rule::*;
mod rule;

pub use self::trs::*;
mod trs;
