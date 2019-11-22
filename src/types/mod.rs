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

/// Represents a place in a [`Term`].
///
/// [`Term`]: enum.Term.html
pub type Place = Vec<usize>;

/// A way of signifying what type of unification is being performed
#[derive(PartialEq, Eq)]
enum Unification {
    Match,
    Alpha,
    Unify,
    Generalize,
}
