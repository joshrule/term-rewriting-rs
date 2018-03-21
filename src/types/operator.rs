use std::sync::atomic::{AtomicUsize, Ordering};

use super::{DeBruin, Arity, Name};

lazy_static! {
    static ref OP_ID: AtomicUsize = AtomicUsize::new(0);
}

/// Returns the next internal counter, incrementing it.
fn op_next() -> usize {
    OP_ID.fetch_add(1, Ordering::Relaxed)
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
