use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicUsize, Ordering};

use super::{DeBruin, Name};

lazy_static! {
    static ref VAR_ID: AtomicUsize = AtomicUsize::new(0);
}

/// Returns the next internal counter, incrementing it.
fn var_next() -> usize {
    VAR_ID.fetch_add(1, Ordering::Relaxed)
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
