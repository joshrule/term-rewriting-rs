use super::Rule;

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
