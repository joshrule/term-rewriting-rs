use super::Signature;

/// A symbol for an unspecified term. Only carries meaning alongside a [`Signature`].
///
/// To construct a `Variable`, use [`Signature::new_var`]
///
/// [`Signature`]: struct.Signature.html
/// [`Signature::new_var`]: struct.Signature.html#method.new_var
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable {
    pub(crate) id: usize,
}
impl Variable {
    /// Returns a `Variable`'s id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let var = sig.new_var(Some("z".to_string()));
    ///
    /// assert_eq!(var.id(), 0);
    /// ```
    pub fn id(self) -> usize {
        self.id
    }
    /// Returns a `Variable`'s name.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let var = sig.new_var(Some("z".to_string()));
    ///
    /// assert_eq!(var.name(&sig), Some("z".to_string()));
    /// ```
    pub fn name(self, sig: &Signature) -> Option<String> {
        sig.sig.read().expect("poisoned signature").variables[self.id].clone()
    }
    /// Serialize a `Variable`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let var = sig.new_var(Some("z".to_string()));
    ///
    /// assert_eq!(var.display(&sig), "z_");
    /// ```
    pub fn display(self, sig: &Signature) -> String {
        if let Some(ref name) = sig.sig.read().expect("poisoned signature").variables[self.id] {
            format!("{}_", name)
        } else {
            format!("var{}_", self.id)
        }
    }
}

/// A symbol with fixed arity. Only carries meaning alongside a [`Signature`].
///
/// To construct an `Operator`, use [`Signature::new_op`].
///
/// [`Signature`]: struct.Signature.html
/// [`Signature::new_op`]: struct.Signature.html#method.new_op
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Operator {
    pub(crate) id: usize,
    pub(crate) arity: u8,
}
impl Operator {
    /// Returns an `Operator`'s id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(2, Some("z".to_string()));
    ///
    /// assert_eq!(op.id(), 0);
    /// ```
    pub fn id(self) -> usize {
        self.id
    }
    /// Returns an `Operator`'s arity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(2, Some("Z".to_string()));
    ///
    /// assert_eq!(op.arity(), 2);
    /// ```
    pub fn arity(self) -> u8 {
        self.arity
    }
    /// Returns an `Operator`'s name.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(2, Some("Z".to_string()));
    ///
    /// assert_eq!(op.name(&sig), Some("Z".to_string()));
    /// ```
    pub fn name(self, sig: &Signature) -> Option<String> {
        sig.sig.read().expect("poisoned signature").operators[self.id]
            .1
            .clone()
    }
    /// Serialize an `Operator`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let op = sig.new_op(2, Some("Z".to_string()));
    ///
    /// assert_eq!(op.display(&sig), "Z");
    /// ```
    pub fn display(self, sig: &Signature) -> String {
        if let (_, Some(ref name)) = sig.sig.read().expect("poisoned signature").operators[self.id]
        {
            name.clone()
        } else {
            format!("op{}", self.id)
        }
    }
}

/// `Atom`s are the parts of a [`TRS`] that are not constructed from smaller parts: [`Variable`]s and [`Operator`]s.
///
/// [`TRS`]: struct.TRS.html
/// [`Variable`]: struct.Variable.html
/// [`Operator`]: struct.Operator.html
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Atom {
    /// The [`Variable`] variant of an `Atom`.
    ///
    /// [`Variable`]: struct.Variable.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Atom};
    /// let mut sig = Signature::default();
    /// let x = sig.new_var(Some("x".to_string()));
    /// let atom = Atom::Variable(x);
    ///
    /// assert_eq!(atom.display(&sig), "x_");
    /// ```
    Variable(Variable),
    /// The [`Operator`] variant of an `Atom`.
    ///
    /// [`Operator`]: struct.Operator.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Atom};
    /// let mut sig = Signature::default();
    /// let a = sig.new_op(0, Some("A".to_string()));
    /// let atom = Atom::Operator(a);
    ///
    /// assert_eq!(atom.display(&sig), "A");
    /// ```
    Operator(Operator),
}
impl Atom {
    /// Serialize an `Atom`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::{Signature, Atom};
    /// let mut sig = Signature::default();
    ///
    /// let a = sig.new_op(0, Some("A".to_string()));
    /// let atom = Atom::Operator(a);
    ///
    /// assert_eq!(atom.display(&sig), "A");
    ///
    /// let x = sig.new_var(Some("x".to_string()));
    /// let atom = Atom::Variable(x);
    ///
    /// assert_eq!(atom.display(&sig), "x_");
    /// ```
    pub fn display(self, sig: &Signature) -> String {
        match self {
            Atom::Variable(v) => v.display(sig),
            Atom::Operator(o) => o.display(sig),
        }
    }
    pub fn constant(self) -> bool {
        match self {
            Atom::Variable(_) => true,
            Atom::Operator(o) => o.arity() == 0,
        }
    }
}
impl From<Variable> for Atom {
    fn from(var: Variable) -> Atom {
        Atom::Variable(var)
    }
}
impl From<Operator> for Atom {
    fn from(op: Operator) -> Atom {
        Atom::Operator(op)
    }
}
