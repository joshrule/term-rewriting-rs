use super::Signature;

/// A symbol for an unspecified term. Only carries meaning alongside a [`Signature`].
///
/// To construct a `Variable`, use [`Signature::new_var`]
///
/// [`Signature`]: struct.Signature.html
/// [`Signature::new_var`]: struct.Signature.html#method.new_var
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable(pub usize);

/// A symbol with fixed arity. Only carries meaning alongside a [`Signature`].
///
/// To construct an `Operator`, use [`Signature::new_op`].
///
/// [`Signature`]: struct.Signature.html
/// [`Signature::new_op`]: struct.Signature.html#method.new_op
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Operator(pub usize);

/// `Atom`s are the parts of a [`TRS`] that are not constructed from smaller parts: [`Variable`]s and [`Operator`]s.
///
/// [`TRS`]: struct.TRS.html
/// [`Variable`]: struct.Variable.html
/// [`Operator`]: struct.Operator.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    /// assert_eq!(atom.display(&sig), "v0_");
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SituatedAtom<'a> {
    pub sig: &'a Signature,
    pub atom: Atom,
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
        self.0
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
    /// assert_eq!(var.name(&sig), Some("z"));
    /// ```
    pub fn name(self, sig: &Signature) -> Option<&str> {
        sig.variables[self.0].as_deref()
    }
    /// Serialize a `Variable`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use term_rewriting::Signature;
    /// let mut sig = Signature::default();
    /// let var = sig.new_var(None);
    ///
    /// assert_eq!(var.display(), "v0_");
    /// ```
    pub fn display(self) -> String {
        format!("v{}_", self.0)
    }
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
        self.0
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
    /// assert_eq!(op.arity(&sig), 2);
    /// ```
    pub fn arity(self, sig: &Signature) -> u8 {
        sig.operators[self.0].0
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
    /// assert_eq!(op.name(&sig), Some("Z"));
    /// ```
    pub fn name(self, sig: &Signature) -> Option<&str> {
        sig.operators[self.0].1.as_deref()
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
        match sig.operators[self.0].1 {
            None => format!("op{}", self.0),
            Some(ref name) => name.clone(),
        }
    }
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
    /// assert_eq!(atom.display(&sig), "v0_");
    /// ```
    pub fn display(self, sig: &Signature) -> String {
        match self {
            Atom::Variable(v) => v.display(),
            Atom::Operator(o) => o.display(sig),
        }
    }
    pub fn constant(self, sig: &Signature) -> bool {
        match self {
            Atom::Variable(_) => true,
            Atom::Operator(o) => o.arity(sig) == 0,
        }
    }
    pub fn is_operator(self) -> bool {
        match self {
            Atom::Variable(_) => false,
            Atom::Operator(_) => true,
        }
    }
    pub fn is_variable(self) -> bool {
        match self {
            Atom::Variable(_) => true,
            Atom::Operator(_) => false,
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

impl<'a> SituatedAtom<'a> {
    pub fn new(atom: Atom, sig: &'a Signature) -> Self {
        SituatedAtom { atom, sig }
    }
}
