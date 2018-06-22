use itertools::Itertools;

use super::{Context, Operator, Signature, Term};

pub trait Pretty: Sized {
    fn as_application(&self) -> Option<(Operator, &[Self])>;
    fn display(&self, sig: &Signature) -> String;

    fn pretty(&self, sig: &Signature) -> String {
        if let Some((op, args)) = self.as_application() {
            let op_str = op.display(sig);
            // the following match `return`s applicable special cases
            match (op_str.as_str(), args.len()) {
                ("NIL", 0) | ("NULL", 0) => return "[]".to_string(),
                (_, 0) => return op_str,
                ("SUCC", 1) => {
                    let mut increments = 1;
                    let mut arg = &args[0];
                    while let Some((op, args)) = arg.as_application() {
                        match (op.display(sig).as_str(), args.len()) {
                            ("SUCC", 1) => {
                                increments += 1;
                                arg = &args[0]
                            }
                            ("ZERO", 0) | ("0", 0) => return increments.to_string(),
                            // number does not terminate with ZERO, so we use the
                            // non-special-case printing style
                            _ => break,
                        }
                    }
                }
                (".", 2) => return format!("({} {})", args[0].pretty(sig), args[1].pretty(sig)),
                ("CONS", 2) => {
                    let mut items = vec![&args[0]];
                    let mut cdr = &args[1];
                    while let Some((op, args)) = cdr.as_application() {
                        match (op.display(sig).as_str(), args.len()) {
                            ("CONS", 2) => {
                                items.push(&args[0]);
                                cdr = &args[1];
                            }
                            ("NIL", 0) | ("NULL", 0) => {
                                return format!(
                                    "[{}]",
                                    items.into_iter().map(|item| item.pretty(sig)).join(", ")
                                )
                            }
                            // list does not terminate with NIL, so we use the
                            // non-special-case printing style
                            _ => break,
                        }
                    }
                }
                _ => (),
            }
            let args_str = args.iter().map(|arg| arg.pretty(sig)).join(", ");
            format!("{}({})", op_str, args_str)
        } else {
            self.display(sig)
        }
    }
}
impl Pretty for Context {
    fn as_application(&self) -> Option<(Operator, &[Context])> {
        match *self {
            Context::Application { op, ref args } => Some((op, args)),
            _ => None,
        }
    }
    fn display(&self, sig: &Signature) -> String {
        self.display(sig)
    }
}
impl Pretty for Term {
    fn as_application(&self) -> Option<(Operator, &[Term])> {
        match *self {
            Term::Application { op, ref args } => Some((op, args)),
            _ => None,
        }
    }
    fn display(&self, sig: &Signature) -> String {
        self.display(sig)
    }
}
