use itertools::Itertools;

use super::{Context, Operator, Signature, Term};

pub trait Pretty: Sized {
    fn as_application(&self) -> Option<(Operator, &[Self])>;
    fn display(&self, sig: &Signature) -> String;

    fn pretty(&self, sig: &Signature) -> String {
        self.pretty_inner(sig, true)
    }
    /// `spaces_allowed` informs whether most top-level prettified item can contain spaces.
    fn pretty_inner(&self, sig: &Signature, spaces_allowed: bool) -> String {
        if let Some((op, args)) = self.as_application() {
            let op_str = op.display(sig);
            // the following match `return`s applicable special cases
            match (op_str.as_str(), args.len()) {
                ("NIL", 0) | ("NULL", 0) => return "[]".to_string(),
                ("ZERO", 0) => return "0".to_string(),
                (_, 0) => return op_str,
                ("SUCC", 1) => {
                    if let Some(s) = pretty_number(sig, args) {
                        return s;
                    }
                }
                ("DECC", 2) => {
                    if let Some(s) = pretty_decimal(sig, args) {
                        return s;
                    }
                }
                (".", 2) => return pretty_binary_application(sig, args, spaces_allowed),
                ("CONS", 2) => {
                    if let Some(s) = pretty_list(sig, args) {
                        return s;
                    }
                }
                _ => (),
            }
            let args_str = args.iter()
                .map(|arg| arg.pretty_inner(sig, true))
                .join(", ");
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

fn pretty_number<T: Pretty>(sig: &Signature, args: &[T]) -> Option<String> {
    let mut increments = 1;
    let mut arg = &args[0];
    while let Some((op, args)) = arg.as_application() {
        match (op.display(sig).as_str(), args.len()) {
            ("SUCC", 1) => {
                increments += 1;
                arg = &args[0]
            }
            ("ZERO", 0) | ("0", 0) => return Some(increments.to_string()),
            // number does not terminate with ZERO, so we use the
            // non-special-case printing style
            _ => break,
        }
    }
    None
}

fn pretty_decimal<T: Pretty>(sig: &Signature, args: &[T]) -> Option<String> {
    println!("{}", args.len());
    let mut arg = &args[0];
    let mut gathered_digits: String;
    if let Some((_, number_arg)) = args[1].as_application() {
        if number_arg.len() == 0 {
            gathered_digits = "0".to_string();
        } else if let Some(val) = pretty_number(sig, number_arg) {
            gathered_digits = val.to_string();
        } else {
            return None;
        }
        while let Some((op, args)) = arg.as_application() {
            match (op.display(sig).as_str(), args.len()) {
                ("DECC", 2) => {
                    if let Some((_, number_arg)) = &args[1].as_application() {
                        arg = &args[0];
                        if number_arg.len() == 0 {
                            gathered_digits = format!("{}{}", "0", gathered_digits);
                        } else if let Some(digit) = pretty_number(sig, number_arg) {
                            gathered_digits = format!("{}{}", digit, gathered_digits);
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                ("SUCC", 1) => {
                    if let Some(digit) = pretty_number(sig, args) {
                        return Some(format!("{}{}", digit, gathered_digits));
                    } else {
                        break;
                    }
                }
                ("ZERO", 0) | ("0", 0) => {
                    return Some(gathered_digits);
                }
                _ => break,
            }
        }
    }
    None
}

fn pretty_binary_application<T: Pretty>(
    sig: &Signature,
    args: &[T],
    spaces_allowed: bool,
) -> String {
    let mut first = &args[0];
    let mut rest = vec![&args[1]]; // in reverse order for fast `push`ing
    while let Some((op, args)) = first.as_application() {
        match (op.display(sig).as_str(), args.len()) {
            (".", 2) => {
                first = &args[0];
                rest.push(&args[1]);
            }
            _ => break,
        }
    }
    rest.push(first);
    rest.reverse();
    let interior = rest.into_iter()
        .map(|x| x.pretty_inner(sig, false))
        .join(" ");
    if spaces_allowed {
        interior
    } else {
        format!("({})", interior)
    }
}

fn pretty_list<T: Pretty>(sig: &Signature, args: &[T]) -> Option<String> {
    let mut items = vec![&args[0]];
    let mut cdr = &args[1];
    while let Some((op, args)) = cdr.as_application() {
        match (op.display(sig).as_str(), args.len()) {
            ("CONS", 2) => {
                items.push(&args[0]);
                cdr = &args[1];
            }
            ("NIL", 0) | ("NULL", 0) => {
                return Some(format!(
                    "[{}]",
                    items
                        .into_iter()
                        .map(|item| item.pretty_inner(sig, true))
                        .join(", ")
                ))
            }
            // list does not terminate with NIL, so we use the
            // non-special-case printing style
            _ => break,
        }
    }
    None
}
