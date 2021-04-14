use super::{Context, Operator, Signature, Term};
use itertools::Itertools;

/// A trait for pretty printing term-like objects.
///
/// # Examples
///
/// ```
/// # use term_rewriting::{Signature, parse_term};
/// let mut sig = Signature::default();
///
/// // Construct a TRS manually.
/// let t = parse_term(&mut sig, "81").expect("81");
/// assert_eq!(t.pretty(&sig), "81");
///
/// let mut t_str = "ZERO".to_string();
/// for _ in 0..81 {
///    t_str = format!("SUCC({})", &t_str);
/// }
/// let t = parse_term(&mut sig, &t_str).expect("81");
/// assert_eq!(t.pretty(&sig), "81");
/// t_str = "ZERO".to_string();
/// for _ in 0..81 {
///    t_str = format!("(SUCC {})", &t_str);
/// }
/// let t = parse_term(&mut sig, &t_str).expect("81");
/// assert_eq!(t.pretty(&sig), "81");
///
/// let t = parse_term(&mut sig, "DECC(DIGIT(8) 1)").expect("81");
/// assert_eq!(t.pretty(&sig), "81");
/// let t = parse_term(&mut sig, "(DECC (DIGIT 8)  1)").expect("81");
/// assert_eq!(t.pretty(&sig), "81");
///
/// let t = parse_term(&mut sig, "NIL").expect("81");
/// assert_eq!(t.pretty(&sig), "[]");
/// let t = parse_term(&mut sig, "CONS(A CONS(B CONS(C NIL)))").expect("81");
/// assert_eq!(t.pretty(&sig), "[A, B, C]");
/// let t = parse_term(&mut sig, "(CONS A (CONS B (CONS C NIL)))").expect("81");
/// assert_eq!(t.pretty(&sig), "[A, B, C]");
/// ```
pub trait Pretty: Sized {
    fn as_application(&self) -> Option<(Operator, &[Self])>;
    fn as_guarded_application(
        &self,
        sig: &Signature,
        name: &str,
        arity: u8,
    ) -> Option<(Operator, &[Self])>;
    fn display(&self, sig: &Signature) -> String;

    fn pretty(&self, sig: &Signature) -> String {
        self.pretty_inner(true, sig)
    }
    /// `spaces_allowed` informs whether most top-level prettified item can contain spaces.
    fn pretty_inner(&self, spaces_allowed: bool, sig: &Signature) -> String {
        if let Some((op, args)) = self.as_application() {
            let op_str = op.display(sig);
            // the following match `return`s applicable special cases
            match (op_str.as_str(), args.len()) {
                (".", 2) => return pretty_binary_application(args, self, spaces_allowed, sig),
                ("NIL", 0) => return "[]".to_string(),
                ("CONS", 2) => {
                    if let Some(s) = pretty_list(args, sig) {
                        return s;
                    }
                }
                ("ZERO", 0) => return "0".to_string(),
                ("SUCC", 1) => {
                    if let Some(s) = pretty_unary(args, sig) {
                        return s;
                    }
                }
                ("DIGIT", 1) => {
                    if let Some(s) = digit_to_number(args, sig) {
                        return format!("{}", s);
                    }
                }
                ("DECC", 2) => {
                    if let Some(s) = pretty_decc(args, sig) {
                        return s;
                    }
                }
                (_, 0) => return op_str,
                _ => (),
            }
            let args_str = args
                .iter()
                .map(|arg| arg.pretty_inner(true, sig))
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
            Context::Application { op, ref args } => Some((op, &args)),
            _ => None,
        }
    }
    fn as_guarded_application(
        &self,
        sig: &Signature,
        name: &str,
        arity: u8,
    ) -> Option<(Operator, &[Self])> {
        match self {
            Context::Hole => None,
            Context::Variable(_) => None,
            Context::Application { op, ref args } => match (op.name(sig), op.arity(sig)) {
                (Some(s), a) if s == name && a == arity => Some((*op, args)),
                _ => None,
            },
        }
    }
    fn display(&self, sig: &Signature) -> String {
        self.display(sig)
    }
}
impl Pretty for Term {
    fn as_application(&self) -> Option<(Operator, &[Term])> {
        match *self {
            Term::Application { op, ref args } => Some((op, &args)),
            _ => None,
        }
    }
    fn as_guarded_application(
        &self,
        sig: &Signature,
        name: &str,
        arity: u8,
    ) -> Option<(Operator, &[Self])> {
        match self {
            Term::Variable(_) => None,
            Term::Application { op, ref args } => match (op.name(sig), op.arity(sig)) {
                (Some(s), a) if s == name && a == arity => Some((*op, args)),
                _ => None,
            },
        }
    }
    fn display(&self, sig: &Signature) -> String {
        self.display(sig)
    }
}

fn pretty_unary<T: Pretty>(args: &[T], sig: &Signature) -> Option<String> {
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

fn digit_to_number<T: Pretty>(args: &[T], sig: &Signature) -> Option<i32> {
    if args.len() == 1 {
        if let Some((op, args)) = &args[0].as_application() {
            if args.is_empty() {
                return str_to_number(&op.display(sig));
            }
        }
    }
    None
}

fn str_to_number(s: &str) -> Option<i32> {
    match s {
        "0" | "ZERO" => Some(0),
        "1" | "ONE" => Some(1),
        "2" | "TWO" => Some(2),
        "3" | "THREE" => Some(3),
        "4" | "FOUR" => Some(4),
        "5" | "FIVE" => Some(5),
        "6" | "SIX" => Some(6),
        "7" | "SEVEN" => Some(7),
        "8" | "EIGHT" => Some(8),
        "9" | "NINE" => Some(9),
        _ => None,
    }
}

fn pretty_decc<T: Pretty>(args: &[T], sig: &Signature) -> Option<String> {
    let mut arg = &args[0];
    let mut gathered_digits;
    let mut order_of_mag = 10;
    if let Some(val) = digit_to_number(&args[1..2], sig) {
        gathered_digits = val;
        while let Some((op, args)) = arg.as_application() {
            match (op.display(sig).as_str(), args.len()) {
                ("DECC", 2) => {
                    if let Some(digit) = digit_to_number(&args[1..2], sig) {
                        arg = &args[0];
                        gathered_digits += digit * order_of_mag;
                        order_of_mag *= 10;
                    } else {
                        break;
                    }
                }
                ("DIGIT", 1) => {
                    if let Some(digit) = digit_to_number(&args[0..1], sig) {
                        gathered_digits += digit * order_of_mag;
                        return Some(gathered_digits.to_string());
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
    }
    None
}

fn pretty_binary_application<T: Pretty>(
    args: &[T],
    term: &T,
    spaces_allowed: bool,
    sig: &Signature,
) -> String {
    if let Some(items) = convert_term_to_list(term, sig) {
        format!("[{}]", items.iter().map(|x| x.pretty(sig)).join(", "))
    } else if let Some(num) = convert_succ_num_to_usize(term, sig) {
        format!("{}", num)
    } else if let Some(num) = convert_decc_num_to_usize(term, sig) {
        format!("{}", num)
    } else {
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
        let interior = rest
            .into_iter()
            .map(|x| x.pretty_inner(false, sig))
            .join(" ");
        if spaces_allowed {
            interior
        } else {
            format!("({})", interior)
        }
    }
}

fn convert_digit_to_usize<T: Pretty>(term: &T, sig: &Signature) -> Option<usize> {
    let (op, _) = term.as_application()?;
    match (op.name(sig), op.arity(sig)) {
        (Some(s), 0) if s == "0" => Some(0),
        (Some(s), 0) if s == "1" => Some(1),
        (Some(s), 0) if s == "2" => Some(2),
        (Some(s), 0) if s == "3" => Some(3),
        (Some(s), 0) if s == "4" => Some(4),
        (Some(s), 0) if s == "5" => Some(5),
        (Some(s), 0) if s == "6" => Some(6),
        (Some(s), 0) if s == "7" => Some(7),
        (Some(s), 0) if s == "8" => Some(8),
        (Some(s), 0) if s == "9" => Some(9),
        _ => None,
    }
}
fn convert_decc_num_to_usize<T: Pretty>(term: &T, sig: &Signature) -> Option<usize> {
    let (_, args) = term.as_guarded_application(sig, ".", 2)?;
    if args[0].as_guarded_application(sig, "DIGIT", 0).is_some() {
        convert_digit_to_usize(&args[1], sig)
    } else {
        let (_, inner_args) = args[0].as_guarded_application(sig, ".", 2)?;
        inner_args[0].as_guarded_application(sig, "DECC", 0)?;
        let sigs = convert_decc_num_to_usize(&inner_args[1], sig)?;
        let digit = convert_digit_to_usize(&args[1], sig)?;
        sigs.checked_mul(10).and_then(|x| x.checked_add(digit))
    }
}

pub fn convert_succ_num_to_usize<T: Pretty>(term: &T, sig: &Signature) -> Option<usize> {
    if term.as_guarded_application(sig, "ZERO", 0).is_some() {
        Some(0)
    } else {
        let (_, args) = term.as_guarded_application(sig, ".", 2)?;
        args[0].as_guarded_application(sig, "SUCC", 0)?;
        Some(1 + convert_succ_num_to_usize(&args[1], sig)?)
    }
}

pub fn convert_term_to_list<'a, T: Pretty>(term: &'a T, sig: &Signature) -> Option<Vec<&'a T>> {
    if term.as_guarded_application(sig, "NIL", 0).is_some() {
        Some(vec![])
    } else {
        let (_, args) = term.as_guarded_application(sig, ".", 2)?;
        let (_, inner_args) = args[0].as_guarded_application(sig, ".", 2)?;
        inner_args[0].as_guarded_application(sig, "CONS", 0)?;
        let mut string = vec![&inner_args[1]];
        string.append(&mut convert_term_to_list(&args[1], sig)?);
        Some(string)
    }
}

fn pretty_list<T: Pretty>(args: &[T], sig: &Signature) -> Option<String> {
    let mut items = vec![&args[0]];
    let mut cdr = &args[1];
    while let Some((op, args)) = cdr.as_application() {
        match (op.display(sig).as_str(), args.len()) {
            ("CONS", 2) => {
                items.push(&args[0]);
                cdr = &args[1];
            }
            ("NIL", 0) => {
                return Some(format!(
                    "[{}]",
                    items
                        .into_iter()
                        .map(|item| item.pretty_inner(true, sig))
                        .join(", ")
                ));
            }
            // list does not terminate with NIL, so we use the
            // non-special-case printing style
            _ => break,
        }
    }
    None
}
