pub mod document;
pub mod github;
pub mod json;
pub mod sarif;
pub mod text;

use crate::source::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    Error,
    Warning,
    Info,
}

impl Severity {
    pub const fn as_str(self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Info => "info",
        }
    }

    pub(crate) const fn sgr(self) -> u8 {
        match self {
            Severity::Error => 31,
            Severity::Warning => 33,
            Severity::Info => 36,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FixSafety {
    Safe,
    Unsafe,
}

impl FixSafety {
    pub const fn as_str(self) -> &'static str {
        match self {
            FixSafety::Safe => "safe",
            FixSafety::Unsafe => "unsafe",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edit {
    pub span: Span,
    pub new_text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fix {
    pub title: String,
    pub safety: FixSafety,
    pub edits: Vec<Edit>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Related {
    pub span: Span,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: &'static str,
    pub severity: Severity,
    pub message: String,
    pub span: Span,
    pub related: Vec<Related>,
    pub help: String,
    pub fixes: Vec<Fix>,
}

pub fn sort(ds: &mut [Diagnostic]) {
    ds.sort_by(|a, b| {
        a.span
            .start
            .cmp(&b.span.start)
            .then_with(|| a.code.as_bytes().cmp(b.code.as_bytes()))
    });
}

pub(crate) fn push_decimal(out: &mut String, value: usize) {
    let mut buffer = [0u8; 20];
    let mut cursor = buffer.len();
    let mut rest = value;
    loop {
        cursor -= 1;
        buffer[cursor] = b'0' + u8::try_from(rest % 10).unwrap_or(0);
        rest /= 10;
        if rest == 0 {
            break;
        }
    }
    for &digit in &buffer[cursor..] {
        out.push(char::from(digit));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn diagnostic(code: &'static str, start: usize, end: usize) -> Diagnostic {
        Diagnostic {
            code,
            severity: Severity::Error,
            message: String::from("m"),
            span: Span { start, end },
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        }
    }

    #[test]
    fn sort_orders_by_start_then_code() {
        let mut ds = vec![
            diagnostic("b/one", 4, 5),
            diagnostic("a/two", 0, 2),
            diagnostic("a/one", 0, 2),
            diagnostic("c/zero", 0, 0),
        ];
        sort(&mut ds);
        let codes: Vec<&str> = ds.iter().map(|d| d.code).collect();
        assert_eq!(codes, ["a/one", "a/two", "c/zero", "b/one"]);
    }

    #[test]
    fn sort_is_stable_for_equal_keys() {
        let mut ds = vec![diagnostic("a/x", 1, 1), diagnostic("a/x", 1, 1)];
        ds[0].message = String::from("first");
        ds[1].message = String::from("second");
        sort(&mut ds);
        assert_eq!(ds[0].message, "first");
        assert_eq!(ds[1].message, "second");
    }

    #[test]
    fn wire_names_are_fixed() {
        assert_eq!(Severity::Error.as_str(), "error");
        assert_eq!(Severity::Warning.as_str(), "warning");
        assert_eq!(Severity::Info.as_str(), "info");
        assert_eq!(FixSafety::Safe.as_str(), "safe");
        assert_eq!(FixSafety::Unsafe.as_str(), "unsafe");
        assert!(FixSafety::Safe < FixSafety::Unsafe);
    }
}
