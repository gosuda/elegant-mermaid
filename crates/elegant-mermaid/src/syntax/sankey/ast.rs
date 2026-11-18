//! Abstract syntax tree of the sankey grammar (`spec/grammar/sankey.md`).
//!
//! Node names retain the upstream production names in PascalCase. A record span runs from
//! the first to the last field, without the line separator.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Start {
    pub span: Span,
    pub header: Option<Token>,
    pub csv: Csv,
    pub opt_eof: OptEof,
}

#[derive(Debug, Clone)]
pub struct Csv {
    pub span: Span,
    pub records: Vec<Record>,
}

#[derive(Debug, Clone, Copy)]
pub struct OptEof {
    pub span: Span,
    pub present: bool,
}

#[derive(Debug, Clone)]
pub struct Record {
    pub span: Span,
    pub source: Field,
    pub target: Field,
    pub value: Field,
    pub index: usize,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub span: Span,
    pub escaped: Option<Escaped>,
    pub non_escaped: Option<NonEscaped>,
}

#[derive(Debug, Clone)]
pub struct Escaped {
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct NonEscaped {
    pub span: Span,
    pub text: String,
}

impl Field {
    pub fn text(&self) -> &str {
        match (&self.escaped, &self.non_escaped) {
            (Some(escaped), _) => &escaped.text,
            (None, Some(plain)) => &plain.text,
            (None, None) => "",
        }
    }
}
