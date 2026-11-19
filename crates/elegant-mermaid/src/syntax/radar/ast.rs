//! AST of the radar grammar (`spec/grammar/radar.md`). Names follow the upstream
//! productions; text is owned and spans are byte offsets into the source.

use crate::source::Span;

pub use super::lexer::Token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Start {
    pub span: Span,
    pub header: Token,
    pub axes: Vec<Axis>,
    pub curves: Vec<Curve>,
    pub options: Vec<RadarOption>,
    pub title: Option<Text>,
    pub acc_title: Option<Text>,
    pub acc_descr: Option<Text>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Text {
    pub value: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub value: Token,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Axis {
    pub span: Span,
    pub name: Token,
    pub label: Option<Label>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Curve {
    pub span: Span,
    pub name: Token,
    pub label: Option<Label>,
    pub entries: Vec<Entry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Number {
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DetailedEntry {
    pub span: Span,
    pub axis: Token,
    pub value: Number,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumberEntry {
    pub value: Number,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Entry {
    Detailed(DetailedEntry),
    Number(NumberEntry),
}

impl Entry {
    pub fn number(&self) -> &Number {
        match self {
            Entry::Detailed(entry) => &entry.value,
            Entry::Number(entry) => &entry.value,
        }
    }

    pub fn reference(&self) -> Option<&Token> {
        match self {
            Entry::Detailed(entry) => Some(&entry.axis),
            Entry::Number(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RadarOption {
    pub span: Span,
    pub name: Token,
    pub value: Token,
}
