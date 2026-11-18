use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

impl Token {
    pub(super) fn new(kind: &'static str, text: &str, span: Span) -> Self {
        Self {
            kind,
            text: text.to_owned(),
            span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Start {
    pub span: Span,
    pub leading: Vec<Token>,
    pub header: Option<Token>,
    pub document: Document,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Document {
    pub span: Span,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Item {
    pub statement: Statement,
    pub stop: Stop,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Statement {
    pub span: Span,
    pub indent: Option<Token>,
    pub text: Option<Token>,
    pub blank: Option<Token>,
}

impl Statement {
    pub(super) fn at(span: Span) -> Self {
        Self {
            span,
            indent: None,
            text: None,
            blank: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stop {
    pub span: Span,
    pub tokens: Vec<Token>,
}
