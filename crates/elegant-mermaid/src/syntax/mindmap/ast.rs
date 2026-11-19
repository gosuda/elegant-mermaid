use crate::source::Span;

/// How a node description was written.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Description {
    #[default]
    Bare,
    Plain,
    Quoted,
    Markdown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
    pub quote: Description,
}

impl Token {
    pub(super) fn new(kind: &'static str, text: &str, span: Span) -> Self {
        Self {
            kind,
            text: text.to_owned(),
            span,
            quote: Description::Bare,
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
    pub node: Option<Node>,
    pub icon: Option<Token>,
    pub class: Option<Token>,
    pub blank: Option<Token>,
}

impl Statement {
    pub(super) fn at(span: Span) -> Self {
        Self {
            span,
            indent: None,
            node: None,
            icon: None,
            class: None,
            blank: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stop {
    pub span: Span,
    pub tokens: Vec<Token>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub span: Span,
    pub id: Option<Token>,
    pub open: Option<Token>,
    pub descr: Option<Token>,
    pub close: Option<Token>,
    pub description: Description,
}
