//! Abstract syntax tree of the journey grammar (`spec/grammar/journey.md`).
//!
//! Node names retain the upstream production names in PascalCase. A statement span runs
//! from its first token to the end of its last token.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value {
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    pub raw: Value,
    pub trimmed: Value,
}

#[derive(Debug, Clone)]
pub struct Start {
    pub span: Span,
    pub header: Token,
    pub document: Document,
}

#[derive(Debug, Clone)]
pub struct Document {
    pub span: Span,
    pub lines: Vec<Line>,
}

#[derive(Debug, Clone)]
pub struct Line {
    pub span: Span,
    pub statement: Option<Statement>,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Title(Title),
    AccTitle(AccTitle),
    AccDescr(AccDescr),
    AccDescrMultiline(AccDescrMultiline),
    Section(Section),
    Task(Task),
}

#[derive(Debug, Clone)]
pub struct Title {
    pub text: Value,
}

#[derive(Debug, Clone)]
pub struct AccTitle {
    pub keyword: Span,
    pub value: Value,
}

#[derive(Debug, Clone)]
pub struct AccDescr {
    pub keyword: Span,
    pub value: Value,
}

#[derive(Debug, Clone)]
pub struct AccDescrMultiline {
    pub open: Span,
    pub close: Option<Span>,
    pub value: Value,
}

#[derive(Debug, Clone)]
pub struct Section {
    pub text: Value,
}

#[derive(Debug, Clone)]
pub struct Task {
    pub name: Value,
    pub data: Value,
    pub fields: Vec<Field>,
}
