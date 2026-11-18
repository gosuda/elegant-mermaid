//! Abstract syntax tree of the timeline grammar (`spec/grammar/timeline.md`).
//!
//! Node names retain the upstream production names in PascalCase. A statement span runs
//! from its first token to the end of its last token.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Start {
    pub span: Span,
    pub header: TimelineHeader,
    pub document: Document,
}

#[derive(Debug, Clone)]
pub struct TimelineHeader {
    pub token: Token,
    pub direction: &'static str,
}

#[derive(Debug, Clone)]
pub struct Document {
    pub span: Span,
    pub lines: Vec<Line>,
}

#[derive(Debug, Clone)]
pub struct Line {
    pub span: Span,
    pub separator: Option<Token>,
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
    AccDescrBlock(AccDescrBlock),
    Section(Section),
    Period(PeriodStatement),
    Event(EventStatement),
}

#[derive(Debug, Clone)]
pub struct Title {
    pub token: Token,
}

#[derive(Debug, Clone)]
pub struct AccTitle {
    pub opener: Token,
    pub value: Token,
}

#[derive(Debug, Clone)]
pub struct AccDescr {
    pub opener: Token,
    pub value: Token,
}

#[derive(Debug, Clone)]
pub struct AccDescrBlock {
    pub value: Token,
}

#[derive(Debug, Clone)]
pub struct Section {
    pub token: Token,
}

#[derive(Debug, Clone)]
pub struct PeriodStatement {
    pub token: Token,
}

#[derive(Debug, Clone)]
pub struct EventStatement {
    pub token: Token,
}
