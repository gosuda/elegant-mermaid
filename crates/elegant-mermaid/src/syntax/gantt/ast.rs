//! Abstract syntax tree of the gantt grammar (`spec/grammar/gantt.md`).
//!
//! Node names retain the upstream production names in PascalCase. A statement span runs
//! from its first token to the end of its last token.

use crate::source::Span;

use super::lexer::Token;

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
    DateFormat(Token),
    InclusiveEndDates(Token),
    TopAxis(Token),
    AxisFormat(Token),
    TickInterval(Token),
    Excludes(Token),
    Includes(Token),
    TodayMarker(Token),
    Weekday(Weekday),
    Weekend(Weekend),
    Title(Token),
    Section(Token),
    AccTitle(Accessibility),
    AccDescr(Accessibility),
    AccDescrBlock(Token),
    Task(Task),
    Click(ClickStatement),
}

#[derive(Debug, Clone)]
pub struct Weekday {
    pub token: Token,
    pub name: &'static str,
}

#[derive(Debug, Clone)]
pub struct Weekend {
    pub token: Token,
    pub name: &'static str,
}

#[derive(Debug, Clone)]
pub struct Accessibility {
    pub opener: Token,
    pub value: Token,
}

#[derive(Debug, Clone)]
pub struct Task {
    pub text: Token,
    pub data: Token,
}

#[derive(Debug, Clone)]
pub struct ClickStatement {
    pub click: ClickToken,
    pub callback: Option<ClickToken>,
    pub args: Option<ClickToken>,
    pub href: Option<ClickToken>,
    pub order: Vec<&'static str>,
}

#[derive(Debug, Clone)]
pub struct ClickToken {
    pub kind: &'static str,
    pub text: String,
    pub value: String,
    pub span: Span,
    pub payload: Span,
}

impl From<Token> for ClickToken {
    fn from(token: Token) -> Self {
        Self {
            kind: token.kind,
            text: token.text,
            value: token.value,
            span: token.span,
            payload: token.payload,
        }
    }
}
