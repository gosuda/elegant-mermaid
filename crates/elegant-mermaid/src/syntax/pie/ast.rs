//! Abstract syntax tree of the pie grammar (`spec/grammar/pie.md`).
//!
//! Node names retain the upstream production names in PascalCase, and statement spans
//! exclude trailing whitespace, comments, and line ends.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Pie {
    pub span: Span,
    pub header: Token,
    pub show_data: bool,
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    PieSection(PieSection),
    TitleAndAccessibilities(TitleAndAccessibilities),
}

#[derive(Debug, Clone, Copy)]
pub struct Eol {
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct PieSection {
    pub label: Token,
    pub number: Token,
    pub eol: Eol,
}

#[derive(Debug, Clone)]
pub struct Metadata {
    pub field: &'static str,
    pub value: String,
    pub span: Span,
    pub eol: Eol,
}

#[derive(Debug, Clone)]
pub struct TitleAndAccessibilities {
    pub items: Vec<Metadata>,
}
