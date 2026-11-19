//! Abstract syntax tree of the gitgraph grammar (`spec/grammar/gitgraph.md`).
//!
//! Node names retain the upstream production names in PascalCase, and statement spans
//! exclude trailing whitespace, comments, and line ends.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Start {
    pub span: Span,
    pub header: Token,
    pub direction: Option<Token>,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Commit(Commit),
    Branch(Branch),
    Merge(Merge),
    Checkout(Checkout),
    CherryPicking(CherryPicking),
    Metadata(Metadata),
}

#[derive(Debug, Clone)]
pub struct Value {
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Order {
    pub value: i64,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Commit {
    pub keyword: Span,
    pub id: Option<Value>,
    pub message: Option<Value>,
    pub tags: Vec<Value>,
    pub commit_type: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct Branch {
    pub keyword: Span,
    pub name: Value,
    pub order: Option<Order>,
}

#[derive(Debug, Clone)]
pub struct Merge {
    pub keyword: Span,
    pub branch: Value,
    pub id: Option<Value>,
    pub tags: Vec<Value>,
    pub commit_type: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct Checkout {
    pub keyword: Span,
    pub switch: bool,
    pub branch: Value,
}

#[derive(Debug, Clone)]
pub struct CherryPicking {
    pub keyword: Span,
    pub id: Option<Value>,
    pub tags: Vec<Value>,
    pub parent: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct Metadata {
    pub field: &'static str,
    pub value: String,
}
