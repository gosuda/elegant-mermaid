//! Abstract syntax tree of the architecture grammar (`spec/grammar/architecture.md`).

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Architecture {
    pub span: Span,
    pub header: Token,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Group(Group),
    Service(Service),
    Junction(Junction),
    Edge(Edge),
    Alignment(Alignment),
    Metadata(Metadata),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value {
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Group {
    pub keyword: Span,
    pub id: Value,
    pub icon: Option<Value>,
    pub title: Option<Value>,
    pub parent: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct Service {
    pub keyword: Span,
    pub id: Value,
    pub icon_text: Option<Value>,
    pub icon: Option<Value>,
    pub title: Option<Value>,
    pub parent: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct Junction {
    pub keyword: Span,
    pub id: Value,
    pub parent: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct Edge {
    pub lhs_id: Value,
    pub lhs_group: Option<Span>,
    pub lhs_dir: Value,
    pub lhs_into: Option<Span>,
    pub title: Option<Value>,
    pub rhs_into: Option<Span>,
    pub rhs_dir: Value,
    pub rhs_id: Value,
    pub rhs_group: Option<Span>,
}

#[derive(Debug, Clone)]
pub struct Alignment {
    pub keyword: Span,
    pub direction: Value,
    pub members: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetadataItem {
    pub field: &'static str,
    pub value: String,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct Metadata {
    pub items: Vec<MetadataItem>,
}
