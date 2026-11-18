//! Abstract syntax tree of the packet grammar (`spec/grammar/packet.md`).
//!
//! Node names retain the upstream production names in PascalCase. A statement span runs
//! from its first token to the end of its last token.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Start {
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
    PacketBlock(PacketBlock),
    Metadata(Metadata),
}

#[derive(Debug, Clone, Copy)]
pub struct Operand {
    pub value: i64,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Label {
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct PacketBlock {
    pub start: Option<Operand>,
    pub end: Option<Operand>,
    pub bits: Option<Operand>,
    pub label: Label,
}

#[derive(Debug, Clone)]
pub struct Metadata {
    pub field: &'static str,
    pub value: String,
}
