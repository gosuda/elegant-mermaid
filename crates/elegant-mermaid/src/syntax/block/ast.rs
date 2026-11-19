//! Abstract syntax tree of the block grammar (`spec/grammar/block.md`).
//!
//! Node names retain the upstream production names in PascalCase, and spans run from the
//! first to the last consumed token.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Start<'a> {
    pub span: Span,
    pub header: Token<'a>,
    pub document: Document<'a>,
}

#[derive(Debug, Clone)]
pub struct Document<'a> {
    pub span: Span,
    pub statements: Vec<Statement<'a>>,
}

#[derive(Debug, Clone)]
pub struct Statement<'a> {
    pub span: Span,
    pub kind: StatementKind<'a>,
}

#[derive(Debug, Clone)]
pub enum StatementKind<'a> {
    Node(Box<NodeStatement<'a>>),
    Columns(ColumnsStatement<'a>),
    Space(SpaceStatement<'a>),
    Block(Box<BlockStatement<'a>>),
    ClassDef(ClassDefStatement<'a>),
    CssClass(CssClassStatement<'a>),
    Style(StyleStatement<'a>),
}

#[derive(Debug, Clone)]
pub struct NodeStatement<'a> {
    pub span: Span,
    pub first: Node<'a>,
    pub size: Option<Token<'a>>,
    pub links: Vec<LinkedNode<'a>>,
}

#[derive(Debug, Clone)]
pub struct LinkedNode<'a> {
    pub link: Link<'a>,
    pub node: Node<'a>,
}

#[derive(Debug, Clone)]
pub struct Link<'a> {
    pub span: Span,
    pub start: Option<Token<'a>>,
    pub label: Option<Token<'a>>,
    pub end: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct Node<'a> {
    pub span: Span,
    pub id: Token<'a>,
    pub shape: Option<NodeShapeNLabel<'a>>,
}

#[derive(Debug, Clone)]
pub struct NodeShapeNLabel<'a> {
    pub span: Span,
    pub open: Token<'a>,
    pub label: Token<'a>,
    pub close: Token<'a>,
    pub dirs: Vec<Token<'a>>,
}

#[derive(Debug, Clone)]
pub struct ColumnsStatement<'a> {
    pub span: Span,
    pub token: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct SpaceStatement<'a> {
    pub span: Span,
    pub token: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct BlockStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub header: Option<NodeStatement<'a>>,
    pub body: Document<'a>,
    pub end: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct ClassDefStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub id: Token<'a>,
    pub style: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct CssClassStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub ids: Token<'a>,
    pub class: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct StyleStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub ids: Token<'a>,
    pub style: Token<'a>,
}
