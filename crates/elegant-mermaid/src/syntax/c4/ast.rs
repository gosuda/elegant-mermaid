use super::lexer::Token;
use crate::source::Span;

#[derive(Debug, Clone)]
pub struct Start<'a> {
    pub span: Span,
    pub kind: StartKind<'a>,
}
#[derive(Debug, Clone)]
pub enum StartKind<'a> {
    MermaidDoc(MermaidDoc<'a>),
    Direction(Direction<'a>),
}
#[derive(Debug, Clone)]
pub struct Direction<'a> {
    pub span: Span,
    pub direction: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct MermaidDoc<'a> {
    pub span: Span,
    pub graph_config: GraphConfig<'a>,
}
#[derive(Debug, Clone)]
pub struct GraphConfig<'a> {
    pub span: Span,
    pub header: Token<'a>,
    pub statements: Statements<'a>,
}
#[derive(Debug, Clone)]
pub struct Statements<'a> {
    pub span: Span,
    pub items: Vec<Statement<'a>>,
}
#[derive(Debug, Clone)]
pub enum Statement<'a> {
    Other(OtherStatement<'a>),
    Diagram(Box<DiagramStatement<'a>>),
}
impl Statement<'_> {
    pub fn span(&self) -> Span {
        match self {
            Self::Other(statement) => statement.span,
            Self::Diagram(statement) => statement.span,
        }
    }
}
#[derive(Debug, Clone)]
pub struct OtherStatements<'a> {
    pub span: Span,
    pub items: Vec<OtherStatement<'a>>,
}
#[derive(Debug, Clone)]
pub struct OtherStatement<'a> {
    pub span: Span,
    pub form: &'static str,
    pub value: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct DiagramStatements<'a> {
    pub span: Span,
    pub items: Vec<Statement<'a>>,
}
#[derive(Debug, Clone)]
pub struct DiagramStatement<'a> {
    pub span: Span,
    pub kind: DiagramStatementKind<'a>,
}
#[derive(Debug, Clone)]
pub enum DiagramStatementKind<'a> {
    Call {
        macro_token: Token<'a>,
        attributes: Attributes<'a>,
    },
    Boundary(Box<BoundaryStatement<'a>>),
}
#[derive(Debug, Clone)]
pub struct BoundaryStatement<'a> {
    pub span: Span,
    pub start: BoundaryStartStatement<'a>,
    pub body: DiagramStatements<'a>,
    pub stop: BoundaryStopStatement<'a>,
}
#[derive(Debug, Clone)]
pub struct BoundaryStartStatement<'a> {
    pub span: Span,
    pub start: BoundaryStart<'a>,
    pub brace: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct BoundaryStart<'a> {
    pub span: Span,
    pub macro_token: Token<'a>,
    pub attributes: Attributes<'a>,
}
#[derive(Debug, Clone)]
pub struct BoundaryStopStatement<'a> {
    pub span: Span,
    pub close: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct Attributes<'a> {
    pub span: Span,
    pub items: Vec<Attribute<'a>>,
}
#[derive(Debug, Clone)]
pub struct Attribute<'a> {
    pub span: Span,
    pub kind: AttributeKind<'a>,
}
#[derive(Debug, Clone)]
pub enum AttributeKind<'a> {
    Positional(Token<'a>),
    Named { key: Token<'a>, value: Token<'a> },
    Empty(Token<'a>),
}
