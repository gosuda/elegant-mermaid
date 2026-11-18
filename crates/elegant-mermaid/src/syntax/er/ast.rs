use std::borrow::Cow;

use super::lexer::Token;
use crate::source::Span;

#[derive(Debug, Clone)]
pub struct Start<'a> {
    pub span: Span,
    pub header: Token<'a>,
    pub document: Document<'a>,
}
#[derive(Debug, Clone)]
pub struct Document<'a> {
    pub span: Span,
    pub lines: Vec<Line<'a>>,
}
#[derive(Debug, Clone)]
pub struct Line<'a> {
    pub span: Span,
    pub statement: Option<Statement<'a>>,
}
#[derive(Debug, Clone)]
pub struct Statement<'a> {
    pub span: Span,
    pub kind: StatementKind<'a>,
}
#[derive(Debug, Clone)]
pub enum StatementKind<'a> {
    Entity {
        name: EntityName<'a>,
        alias: Option<EntityName<'a>>,
        classes: Option<IdList<'a>>,
        attributes: Option<Attributes<'a>>,
        delimiters: Option<(Span, Span)>,
    },
    Relationship {
        from: EntityName<'a>,
        from_classes: Option<IdList<'a>>,
        relation: Box<RelSpec<'a>>,
        to: EntityName<'a>,
        to_classes: Option<IdList<'a>>,
        role: Role<'a>,
    },
    Accessibility {
        title: bool,
        value: Token<'a>,
    },
    Direction(Direction),
    ClassDef(ClassDefStatement<'a>),
    Class(ClassStatement<'a>),
    Style(StyleStatement<'a>),
    Subgraph {
        header: SubgraphHeader<'a>,
        document: Document<'a>,
        close: Token<'a>,
    },
}
#[derive(Debug, Clone)]
pub struct SubgraphHeader<'a> {
    pub span: Span,
    pub id: EntityName<'a>,
    pub title: Option<SubgraphTitle<'a>>,
}
#[derive(Debug, Clone)]
pub struct SubgraphTitle<'a> {
    pub span: Span,
    pub parts: Vec<EntityName<'a>>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Direction {
    pub span: Span,
    pub value: &'static str,
}
#[derive(Debug, Clone)]
pub struct ClassDefStatement<'a> {
    pub span: Span,
    pub ids: IdList<'a>,
    pub styles: StylesOpt<'a>,
}
#[derive(Debug, Clone)]
pub struct ClassStatement<'a> {
    pub span: Span,
    pub targets: IdList<'a>,
    pub classes: IdList<'a>,
}
#[derive(Debug, Clone)]
pub struct StyleStatement<'a> {
    pub span: Span,
    pub targets: IdList<'a>,
    pub styles: StylesOpt<'a>,
}
#[derive(Debug, Clone)]
pub struct IdList<'a> {
    pub span: Span,
    pub names: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct StylesOpt<'a> {
    pub span: Span,
    pub styles: Vec<Style<'a>>,
}
#[derive(Debug, Clone)]
pub struct Style<'a> {
    pub span: Span,
    pub components: Vec<StyleComponent<'a>>,
}
#[derive(Debug, Clone)]
pub struct StyleComponent<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct Separator<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct EntityName<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub name: Cow<'a, str>,
}
#[derive(Debug, Clone)]
pub struct Attributes<'a> {
    pub span: Span,
    pub attributes: Vec<Attribute<'a>>,
}
#[derive(Debug, Clone)]
pub struct Attribute<'a> {
    pub span: Span,
    pub attribute_type: AttributeType<'a>,
    pub name: AttributeName<'a>,
    pub keys: Option<AttributeKeyTypeList<'a>>,
    pub comment: Option<AttributeComment<'a>>,
}
#[derive(Debug, Clone)]
pub struct AttributeType<'a> {
    pub span: Span,
    pub word: Token<'a>,
    pub question: Option<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct AttributeName<'a> {
    pub span: Span,
    pub word: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct AttributeKeyTypeList<'a> {
    pub span: Span,
    pub keys: Vec<AttributeKeyType<'a>>,
}
#[derive(Debug, Clone)]
pub struct AttributeKeyType<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub value: &'static str,
}
#[derive(Debug, Clone)]
pub struct AttributeComment<'a> {
    pub span: Span,
    pub text: Cow<'a, str>,
}
#[derive(Debug, Clone)]
pub struct RelSpec<'a> {
    pub span: Span,
    pub left: Cardinality<'a>,
    pub relation_type: RelType<'a>,
    pub right: Cardinality<'a>,
}
#[derive(Debug, Clone)]
pub struct Cardinality<'a> {
    pub span: Span,
    pub kind: CardinalityKind,
    pub token: Token<'a>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CardinalityKind {
    ZeroOrOne,
    ZeroOrMore,
    OneOrMore,
    OnlyOne,
    MdParent,
}
#[derive(Debug, Clone)]
pub struct RelType<'a> {
    pub span: Span,
    pub identifying: bool,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct Role<'a> {
    pub span: Span,
    pub label: Cow<'a, str>,
    pub token: Token<'a>,
}
