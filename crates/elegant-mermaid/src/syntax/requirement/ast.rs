use std::borrow::Cow;

use super::lexer::Token;
use crate::source::Span;

#[derive(Debug, Clone)]
pub struct Start<'a> {
    pub span: Span,
    pub header: Token<'a>,
    pub diagram: Diagram<'a>,
    pub directives: Vec<Directive<'a>>,
}
#[derive(Debug, Clone)]
pub struct Diagram<'a> {
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
    Requirement(RequirementDef<'a>),
    Element(ElementDef<'a>),
    Relationship(RelationshipDef<'a>),
    Directive(Directive<'a>),
    Direction(Direction),
    ClassDef(ClassDefStatement<'a>),
    Class(ClassStatement<'a>),
    Style(StyleStatement<'a>),
}
#[derive(Debug, Clone)]
pub struct Directive<'a> {
    pub span: Span,
    pub title: bool,
    pub multiline: bool,
    pub value: Token<'a>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Direction {
    pub span: Span,
    pub value: &'static str,
}
#[derive(Debug, Clone)]
pub struct RequirementDef<'a> {
    pub span: Span,
    pub requirement_type: RequirementType,
    pub name: RequirementName<'a>,
    pub classes: Option<IdList<'a>>,
    pub body: RequirementBody<'a>,
    pub delimiters: (Span, Span),
}
#[derive(Debug, Clone)]
pub struct RequirementBody<'a> {
    pub span: Span,
    pub fields: Vec<RequirementField<'a>>,
}
#[derive(Debug, Clone)]
pub struct RequirementField<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub colon: Span,
    pub value: RequirementFieldValue<'a>,
}
#[derive(Debug, Clone)]
pub enum RequirementFieldValue<'a> {
    Id(Id<'a>),
    Text(Text<'a>),
    Risk(RiskLevel),
    Verify(VerifyType),
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RequirementType {
    pub span: Span,
    pub value: &'static str,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RiskLevel {
    pub span: Span,
    pub value: &'static str,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerifyType {
    pub span: Span,
    pub value: &'static str,
}
#[derive(Debug, Clone)]
pub struct ElementDef<'a> {
    pub span: Span,
    pub name: ElementName<'a>,
    pub classes: Option<IdList<'a>>,
    pub body: ElementBody<'a>,
    pub delimiters: (Span, Span),
}
#[derive(Debug, Clone)]
pub struct ElementBody<'a> {
    pub span: Span,
    pub fields: Vec<ElementField<'a>>,
}
#[derive(Debug, Clone)]
pub struct ElementField<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub colon: Span,
    pub value: ElementFieldValue<'a>,
}
#[derive(Debug, Clone)]
pub enum ElementFieldValue<'a> {
    Type(Type<'a>),
    Ref(Ref<'a>),
}
#[derive(Debug, Clone)]
pub struct RelationshipDef<'a> {
    pub span: Span,
    pub left: Id<'a>,
    pub right: Id<'a>,
    pub relationship: Relationship,
    pub arrow: Token<'a>,
    pub line: Span,
    pub reversed: bool,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Relationship {
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
    pub separator: Option<Span>,
}
#[derive(Debug, Clone)]
pub struct StyleStatement<'a> {
    pub span: Span,
    pub ids: IdList<'a>,
    pub styles: StylesOpt<'a>,
}
#[derive(Debug, Clone)]
pub struct IdList<'a> {
    pub span: Span,
    pub names: Vec<Id<'a>>,
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
    pub kind: &'static str,
    pub text: Cow<'a, str>,
}
#[derive(Debug, Clone)]
pub struct RequirementName<'a> {
    pub span: Span,
    pub quoted: bool,
    pub value: Cow<'a, str>,
}
#[derive(Debug, Clone)]
pub struct Id<'a> {
    pub span: Span,
    pub quoted: bool,
    pub value: Cow<'a, str>,
}
#[derive(Debug, Clone)]
pub struct Text<'a> {
    pub span: Span,
    pub quoted: bool,
    pub value: Cow<'a, str>,
}
#[derive(Debug, Clone)]
pub struct ElementName<'a> {
    pub span: Span,
    pub quoted: bool,
    pub value: Cow<'a, str>,
}
#[derive(Debug, Clone)]
pub struct Type<'a> {
    pub span: Span,
    pub quoted: bool,
    pub value: Cow<'a, str>,
}
#[derive(Debug, Clone)]
pub struct Ref<'a> {
    pub span: Span,
    pub quoted: bool,
    pub value: Cow<'a, str>,
}
