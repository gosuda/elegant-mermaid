use std::borrow::Cow;

use super::lexer::Token;
use crate::source::Span;

#[derive(Debug, Clone)]
pub struct Start<'a> {
    pub span: Span,
    pub header: Token<'a>,
    pub line_end: LineEnd<'a>,
    pub tokens: Vec<Token<'a>>,
    pub lines: Vec<Line<'a>>,
}
#[derive(Debug, Clone)]
pub struct Line<'a> {
    pub span: Span,
    pub kind: LineKind<'a>,
}
#[derive(Debug, Clone)]
pub enum LineKind<'a> {
    Blank(BlankLine<'a>),
    Comment(CommentLine<'a>),
    Statement(Box<Statement<'a>>),
}
#[derive(Debug, Clone)]
pub struct LineEnd<'a> {
    pub span: Span,
    pub token: Option<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct BlankLine<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct CommentLine<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub line_end: LineEnd<'a>,
}
#[derive(Debug, Clone)]
pub struct Statement<'a> {
    pub span: Span,
    pub kind: StatementKind<'a>,
    pub line_end: LineEnd<'a>,
}
#[derive(Debug, Clone)]
pub enum StatementKind<'a> {
    AccTitle(AccTitleStatement<'a>),
    AccDescr(AccDescrStatement<'a>),
    Direction(DirectionStatement<'a>),
    Actor(Box<ActorStatement<'a>>),
    Entity(Box<EntityStatement<'a>>),
    SystemBoundary(Box<SystemBoundaryStatement<'a>>),
    MetadataAssignment(MetadataAssignmentStatement<'a>),
    Note(NoteStatement<'a>),
    Json(JsonStatement<'a>),
    ClassDef(ClassDefStatement<'a>),
    Class(ClassStatement<'a>),
    Style(StyleStatement<'a>),
}
#[derive(Debug, Clone)]
pub struct AccTitleStatement<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub value: Cow<'a, str>,
    pub content_span: Span,
}
#[derive(Debug, Clone)]
pub struct AccDescrStatement<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub value: Cow<'a, str>,
    pub content_span: Span,
}
#[derive(Debug, Clone)]
pub struct DirectionStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub direction: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct ActorStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub items: Vec<ActorItem<'a>>,
    pub relation: Option<RelationTail<'a>>,
}
#[derive(Debug, Clone)]
pub struct ActorDeclarationOnly<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub items: Vec<ActorItem<'a>>,
    pub line_end: LineEnd<'a>,
}
#[derive(Debug, Clone)]
pub struct ActorItem<'a> {
    pub span: Span,
    pub name: ActorName<'a>,
    pub metadata: Option<Metadata<'a>>,
    pub stereotype: Option<Stereotype<'a>>,
    pub classes: Option<ClassSuffix<'a>>,
}
#[derive(Debug, Clone)]
pub struct ActorName<'a> {
    pub span: Span,
    pub id: Token<'a>,
    pub id_content_span: Span,
    pub label: Option<NodeLabel<'a>>,
    pub delimiters: Option<(Token<'a>, Token<'a>)>,
}
#[derive(Debug, Clone)]
pub struct EntityStatement<'a> {
    pub span: Span,
    pub name: EntityName<'a>,
    pub relation: Option<RelationTail<'a>>,
}
#[derive(Debug, Clone)]
pub struct EntityName<'a> {
    pub span: Span,
    pub id: Token<'a>,
    pub id_content_span: Span,
    pub label: Option<NodeLabel<'a>>,
    pub delimiters: Option<(Token<'a>, Token<'a>)>,
    pub metadata: Option<UseCaseMetadata<'a>>,
    pub stereotype: Option<Stereotype<'a>>,
    pub classes: Option<ClassSuffix<'a>>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelKind {
    Plain,
    Quoted,
    Markdown,
}
#[derive(Debug, Clone)]
pub struct NodeLabel<'a> {
    pub span: Span,
    pub text: Cow<'a, str>,
    pub content_span: Span,
    pub kind: LabelKind,
    pub tokens: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct UseCaseMetadata<'a> {
    pub span: Span,
    pub metadata: Metadata<'a>,
}
#[derive(Debug, Clone)]
pub struct RelationTail<'a> {
    pub span: Span,
    pub id: Option<Token<'a>>,
    pub at: Option<Token<'a>>,
    pub arrow: Arrow<'a>,
    pub endpoint: EntityName<'a>,
}
#[derive(Debug, Clone)]
pub struct Arrow<'a> {
    pub span: Span,
    pub kind: ArrowKind<'a>,
}
#[derive(Debug, Clone)]
pub enum ArrowKind<'a> {
    Semantic(SemanticRelation<'a>),
    ForwardSolid(ForwardSolidOperator<'a>),
    BackwardSolid(BackwardSolidOperator<'a>),
    MarkerlessSolid(MarkerlessSolidOperator<'a>),
    ForwardCircle(ForwardCircleOperator<'a>),
    BackwardCircle(BackwardCircleOperator<'a>),
    ForwardCross(ForwardCrossOperator<'a>),
    BackwardCross(BackwardCrossOperator<'a>),
}
#[derive(Debug, Clone)]
pub struct SemanticRelation<'a> {
    pub span: Span,
    pub operator: Token<'a>,
    pub colon: Option<Token<'a>>,
    pub relation: Option<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct ForwardSolidOperator<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct ForwardCircleOperator<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct ForwardCrossOperator<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct BackwardSolidOperator<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub label: Option<EdgeLabel<'a>>,
    pub right: Option<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct MarkerlessSolidOperator<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub label: Option<EdgeLabel<'a>>,
    pub right: Option<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct BackwardCircleOperator<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub label: Option<EdgeLabel<'a>>,
    pub right: Option<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct BackwardCrossOperator<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub label: Option<EdgeLabel<'a>>,
    pub right: Option<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct EdgeLabel<'a> {
    pub span: Span,
    pub label: NodeLabel<'a>,
}
#[derive(Debug, Clone)]
pub struct Metadata<'a> {
    pub span: Span,
    pub open: Token<'a>,
    pub properties: Vec<MetadataProperty<'a>>,
    pub separators: Vec<MetadataSeparator<'a>>,
    pub close: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct MetadataProperty<'a> {
    pub span: Span,
    pub key: Token<'a>,
    pub value: Token<'a>,
    pub key_content_span: Span,
    pub value_content_span: Span,
}
#[derive(Debug, Clone)]
pub struct MetadataSeparator<'a> {
    pub span: Span,
    pub tokens: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct MetadataAssignmentStatement<'a> {
    pub span: Span,
    pub target: MetadataAssignmentTarget<'a>,
    pub metadata: Metadata<'a>,
}
#[derive(Debug, Clone)]
pub struct MetadataAssignmentTarget<'a> {
    pub span: Span,
    pub token: Token<'a>,
    pub content_span: Span,
}
#[derive(Debug, Clone)]
pub struct SystemBoundaryStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub name: SystemBoundaryName<'a>,
    pub metadata: Option<Metadata<'a>>,
    pub classes: Option<ClassSuffix<'a>>,
    pub line_end: LineEnd<'a>,
    pub content: SystemBoundaryContent<'a>,
    pub close: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct SystemBoundaryName<'a> {
    pub span: Span,
    pub id: Token<'a>,
    pub id_content_span: Span,
    pub label: Option<NodeLabel<'a>>,
    pub delimiters: Option<(Token<'a>, Token<'a>)>,
}
#[derive(Debug, Clone)]
pub struct SystemBoundaryContent<'a> {
    pub span: Span,
    pub elements: Vec<BoundaryElement<'a>>,
}
#[derive(Debug, Clone)]
pub struct BoundaryElement<'a> {
    pub span: Span,
    pub kind: BoundaryElementKind<'a>,
}
#[derive(Debug, Clone)]
pub enum BoundaryElementKind<'a> {
    Blank(BlankLine<'a>),
    Comment(CommentLine<'a>),
    Actor(ActorDeclarationOnly<'a>),
    Entity(Box<EntityName<'a>>, LineEnd<'a>),
}
#[derive(Debug, Clone)]
pub struct NoteStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub for_token: Token<'a>,
    pub target: Token<'a>,
    pub label: NodeLabel<'a>,
}
#[derive(Debug, Clone)]
pub struct Stereotype<'a> {
    pub span: Span,
    pub open: Token<'a>,
    pub content: Token<'a>,
    pub content_span: Span,
    pub close: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct ClassSuffix<'a> {
    pub span: Span,
    pub separator: Token<'a>,
    pub classes: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct JsonStatement<'a> {
    pub span: Span,
    pub header: Token<'a>,
    pub id: Token<'a>,
    pub object: JsonObject<'a>,
    pub classes: Option<ClassSuffix<'a>>,
}
#[derive(Debug, Clone)]
pub struct JsonObject<'a> {
    pub span: Span,
    pub properties: Vec<JsonProperty<'a>>,
}
#[derive(Debug, Clone)]
pub struct JsonProperty<'a> {
    pub span: Span,
    pub key: Token<'a>,
    pub value: JsonValue<'a>,
}
#[derive(Debug, Clone)]
pub struct JsonValue<'a> {
    pub span: Span,
    pub kind: JsonValueKind<'a>,
}
#[derive(Debug, Clone)]
pub enum JsonValueKind<'a> {
    Object(JsonObject<'a>),
    Array(Vec<JsonValue<'a>>),
    Scalar(Token<'a>),
}
#[derive(Debug, Clone)]
pub struct ClassDefStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub classes: Vec<Token<'a>>,
    pub styles: Styles<'a>,
}
#[derive(Debug, Clone)]
pub struct ClassStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub targets: Vec<Token<'a>>,
    pub classes: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct StyleStatement<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub target: Token<'a>,
    pub styles: Styles<'a>,
}
#[derive(Debug, Clone)]
pub struct Styles<'a> {
    pub span: Span,
    pub values: Vec<StyleValue<'a>>,
}
#[derive(Debug, Clone)]
pub struct StyleValue<'a> {
    pub span: Span,
    pub key: Vec<Token<'a>>,
    pub components: Vec<StyleComponent<'a>>,
}
#[derive(Debug, Clone)]
pub struct StyleComponent<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
