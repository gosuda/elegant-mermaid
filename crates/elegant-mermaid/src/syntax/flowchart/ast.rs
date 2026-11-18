//! Abstract syntax tree of the flowchart grammar, `flowchart-053` to `flowchart-056`.
//!
//! Node names follow the authority rule names of `spec/grammar/flowchart.md`.

use crate::source::Span;
use crate::syntax::flowchart::tokens::Token;

/// The `document` node: the header and the body statements in source order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Document {
    pub span: Span,
    pub config: GraphConfig,
    pub lines: Vec<Line>,
}

/// The `graphConfig` node: the header keyword and its optional direction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphConfig {
    pub span: Span,
    pub keyword: Span,
    /// The raw direction token text, for example `LR`, `TD` or `BR`; `None` for `NODIR`.
    pub direction: Option<Span>,
}

/// One `line`: a statement together with its span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Line {
    pub span: Span,
    pub kind: Statement,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Vertex(VertexStatement),
    Style(StyleStatement),
    ClassDef(ClassDefStatement),
    Class(ClassStatement),
    LinkStyle(LinkStyleStatement),
    Click(ClickStatement),
    Subgraph(Subgraph),
    Direction(Direction),
    AccTitle(AccTitle),
    AccDescr(AccDescr),
    AccDescrBlock(AccDescrBlock),
}

/// The `vertexStatement` node: at least one node group, joined by links.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VertexStatement {
    pub span: Span,
    pub first: NodeGroup,
    pub rest: Vec<(Link, NodeGroup)>,
}

/// A run of nodes joined by `&`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NodeGroup {
    pub span: Span,
    pub nodes: Vec<StyledVertex>,
}

/// The `styledVertex` node: a vertex with an optional `:::` class and shape data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StyledVertex {
    pub span: Span,
    pub vertex: Vertex,
    pub class: Option<IdString>,
    pub shape_data: Option<ShapeData>,
}

/// The `vertex` node: an id and an optional label.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Vertex {
    pub span: Span,
    pub id: IdString,
    pub label: Option<Label>,
}

/// A bracket pair with its text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub form: LabelForm,
    pub text: Text,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LabelForm {
    Square,
    Round,
    Round2,
    Circle,
    Ellipse,
    Stadium,
    Subroutine,
    RectProps { field: String, value: String },
    Cylinder,
    Diamond,
    Diamond2,
    Odd,
    Trap { closer: TrapCloser },
    InvTrap { closer: TrapCloser },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrapCloser {
    Trap,
    InvTrap,
}

/// The `link` node: the link halves and their optional arrow text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Link {
    pub span: Span,
    pub statement: LinkStatement,
    pub arrow_text: Option<ArrowText>,
    pub edge_text: Option<EdgeText>,
}

/// The `linkStatement` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkStatement {
    pub span: Span,
    pub link_id: Option<Span>,
    pub start: Option<Span>,
    pub end: Span,
    pub start_text: Option<String>,
    pub end_text: String,
}

/// The `arrowText` node: the `|label|` form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrowText {
    pub span: Span,
    pub text: Text,
}

/// The `edgeText` node: the bare text between the two halves of a link.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EdgeText {
    pub span: Span,
    pub kind: TextKind,
    pub text: String,
}

/// The `text` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Text {
    pub span: Span,
    pub kind: TextKind,
    pub text: String,
    /// The tokens the text was parsed from, in source order.
    pub tokens: Vec<Token>,
}

/// The `textNoTags` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextNoTags {
    pub span: Span,
    pub text: String,
}

/// The `idString` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdString {
    pub span: Span,
    pub text: String,
}

/// The `alphaNum` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlphaNum {
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TextKind {
    Plain,
    String,
    Markdown,
}

/// The `shapeData` node: the concatenated body of an `@{ ... }` block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShapeData {
    pub span: Span,
    pub text: String,
    pub src_at: Vec<usize>,
}

/// The `subgraph` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subgraph {
    pub span: Span,
    pub keyword: Span,
    pub id: Option<TextNoTags>,
    pub title: Option<Text>,
    pub body: Vec<Line>,
    pub end_span: Option<Span>,
}

/// The `styleStatement` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StyleStatement {
    pub span: Span,
    pub target: IdString,
    pub styles: StylesOpt,
}

/// The `classDefStatement` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassDefStatement {
    pub span: Span,
    pub names: IdString,
    pub styles: StylesOpt,
}

/// The `classStatement` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassStatement {
    pub span: Span,
    pub targets: IdString,
    pub class_name: IdString,
}

/// The `linkStyleStatement` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkStyleStatement {
    pub span: Span,
    pub selector: LinkSelector,
    pub interpolate: Option<AlphaNum>,
    pub styles: Option<StylesOpt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinkSelector {
    Default(Span),
    NumList(NumList),
}

/// The `numList` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumList {
    pub span: Span,
    pub numbers: Vec<Span>,
}

/// The `stylesOpt` node: one style string per comma-separated entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StylesOpt {
    pub span: Span,
    pub styles: Vec<String>,
}

/// The `clickStatement` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClickStatement {
    pub span: Span,
    pub target: Span,
    pub action: ClickAction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClickAction {
    Call {
        name: String,
        name_span: Span,
        args: Option<String>,
        tooltip: Option<String>,
    },
    PlainCall {
        name: String,
        name_span: Span,
        tooltip: Option<String>,
    },
    Link {
        href: String,
        href_span: Span,
        tooltip: Option<String>,
        target: Option<String>,
    },
}

/// The `direction` node of a `direction TB` statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Direction {
    pub span: Span,
}

/// The `acc_title` alternative of `statement`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccTitle {
    pub span: Span,
    pub value: Span,
    pub text: String,
}

/// The `acc_descr` alternative of `statement`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccDescr {
    pub span: Span,
    pub value: Span,
    pub text: String,
}

/// The `acc_descr_multiline_value` alternative of `statement`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccDescrBlock {
    pub span: Span,
    pub value: Span,
    pub text: String,
}
