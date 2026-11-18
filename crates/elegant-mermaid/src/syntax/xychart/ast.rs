//! Abstract syntax tree of the xychart grammar (`spec/grammar/xychart.md`).
//!
//! Node names retain the upstream production names in PascalCase, and spans run from
//! the first to the last consumed token without a trailing statement separator.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Start<'a> {
    pub span: Span,
    pub headers: Vec<Header<'a>>,
    pub document: Document<'a>,
}

#[derive(Debug, Clone)]
pub struct Header<'a> {
    pub span: Span,
    pub keyword: Token<'a>,
    pub orientation: Option<Token<'a>>,
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
    Title(Title),
    Axis(AxisStatement<'a>),
    Plot(PlotStatement<'a>),
    Accessibility(Accessibility<'a>),
}

#[derive(Debug, Clone)]
pub struct Text {
    pub span: Span,
    pub value: String,
    pub markdown: bool,
}

#[derive(Debug, Clone)]
pub struct Number<'a> {
    pub span: Span,
    pub text: &'a str,
}

#[derive(Debug, Clone)]
pub struct Title {
    pub span: Span,
    pub text: Text,
}

#[derive(Debug, Clone)]
pub struct Range<'a> {
    pub span: Span,
    pub min: Number<'a>,
    pub max: Number<'a>,
}

#[derive(Debug, Clone)]
pub struct BandData {
    pub span: Span,
    pub categories: Vec<Text>,
}

#[derive(Debug, Clone)]
pub struct AxisStatement<'a> {
    pub span: Span,
    pub y: bool,
    pub title: Option<Text>,
    pub band: Option<BandData>,
    pub range: Option<Range<'a>>,
}

#[derive(Debug, Clone)]
pub struct DataPoint<'a> {
    pub span: Span,
    pub number: Number<'a>,
    pub label: Option<Text>,
}

#[derive(Debug, Clone)]
pub struct PlotData<'a> {
    pub span: Span,
    pub points: Vec<DataPoint<'a>>,
}

#[derive(Debug, Clone)]
pub struct PlotStatement<'a> {
    pub span: Span,
    pub line: bool,
    pub title: Option<Text>,
    pub data: PlotData<'a>,
}

#[derive(Debug, Clone)]
pub struct Accessibility<'a> {
    pub span: Span,
    pub title: bool,
    pub multiline: bool,
    pub value: Token<'a>,
}
