//! Abstract syntax tree of the quadrant grammar (`spec/grammar/quadrant.md`).
//!
//! Node names retain the upstream production names in PascalCase, and spans run from
//! the first to the last consumed token without a trailing statement separator.

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
    pub lines: Vec<Line<'a>>,
}

#[derive(Debug, Clone)]
pub struct Line<'a> {
    pub span: Span,
    pub statement: Statement<'a>,
    pub eol: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct Statement<'a> {
    pub span: Span,
    pub kind: Option<StatementKind<'a>>,
}

#[derive(Debug, Clone)]
pub enum StatementKind<'a> {
    Title(Title<'a>),
    Accessibility(Accessibility<'a>),
    AxisDetails(AxisDetails<'a>),
    QuadrantDetails(QuadrantDetails),
    ClassDef(ClassDefStatement),
    Points(Points<'a>),
}

#[derive(Debug, Clone)]
pub struct Text {
    pub span: Span,
    pub content: Span,
    pub value: String,
    pub markdown: bool,
}

#[derive(Debug, Clone)]
pub struct Title<'a> {
    pub span: Span,
    pub value: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct Accessibility<'a> {
    pub span: Span,
    pub title: bool,
    pub multiline: bool,
    pub value: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct AxisDetails<'a> {
    pub span: Span,
    pub y: bool,
    pub first: Text,
    pub delimiter: Option<Token<'a>>,
    pub second: Option<Text>,
}

#[derive(Debug, Clone)]
pub struct QuadrantDetails {
    pub span: Span,
    pub number: usize,
    pub text: Text,
}

#[derive(Debug, Clone)]
pub struct Style {
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct StylesOpt {
    pub span: Span,
    pub styles: Vec<Style>,
}

#[derive(Debug, Clone)]
pub struct IdString {
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct ClassDefStatement {
    pub span: Span,
    pub name: IdString,
    pub styles: StylesOpt,
}

#[derive(Debug, Clone)]
pub struct Points<'a> {
    pub span: Span,
    pub text: Text,
    pub class: Option<Token<'a>>,
    pub point_x: Token<'a>,
    pub point_y: Token<'a>,
    pub styles: Option<StylesOpt>,
}
