//! Abstract syntax tree of the venn grammar (`spec/grammar/venn.md`).
//!
//! Node names retain the upstream production names in PascalCase, and spans run from
//! the first to the last consumed token without a trailing statement separator.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Start {
    pub span: Span,
    pub leading: OptNewlines,
    pub header: Option<Token>,
    pub document: Document,
}

#[derive(Debug, Clone)]
pub struct OptNewlines {
    pub span: Span,
    pub newlines: Vec<Token>,
}

#[derive(Debug, Clone)]
pub struct Document {
    pub span: Span,
    pub lines: Vec<Line>,
}

#[derive(Debug, Clone)]
pub struct Line {
    pub span: Span,
    pub newline: Option<Token>,
    pub statement: Option<Statement>,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Title(Title),
    Set(Set),
    Union(Union),
    Text(Text),
    IndentedText(IndentedText),
    Style(Style),
}

#[derive(Debug, Clone)]
pub struct Number {
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub span: Span,
    pub kind: &'static str,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct IdentifierList {
    pub span: Span,
    pub ids: Vec<Identifier>,
}

#[derive(Debug, Clone)]
pub struct Title {
    pub span: Span,
    pub token: Token,
}

#[derive(Debug, Clone)]
pub struct Set {
    pub span: Span,
    pub keyword: Token,
    pub id: Identifier,
    pub label: Option<Token>,
    pub size: Option<Number>,
}

#[derive(Debug, Clone)]
pub struct Union {
    pub span: Span,
    pub keyword: Token,
    pub ids: IdentifierList,
    pub label: Option<Token>,
    pub size: Option<Number>,
}

#[derive(Debug, Clone)]
pub struct Text {
    pub span: Span,
    pub keyword: Token,
    pub targets: IdentifierList,
    pub id: Identifier,
    pub label: Option<Token>,
}

#[derive(Debug, Clone)]
pub struct IndentedTextTail {
    pub span: Span,
    pub id: Identifier,
    pub label: Option<Token>,
}

#[derive(Debug, Clone)]
pub struct IndentedText {
    pub span: Span,
    pub keyword: Token,
    pub tail: IndentedTextTail,
}

#[derive(Debug, Clone)]
pub struct ValueToken {
    pub span: Span,
    pub kind: &'static str,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct ValueTokens {
    pub span: Span,
    pub tokens: Vec<ValueToken>,
}

#[derive(Debug, Clone)]
pub struct StyleValue {
    pub span: Span,
    pub string: Option<Token>,
    pub tokens: Option<ValueTokens>,
}

#[derive(Debug, Clone)]
pub struct StyleField {
    pub span: Span,
    pub key: Token,
    pub value: StyleValue,
}

#[derive(Debug, Clone)]
pub struct StylesOpt {
    pub span: Span,
    pub fields: Vec<StyleField>,
}

#[derive(Debug, Clone)]
pub struct Style {
    pub span: Span,
    pub keyword: Token,
    pub targets: IdentifierList,
    pub styles: StylesOpt,
}
