use crate::{diag::Diagnostic, source::Span};

#[derive(Debug, PartialEq, Eq)]
pub struct Parsed<'a> {
    pub source: &'a str,
    pub expression: Expr<'a>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Expr<'a> {
    pub span: Span,
    pub kind: ExprKind<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExprKind<'a> {
    Literal(&'a str),
    Row(Vec<Expr<'a>>),
    Group(Box<Expr<'a>>),
    Glyph {
        character: char,
        font: Font,
    },
    Limit {
        font: Font,
    },
    Symbol {
        command: &'a str,
        character: char,
        class: SymbolClass,
        font: Font,
    },
    Fraction {
        numerator: Box<Expr<'a>>,
        denominator: Box<Expr<'a>>,
    },
    Scripts {
        base: Box<Expr<'a>>,
        superscript: Option<Box<Expr<'a>>>,
        subscript: Option<Box<Expr<'a>>>,
    },
    Radical {
        index: Option<Box<Expr<'a>>>,
        radicand: Box<Expr<'a>>,
    },
    Delimited {
        left: Delimiter,
        body: Box<Expr<'a>>,
        right: Delimiter,
    },
    Styled {
        font: Font,
        body: Box<Expr<'a>>,
    },
    Text {
        body: Box<Expr<'a>>,
    },
    Space(Space),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Font {
    Roman,
    Italic,
    Bold,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolClass {
    Greek,
    Ordinary,
    Binary,
    Relation,
    Sum,
    Product,
    Integral,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Space {
    Thin,
    Medium,
    Quad,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delimiter {
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    Bar,
    Invisible,
}
