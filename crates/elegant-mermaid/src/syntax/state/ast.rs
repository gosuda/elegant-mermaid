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
    Id {
        id: IdStatement<'a>,
        description: Option<Token<'a>>,
    },
    Transition {
        from: IdStatement<'a>,
        arrow: Token<'a>,
        to: IdStatement<'a>,
        description: Option<Token<'a>>,
    },
    Composite {
        id: Token<'a>,
        description: Option<Token<'a>>,
        body: Option<Document<'a>>,
        delimiters: Option<(Span, Span)>,
    },
    Stereotype {
        id: Token<'a>,
        stereotype: Stereotype,
    },
    Concurrent,
    Note {
        position: NotePosition,
        target: Token<'a>,
        text: Token<'a>,
    },
    FloatingNote {
        text: Token<'a>,
        id: Token<'a>,
    },
    ClassDef(ClassDefStatement<'a>),
    Style(StyleStatement<'a>),
    CssClass(CssClassStatement<'a>),
    Direction(Direction),
    Click {
        target: IdStatement<'a>,
        url: Token<'a>,
        tooltip: Option<Token<'a>>,
    },
    Accessibility {
        title: bool,
        value: Token<'a>,
    },
    Scale(Token<'a>),
    HideEmpty,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stereotype {
    Fork,
    Join,
    Choice,
}
#[derive(Debug, Clone)]
pub struct ClassDefStatement<'a> {
    pub span: Span,
    pub id: Token<'a>,
    pub styles: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct StyleStatement<'a> {
    pub span: Span,
    pub targets: Token<'a>,
    pub styles: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct CssClassStatement<'a> {
    pub span: Span,
    pub targets: Token<'a>,
    pub class: Token<'a>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Direction {
    pub span: Span,
    pub value: &'static str,
}
#[derive(Debug, Clone)]
pub struct IdStatement<'a> {
    pub span: Span,
    pub id: Token<'a>,
    pub css_class: Option<Token<'a>>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NotePosition {
    pub span: Span,
    pub value: &'static str,
}
