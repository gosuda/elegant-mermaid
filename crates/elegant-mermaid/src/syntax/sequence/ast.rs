//! Abstract syntax tree of the sequence grammar (`spec/grammar/sequence.md`).
//!
//! Node names retain the upstream production names in PascalCase, and spans run from
//! the first to the last consumed token without a trailing statement separator.

use std::borrow::Cow;

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
    pub statement: Option<Statement<'a>>,
}

#[derive(Debug, Clone)]
pub struct Statement<'a> {
    pub span: Span,
    pub kind: StatementKind<'a>,
}

#[derive(Debug, Clone)]
pub enum StatementKind<'a> {
    Participant(ParticipantStatement<'a>),
    Signal(Signal<'a>),
    Autonumber {
        span: Span,
        start: Option<Token<'a>>,
        step: Option<Token<'a>>,
        off: bool,
        off_span: Span,
    },
    Activate {
        span: Span,
        keyword: Span,
        actor: Actor<'a>,
    },
    Deactivate {
        span: Span,
        keyword: Span,
        actor: Actor<'a>,
    },
    Note(NoteStatement<'a>),
    Links {
        span: Span,
        keyword: Span,
        actor: Actor<'a>,
        text: Text2<'a>,
    },
    Link {
        span: Span,
        keyword: Span,
        actor: Actor<'a>,
        text: Text2<'a>,
    },
    Properties {
        span: Span,
        keyword: Span,
        actor: Actor<'a>,
        text: Text2<'a>,
    },
    Details {
        span: Span,
        keyword: Span,
        actor: Actor<'a>,
        text: Text2<'a>,
    },
    Title {
        span: Span,
        legacy: bool,
        value: Cow<'a, str>,
    },
    Accessibility {
        span: Span,
        title: bool,
        value: Span,
    },
    Box(BoxBlock<'a>),
    Control(ControlBlock<'a>),
}

#[derive(Debug, Clone)]
pub struct ParticipantStatement<'a> {
    pub create: Option<Span>,
    pub keyword: Span,
    pub draw: Option<&'static str>,
    pub destroy: bool,
    pub actor: Actor<'a>,
    pub alias: Option<Alias<'a>>,
    pub config: Option<ConfigObject<'a>>,
}

#[derive(Debug, Clone)]
pub struct Alias<'a> {
    pub token: Token<'a>,
    pub text: Text2<'a>,
}

#[derive(Debug, Clone)]
pub struct ConfigObject<'a> {
    pub span: Span,
    pub content: Cow<'a, str>,
    pub content_span: Span,
}

#[derive(Debug, Clone)]
pub struct Actor<'a> {
    pub span: Span,
    pub text: Cow<'a, str>,
}

#[derive(Debug, Clone)]
pub struct Signal<'a> {
    pub span: Span,
    pub source: Actor<'a>,
    pub central_start: bool,
    pub arrow: Token<'a>,
    pub suffix: Option<Token<'a>>,
    pub central_end: bool,
    pub target: Actor<'a>,
    pub text: Text2<'a>,
}

#[derive(Debug, Clone)]
pub struct NoteStatement<'a> {
    pub span: Span,
    pub placement: Span,
    pub over: bool,
    pub actors: Vec<Actor<'a>>,
    pub text: Text2<'a>,
}

#[derive(Debug, Clone)]
pub struct Text2<'a> {
    pub span: Span,
    pub text: Cow<'a, str>,
}

#[derive(Debug, Clone)]
pub struct BoxBlock<'a> {
    pub span: Span,
    pub keyword: Span,
    pub text: Text2<'a>,
    pub section: BoxSection<'a>,
    pub close: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct BoxSection<'a> {
    pub span: Span,
    pub lines: Vec<Line<'a>>,
}

#[derive(Debug, Clone)]
pub struct ControlBlock<'a> {
    pub span: Span,
    pub keyword: Span,
    pub kind: &'static str,
    pub text: Text2<'a>,
    pub sections: Vec<Section<'a>>,
    pub close: Token<'a>,
}

#[derive(Debug, Clone)]
pub struct Section<'a> {
    pub separator: Option<Token<'a>>,
    pub title: Text2<'a>,
    pub document: Document<'a>,
}
