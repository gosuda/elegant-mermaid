use std::borrow::Cow;

use super::lexer::Token;
use crate::source::Span;

#[derive(Debug, Clone)]
pub struct Start<'a> {
    pub span: Span,
    pub statements: Vec<Statement<'a>>,
}

#[derive(Debug, Clone)]
pub struct ClassName<'a> {
    pub span: Span,
    pub tokens: Vec<Token<'a>>,
    pub value: String,
    pub generic: String,
}

#[derive(Debug, Clone)]
pub struct ClassStatement<'a> {
    pub span: Span,
    pub name: ClassName<'a>,
    pub label: Option<Cow<'a, str>>,
    pub css_class: Option<Cow<'a, str>>,
    pub annotation: Option<String>,
    pub members: Vec<MemberStatement<'a>>,
    pub has_body: bool,
}

#[derive(Debug, Clone)]
pub struct MemberStatement<'a> {
    pub span: Span,
    pub text: Cow<'a, str>,
}

#[derive(Debug, Clone)]
pub struct NamespaceStatement<'a> {
    pub span: Span,
    pub name: ClassName<'a>,
    pub label: Option<Cow<'a, str>>,
    pub children: Vec<Statement<'a>>,
}

#[derive(Debug, Clone)]
pub struct RelationStatement<'a> {
    pub span: Span,
    pub from: ClassName<'a>,
    pub to: ClassName<'a>,
    pub multiplicity_start: Option<Cow<'a, str>>,
    pub multiplicity_end: Option<Cow<'a, str>>,
    pub marker_start: Option<&'static str>,
    pub marker_end: Option<&'static str>,
    pub dashed: bool,
    pub label: Option<Cow<'a, str>>,
}

#[derive(Debug, Clone)]
pub enum Statement<'a> {
    Class(ClassStatement<'a>),
    Namespace(NamespaceStatement<'a>),
    Relation(RelationStatement<'a>),
    Member {
        name: ClassName<'a>,
        member: Option<MemberStatement<'a>>,
    },
    Annotation {
        name: ClassName<'a>,
        annotation: String,
    },
    Note {
        span: Span,
        target: Option<ClassName<'a>>,
        text: Cow<'a, str>,
    },
    Direction(Cow<'a, str>),
    Accessibility {
        title: bool,
        text: Cow<'a, str>,
    },
    Style {
        target: String,
        text: Cow<'a, str>,
    },
    ClassDef {
        target: String,
        text: Cow<'a, str>,
    },
    CssClass {
        target: Cow<'a, str>,
        name: Cow<'a, str>,
    },
    Click {
        target: String,
        values: Vec<Cow<'a, str>>,
    },
}
