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
    pub label: Option<&'a str>,
    pub css_class: Option<&'a str>,
    pub annotation: Option<String>,
    pub members: Vec<MemberStatement<'a>>,
    pub has_body: bool,
}

#[derive(Debug, Clone)]
pub struct MemberStatement<'a> {
    pub span: Span,
    pub text: &'a str,
}

#[derive(Debug, Clone)]
pub struct NamespaceStatement<'a> {
    pub span: Span,
    pub name: ClassName<'a>,
    pub label: Option<&'a str>,
    pub children: Vec<Statement<'a>>,
}

#[derive(Debug, Clone)]
pub struct RelationStatement<'a> {
    pub span: Span,
    pub from: ClassName<'a>,
    pub to: ClassName<'a>,
    pub multiplicity_start: Option<&'a str>,
    pub multiplicity_end: Option<&'a str>,
    pub marker_start: Option<&'static str>,
    pub marker_end: Option<&'static str>,
    pub dashed: bool,
    pub label: Option<&'a str>,
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
        text: &'a str,
    },
    Direction(&'a str),
    Accessibility {
        title: bool,
        text: &'a str,
    },
    Style {
        target: String,
        text: &'a str,
    },
    ClassDef {
        target: String,
        text: &'a str,
    },
    CssClass {
        target: &'a str,
        name: &'a str,
    },
    Click {
        target: String,
        values: Vec<&'a str>,
    },
}
