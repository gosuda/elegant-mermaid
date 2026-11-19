//! The abstract syntax tree of the cynefin grammar; nodes carry byte spans of the source.

use crate::source::Span;
use crate::syntax::langium::Token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value {
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DomainItem {
    pub span: Span,
    pub label: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DomainBlock {
    pub span: Span,
    pub domain: Token,
    pub items: Vec<DomainItem>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transition {
    pub span: Span,
    pub from: Token,
    pub to: Token,
    pub label: Option<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cynefin {
    pub span: Span,
    pub header: Token,
    pub domains: Vec<DomainBlock>,
    pub transitions: Vec<Transition>,
    pub title: Option<Value>,
    pub acc_title: Option<Value>,
    pub acc_descr: Option<Value>,
}
