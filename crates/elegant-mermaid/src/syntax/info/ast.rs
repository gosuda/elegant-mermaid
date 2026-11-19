//! The abstract syntax tree of the info grammar; nodes carry byte spans of the source.

use crate::source::Span;
use crate::syntax::langium::Token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value {
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Info {
    pub span: Span,
    pub header: Token,
    pub show_info: Option<Token>,
    pub title: Option<Value>,
    pub acc_title: Option<Value>,
    pub acc_descr: Option<Value>,
}
