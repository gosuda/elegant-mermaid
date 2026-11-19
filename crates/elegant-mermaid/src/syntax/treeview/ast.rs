use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub value: String,
    pub span: Span,
    pub(super) from: usize,
    pub(super) to: usize,
}

impl Token {
    pub(super) fn end_of(span: Span, at: usize) -> Self {
        Self {
            kind: super::lexer::K_EOF,
            text: String::new(),
            value: String::new(),
            span,
            from: at,
            to: at,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TreeView {
    pub span: Span,
    pub header: Option<Token>,
    pub title: Option<Token>,
    pub acc_title: Option<Token>,
    pub acc_descr: Option<Token>,
    pub nodes: Vec<TreeNode>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TreeNode {
    pub span: Span,
    pub indent: Option<Token>,
    pub name: Token,
    pub class: Option<Token>,
    pub icon: Option<Token>,
    pub desc: Option<Token>,
}
