//! The resolved model of an `ishikawa` diagram: the effect and its causes in
//! statement order, as one tree.

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::entities::decode_entities as decode;
use crate::syntax::ishikawa::ast::{Start, Statement, Token};
use crate::syntax::ishikawa::{diagnostic, is_space};

/// The deepest cause nesting; the effect is depth 0.
pub const MAX_DEPTH: usize = 64;

const C_NESTING: &str = "limit/nesting-depth";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub index: usize,
    pub parent: Option<usize>,
    pub depth: usize,
    pub children: Vec<usize>,
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Model {
    pub nodes: Vec<Node>,
}

pub fn resolve(document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model::default(),
        diagnostics: Vec::new(),
        stack: Vec::new(),
        base: None,
    };
    for item in &document.document.items {
        if let Some(text) = &item.statement.text {
            resolver.add(&item.statement, text);
        }
    }
    (resolver.model, resolver.diagnostics)
}

struct Active {
    level: usize,
    node: usize,
}

struct Resolver {
    model: Model,
    diagnostics: Vec<Diagnostic>,
    stack: Vec<Active>,
    base: Option<usize>,
}

impl Resolver {
    fn add(&mut self, statement: &Statement, text: &Token) {
        let raw = statement
            .indent
            .as_ref()
            .map_or(0, |indent| indent.text.chars().count());
        let mut node = Node {
            index: self.model.nodes.len(),
            parent: None,
            depth: 0,
            children: Vec::new(),
            label: decode(text.text.trim_matches(is_space)),
            span: text.span,
        };
        if self.model.nodes.is_empty() {
            self.model.nodes.push(node);
            self.stack = vec![Active { level: 0, node: 0 }];
            return;
        }
        let base = *self.base.get_or_insert(raw);
        let level = (raw + 1).saturating_sub(base).max(1);
        while self.stack.len() > 1 && self.stack.last().is_some_and(|top| top.level >= level) {
            self.stack.pop();
        }
        if self.stack.len() > MAX_DEPTH {
            self.diagnostics.push(diagnostic(
                C_NESTING,
                "nesting depth exceeds 64".to_owned(),
                text.span,
            ));
            return;
        }
        let Some(parent) = self.stack.last().map(|top| top.node) else {
            return;
        };
        node.parent = Some(parent);
        node.depth = self.stack.len();
        let index = node.index;
        if let Some(owner) = self.model.nodes.get_mut(parent) {
            owner.children.push(index);
        }
        self.model.nodes.push(node);
        self.stack.push(Active { level, node: index });
    }
}

#[cfg(test)]
mod tests;
