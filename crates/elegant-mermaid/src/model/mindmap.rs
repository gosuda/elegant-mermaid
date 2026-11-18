//! The resolved model of a `mindmap` diagram: one tree of nodes in declaration order.

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::entities::decode_entities as decode;
use crate::syntax::mindmap::ast::{Description, Node as AstNode, Start, Statement, Token};
use crate::syntax::mindmap::{C_NO_TARGET, C_SECOND_ROOT, diagnostic};
use crate::syntax::preprocess::preprocess;

/// The shape of a node, named after its dump shape id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Shape {
    #[default]
    Default,
    Square,
    Rounded,
    Circle,
    Cloud,
    Bang,
    Hexagon,
}

impl Shape {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Square => "rect",
            Self::Rounded => "rounded",
            Self::Circle => "mindmapCircle",
            Self::Cloud => "cloud",
            Self::Bang => "bang",
            Self::Hexagon => "hexagon",
            Self::Default => "defaultMindmapNode",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub index: usize,
    pub parent: Option<usize>,
    pub level: i64,
    pub children: Vec<usize>,
    pub source_id: String,
    pub description: String,
    pub label: String,
    pub markdown: bool,
    pub shape: Shape,
    pub icon: String,
    pub class: String,
    pub span: Span,
}

/// The honoured `mindmap` config keys, in px.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Config {
    pub padding: Option<i64>,
    pub max_node_width: Option<i64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Model {
    pub nodes: Vec<Node>,
    pub config: Config,
}

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            nodes: Vec::new(),
            config: read_config(source),
        },
        diagnostics: Vec::new(),
        base: 0,
    };
    for item in &document.document.items {
        resolver.statement(&item.statement);
    }
    (resolver.model, resolver.diagnostics)
}

struct Resolver {
    model: Model,
    diagnostics: Vec<Diagnostic>,
    base: i64,
}

impl Resolver {
    fn statement(&mut self, statement: &Statement) {
        if let Some(node) = &statement.node {
            self.insert(statement, node);
        } else if let Some(icon) = &statement.icon {
            self.decorate(icon, |node, text| node.icon = text);
        } else if let Some(class) = &statement.class {
            self.decorate(class, |node, text| node.class = text);
        }
    }

    fn decorate(&mut self, token: &Token, apply: impl Fn(&mut Node, String)) {
        match self.model.nodes.last_mut() {
            Some(node) => apply(node, normalize_newlines(&token.text)),
            None => self.diagnostics.push(diagnostic(
                C_NO_TARGET,
                "decoration has no preceding node".to_owned(),
                token.span,
            )),
        }
    }

    fn insert(&mut self, statement: &Statement, ast: &AstNode) {
        let mut node = node_of(ast);
        let raw = statement.indent.as_ref().map_or(0, |indent| {
            i64::try_from(indent.text.chars().count()).unwrap_or(i64::MAX)
        });
        node.index = self.model.nodes.len();
        if node.index == 0 {
            self.base = raw;
        }
        node.level = raw - self.base;
        if node.index > 0 {
            let Some(parent) = self.parent_of(node.level) else {
                let message = format!(
                    "node {} has no parent; only one root is allowed",
                    node.label
                );
                self.diagnostics
                    .push(diagnostic(C_SECOND_ROOT, message, node.span));
                return;
            };
            node.parent = Some(parent);
            self.model.nodes[parent].children.push(node.index);
        }
        self.model.nodes.push(node);
    }

    fn parent_of(&self, level: i64) -> Option<usize> {
        self.model.nodes.iter().rposition(|node| node.level < level)
    }
}

fn node_of(ast: &AstNode) -> Node {
    let id = ast.id.as_ref().map(|t| normalize_newlines(&t.text));
    let (source_id, description, shape) = match (&ast.open, &ast.descr, &ast.close) {
        (Some(open), Some(descr), Some(close)) => {
            let description = normalize_newlines(&descr.text);
            (
                id.unwrap_or_else(|| description.clone()),
                description,
                shape_of(&open.text, &close.text),
            )
        }
        _ => {
            let id = id.unwrap_or_default();
            (id.clone(), id, Shape::Default)
        }
    };
    Node {
        index: 0,
        parent: None,
        level: 0,
        children: Vec::new(),
        label: decode(description.trim()),
        source_id,
        description,
        markdown: ast.description == Description::Markdown,
        shape,
        icon: String::new(),
        class: String::new(),
        span: ast.span,
    }
}

fn normalize_newlines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

fn shape_of(open: &str, closing: &str) -> Shape {
    match open {
        "[" => Shape::Square,
        "(" if closing == ")" => Shape::Rounded,
        "(" | ")" => Shape::Cloud,
        "((" => Shape::Circle,
        "))" => Shape::Bang,
        "{{" => Shape::Hexagon,
        _ => Shape::Default,
    }
}

fn read_config(source: &str) -> Config {
    let preprocessed = preprocess(source);
    let mut config = Config::default();
    for block in [
        preprocessed.frontmatter.and_then(|f| f.config),
        preprocessed.init_config,
    ]
    .into_iter()
    .flatten()
    {
        read_block(&mut config, &block);
    }
    config
}

fn read_block(config: &mut Config, block: &ConfigValue) {
    let ConfigValue::Mapping(entries) = block else {
        return;
    };
    let Some(entry) = entries.iter().find(|entry| entry.key == "mindmap") else {
        return;
    };
    let ConfigValue::Mapping(fields) = &entry.value else {
        return;
    };
    for field in fields {
        let ConfigValue::Integer(text) = &field.value else {
            continue;
        };
        let Some(value) = text.parse::<i64>().ok().filter(|value| *value >= 0) else {
            continue;
        };
        match field.key.as_str() {
            "padding" => config.padding = Some(value),
            "maxNodeWidth" => config.max_node_width = Some(value),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests;
