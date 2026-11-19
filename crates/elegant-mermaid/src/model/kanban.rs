//! The resolved model of a `kanban` diagram: sections, cards, and node metadata.

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::entities::decode_entities as decode;
use crate::syntax::kanban::ast::{Node as AstNode, Start, Statement, Token};
use crate::syntax::kanban::diagnostic;
use crate::syntax::preprocess::preprocess;

mod js;
mod metadata;

const C_ITEMS_WITHOUT_SECTION: &str = "kanban/items-without-section";
const C_MALFORMED_METADATA: &str = "kanban/malformed-metadata";
const C_INVALID_SHAPE: &str = "kanban/invalid-shape";
const C_NO_NODE: &str = "kanban/decoration-without-node";

const DEFAULT_NODE_PADDING: i64 = 10;
const DEFAULT_NODE_MAX_WIDTH: i64 = 200;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum NodeType {
    #[default]
    Default,
    RoundedRect,
    Rect,
    Circle,
    Cloud,
    Bang,
    Hexagon,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub index: usize,
    pub id: String,
    pub level: usize,
    pub label: String,
    pub width: i64,
    pub padding: i64,
    pub node_type: NodeType,
    pub parent: Option<usize>,
    pub parent_id: String,
    pub ticket: String,
    pub assigned: String,
    pub icon: String,
    pub class: String,
    pub priority: String,
    pub has_priority: bool,
    pub anchor: Span,
    pub span: Span,
}

impl Node {
    #[must_use]
    pub const fn is_section(&self) -> bool {
        self.parent.is_none()
    }
}

/// The honoured config keys: the `kanban` block and the `mindmap` node defaults, in px.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
    pub section_width: Option<i64>,
    pub padding: Option<i64>,
    pub node_padding: i64,
    pub node_max_width: i64,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            section_width: None,
            padding: None,
            node_padding: DEFAULT_NODE_PADDING,
            node_max_width: DEFAULT_NODE_MAX_WIDTH,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Model {
    pub nodes: Vec<Node>,
    pub sections: Vec<usize>,
    pub config: Config,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Column {
    pub section: usize,
    pub cards: Vec<usize>,
}

impl Model {
    #[must_use]
    pub fn columns(&self) -> Vec<Column> {
        self.sections
            .iter()
            .map(|&section| {
                let id = self.nodes.get(section).map_or("", |node| node.id.as_str());
                let cards = self
                    .nodes
                    .iter()
                    .filter(|node| node.parent.is_some() && node.parent_id == id)
                    .map(|node| node.index)
                    .collect();
                Column { section, cards }
            })
            .collect()
    }
}

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        source,
        model: Model {
            nodes: Vec::new(),
            sections: Vec::new(),
            config: read_config(source),
        },
        diagnostics: Vec::new(),
        counter: 0,
        offender: None,
    };
    for item in &document.document.items {
        resolver.statement(&item.statement);
    }
    (resolver.model, resolver.diagnostics)
}

struct Resolver<'a> {
    source: &'a str,
    model: Model,
    diagnostics: Vec<Diagnostic>,
    counter: usize,
    offender: Option<usize>,
}

impl Resolver<'_> {
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
            Some(node) => apply(node, decode(&normalize_newlines(&token.text))),
            None => self.diagnostics.push(diagnostic(
                C_NO_NODE,
                "decoration requires a preceding node".to_owned(),
                token.span,
            )),
        }
    }

    fn insert(&mut self, statement: &Statement, ast: &AstNode) {
        let mut node = self.node_of(statement, ast);
        if let Some(data) = &statement.data
            && !self.apply_metadata(&mut node, data)
        {
            return;
        }
        let Some(parent) = self.section_for(node.level) else {
            return;
        };
        node.index = self.model.nodes.len();
        match parent {
            Some(parent) => {
                node.parent = Some(parent);
                node.parent_id = self
                    .model
                    .nodes
                    .get(parent)
                    .map(|section| section.id.clone())
                    .unwrap_or_default();
            }
            None => self.model.sections.push(node.index),
        }
        self.model.nodes.push(node);
    }

    fn node_of(&mut self, statement: &Statement, ast: &AstNode) -> Node {
        let first = ast
            .id
            .as_ref()
            .or(ast.open.as_ref())
            .map_or(ast.span, |token| token.span);
        let (level, anchor) = statement.indent.as_ref().map_or((0, first), |indent| {
            (indent.text.chars().count(), indent.span)
        });
        let (identity, descr, node_type) = match (&ast.open, &ast.descr, &ast.close) {
            (Some(open), Some(descr), Some(close)) => (
                ast.id
                    .as_ref()
                    .map_or_else(|| descr.text.clone(), |id| id.text.clone()),
                descr.text.clone(),
                type_of(&open.text, &close.text),
            ),
            _ => {
                let id = ast
                    .id
                    .as_ref()
                    .map(|id| id.text.clone())
                    .unwrap_or_default();
                (id.clone(), id, NodeType::Default)
            }
        };
        let id = self.identifier(decode(&normalize_newlines(&identity)));
        let mut padding = self.model.config.node_padding;
        if matches!(
            node_type,
            NodeType::RoundedRect | NodeType::Rect | NodeType::Hexagon
        ) {
            padding *= 2;
        }
        Node {
            index: 0,
            id,
            level,
            label: decode(&normalize_newlines(&descr)),
            width: self.model.config.node_max_width,
            padding,
            node_type,
            parent: None,
            parent_id: String::new(),
            ticket: String::new(),
            assigned: String::new(),
            icon: String::new(),
            class: String::new(),
            priority: String::new(),
            has_priority: false,
            anchor,
            span: ast.span,
        }
    }

    fn identifier(&mut self, id: String) -> String {
        if !id.is_empty() {
            return id;
        }
        let generated = format!("kbn{}", self.counter);
        self.counter += 1;
        generated
    }

    fn section_for(&mut self, level: usize) -> Option<Option<usize>> {
        let base = self.model.nodes.first().map_or(level, |node| node.level);
        let mut last = None;
        for index in (0..self.model.nodes.len()).rev() {
            let node_level = self.model.nodes.get(index).map_or(base, |node| node.level);
            if node_level == base && last.is_none() {
                last = Some(index);
            }
            if node_level < base {
                self.reject_below(index);
                return None;
            }
        }
        if level == base {
            return Some(None);
        }
        Some(last)
    }

    fn reject_below(&mut self, offender: usize) {
        if self.offender == Some(offender) {
            return;
        }
        self.offender = Some(offender);
        let Some(node) = self.model.nodes.get(offender) else {
            return;
        };
        let message = format!("items without section detected at {}", node.label);
        let anchor = node.anchor;
        self.diagnostics
            .push(diagnostic(C_ITEMS_WITHOUT_SECTION, message, anchor));
    }
}

fn normalize_newlines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

fn type_of(open: &str, closing: &str) -> NodeType {
    match open {
        "[" => NodeType::Rect,
        "(" if closing == ")" => NodeType::RoundedRect,
        "(" | ")" => NodeType::Cloud,
        "((" => NodeType::Circle,
        "))" => NodeType::Bang,
        "{{" => NodeType::Hexagon,
        _ => NodeType::Default,
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
    for entry in entries {
        let ConfigValue::Mapping(fields) = &entry.value else {
            continue;
        };
        for field in fields {
            let ConfigValue::Integer(text) = &field.value else {
                continue;
            };
            let Some(value) = text.parse::<i64>().ok().filter(|value| *value >= 0) else {
                continue;
            };
            match (entry.key.as_str(), field.key.as_str()) {
                ("kanban", "padding") => config.padding = Some(value),
                ("kanban", "sectionWidth") if value > 0 => config.section_width = Some(value),
                ("mindmap", "padding") => config.node_padding = value,
                ("mindmap", "maxNodeWidth") => config.node_max_width = value,
                _ => {}
            }
        }
    }
}

#[cfg(test)]
mod tests;
