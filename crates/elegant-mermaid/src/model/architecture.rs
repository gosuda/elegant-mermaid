//! Resolved model of the `architecture` kind (`spec/grammar/architecture.md`, semantic
//! resolution).
//!
//! Resolution order is fixed: metadata, every group, every service, every junction, edges,
//! then alignments. The first failing check of an element drops it.

use std::collections::{BTreeMap, BTreeSet};

use crate::diag::{Diagnostic, Related};
use crate::source::Span;
use crate::syntax::architecture::ast::{
    Alignment as AlignmentNode, Architecture, Edge as EdgeNode, Junction, Service, Statement,
    StatementKind, Value,
};
use crate::syntax::architecture::diagnostic;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::preprocess::preprocess;

const MAX_PADDING: i64 = 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Group {
    pub id: String,
    pub icon: String,
    pub title: String,
    pub parent: String,
    pub span: Span,
    pub id_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub id: String,
    pub junction: bool,
    pub icon: String,
    pub icon_text: String,
    pub title: String,
    pub parent: String,
    pub span: Span,
    pub id_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edge {
    pub from: String,
    pub to: String,
    pub from_side: String,
    pub to_side: String,
    pub from_into: bool,
    pub to_into: bool,
    pub from_group: bool,
    pub to_group: bool,
    pub title: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Alignment {
    pub direction: String,
    pub members: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfigEntry {
    pub key: String,
    pub value: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EdgeDeclaration {
    Resolved(usize),
    Rejected(Box<Edge>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Model {
    pub header_span: Span,
    pub element_declarations: usize,
    pub edge_declarations: Vec<EdgeDeclaration>,
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub groups: Vec<Group>,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub alignments: Vec<Alignment>,
    pub config: Vec<ConfigEntry>,
}

#[derive(Debug, Clone, Copy)]
struct Registration {
    group: bool,
    id_span: Span,
}

pub fn resolve(source: &str, document: &Architecture) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            header_span: document.header.span,
            element_declarations: document
                .statements
                .iter()
                .filter(|statement| {
                    matches!(
                        statement.kind,
                        StatementKind::Group(_)
                            | StatementKind::Service(_)
                            | StatementKind::Junction(_)
                    )
                })
                .count(),
            edge_declarations: Vec::new(),
            acc_title: String::new(),
            acc_descr: String::new(),
            title: String::new(),
            groups: Vec::new(),
            nodes: Vec::new(),
            edges: Vec::new(),
            alignments: Vec::new(),
            config: Vec::new(),
        },
        diags: Vec::new(),
        registered: BTreeMap::new(),
    };
    resolver.read_config(source);
    resolver.metadata(&document.statements);
    resolver.groups(&document.statements);
    resolver.nodes(&document.statements);
    resolver.edges(&document.statements);
    resolver.alignments(&document.statements);
    (resolver.model, resolver.diags)
}

struct Resolver {
    model: Model,
    diags: Vec<Diagnostic>,
    registered: BTreeMap<String, Registration>,
}

fn parse_non_negative(text: &str) -> Option<i64> {
    let mut value = 0i64;
    for byte in text.bytes() {
        if !byte.is_ascii_digit() || value > MAX_PADDING {
            return None;
        }
        value = value * 10 + i64::from(byte - b'0');
    }
    (!text.is_empty() && value <= MAX_PADDING).then_some(value)
}

#[derive(Default)]
struct Sizes {
    padding: Option<i64>,
    icon_size: Option<i64>,
}

fn read_sizes(block: &ConfigValue, sizes: &mut Sizes) {
    let ConfigValue::Mapping(root) = block else {
        return;
    };
    let Some(entry) = root.iter().find(|entry| entry.key == "architecture") else {
        return;
    };
    let ConfigValue::Mapping(fields) = &entry.value else {
        return;
    };
    for field in fields {
        let ConfigValue::Integer(text) = &field.value else {
            continue;
        };
        let Some(value) = parse_non_negative(text) else {
            continue;
        };
        match field.key.as_str() {
            "padding" => sizes.padding = Some(value),
            "iconSize" if value > 0 => sizes.icon_size = Some(value),
            _ => {}
        }
    }
}

fn text(value: &Option<Value>) -> String {
    value.as_ref().map_or_else(String::new, |v| v.text.clone())
}

fn parent_id(parent: &Option<Value>) -> String {
    text(parent)
}

impl Resolver {
    fn read_config(&mut self, source: &str) {
        let preprocessed = preprocess(source);
        let frontmatter = preprocessed
            .frontmatter
            .as_ref()
            .and_then(|frontmatter| frontmatter.config.as_ref());
        let mut sizes = Sizes::default();
        for block in [frontmatter, preprocessed.init_config.as_ref()]
            .into_iter()
            .flatten()
        {
            read_sizes(block, &mut sizes);
        }
        for (key, value) in [("iconSize", sizes.icon_size), ("padding", sizes.padding)] {
            if let Some(value) = value {
                self.model.config.push(ConfigEntry {
                    key: key.into(),
                    value,
                });
            }
        }
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diags.push(diagnostic(code, message, span));
    }

    fn metadata(&mut self, statements: &[Statement]) {
        for statement in statements {
            let StatementKind::Metadata(items) = &statement.kind else {
                continue;
            };
            for item in &items.items {
                match item.field {
                    "title" => self.model.title = item.value.clone(),
                    "accTitle" => self.model.acc_title = item.value.clone(),
                    _ => self.model.acc_descr = item.value.clone(),
                }
            }
        }
    }

    fn free(&mut self, id: &Value) -> bool {
        let Some(first) = self.registered.get(&id.text).copied() else {
            return true;
        };
        let mut found = diagnostic(
            "architecture/duplicate-id",
            format!("id {} is already in use", id.text),
            id.span,
        );
        found.related.push(Related {
            span: first.id_span,
            message: "first declared here".into(),
        });
        self.diags.push(found);
        false
    }

    fn record(&mut self, id: &Value, group: bool) {
        self.registered.insert(
            id.text.clone(),
            Registration {
                group,
                id_span: id.span,
            },
        );
    }

    fn valid_parent(&mut self, id: &Value, parent: &Option<Value>) -> bool {
        let Some(parent) = parent else {
            return true;
        };
        let known = self.registered.get(&parent.text).copied();
        match known {
            _ if id.text == parent.text => self.issue(
                "architecture/self-parent",
                format!("element {} cannot contain itself", id.text),
                parent.span,
            ),
            None => self.issue(
                "architecture/parent-not-found",
                format!("parent {} does not exist", parent.text),
                parent.span,
            ),
            Some(found) if !found.group => self.issue(
                "architecture/parent-not-group",
                format!("parent {} is not a group", parent.text),
                parent.span,
            ),
            Some(_) => return true,
        }
        false
    }

    fn groups(&mut self, statements: &[Statement]) {
        for statement in statements {
            let StatementKind::Group(node) = &statement.kind else {
                continue;
            };
            if !self.free(&node.id) || !self.valid_parent(&node.id, &node.parent) {
                continue;
            }
            self.record(&node.id, true);
            self.model.groups.push(Group {
                id: node.id.text.clone(),
                icon: text(&node.icon),
                title: text(&node.title),
                parent: parent_id(&node.parent),
                span: statement.span,
                id_span: node.id.span,
            });
        }
    }

    fn nodes(&mut self, statements: &[Statement]) {
        for statement in statements {
            if let StatementKind::Service(service) = &statement.kind {
                self.service(statement.span, service);
            }
        }
        for statement in statements {
            if let StatementKind::Junction(junction) = &statement.kind {
                self.junction(statement.span, junction);
            }
        }
        self.model.nodes.sort_by_key(|node| node.span.start);
    }

    fn service(&mut self, span: Span, service: &Service) {
        let node = Node {
            icon: text(&service.icon),
            icon_text: text(&service.icon_text),
            title: text(&service.title),
            ..Node::blank()
        };
        self.add_node(span, &service.id, &service.parent, node);
    }

    fn junction(&mut self, span: Span, junction: &Junction) {
        let node = Node {
            junction: true,
            ..Node::blank()
        };
        self.add_node(span, &junction.id, &junction.parent, node);
    }

    fn add_node(&mut self, span: Span, id: &Value, parent: &Option<Value>, node: Node) {
        if !self.free(id) || !self.valid_parent(id, parent) {
            return;
        }
        self.record(id, false);
        self.model.nodes.push(Node {
            id: id.text.clone(),
            parent: parent_id(parent),
            span,
            id_span: id.span,
            ..node
        });
    }

    fn edges(&mut self, statements: &[Statement]) {
        for statement in statements {
            if let StatementKind::Edge(node) = &statement.kind {
                let index = self.model.edges.len();
                self.edge(statement.span, node);
                let declaration = if self.model.edges.len() == index {
                    EdgeDeclaration::Rejected(Box::new(Edge {
                        from: node.lhs_id.text.clone(),
                        to: node.rhs_id.text.clone(),
                        from_side: node.lhs_dir.text.clone(),
                        to_side: node.rhs_dir.text.clone(),
                        from_into: node.lhs_into.is_some(),
                        to_into: node.rhs_into.is_some(),
                        from_group: node.lhs_group.is_some(),
                        to_group: node.rhs_group.is_some(),
                        title: String::new(),
                        span: statement.span,
                    }))
                } else {
                    EdgeDeclaration::Resolved(index)
                };
                self.model.edge_declarations.push(declaration);
            }
        }
    }

    fn exists(&mut self, id: &Value) -> bool {
        let found = self.registered.contains_key(&id.text);
        if !found {
            self.issue(
                "architecture/endpoint-not-found",
                format!("edge endpoint {} does not exist", id.text),
                id.span,
            );
        }
        found
    }

    fn is_node(&mut self, id: &Value) -> bool {
        let group = self.registered.get(&id.text).is_some_and(|r| r.group);
        if group {
            self.issue(
                "architecture/endpoint-not-node",
                format!("edge endpoint {} is not a service or junction", id.text),
                id.span,
            );
        }
        !group
    }

    fn parent_of(&self, id: &str) -> &str {
        self.model
            .nodes
            .iter()
            .find(|node| node.id == id)
            .map_or("", |node| node.parent.as_str())
    }

    fn edge(&mut self, span: Span, node: &EdgeNode) {
        if !self.exists(&node.lhs_id)
            || !self.exists(&node.rhs_id)
            || !self.is_node(&node.lhs_id)
            || !self.is_node(&node.rhs_id)
        {
            return;
        }
        let left = self.parent_of(&node.lhs_id.text);
        if !left.is_empty() && left == self.parent_of(&node.rhs_id.text) {
            for (id, modifier) in [
                (&node.lhs_id, node.lhs_group),
                (&node.rhs_id, node.rhs_group),
            ] {
                if let Some(modifier) = modifier {
                    self.issue(
                        "architecture/group-boundary-not-crossed",
                        format!(
                            "endpoint {} has a group modifier but the edge stays in one group",
                            id.text
                        ),
                        modifier,
                    );
                    return;
                }
            }
        }
        self.model.edges.push(Edge {
            from: node.lhs_id.text.clone(),
            to: node.rhs_id.text.clone(),
            from_side: node.lhs_dir.text.clone(),
            to_side: node.rhs_dir.text.clone(),
            from_into: node.lhs_into.is_some(),
            to_into: node.rhs_into.is_some(),
            from_group: node.lhs_group.is_some(),
            to_group: node.rhs_group.is_some(),
            title: text(&node.title),
            span,
        });
    }

    fn alignments(&mut self, statements: &[Statement]) {
        for statement in statements {
            let StatementKind::Alignment(node) = &statement.kind else {
                continue;
            };
            if let Some(members) = self.members(node) {
                self.model.alignments.push(Alignment {
                    direction: node.direction.text.clone(),
                    members,
                    span: statement.span,
                });
            }
        }
    }

    fn members(&mut self, node: &AlignmentNode) -> Option<Vec<String>> {
        let mut seen = BTreeSet::new();
        let mut out = Vec::with_capacity(node.members.len());
        for member in &node.members {
            let known = self.registered.get(&member.text).copied();
            if known.is_none_or(|r| r.group) {
                self.issue(
                    "architecture/align-member-not-node",
                    format!(
                        "alignment member {} is not a service or junction",
                        member.text
                    ),
                    member.span,
                );
                return None;
            }
            if !seen.insert(member.text.clone()) {
                self.issue(
                    "architecture/align-duplicate-member",
                    format!("alignment lists {} more than once", member.text),
                    member.span,
                );
                return None;
            }
            out.push(member.text.clone());
        }
        Some(out)
    }
}

impl Node {
    fn blank() -> Self {
        Self {
            id: String::new(),
            junction: false,
            icon: String::new(),
            icon_text: String::new(),
            title: String::new(),
            parent: String::new(),
            span: Span { start: 0, end: 0 },
            id_span: Span { start: 0, end: 0 },
        }
    }
}

#[cfg(test)]
mod tests;
