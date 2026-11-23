use crate::syntax::agentflow::diagnostic;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::entities::decode_entities as decode;
use crate::{
    diag::{Diagnostic, Severity},
    source::Span,
    syntax::agentflow::ast::*,
};
use std::collections::{BTreeMap, BTreeSet};

mod metadata;
mod resolve;
#[cfg(test)]
use metadata::metadata_entries;
use metadata::{merge, value_text};

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub nodes: Vec<VertexModel>,
    pub edges: Vec<Edge>,
    pub groups: Vec<Flow>,
    pub declarations: Vec<Declaration>,
    pub class_defs: Vec<ClassDefinition>,
    pub links: Vec<Interaction>,
    pub direction: String,
    pub authored_direction: String,
    pub acc_title: String,
    pub acc_descr: String,
    pub default_edge_styles: Vec<String>,
    pub default_interpolation: String,
    pub padding: Option<i32>,
    global: BTreeSet<String>,
    reserved: BTreeSet<String>,
    diagnostics: Vec<Diagnostic>,
    anonymous: usize,
}
#[derive(Debug, Clone, Copy)]
pub enum Declaration {
    Node(usize),
    Group(usize),
}
#[derive(Debug, Clone, Default)]
pub struct Appearance {
    pub classes: Vec<String>,
    pub styles: Vec<String>,
    pub metadata: Vec<Entry>,
}
#[derive(Debug, Clone)]
pub struct VertexModel {
    pub id: String,
    pub label: String,
    pub label_kind: TextKind,
    pub shape: String,
    pub parent: String,
    pub span: Span,
    pub id_span: Span,
    pub metadata_span: Option<Span>,
    pub connector: bool,
    pub appearance: Appearance,
}
#[derive(Debug, Clone)]
pub struct Edge {
    pub id: String,
    pub from: String,
    pub to: String,
    pub from_span: Span,
    pub to_span: Span,
    pub span: Span,
    pub statement_span: Span,
    pub operator_span: Span,
    pub label: String,
    pub label_kind: TextKind,
    pub label_span: Option<Span>,
    pub marker: String,
    pub line: String,
    pub semantics: String,
    pub length: usize,
    pub interpolation: String,
    pub appearance: Appearance,
}
#[derive(Debug, Clone)]
pub struct Flow {
    pub id: String,
    pub title: String,
    pub parent: String,
    pub direction: String,
    pub direction_span: Span,
    pub span: Span,
    pub opening: Span,
    pub members: Vec<String>,
    pub appearance: Appearance,
}
#[derive(Debug, Clone)]
pub struct ClassDefinition {
    pub id: String,
    pub styles: Vec<String>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Interaction {
    pub id: String,
    pub url: Option<String>,
    pub callback: Option<String>,
    pub arguments: Option<String>,
    pub tooltip: Option<String>,
    pub target: Option<String>,
    pub span: Span,
}
#[derive(Clone, Copy)]
enum Scope<'a> {
    Root,
    Flow(&'a str),
    Global,
}

pub fn resolve(source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        direction: canonical_direction(document.config.direction.value).into(),
        authored_direction: document
            .config
            .authored
            .as_ref()
            .map_or("", |t| &*t.text)
            .trim()
            .into(),
        padding: configured_padding(source),
        ..Model::default()
    };
    reserve_ids(&document.document, &mut model.reserved);
    model.walk(&document.document, Scope::Root);
    model.finish_classes();
    model.collapse();
    let mut diagnostics = std::mem::take(&mut model.diagnostics);
    crate::diag::sort(&mut diagnostics);
    (model, diagnostics)
}
impl Model {
    fn walk(&mut self, document: &Document<'_>, scope: Scope<'_>) {
        for statement in document
            .lines
            .iter()
            .filter_map(|line| line.statement.as_ref())
        {
            self.statement(statement, scope);
        }
    }
    fn statement(&mut self, statement: &Statement<'_>, scope: Scope<'_>) {
        match &statement.kind {
            StatementKind::Vertex(value) => self.vertices(value, scope),
            StatementKind::Flow {
                name,
                title,
                metadata,
                opening,
                body,
                ..
            } => {
                self.flow(
                    (name.as_ref(), title.as_ref(), metadata),
                    (*opening, statement.span),
                    body,
                    scope,
                );
            }
            StatementKind::Global { body, .. } => self.walk(body, Scope::Global),
            StatementKind::Connector {
                name,
                title,
                metadata,
            } => self.connector(name, title.as_ref(), metadata, scope),
            StatementKind::Direction(value) => self.set_direction(*value, scope),
            StatementKind::Accessibility { title, value } => {
                if *title {
                    self.acc_title = value.text.trim().into();
                } else {
                    self.acc_descr = value.text.trim().into();
                }
            }
            _ => self.directive(statement),
        }
    }
    fn set_direction(&mut self, value: Direction, scope: Scope<'_>) {
        if let Scope::Flow(id) = scope {
            if let Some(flow) = self.groups.iter_mut().find(|flow| flow.id == id) {
                flow.direction = canonical_direction(value.value).into();
                flow.direction_span = value.span;
            }
        } else {
            self.direction = canonical_direction(value.value).into();
        }
    }
    fn ensure(&mut self, id: &str, span: Span) -> Option<usize> {
        if id.is_empty() || id == "connectors" || self.groups.iter().any(|g| g.id == id) {
            return None;
        }
        if let Some(index) = self.nodes.iter().position(|node| node.id == id) {
            return Some(index);
        }
        let index = self.nodes.len();
        self.nodes.push(VertexModel {
            id: id.into(),
            label: decode(id.trim()),
            label_kind: TextKind::Plain,
            shape: "roundedRect".into(),
            parent: String::new(),
            span,
            id_span: span,
            metadata_span: None,
            connector: false,
            appearance: Appearance::default(),
        });
        self.declarations.push(Declaration::Node(index));
        Some(index)
    }
    fn parent(&self, id: &str) -> &str {
        self.nodes
            .iter()
            .find(|n| n.id == id)
            .map(|n| n.parent.as_str())
            .or_else(|| {
                self.groups
                    .iter()
                    .find(|g| g.id == id)
                    .map(|g| g.parent.as_str())
            })
            .unwrap_or("")
    }
    fn join(&mut self, id: &str, span: Span, scope: Scope<'_>) {
        if matches!(scope, Scope::Global) {
            self.global.insert(id.into());
            self.release(id);
            return;
        }
        let Scope::Flow(parent) = scope else {
            return;
        };
        if self.global.contains(id) || !self.parent(id).is_empty() {
            return;
        }
        let mut ancestor = parent;
        while !ancestor.is_empty() {
            if ancestor == id {
                self.diagnostics.push(report("agentflow/containment-violation", format!("container {parent} cannot contain {id} because it closes a containment cycle"), span));
                return;
            }
            ancestor = self.parent(ancestor);
        }
        if let Some(node) = self.nodes.iter_mut().find(|n| n.id == id) {
            node.parent = parent.into();
        }
        if let Some(group) = self.groups.iter_mut().find(|g| g.id == id) {
            group.parent = parent.into();
        }
        if let Some(group) = self.groups.iter_mut().find(|g| g.id == parent)
            && !group.members.iter().any(|member| member == id)
        {
            group.members.push(id.into());
        }
    }
    fn release(&mut self, id: &str) {
        if let Some(node) = self.nodes.iter_mut().find(|n| n.id == id) {
            node.parent.clear();
        }
        if let Some(group) = self.groups.iter_mut().find(|g| g.id == id) {
            group.parent.clear();
        }
        for group in &mut self.groups {
            group.members.retain(|member| member != id);
        }
    }
    fn endpoint(&mut self, styled: &StyledVertex<'_>, scope: Scope<'_>) -> Option<(String, Span)> {
        let id = id_text(&styled.vertex.id);
        if id.is_empty() {
            return None;
        }
        let mut entries = Vec::new();
        if let Some((key, value)) = &styled.vertex.property {
            entries.push(Entry {
                key: key.text.to_string(),
                key_span: key.span,
                value: ConfigValue::String(value.text.to_string()),
            });
        }
        merge(&mut entries, self.metadata(&styled.metadata));
        if self.reference(&id, &entries, styled) {
            if let Some(class) = &styled.class
                && let Some(appearance) = self.appearance(&id)
            {
                appearance.classes.push(id_text(class));
            }
            if !self.groups.iter().any(|group| group.id == id) {
                return None;
            }
            self.join(&id, styled.vertex.id.span, scope);
            return Some((id, styled.vertex.id.span));
        }
        let index = self.ensure(&id, styled.vertex.id.span)?;
        let shape = styled
            .vertex
            .shape
            .map(|shape| self.normalize(shape, styled.vertex.span));
        if let Some(node) = self.nodes.get_mut(index) {
            node.span = styled.span;
            if let Some(label) = &styled.vertex.label {
                node.label = text(label);
                node.label_kind = label.kind;
            }
            if let Some(shape) = shape {
                node.shape = shape;
            }
            if let Some(class) = &styled.class {
                node.appearance.classes.push(id_text(class));
            }
            node.metadata_span = styled.metadata.last().map(|data| data.span);
            merge(&mut node.appearance.metadata, entries.clone());
        }
        self.node_metadata(index, &entries, &styled.metadata);
        self.join(&id, styled.vertex.id.span, scope);
        Some((id, styled.vertex.id.span))
    }
    fn vertices(&mut self, value: &VertexStatement<'_>, scope: Scope<'_>) {
        let mut previous = Vec::new();
        for (index, set) in value.nodes.iter().enumerate() {
            let next = set
                .vertices
                .iter()
                .filter_map(|v| self.endpoint(v, scope))
                .collect::<Vec<_>>();
            if let Some(link) = index.checked_sub(1).and_then(|i| value.links.get(i)) {
                self.product(&previous, &next, link, value.span);
            }
            previous = next;
        }
    }
    fn product(
        &mut self,
        from: &[(String, Span)],
        to: &[(String, Span)],
        link: &Link<'_>,
        statement_span: Span,
    ) {
        for (source_index, source) in from.iter().enumerate() {
            for (target_index, target) in to.iter().enumerate() {
                let authored = if source_index + 1 == from.len() && target_index == 0 {
                    link.statement
                        .id
                        .as_ref()
                        .map_or("", |id| id.text.trim_end_matches('@'))
                } else {
                    ""
                };
                self.edge(source, target, link, authored, statement_span);
            }
        }
    }
    fn edge(
        &mut self,
        from: &(String, Span),
        to: &(String, Span),
        link: &Link<'_>,
        authored: &str,
        statement_span: Span,
    ) {
        let id = self.edge_id(authored);
        let operator = link.statement.operator.text.trim();
        let dotted = operator.contains('.');
        let marker = if operator.ends_with('x') {
            "cross"
        } else if operator.ends_with('>') {
            "point"
        } else {
            "none"
        };
        let length = if dotted {
            operator.matches('.').count()
        } else {
            operator.matches('-').count().saturating_sub(1)
        }
        .clamp(1, 10);
        self.edges.push(Edge {
            id,
            from: from.0.clone(),
            to: to.0.clone(),
            from_span: from.1,
            to_span: to.1,
            span: link.span,
            statement_span,
            operator_span: link.statement.operator.span,
            label: link.label().map_or_else(String::new, text),
            label_kind: link.label().map_or(TextKind::Plain, |t| t.kind),
            label_span: link.label().map(|t| t.span),
            marker: marker.into(),
            line: if dotted { "dotted" } else { "normal" }.into(),
            semantics: if dotted {
                "reference"
            } else if marker == "cross" {
                "failure"
            } else {
                "sequence"
            }
            .into(),
            length,
            interpolation: self.default_interpolation.clone(),
            appearance: Appearance {
                styles: self.default_edge_styles.clone(),
                ..Appearance::default()
            },
        });
    }
    fn edge_id(&self, authored: &str) -> String {
        if !authored.is_empty() && !self.edges.iter().any(|edge| edge.id == authored) {
            return authored.into();
        }
        let mut ordinal = self.edges.len();
        loop {
            let id = format!("e{ordinal}");
            if !self.edges.iter().any(|edge| edge.id == id) {
                return id;
            }
            ordinal += 1;
        }
    }
    fn flow(
        &mut self,
        header: (Option<&TextNoTags<'_>>, Option<&Text<'_>>, &[ShapeData<'_>]),
        spans: (Span, Span),
        body: &Document<'_>,
        scope: Scope<'_>,
    ) {
        let (name, title, data) = header;
        let id = name
            .map(no_tags)
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| self.flow_id());
        let title = title
            .map(text)
            .or_else(|| name.map(no_tags))
            .unwrap_or_default();
        let entries = self.metadata(data);
        if !self.groups.iter().any(|group| group.id == id) {
            self.nodes.retain(|node| node.id != id);
            self.reindex_nodes();
            self.declarations
                .push(Declaration::Group(self.groups.len()));
            self.groups.push(Flow {
                id: id.clone(),
                title: String::new(),
                parent: String::new(),
                direction: String::new(),
                direction_span: spans.0,
                span: spans.1,
                opening: spans.0,
                members: Vec::new(),
                appearance: Appearance::default(),
            });
        }
        if let Some(group) = self.groups.iter_mut().find(|g| g.id == id) {
            if !title.is_empty() {
                group.title = title;
            }
            merge(&mut group.appearance.metadata, entries);
        }
        self.join(&id, spans.0, scope);
        self.walk(body, Scope::Flow(&id));
    }
    fn flow_id(&mut self) -> String {
        loop {
            let id = format!("flow{}", self.anonymous);
            self.anonymous += 1;
            if self.reserved.insert(id.clone()) {
                return id;
            }
        }
    }
    fn connector(
        &mut self,
        name: &TextNoTags<'_>,
        title: Option<&Text<'_>>,
        data: &[ShapeData<'_>],
        scope: Scope<'_>,
    ) {
        let id = no_tags(name);
        let entries = self.metadata(data);
        let Some(index) = self.ensure(&id, name.span) else {
            return;
        };
        if let Some(node) = self.nodes.get_mut(index) {
            node.connector = true;
            node.shape = "connector".into();
            if let Some(label) = title.map(text).filter(|s| !s.is_empty()) {
                node.label = label;
            }
            merge(&mut node.appearance.metadata, entries.clone());
        }
        self.node_metadata(index, &entries, data);
        self.join(&id, name.span, scope);
    }
    fn collapsed_owner(&self, id: &str) -> String {
        let mut owner = String::new();
        let mut ancestor = self.parent(id);
        while !ancestor.is_empty() {
            if self.groups.iter().any(|g| g.id == ancestor && collapsed(g)) {
                owner = ancestor.into();
            }
            ancestor = self.parent(ancestor);
        }
        owner
    }
    fn collapse(&mut self) {
        let redirects = self
            .nodes
            .iter()
            .map(|n| &n.id)
            .chain(self.groups.iter().map(|g| &g.id))
            .map(|id| (id.clone(), self.collapsed_owner(id)))
            .collect::<BTreeMap<_, _>>();
        for edge in &mut self.edges {
            let authored_loop = edge.from == edge.to;
            let from = redirects.get(&edge.from).filter(|s| !s.is_empty());
            let to = redirects.get(&edge.to).filter(|s| !s.is_empty());
            if let Some(id) = from {
                edge.from = id.clone();
            }
            if let Some(id) = to {
                edge.to = id.clone();
            }
            if !authored_loop && edge.from == edge.to && (from.is_some() || to.is_some()) {
                edge.line = "invisible".into();
            }
        }
        self.edges.retain(|e| e.line != "invisible");
        self.nodes
            .retain(|n| redirects.get(&n.id).is_none_or(String::is_empty));
        self.reindex_nodes();
    }
    fn reindex_nodes(&mut self) {
        let mut declarations = (0..self.nodes.len())
            .map(Declaration::Node)
            .chain((0..self.groups.len()).map(Declaration::Group))
            .collect::<Vec<_>>();
        declarations.sort_by_key(|declaration| match declaration {
            Declaration::Node(index) => self
                .nodes
                .get(*index)
                .map_or(usize::MAX, |node| node.id_span.start),
            Declaration::Group(index) => self
                .groups
                .get(*index)
                .map_or(usize::MAX, |group| group.opening.start),
        });
        self.declarations = declarations;
    }
}
fn reserve_ids(document: &Document<'_>, reserved: &mut BTreeSet<String>) {
    for statement in document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref())
    {
        match &statement.kind {
            StatementKind::Vertex(value) => {
                for vertex in value.nodes.iter().flat_map(|node| &node.vertices) {
                    reserved.insert(id_text(&vertex.vertex.id));
                }
            }
            StatementKind::Flow { name, body, .. } => {
                if let Some(name) = name {
                    reserved.insert(no_tags(name));
                }
                reserve_ids(body, reserved);
            }
            StatementKind::Global { body, .. } => reserve_ids(body, reserved),
            StatementKind::Connector { name, .. } => {
                reserved.insert(no_tags(name));
            }
            _ => {}
        }
    }
}
fn configured_padding(source: &str) -> Option<i32> {
    let preprocessed = crate::syntax::preprocess::preprocess(source);
    let frontmatter = preprocessed
        .frontmatter
        .as_ref()
        .and_then(|frontmatter| frontmatter.config.as_ref());
    [frontmatter, preprocessed.init_config.as_ref()]
        .into_iter()
        .flatten()
        .filter_map(|config| {
            let ConfigValue::Mapping(root) = config else {
                return None;
            };
            let flowchart = root.iter().find(|entry| entry.key == "flowchart")?;
            let ConfigValue::Mapping(entries) = &flowchart.value else {
                return None;
            };
            let padding = entries.iter().find(|entry| entry.key == "padding")?;
            let ConfigValue::Integer(value) = &padding.value else {
                return None;
            };
            value.parse::<i32>().ok()
        })
        .next_back()
}
fn canonical_direction(value: &str) -> &str {
    match value.trim() {
        "LR" | ">" => "LR",
        "RL" | "<" => "RL",
        "BT" | "^" => "BT",
        _ => "TB",
    }
}
fn tokens<'a>(parts: impl Iterator<Item = &'a str>) -> String {
    parts.collect::<String>().trim().into()
}
fn id_text(id: &IdString<'_>) -> String {
    tokens(id.tokens.iter().map(|t| &*t.text))
}
fn text(value: &Text<'_>) -> String {
    decode(tokens(value.pieces.iter().map(|t| &*t.text)).trim())
}
fn no_tags(value: &TextNoTags<'_>) -> String {
    decode(tokens(value.pieces.iter().map(|t| &*t.text)).trim())
}
fn styles(value: &StylesOpt<'_>) -> Vec<String> {
    value
        .styles
        .iter()
        .map(|s| tokens(s.components.iter().map(|c| &*c.token.text)))
        .collect()
}
fn collapsed(flow: &Flow) -> bool {
    flow.appearance
        .metadata
        .iter()
        .any(|e| e.key == "view" && value_text(&e.value) == "collapsed")
}
fn report(code: &'static str, message: String, span: Span) -> Diagnostic {
    let mut diagnostic = diagnostic(code, message, span);
    diagnostic.severity = match code {
        "agentflow/shape-unsupported"
        | "agentflow/containment-violation"
        | "interaction/unsafe-url" => Severity::Warning,
        "interaction/callback-ignored" => Severity::Info,
        _ => Severity::Error,
    };
    diagnostic
}
#[cfg(test)]
mod tests;
