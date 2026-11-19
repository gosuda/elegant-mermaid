//! Semantic resolution of the `wardley` kind (`spec/grammar/wardley.md`): components,
//! links, pipelines, evolution stages, annotations, and the honoured config keys.
//! Coordinates are integers in thousandths of a percent of the map.

use crate::syntax::entities::decode_entities as decode;
use std::collections::BTreeMap;

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::preprocess::preprocess;
use crate::syntax::wardley::ast::{
    Annotation as AnnotationNode, Component, Label, Pipeline as PipelineNode, Value, Wardley,
};
use crate::syntax::wardley::diagnostic;
use crate::syntax::wardley::lexer::trim_js;

const CONFIG_KEY: &str = "wardley-beta";
const MAX_CANVAS_PX: i64 = 65536;
const MAX_PADDING_PX: i64 = 4096;
const OFFSET_CAP: i64 = 1 << 31;
const NUMBER_CAP: i64 = 1 << 62;
const RANGE_MESSAGE: &str = " must be between 0-1 (decimal) or 0-100 (percentage). Received: ";
const PERCENT_PLACES: usize = 5;
const THOUSANDTH_PLACES: usize = 3;
const SATURATION: i64 = 1 << 40;
const DIGITS_LIMIT: usize = 12;

const INTEGER_KEYS: &[(&str, i64, i64)] = &[
    ("width", 1, MAX_CANVAS_PX),
    ("height", 1, MAX_CANVAS_PX),
    ("padding", 0, MAX_PADDING_PX),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Strategy {
    #[default]
    None,
    Build,
    Buy,
    Outsource,
    Market,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Flow {
    #[default]
    None,
    Forward,
    Backward,
    Bidirectional,
}

#[derive(Debug, Clone)]
pub struct Node {
    pub id: String,
    pub name: String,
    pub label: String,
    pub x: i64,
    pub y: i64,
    pub anchor: bool,
    pub has_offset: bool,
    pub offset_x: i64,
    pub offset_y: i64,
    pub inertia: bool,
    pub strategy: Strategy,
    pub pipeline_parent: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Link {
    pub source: String,
    pub target: String,
    pub dashed: bool,
    pub label: String,
    pub flow: Flow,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Trend {
    pub node: String,
    pub target_x: i64,
    pub target_y: i64,
}

#[derive(Debug, Clone)]
pub struct Pipeline {
    pub node: String,
    pub components: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Annotation {
    pub number: i64,
    pub x: i64,
    pub y: i64,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct Note {
    pub text: String,
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone)]
pub struct Force {
    pub name: String,
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone, Copy)]
pub struct Point {
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone)]
pub struct ConfigEntry {
    pub key: String,
    pub value: i64,
}

#[derive(Debug, Clone)]
pub struct Declaration {
    pub node: usize,
    pub span: Span,
    pub scale: u8,
}

#[derive(Debug, Clone)]
pub struct Reference {
    pub node: Option<usize>,
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub header: Span,
    pub declarations: Vec<Declaration>,
    pub references: Vec<Reference>,
    pub pipeline_uses: Vec<Reference>,
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub stages: Vec<String>,
    pub boundaries: Vec<i64>,
    pub nodes: Vec<Node>,
    pub links: Vec<Link>,
    pub trends: Vec<Trend>,
    pub pipelines: Vec<Pipeline>,
    pub annotations: Vec<Annotation>,
    pub notes: Vec<Note>,
    pub accelerators: Vec<Force>,
    pub deaccelerators: Vec<Force>,
    pub box_point: Option<Point>,
    pub config: Vec<ConfigEntry>,
}

impl Model {
    pub fn reference_name<'a>(&'a self, reference: &'a Reference) -> &'a str {
        match reference.node {
            Some(index) => &self.nodes[index].id,
            None => &reference.name,
        }
    }

    pub fn node_index(&self, id: &str) -> Option<usize> {
        self.nodes.iter().position(|node| node.id == id)
    }

    pub fn integer(&self, key: &str) -> Option<i64> {
        self.config
            .iter()
            .find(|entry| entry.key == key)
            .map(|entry| entry.value)
    }
}

struct Decimal {
    whole: String,
    fraction: String,
}

impl Decimal {
    fn parse(text: &str) -> Decimal {
        let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
        Decimal {
            whole: whole.trim_start_matches('0').to_owned(),
            fraction: fraction.trim_end_matches('0').to_owned(),
        }
    }

    fn at_most_one(&self) -> bool {
        self.whole.is_empty() || (self.whole == "1" && self.fraction.is_empty())
    }

    fn exceeds_hundred(&self) -> bool {
        if self.whole.len() != 3 {
            return self.whole.len() > 3;
        }
        if self.whole != "100" {
            return self.whole.as_str() > "100";
        }
        !self.fraction.is_empty()
    }

    fn fraction_digit(&self, at: usize) -> u8 {
        self.fraction.as_bytes().get(at).copied().unwrap_or(b'0')
    }

    fn scaled(&self, places: usize) -> i64 {
        if self.whole.len() + places > DIGITS_LIMIT {
            return SATURATION;
        }
        let mut value = self
            .whole
            .bytes()
            .fold(0_i64, |acc, b| acc * 10 + i64::from(b - b'0'));
        for i in 0..places {
            value = value * 10 + i64::from(self.fraction_digit(i) - b'0');
        }
        if self.fraction_digit(places) >= b'5' {
            value += 1;
        }
        value
    }

    fn display(&self) -> String {
        let whole = if self.whole.is_empty() {
            "0"
        } else {
            &self.whole
        };
        if self.fraction.is_empty() {
            return whole.to_owned();
        }
        format!("{whole}.{}", self.fraction)
    }

    fn to_percent(&self) -> Option<i64> {
        if self.at_most_one() {
            return Some(self.scaled(PERCENT_PLACES));
        }
        if self.exceeds_hundred() {
            return None;
        }
        Some(self.scaled(THOUSANDTH_PLACES))
    }
}

fn integer(text: &str, limit: i64) -> i64 {
    text.bytes().fold(0_i64, |value, b| {
        (value * 10 + i64::from(b.wrapping_sub(b'0'))).min(limit)
    })
}

struct Resolver {
    model: Model,
    diagnostics: Vec<Diagnostic>,
    nodes: BTreeMap<String, usize>,
    pipelines: BTreeMap<String, usize>,
    trends: BTreeMap<String, usize>,
}

pub fn resolve(source: &str, document: &Wardley) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            header: document.header.as_ref().map_or(document.span, |h| h.span),
            declarations: Vec::new(),
            references: Vec::new(),
            pipeline_uses: Vec::new(),
            acc_title: String::new(),
            acc_descr: String::new(),
            title: String::new(),
            stages: Vec::new(),
            boundaries: Vec::new(),
            nodes: Vec::new(),
            links: Vec::new(),
            trends: Vec::new(),
            pipelines: Vec::new(),
            annotations: Vec::new(),
            notes: Vec::new(),
            accelerators: Vec::new(),
            deaccelerators: Vec::new(),
            box_point: None,
            config: Vec::new(),
        },
        diagnostics: Vec::new(),
        nodes: BTreeMap::new(),
        pipelines: BTreeMap::new(),
        trends: BTreeMap::new(),
    };
    resolver.read_config(source);
    resolver.metadata(document);
    resolver.size(document);
    resolver.evolution(document);
    resolver.declare_nodes(document);
    resolver.retain_evidence(document);
    resolver.declare_relations(document);
    resolver.declare_annotations(document);
    resolver.model.config.sort_by(|a, b| a.key.cmp(&b.key));
    (resolver.model, resolver.diagnostics)
}

fn coordinate_scale(text: &str) -> u8 {
    let text = text.trim_start_matches('+');
    if text.starts_with('-') {
        return 0;
    }
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    let whole = whole.trim_start_matches('0');
    let fraction = fraction.trim_matches('0');
    if whole.is_empty() && fraction.is_empty() {
        0
    } else if whole.is_empty() || (whole == "1" && fraction.is_empty()) {
        1
    } else {
        2
    }
}

fn child<'a>(entries: &'a [Entry], key: &str) -> Option<&'a [Entry]> {
    entries
        .iter()
        .find(|entry| entry.key == key)
        .and_then(|entry| match &entry.value {
            ConfigValue::Mapping(inner) => Some(inner.as_slice()),
            _ => None,
        })
}

impl Resolver {
    fn retain_evidence(&mut self, document: &Wardley) {
        let reference = |value: &Value| {
            let node = self.nodes.get(&value.text).copied();
            Reference {
                name: if node.is_none() {
                    value.text.clone()
                } else {
                    String::new()
                },
                node,
                span: value.span,
            }
        };
        self.model.header = document.header.as_ref().map_or(document.span, |h| h.span);
        for (name, visibility, evolution) in document
            .anchors
            .iter()
            .map(|a| (&a.name, &a.visibility, &a.evolution))
            .chain(
                document
                    .components
                    .iter()
                    .map(|c| (&c.name, &c.visibility, &c.evolution)),
            )
        {
            self.model.declarations.push(Declaration {
                node: self.nodes[&name.text],
                span: name.span,
                scale: coordinate_scale(&visibility.text) | coordinate_scale(&evolution.text),
            });
        }
        self.model.declarations.sort_by_key(|d| d.span.start);
        for value in document
            .links
            .iter()
            .flat_map(|l| [&l.from, &l.to])
            .chain(document.evolves.iter().map(|e| &e.component))
        {
            self.model.references.push(reference(value));
        }
        for pipeline in &document.pipelines {
            self.model.pipeline_uses.push(reference(&pipeline.parent));
            self.model
                .pipeline_uses
                .extend(pipeline.components.iter().map(|c| reference(&c.name)));
        }
    }

    fn read_config(&mut self, source: &str) {
        let preprocessed = preprocess(source);
        let mut blocks = Vec::new();
        if let Some(front) = preprocessed.frontmatter {
            self.read_front_title(&front.value);
            blocks.extend(front.config);
        }
        blocks.extend(preprocessed.init_config);
        for block in &blocks {
            self.read_map(block);
        }
    }

    fn read_front_title(&mut self, root: &ConfigValue) {
        let ConfigValue::Mapping(entries) = root else {
            return;
        };
        for entry in entries.iter().filter(|entry| entry.key == "title") {
            if let ConfigValue::String(value) = &entry.value {
                self.model.title = trim_js(&decode(value)).to_owned();
            }
        }
    }

    fn read_map(&mut self, block: &ConfigValue) {
        let ConfigValue::Mapping(entries) = block else {
            return;
        };
        for field in child(entries, CONFIG_KEY).unwrap_or_default() {
            let ConfigValue::Integer(text) = &field.value else {
                continue;
            };
            if text.starts_with('-') {
                continue;
            }
            self.set_bounded(
                &field.key,
                integer(text.trim_start_matches('+'), NUMBER_CAP),
            );
        }
    }

    fn set_bounded(&mut self, key: &str, n: i64) {
        let Some((_, low, high)) = INTEGER_KEYS.iter().find(|(name, _, _)| *name == key) else {
            return;
        };
        if n >= *low && n <= *high {
            self.upsert(key, n);
        }
    }

    fn upsert(&mut self, key: &str, value: i64) {
        match self.model.config.iter_mut().find(|e| e.key == key) {
            Some(entry) => entry.value = value,
            None => self.model.config.push(ConfigEntry {
                key: key.to_owned(),
                value,
            }),
        }
    }

    fn metadata(&mut self, document: &Wardley) {
        let mut last: BTreeMap<&str, &str> = BTreeMap::new();
        for item in &document.metadata {
            last.insert(item.field, item.value.as_str());
        }
        if let Some(title) = last.get("title").filter(|v| !v.is_empty()) {
            self.model.title = decode(title);
        }
        self.model.acc_title = last.get("accTitle").copied().unwrap_or("").to_owned();
        self.model.acc_descr = last.get("accDescr").copied().unwrap_or("").to_owned();
    }

    fn size(&mut self, document: &Wardley) {
        let Some(size) = &document.size else {
            return;
        };
        self.set_bounded("width", integer(&size.width.text, NUMBER_CAP));
        self.set_bounded("height", integer(&size.height.text, NUMBER_CAP));
    }

    fn evolution(&mut self, document: &Wardley) {
        let Some(evolution) = &document.evolution else {
            return;
        };
        for stage in &evolution.stages {
            let mut name = trim_js(&stage.name.text).to_owned();
            if let Some(second) = &stage.second_name {
                name.push_str(" / ");
                name.push_str(trim_js(&second.text));
            }
            self.model.stages.push(decode(&name));
            if let Some(boundary) = &stage.boundary {
                let scaled = Decimal::parse(&boundary.text).scaled(THOUSANDTH_PLACES);
                self.model.boundaries.push(scaled);
            }
        }
    }

    fn percent(&mut self, value: &Value, context: &str) -> i64 {
        let decimal = Decimal::parse(&value.text);
        decimal.to_percent().unwrap_or_else(|| {
            let message = format!("{context}{RANGE_MESSAGE}{}", decimal.display());
            self.diagnostics.push(diagnostic(
                "wardley/coordinate-out-of-range",
                message,
                value.span,
            ));
            0
        })
    }

    fn coordinates(&mut self, visibility: &Value, evolution: &Value, context: &str) -> (i64, i64) {
        let x = self.percent(evolution, &format!("{context} evolution"));
        let y = self.percent(visibility, &format!("{context} visibility"));
        (x, y)
    }

    fn add_node(&mut self, mut node: Node) {
        let Some(&at) = self.nodes.get(&node.id) else {
            self.nodes.insert(node.id.clone(), self.model.nodes.len());
            self.model.nodes.push(node);
            return;
        };
        let old = &self.model.nodes[at];
        node.pipeline_parent = old.pipeline_parent;
        if !node.has_offset {
            node.has_offset = old.has_offset;
            node.offset_x = old.offset_x;
            node.offset_y = old.offset_y;
        }
        self.model.nodes[at] = node;
    }

    fn declare_nodes(&mut self, document: &Wardley) {
        for anchor in &document.anchors {
            let context = format!("Anchor \"{}\"", anchor.name.text);
            let (x, y) = self.coordinates(&anchor.visibility, &anchor.evolution, &context);
            let mut node = base_node(&anchor.name, x, y);
            node.anchor = true;
            self.add_node(node);
        }
        for component in &document.components {
            self.component(component);
        }
        for note in &document.notes {
            let context = format!("Note \"{}\"", note.text.text);
            let (x, y) = self.coordinates(&note.visibility, &note.evolution, &context);
            self.model.notes.push(Note {
                text: decode(&note.text.text),
                x,
                y,
            });
        }
        for pipeline in &document.pipelines {
            self.pipeline_block(pipeline);
        }
    }

    fn component(&mut self, component: &Component) {
        let context = format!("Component \"{}\"", component.name.text);
        let (x, y) = self.coordinates(&component.visibility, &component.evolution, &context);
        let mut node = base_node(&component.name, x, y);
        node.inertia = component.inertia;
        apply_label(&mut node, component.label.as_ref());
        if let Some(decorator) = &component.decorator {
            node.strategy = strategy_of(&decorator.strategy.text);
        }
        self.add_node(node);
    }

    fn pipeline_block(&mut self, pipeline: &PipelineNode) {
        let parent_text = &pipeline.parent.text;
        let Some(&parent) = self.nodes.get(parent_text) else {
            let message = format!(
                "Pipeline \"{parent_text}\" must reference an existing component with coordinates."
            );
            self.diagnostics.push(diagnostic(
                "wardley/pipeline-parent-unknown",
                message,
                pipeline.parent.span,
            ));
            return;
        };
        let y = self.model.nodes[parent].y;
        self.model.nodes[parent].pipeline_parent = true;
        let at = self.start_pipeline(parent_text);
        for component in &pipeline.components {
            let id = format!("{parent_text}_{}", component.name.text);
            let mut node = base_node(&component.name, 0, y);
            node.id = id.clone();
            let context = format!("Pipeline component \"{}\" evolution", component.name.text);
            node.x = self.percent(&component.evolution, &context);
            apply_label(&mut node, component.label.as_ref());
            self.add_node(node);
            self.model.pipelines[at].components.push(id);
        }
    }

    fn start_pipeline(&mut self, node: &str) -> usize {
        let at = match self.pipelines.get(node) {
            Some(&at) => at,
            None => {
                let at = self.model.pipelines.len();
                self.pipelines.insert(node.to_owned(), at);
                self.model.pipelines.push(Pipeline {
                    node: node.to_owned(),
                    components: Vec::new(),
                });
                at
            }
        };
        self.model.pipelines[at].components.clear();
        at
    }

    fn resolve_name(&self, name: &str) -> String {
        if self.nodes.contains_key(name) {
            return name.to_owned();
        }
        self.model
            .nodes
            .iter()
            .find(|node| node.name == name)
            .map_or_else(|| name.to_owned(), |node| node.id.clone())
    }

    fn declare_relations(&mut self, document: &Wardley) {
        for link in &document.links {
            self.link(link);
        }
        for evolve in &document.evolves {
            self.evolve(evolve);
        }
    }

    fn link(&mut self, link: &crate::syntax::wardley::ast::Link) {
        let (arrow_flow, flow_label) = arrow_flow(link.arrow.as_ref());
        let flow = [
            port_flow(link.from_port.as_ref()),
            port_flow(link.to_port.as_ref()),
            arrow_flow,
        ]
        .into_iter()
        .find(|flow| *flow != Flow::None)
        .unwrap_or(Flow::None);
        let label = match (flow_label, &link.link_label) {
            (Some(text), _) => decode(&text),
            (None, Some(label)) => decode(&label.text),
            (None, None) => String::new(),
        };
        let dashed = link
            .arrow
            .as_ref()
            .is_some_and(|arrow| arrow.text.contains("-.->") || arrow.text.contains(".-."));
        self.model.links.push(Link {
            source: self.resolve_name(&link.from.text),
            target: self.resolve_name(&link.to.text),
            dashed,
            label,
            flow,
            span: link.span,
        });
    }

    fn evolve(&mut self, evolve: &crate::syntax::wardley::ast::Evolve) {
        let Some(&at) = self.nodes.get(&evolve.component.text) else {
            return;
        };
        let context = format!("Evolve target for \"{}\"", evolve.component.text);
        let trend = Trend {
            node: evolve.component.text.clone(),
            target_x: self.percent(&evolve.target, &context),
            target_y: self.model.nodes[at].y,
        };
        if let Some(&replaced) = self.trends.get(&trend.node) {
            self.model.trends[replaced] = trend;
            return;
        }
        self.trends
            .insert(trend.node.clone(), self.model.trends.len());
        self.model.trends.push(trend);
    }

    fn declare_annotations(&mut self, document: &Wardley) {
        if let Some(first) = document.annotations.first() {
            let (x, y) = self.coordinates(&first.x, &first.y, "Annotations box");
            self.model.box_point = Some(Point { x, y });
        }
        for annotation in &document.annotation {
            self.annotation(annotation);
        }
        for force in &document.accelerators {
            let value = self.force(force, "Accelerator");
            self.model.accelerators.push(value);
        }
        for force in &document.deaccelerators {
            let value = self.force(force, "Deaccelerator");
            self.model.deaccelerators.push(value);
        }
    }

    fn annotation(&mut self, annotation: &AnnotationNode) {
        let number = integer(&annotation.number.text, NUMBER_CAP);
        let context = format!("Annotation {}", annotation.number.text);
        let (x, y) = self.coordinates(&annotation.x, &annotation.y, &context);
        self.model.annotations.push(Annotation {
            number,
            x,
            y,
            text: decode(&annotation.text.text),
        });
    }

    fn force(&mut self, force: &crate::syntax::wardley::ast::Accelerator, kind: &str) -> Force {
        let context = format!("{kind} \"{}\"", force.name.text);
        let (x, y) = self.coordinates(&force.x, &force.y, &context);
        Force {
            name: decode(&force.name.text),
            x,
            y,
        }
    }
}

fn base_node(name: &Value, x: i64, y: i64) -> Node {
    Node {
        id: name.text.clone(),
        name: name.text.clone(),
        label: decode(&name.text),
        x,
        y,
        anchor: false,
        has_offset: false,
        offset_x: 0,
        offset_y: 0,
        inertia: false,
        strategy: Strategy::None,
        pipeline_parent: false,
        span: name.span,
    }
}

fn strategy_of(text: &str) -> Strategy {
    match text {
        "build" => Strategy::Build,
        "buy" => Strategy::Buy,
        "outsource" => Strategy::Outsource,
        "market" => Strategy::Market,
        _ => Strategy::None,
    }
}

fn apply_label(node: &mut Node, label: Option<&Label>) {
    let Some(label) = label else {
        return;
    };
    node.has_offset = true;
    node.offset_x = signed(label.neg_x, &label.offset_x.text);
    node.offset_y = signed(label.neg_y, &label.offset_y.text);
}

fn signed(negative: bool, digits: &str) -> i64 {
    let n = integer(digits, OFFSET_CAP);
    if negative { -n } else { n }
}

fn port_flow(port: Option<&Value>) -> Flow {
    port.map_or(Flow::None, |port| flow_of(&port.text))
}

fn flow_of(text: &str) -> Flow {
    if text.contains("<>") {
        Flow::Bidirectional
    } else if text.contains('<') {
        Flow::Backward
    } else if text.contains('>') {
        Flow::Forward
    } else {
        Flow::None
    }
}

fn arrow_flow(arrow: Option<&Value>) -> (Flow, Option<String>) {
    let Some(arrow) = arrow.filter(|arrow| arrow.text.starts_with('+')) else {
        return (Flow::None, None);
    };
    let label = arrow
        .text
        .strip_prefix("+'")
        .and_then(|rest| rest.find('\'').map(|end| rest[..end].to_owned()));
    (flow_of(&arrow.text), label)
}

#[cfg(test)]
mod tests;
