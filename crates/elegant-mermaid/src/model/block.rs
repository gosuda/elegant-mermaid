//! Resolved model of the `block` kind (`spec/grammar/block.md`, semantic resolution).
//!
//! The resolver keeps blocks in an arena so that the id database, which reaches blocks
//! that sit in the tree and blocks that a class statement created off the tree, mutates
//! one value per block. [`resolve`] folds the arena into the nested tree at the end.

use crate::syntax::entities::decode_entities;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::block::ast::{
    BlockStatement, ClassDefStatement, CssClassStatement, Document, Link, Node, NodeStatement,
    SpaceStatement, Start, StatementKind, StyleStatement,
};
use crate::syntax::block::diagnostic;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::preprocess::preprocess;

pub const AUTO_COLUMNS: i32 = -1;

const MAX_SPACE_SLOTS: i32 = 1 << 16;
const MAX_PADDING: i64 = 1024;
const C_STYLE_TARGET: &str = "block/style-target-unknown";
const C_WIDTH_EXCEEDS: &str = "block/width-exceeds-columns";
const NO_SPAN: Span = Span { start: 0, end: 0 };

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub id: String,
    pub kind: String,
    pub label: String,
    pub span: i32,
    pub size_span: Span,
    pub id_span: Span,
    pub columns: i32,
    pub directions: Vec<String>,
    pub children: Vec<Block>,
    pub classes: Vec<String>,
    pub styles: Vec<String>,
}

impl Block {
    fn named(id: String, kind: &str, columns: i32) -> Self {
        Self {
            id,
            kind: kind.into(),
            label: String::new(),
            span: 1,
            size_span: NO_SPAN,
            id_span: NO_SPAN,
            columns,
            directions: Vec::new(),
            children: Vec::new(),
            classes: Vec::new(),
            styles: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edge {
    pub start: String,
    pub end: String,
    pub label: String,
    pub span: Span,
    pub statement_span: Span,
    pub thickness: String,
    pub pattern: String,
    pub arrow_start: String,
    pub arrow_end: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassDef {
    pub id: String,
    pub styles: Vec<String>,
    pub text_styles: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfigEntry {
    pub key: String,
    pub value: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Model {
    pub root: Block,
    pub edges: Vec<Edge>,
    pub classes: Vec<ClassDef>,
    pub config: Vec<ConfigEntry>,
}

impl Model {
    pub fn find(&self, id: &str) -> Option<&Block> {
        find(&self.root, id)
    }
}

fn find<'m>(block: &'m Block, id: &str) -> Option<&'m Block> {
    block.children.iter().find_map(|child| {
        (child.id == id)
            .then_some(child)
            .or_else(|| find(child, id))
    })
}

fn descendants<'m>(block: &'m Block, ids: &mut BTreeSet<&'m str>) {
    for child in &block.children {
        ids.insert(child.id.as_str());
        descendants(child, ids);
    }
}

pub fn resolve(source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver::new(source, document);
    resolver.document(0, &document.document);
    resolver.finish()
}

struct Slot {
    block: Block,
    kids: Vec<usize>,
}

struct Resolver {
    arena: Vec<Slot>,
    database: BTreeMap<String, usize>,
    explicit: BTreeSet<String>,
    edges: Vec<Edge>,
    classes: Vec<ClassDef>,
    config: Vec<ConfigEntry>,
    diags: Vec<Diagnostic>,
    anonymous: usize,
    spaces: usize,
    slots: i32,
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

fn read_padding(config: &ConfigValue) -> Option<i64> {
    let ConfigValue::Mapping(root) = config else {
        return None;
    };
    let block = root.iter().find(|entry| entry.key == "block")?;
    let ConfigValue::Mapping(fields) = &block.value else {
        return None;
    };
    fields
        .iter()
        .filter(|field| field.key == "padding")
        .filter_map(|field| match &field.value {
            ConfigValue::Integer(text) => parse_non_negative(text),
            _ => None,
        })
        .next_back()
}

fn padding_config(source: &str) -> Vec<ConfigEntry> {
    let preprocessed = preprocess(source);
    let frontmatter = preprocessed
        .frontmatter
        .as_ref()
        .and_then(|frontmatter| frontmatter.config.as_ref());
    [frontmatter, preprocessed.init_config.as_ref()]
        .into_iter()
        .flatten()
        .filter_map(read_padding)
        .next_back()
        .map(|value| {
            vec![ConfigEntry {
                key: "padding".into(),
                value,
            }]
        })
        .unwrap_or_default()
}

fn clamp(text: &str) -> i32 {
    text.parse::<i64>()
        .ok()
        .and_then(|value| i32::try_from(value).ok())
        .unwrap_or(i32::MAX)
}

fn shape_kind(open: &str, close: &str) -> &'static str {
    match format!("{open}{close}").as_str() {
        "[]" => "square",
        "()" => "round",
        "(())" => "circle",
        ">]" => "rect_left_inv_arrow",
        "{}" => "diamond",
        "{{}}" => "hexagon",
        "([])" => "stadium",
        "[[]]" => "subroutine",
        "[()]" => "cylinder",
        "((()))" => "doublecircle",
        "[//]" => "lean_right",
        "[\\\\]" => "lean_left",
        "[/\\]" => "trapezoid",
        "[\\/]" => "inv_trapezoid",
        "<[]>" => "block_arrow",
        _ => "na",
    }
}

fn arrow_end(spelling: &str) -> &'static str {
    match spelling.bytes().next_back() {
        Some(b'x') => "arrow_cross",
        Some(b'o') => "arrow_circle",
        Some(b'>') => "arrow_point",
        _ => "",
    }
}

fn arrow_start(spelling: &str) -> &'static str {
    match spelling.bytes().next() {
        Some(b'x') => "arrow_cross",
        Some(b'o') => "arrow_circle",
        Some(b'<') => "arrow_point",
        _ => "arrow_open",
    }
}

fn edge(start: &str, end: &str, link: &Link<'_>, statement_span: Span) -> Edge {
    let spelling = link.end.text.trim();
    Edge {
        start: start.into(),
        end: end.into(),
        label: link
            .label
            .map_or_else(String::new, |label| decode_entities(label.text)),
        span: link.span,
        statement_span,
        thickness: if spelling.contains("==") {
            "thick"
        } else {
            "normal"
        }
        .into(),
        pattern: if spelling.contains(".-") {
            "dotted"
        } else {
            "solid"
        }
        .into(),
        arrow_start: arrow_start(spelling).into(),
        arrow_end: arrow_end(spelling).into(),
    }
}

fn remove_first_semicolon(text: &str) -> String {
    match text.find(';') {
        Some(at) => format!("{}{}", &text[..at], &text[at + 1..]),
        None => text.into(),
    }
}

impl Resolver {
    fn new(source: &str, document: &Start<'_>) -> Self {
        let mut resolver = Self {
            arena: vec![Slot {
                block: Block::named(String::new(), "composite", AUTO_COLUMNS),
                kids: Vec::new(),
            }],
            database: BTreeMap::new(),
            explicit: BTreeSet::new(),
            edges: Vec::new(),
            classes: Vec::new(),
            config: padding_config(source),
            diags: Vec::new(),
            anonymous: 0,
            spaces: 0,
            slots: 0,
        };
        resolver.collect_ids(&document.document);
        resolver.arena[0].block.id = resolver.generate("root", 0);
        resolver
    }

    fn finish(mut self) -> (Model, Vec<Diagnostic>) {
        let root = self.materialize(0);
        let mut known = BTreeSet::new();
        descendants(&root, &mut known);
        self.edges
            .retain(|e| known.contains(e.start.as_str()) && known.contains(e.end.as_str()));
        let model = Model {
            root,
            edges: self.edges,
            classes: self.classes,
            config: self.config,
        };
        (model, self.diags)
    }

    fn materialize(&self, index: usize) -> Block {
        let slot = &self.arena[index];
        let mut block = slot.block.clone();
        block.children = slot.kids.iter().map(|&kid| self.materialize(kid)).collect();
        block
    }

    fn collect_ids(&mut self, document: &Document<'_>) {
        for statement in &document.statements {
            match &statement.kind {
                StatementKind::Node(st) => self.collect_node(st),
                StatementKind::Block(st) => {
                    if let Some(header) = &st.header {
                        self.collect_node(header);
                    }
                    self.collect_ids(&st.body);
                }
                StatementKind::CssClass(st) => self.collect_list(st.ids.text),
                StatementKind::Style(st) => {
                    self.explicit.insert(st.ids.text.trim().into());
                }
                _ => {}
            }
        }
    }

    fn collect_node(&mut self, statement: &NodeStatement<'_>) {
        self.explicit.insert(statement.first.id.text.into());
        for linked in &statement.links {
            self.explicit.insert(linked.node.id.text.into());
        }
    }

    fn collect_list(&mut self, ids: &str) {
        for id in ids.split(',') {
            self.explicit.insert(id.trim().into());
        }
    }

    fn generate(&mut self, prefix: &str, ordinal: usize) -> String {
        let wanted = format!("{prefix}{ordinal}");
        let mut candidate = wanted.clone();
        let mut suffix = 1usize;
        while !self.explicit.insert(candidate.clone()) {
            candidate = format!("{wanted}~{suffix}");
            suffix += 1;
        }
        candidate
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diags.push(diagnostic(code, message, span));
    }

    fn document(&mut self, parent: usize, document: &Document<'_>) {
        let reference = document
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StatementKind::Columns(st) => Some(clamp(st.token.text)),
                _ => None,
            })
            .unwrap_or(AUTO_COLUMNS);
        for statement in &document.statements {
            self.statement(parent, &statement.kind, reference);
        }
    }

    fn statement(&mut self, parent: usize, kind: &StatementKind<'_>, reference: i32) {
        match kind {
            StatementKind::Columns(st) => self.arena[parent].block.columns = clamp(st.token.text),
            StatementKind::Space(st) => self.space(parent, st),
            StatementKind::Node(st) => self.node_statement(parent, st, reference),
            StatementKind::Block(st) => self.composite(parent, st, reference),
            StatementKind::ClassDef(st) => self.class_def(st),
            StatementKind::CssClass(st) => self.apply_class(st),
            StatementKind::Style(st) => self.apply_style(st),
        }
    }

    fn push_slot(&mut self, block: Block) -> usize {
        self.arena.push(Slot {
            block,
            kids: Vec::new(),
        });
        self.arena.len() - 1
    }

    fn space(&mut self, parent: usize, st: &SpaceStatement<'_>) {
        let count = clamp(st.token.text).min(MAX_SPACE_SLOTS - self.slots);
        let template = self.generate("space", self.spaces);
        self.spaces += 1;
        for slot in 0..count {
            let mut child = Block::named(format!("{template}-{slot}"), "space", 0);
            child.id_span = st.token.span;
            let id = child.id.clone();
            let index = self.push_slot(child);
            self.database.insert(id, index);
            self.arena[parent].kids.push(index);
        }
        self.slots += count;
    }

    fn node_block(
        &self,
        node: &Node<'_>,
        size: Option<&crate::syntax::block::lexer::Token<'_>>,
    ) -> Block {
        let mut block = Block::named(node.id.text.into(), "na", AUTO_COLUMNS);
        block.id_span = node.id.span;
        if let Some(size) = size {
            block.span = clamp(size.text);
            block.size_span = size.span;
        }
        if let Some(shape) = &node.shape {
            block.kind = shape_kind(shape.open.text, shape.close.text).into();
            block.label = decode_entities(shape.label.text);
            block.directions = shape.dirs.iter().map(|dir| dir.text.into()).collect();
        }
        if block.label.is_empty() {
            block.label = block.id.clone();
        }
        block
    }

    fn place(&mut self, parent: usize, block: Block) {
        let Some(&index) = self.database.get(&block.id) else {
            let id = block.id.clone();
            let index = self.push_slot(block);
            self.database.insert(id, index);
            self.arena[parent].kids.push(index);
            return;
        };
        let existing = &mut self.arena[index].block;
        if existing.kind == "composite" || existing.kind == "space" {
            return;
        }
        if block.kind != "na" {
            existing.kind = block.kind;
        }
        if block.label != block.id {
            existing.label = block.label;
        }
    }

    fn check_width(&mut self, block: &Block, reference: i32) {
        if reference > 0 && block.size_span != NO_SPAN && block.span > reference {
            let message = format!(
                "block {} width {} exceeds configured column width {}",
                block.id, block.span, reference
            );
            self.issue(C_WIDTH_EXCEEDS, message, block.size_span);
        }
    }

    fn node_statement(&mut self, parent: usize, st: &NodeStatement<'_>, reference: i32) {
        let first = self.node_block(&st.first, st.size.as_ref());
        self.check_width(&first, reference);
        let mut previous = first.id.clone();
        self.place(parent, first);
        for linked in &st.links {
            let target = self.node_block(&linked.node, None);
            let target_id = target.id.clone();
            self.place(parent, target);
            self.edges
                .push(edge(&previous, &target_id, &linked.link, st.span));
            previous = target_id;
        }
    }

    fn composite(&mut self, parent: usize, st: &BlockStatement<'_>, reference: i32) {
        let mut block = Block::named(String::new(), "composite", AUTO_COLUMNS);
        if let Some(header) = &st.header {
            let named = self.node_block(&header.first, header.size.as_ref());
            block.id = named.id;
            block.label = named.label;
            block.span = named.span;
            block.size_span = named.size_span;
            block.id_span = named.id_span;
            self.check_width(&block, reference);
        } else {
            block.id = self.generate("block", self.anonymous);
            self.anonymous += 1;
        }
        let id = block.id.clone();
        let index = self.push_slot(block);
        if let Entry::Vacant(slot) = self.database.entry(id) {
            slot.insert(index);
            self.arena[parent].kids.push(index);
        }
        self.document(index, &st.body);
    }

    fn class_def(&mut self, st: &ClassDefStatement<'_>) {
        let id = st.id.text.trim();
        let at = self
            .classes
            .iter()
            .position(|class| class.id == id)
            .unwrap_or_else(|| {
                self.classes.push(ClassDef {
                    id: id.into(),
                    styles: Vec::new(),
                    text_styles: Vec::new(),
                });
                self.classes.len() - 1
            });
        let class = &mut self.classes[at];
        for attribute in st.style.text.trim().split(',') {
            let fixed = remove_first_semicolon(attribute).trim().to_owned();
            if attribute.contains("color") {
                let text = fixed.replacen("fill", "bgFill", 1);
                class.text_styles.push(text.replacen("color", "fill", 1));
            }
            class.styles.push(fixed);
        }
    }

    fn apply_class(&mut self, st: &CssClassStatement<'_>) {
        let class = st.class.text.trim();
        for id in st.ids.text.split(',') {
            let id = id.trim();
            let index = match self.database.get(id) {
                Some(&index) => index,
                None => {
                    let index = self.push_slot(Block::named(id.into(), "na", AUTO_COLUMNS));
                    self.database.insert(id.into(), index);
                    index
                }
            };
            self.arena[index].block.classes.push(class.into());
        }
    }

    fn apply_style(&mut self, st: &StyleStatement<'_>) {
        let text = st.style.text.trim();
        if text.is_empty() {
            return;
        }
        let target = st.ids.text.trim();
        let Some(&index) = self.database.get(target) else {
            let message = format!("style references unknown block {target}");
            self.issue(C_STYLE_TARGET, message, st.ids.span);
            return;
        };
        self.arena[index].block.styles = text.split(',').map(String::from).collect();
    }
}

#[cfg(test)]
mod tests;
