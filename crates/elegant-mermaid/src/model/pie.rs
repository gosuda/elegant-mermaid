//! Semantic resolution of the `pie` kind (`spec/grammar/pie.md`): ordered sections, the
//! legend flag, metadata, and the honoured config keys. Numbers are integers in
//! thousandths.

use crate::syntax::entities::decode_entities as decode;
use std::collections::BTreeMap;

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::pie::ast::{Pie, PieSection, StatementKind};
use crate::syntax::pie::diagnostic;
use crate::syntax::preprocess::preprocess;

const SCALE: i64 = 1000;
const CONFIG_KEY: &str = "pie";
pub const DONUT_HOLE_KEY: &str = "donutHole";
pub const TEXT_POSITION_KEY: &str = "textPosition";
const DONUT_HOLE_MAX: i64 = 900;
const TEXT_POSITION_MAX: i64 = 1000;
pub const OVERFLOW: i64 = 1 << 32;
const C_NEGATIVE: &str = "pie/negative-value";

#[derive(Debug, Clone)]
pub struct Section {
    pub label: String,
    pub value: i64,
    pub index: usize,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct SectionOccurrence {
    pub section: Option<usize>,
    pub label: String,
    pub label_span: Span,
    pub number_span: Span,
    pub exact_zero: bool,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub show_data: bool,
    pub sections: Vec<Section>,
    pub config: BTreeMap<String, i64>,
    pub header: Span,
    pub occurrences: Vec<SectionOccurrence>,
}

struct Resolver {
    model: Model,
    diagnostics: Vec<Diagnostic>,
    seen: usize,
    last: BTreeMap<&'static str, String>,
}

pub fn resolve(source: &str, document: &Pie) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            acc_title: String::new(),
            acc_descr: String::new(),
            title: String::new(),
            show_data: document.show_data,
            sections: Vec::new(),
            config: BTreeMap::new(),
            header: document.header.span,
            occurrences: Vec::new(),
        },
        diagnostics: Vec::new(),
        seen: 0,
        last: BTreeMap::new(),
    };
    resolver.read_config(source);
    for statement in &document.body {
        match &statement.kind {
            StatementKind::PieSection(section) => resolver.section(section),
            StatementKind::TitleAndAccessibilities(group) => {
                for item in &group.items {
                    resolver.last.insert(item.field, item.value.clone());
                }
            }
        }
    }
    resolver.apply_metadata();
    (resolver.model, resolver.diagnostics)
}

fn child<'v>(entries: &'v [Entry], key: &str) -> Option<&'v [Entry]> {
    match &entries.iter().find(|entry| entry.key == key)?.value {
        ConfigValue::Mapping(fields) => Some(fields),
        _ => None,
    }
}

impl Resolver {
    fn read_config(&mut self, source: &str) {
        let preprocessed = preprocess(source);
        let mut blocks = Vec::new();
        if let Some(front) = preprocessed.frontmatter {
            self.read_front_title(&front.value);
            blocks.extend(front.config);
        }
        blocks.extend(preprocessed.init_config);
        for block in &blocks {
            self.read_pie(block);
        }
    }

    fn read_front_title(&mut self, root: &ConfigValue) {
        let ConfigValue::Mapping(entries) = root else {
            return;
        };
        for entry in entries.iter().filter(|entry| entry.key == "title") {
            if let ConfigValue::String(value) = &entry.value {
                self.model.title = decode(value).trim().to_owned();
            }
        }
    }

    fn read_pie(&mut self, block: &ConfigValue) {
        let ConfigValue::Mapping(entries) = block else {
            return;
        };
        for field in child(entries, CONFIG_KEY).unwrap_or_default() {
            self.read_field(field);
        }
    }

    fn read_field(&mut self, field: &Entry) {
        let limit = match field.key.as_str() {
            DONUT_HOLE_KEY => DONUT_HOLE_MAX,
            TEXT_POSITION_KEY => TEXT_POSITION_MAX,
            _ => return,
        };
        let (ConfigValue::Integer(text) | ConfigValue::Decimal(text)) = &field.value else {
            return;
        };
        let (magnitude, negative) = thousandths(text);
        if !negative && magnitude <= limit {
            self.model.config.insert(field.key.clone(), magnitude);
        }
    }

    fn section(&mut self, node: &PieSection) {
        let index = self.seen;
        self.seen += 1;
        let label = decode(&node.label.text);
        let (value, negative) = thousandths(&node.number.text);
        let section = (!negative).then(|| {
            self.model
                .sections
                .iter()
                .position(|s| s.label == label)
                .unwrap_or(self.model.sections.len())
        });
        self.model.occurrences.push(SectionOccurrence {
            section,
            label: if negative {
                label.clone()
            } else {
                String::new()
            },
            label_span: node.label.span,
            number_span: node.number.span,
            exact_zero: node
                .number
                .text
                .bytes()
                .all(|c| matches!(c, b'0' | b'.' | b'+' | b'-')),
        });
        if negative {
            let message = format!("slice {label} has negative value {}", node.number.text);
            self.diagnostics
                .push(diagnostic(C_NEGATIVE, message, node.number.span));
            return;
        }
        if section.is_some_and(|index| index < self.model.sections.len()) {
            return;
        }
        self.model.sections.push(Section {
            label,
            value,
            index,
            span: node.number.span,
        });
    }

    fn apply_metadata(&mut self) {
        let title = self
            .last
            .get("title")
            .map_or_else(String::new, |value| decode(value).trim().to_owned());
        if !title.is_empty() {
            self.model.title = title;
        }
        if let Some(value) = self.last.get("accTitle").filter(|v| !v.is_empty()) {
            self.model.acc_title.clone_from(value);
        }
        if let Some(value) = self.last.get("accDescr").filter(|v| !v.is_empty()) {
            self.model.acc_descr.clone_from(value);
        }
    }
}

fn digit(byte: u8) -> i64 {
    i64::from(byte.wrapping_sub(b'0'))
}

pub fn thousandths(literal: &str) -> (i64, bool) {
    let body = literal.trim_start_matches(['+', '-']);
    let (whole, fraction) = body.split_once('.').unwrap_or((body, ""));
    let mut units = 0i64;
    for byte in whole.bytes() {
        units = (units * 10 + digit(byte)).min(OVERFLOW);
    }
    let mut magnitude = units * SCALE;
    let mut tail = 0i64;
    for index in 0..4 {
        tail *= 10;
        if let Some(byte) = fraction.as_bytes().get(index) {
            tail += digit(*byte);
        }
    }
    magnitude += tail / 10;
    if tail % 10 >= 5 {
        magnitude += 1;
    }
    let negative = literal.starts_with('-') && !literal.trim_matches(['-', '0', '.']).is_empty();
    (magnitude.min(OVERFLOW), negative)
}

#[cfg(test)]
mod tests;
