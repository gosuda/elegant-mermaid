//! Semantic resolution of the `radar` kind (`spec/grammar/radar.md`): axes, curves, option
//! defaults, range check, and the honoured config keys. Numbers are integers in thousandths.

use crate::syntax::entities::decode_entities as decode;
use std::collections::BTreeMap;

use crate::diag::{Diagnostic, Severity};
use crate::scene::DumpValue;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry as ConfigEntry};
use crate::syntax::preprocess::preprocess;
use crate::syntax::radar::ast::{Curve as CurveNode, Label, Start, Text, Token};
use crate::syntax::radar::diagnostic;

pub use super::chart::Graticule;

const SCALE: i64 = 1000;
const WHOLE_CAP: i64 = 1 << 32;
const MAX_CANVAS_PX: i64 = 65536;
const MAX_TICKS: i64 = 32 * SCALE;
const DEFAULT_TICKS: i64 = 5 * SCALE;
const CONFIG_KEY: &str = "radar";
const TENSION_CEILING: i64 = SCALE;
const NO_SPAN: Span = Span { start: 0, end: 0 };

const CODE_AXES_REQUIRED: &str = "radar/axes-required";
const CODE_MISSING_AXIS_ENTRY: &str = "radar/missing-axis-entry";
const CODE_TICKS_CLAMPED: &str = "radar/ticks-clamped";
const CODE_EMPTY_RANGE: &str = "radar/empty-range";

const INTEGER_KEYS: &[(&str, i64, i64)] = &[
    ("width", 1, MAX_CANVAS_PX),
    ("height", 1, MAX_CANVAS_PX),
    ("marginTop", 0, MAX_CANVAS_PX),
    ("marginRight", 0, MAX_CANVAS_PX),
];

#[derive(Debug, Clone)]
pub struct Axis {
    pub name: String,
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Curve {
    pub name: String,
    pub label: String,
    pub values: Vec<i64>,
    pub span: Span,
    pub entry_count: usize,
    pub positional: bool,
}

#[derive(Debug, Clone)]
pub struct Options {
    pub show_legend: bool,
    pub ticks: i64,
    pub has_max: bool,
    pub max: i64,
    pub min: i64,
    pub graticule: Graticule,
    pub max_span: Span,
    pub min_span: Span,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub header_span: Span,
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub title_span: Span,
    pub config: BTreeMap<String, DumpValue>,
    pub axes: Vec<Axis>,
    pub curves: Vec<Curve>,
    pub options: Options,
}

struct Resolver {
    model: Model,
    diagnostics: Vec<Diagnostic>,
}

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            header_span: document.header.span,
            acc_title: String::new(),
            acc_descr: String::new(),
            title: String::new(),
            title_span: NO_SPAN,
            config: BTreeMap::new(),
            axes: Vec::new(),
            curves: Vec::new(),
            options: Options {
                show_legend: true,
                ticks: DEFAULT_TICKS,
                has_max: false,
                max: 0,
                min: 0,
                graticule: Graticule::Circle,
                max_span: NO_SPAN,
                min_span: NO_SPAN,
            },
        },
        diagnostics: Vec::new(),
    };
    resolver.read_config(source);
    resolver.metadata(document);
    resolver.axes(document);
    for curve in &document.curves {
        resolver.curve(curve);
    }
    resolver.options(document);
    resolver.check_range(document.header.span);
    (resolver.model, resolver.diagnostics)
}

fn text(value: &str) -> String {
    decode(value).trim().to_owned()
}

fn label_of(name: &str, label: Option<&Label>) -> String {
    label.map_or_else(|| name.to_owned(), |label| text(&label.value.text))
}

fn child<'v>(entries: &'v [ConfigEntry], key: &str) -> Option<&'v [ConfigEntry]> {
    match &entries.iter().find(|entry| entry.key == key)?.value {
        ConfigValue::Mapping(fields) => Some(fields),
        _ => None,
    }
}

fn integer(value: &ConfigValue, low: i64, high: i64) -> Option<i64> {
    let ConfigValue::Integer(literal) = value else {
        return None;
    };
    literal
        .parse::<i64>()
        .ok()
        .filter(|n| (low..=high).contains(n))
}

fn graticule_of(name: &str) -> Graticule {
    if name == "polygon" {
        Graticule::Polygon
    } else {
        Graticule::Circle
    }
}

impl Resolver {
    fn issue(&mut self, code: &'static str, message: &str, span: Span) {
        self.diagnostics
            .push(diagnostic(code, message.to_owned(), span));
    }

    fn warn(&mut self, code: &'static str, message: &str, span: Span) {
        let mut warning = diagnostic(code, message.to_owned(), span);
        warning.severity = Severity::Warning;
        self.diagnostics.push(warning);
    }

    fn metadata(&mut self, document: &Start) {
        if let Some(Text { value, span }) = document.title.as_ref().filter(|t| !t.value.is_empty())
        {
            self.model.title = text(value);
            self.model.title_span = *span;
        }
        if let Some(t) = document.acc_title.as_ref().filter(|t| !t.value.is_empty()) {
            self.model.acc_title = t.value.trim().to_owned();
        }
        if let Some(t) = document.acc_descr.as_ref().filter(|t| !t.value.is_empty()) {
            self.model.acc_descr = t.value.trim().to_owned();
        }
    }

    fn axes(&mut self, document: &Start) {
        for axis in &document.axes {
            self.model.axes.push(Axis {
                name: axis.name.text.clone(),
                label: label_of(&axis.name.text, axis.label.as_ref()),
                span: axis.span,
            });
        }
    }

    fn curve(&mut self, node: &CurveNode) {
        let values = self.values(node).unwrap_or_default();
        self.model.curves.push(Curve {
            name: node.name.text.clone(),
            label: label_of(&node.name.text, node.label.as_ref()),
            values,
            span: node.span,
            entry_count: node.entries.len(),
            positional: node.entries.iter().all(|entry| entry.reference().is_none()),
        });
    }

    fn values(&mut self, node: &CurveNode) -> Option<Vec<i64>> {
        let first = node.entries.first()?;
        if first.reference().is_none() {
            return Some(
                node.entries
                    .iter()
                    .map(|entry| thousandths(&entry.number().text))
                    .collect(),
            );
        }
        if self.model.axes.is_empty() {
            self.issue(
                CODE_AXES_REQUIRED,
                "keyed curve requires declared axes",
                node.span,
            );
            return None;
        }
        let axes = self.model.axes.clone();
        let mut values = Vec::with_capacity(axes.len());
        for axis in &axes {
            let Some(entry) = node
                .entries
                .iter()
                .find(|entry| entry.reference().is_some_and(|r| r.text == axis.name))
            else {
                let message = format!("missing entry for axis {}", axis.label);
                self.issue(CODE_MISSING_AXIS_ENTRY, &message, node.span);
                return None;
            };
            values.push(thousandths(&entry.number().text));
        }
        Some(values)
    }

    fn options(&mut self, document: &Start) {
        for option in &document.options {
            let value = &option.value;
            match option.name.kind {
                "showLegend" => self.model.options.show_legend = value.text == "true",
                "ticks" => self.ticks(value),
                "max" => {
                    let o = &mut self.model.options;
                    o.has_max = true;
                    o.max = thousandths(&value.text);
                    o.max_span = value.span;
                }
                "min" => {
                    let o = &mut self.model.options;
                    o.min = thousandths(&value.text);
                    o.min_span = value.span;
                }
                "graticule" => self.model.options.graticule = graticule_of(&value.text),
                _ => {}
            }
        }
    }

    fn ticks(&mut self, value: &Token) {
        let mut ticks = thousandths(&value.text);
        if ticks > MAX_TICKS {
            let message = format!("ticks {} exceeds 32; using 32", value.text);
            self.warn(CODE_TICKS_CLAMPED, &message, value.span);
            ticks = MAX_TICKS;
        }
        self.model.options.ticks = ticks;
    }

    fn check_range(&mut self, header: Span) {
        let o = &self.model.options;
        let high = if o.has_max {
            Some(o.max)
        } else {
            self.largest_value()
        };
        let Some(high) = high else {
            return;
        };
        if high > o.min {
            return;
        }
        let span = if o.has_max {
            o.max_span
        } else if o.min_span == NO_SPAN {
            header
        } else {
            o.min_span
        };
        self.issue(
            CODE_EMPTY_RANGE,
            "radar maximum must be greater than minimum",
            span,
        );
    }

    fn largest_value(&self) -> Option<i64> {
        self.model
            .curves
            .iter()
            .flat_map(|curve| curve.values.iter().copied())
            .max()
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
            self.read_radar(block);
        }
    }

    fn read_front_title(&mut self, root: &ConfigValue) {
        let ConfigValue::Mapping(entries) = root else {
            return;
        };
        for entry in entries.iter().filter(|entry| entry.key == "title") {
            if let ConfigValue::String(value) = &entry.value {
                self.model.title = text(value);
            }
        }
    }

    fn read_radar(&mut self, block: &ConfigValue) {
        let ConfigValue::Mapping(entries) = block else {
            return;
        };
        let Some(radar) = child(entries, CONFIG_KEY) else {
            return;
        };
        for field in radar {
            self.read_field(field);
        }
    }

    fn read_field(&mut self, field: &ConfigEntry) {
        if field.key == "curveTension" {
            self.read_tension(&field.value);
            return;
        }
        let Some((_, low, high)) = INTEGER_KEYS.iter().find(|(key, _, _)| *key == field.key) else {
            return;
        };
        if let Some(n) = integer(&field.value, *low, *high) {
            self.model
                .config
                .insert(field.key.clone(), DumpValue::Integer(n));
        }
    }

    fn read_tension(&mut self, value: &ConfigValue) {
        let (ConfigValue::Integer(literal) | ConfigValue::Decimal(literal)) = value else {
            return;
        };
        if literal.starts_with('-') {
            return;
        }
        let tension = thousandths(literal);
        if tension <= TENSION_CEILING {
            self.model
                .config
                .insert("curveTension".to_owned(), DumpValue::Integer(tension));
        }
    }
}

fn digit(byte: u8) -> i64 {
    i64::from(byte.wrapping_sub(b'0'))
}

pub fn thousandths(literal: &str) -> i64 {
    let (whole, fraction) = literal.split_once('.').unwrap_or((literal, ""));
    let mut value = 0i64;
    for byte in whole.bytes() {
        value = (value * 10 + digit(byte)).min(WHOLE_CAP);
    }
    value *= SCALE;
    let digits = fraction.bytes().chain(std::iter::repeat(b'0')).take(4);
    let tail = digits.fold(0i64, |acc, byte| acc * 10 + digit(byte));
    value += tail / 10;
    if tail % 10 >= 5 {
        value += 1;
    }
    value
}

#[cfg(test)]
mod tests;
