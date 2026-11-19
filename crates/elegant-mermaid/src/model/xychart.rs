//! Semantic resolution of the `xychart` kind (`spec/grammar/xychart.md`): axes, plots,
//! point placement, and the honoured config keys. Numbers are integers in thousandths.

use crate::syntax::entities::decode_entities as decode;
use std::collections::BTreeMap;

use crate::diag::Diagnostic;
use crate::geom::floor_div;
use crate::scene::DumpValue;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::preprocess::preprocess;
use crate::syntax::xychart::ast::{AxisStatement, PlotStatement, Start, StatementKind, Text};

pub use super::chart::Orientation;

const SCALE: i64 = 1000;
const WHOLE_CAP: i64 = 1 << 32;
const CONFIG_KEY: &str = "xyChart";
const HORIZONTAL: &str = "horizontal";
const MAX_CANVAS_PX: i64 = 65536;
const NO_SPAN: Span = Span { start: 0, end: 0 };

const INTEGER_KEYS: &[(&str, i64, i64)] = &[
    ("width", 1, MAX_CANVAS_PX),
    ("height", 1, MAX_CANVAS_PX),
    ("plotReservedSpacePercent", 30, 100),
];

#[derive(Debug, Clone)]
pub struct Point {
    pub present: bool,
    pub slot: Option<usize>,
    pub has_x: bool,
    pub x: i64,
    pub y: i64,
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Plot {
    pub line: bool,
    pub title: String,
    pub span: Span,
    pub raw_point_count: usize,
    pub points: Vec<Point>,
}

#[derive(Debug, Clone)]
pub struct Axis {
    pub title: String,
    pub span: Span,
    pub categories: Vec<String>,
    pub spans: Vec<Span>,
    pub min: i64,
    pub max: i64,
    pub band: bool,
}

impl Axis {
    fn banded() -> Axis {
        Axis {
            title: String::new(),
            span: NO_SPAN,
            categories: Vec::new(),
            spans: Vec::new(),
            min: 0,
            max: 0,
            band: true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Model {
    pub header_span: Span,
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub title_span: Span,
    pub orientation: Orientation,
    pub config: BTreeMap<String, DumpValue>,
    pub x: Axis,
    pub y: Axis,
    pub plots: Vec<Plot>,
}

struct Placement {
    band: bool,
    names: Vec<String>,
    xs: Vec<i64>,
}

struct Resolver {
    model: Model,
    x_set: bool,
    y_set: bool,
    y_observed: bool,
    placed: Vec<Placement>,
}

pub fn resolve(source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            header_span: document
                .headers
                .first()
                .map_or(NO_SPAN, |header| header.keyword.span),
            acc_title: String::new(),
            acc_descr: String::new(),
            title: String::new(),
            title_span: NO_SPAN,
            orientation: Orientation::Vertical,
            config: BTreeMap::new(),
            x: Axis::banded(),
            y: Axis {
                band: false,
                ..Axis::banded()
            },
            plots: Vec::new(),
        },
        x_set: false,
        y_set: false,
        y_observed: false,
        placed: Vec::new(),
    };
    resolver.read_config(source);
    for header in &document.headers {
        if let Some(orientation) = &header.orientation {
            resolver.model.orientation = orientation_of(orientation.text);
        }
    }
    for statement in &document.document.statements {
        resolver.statement(&statement.kind);
    }
    resolver.bind_placements();
    (resolver.model, Vec::new())
}

fn orientation_of(text: &str) -> Orientation {
    if text == HORIZONTAL {
        Orientation::Horizontal
    } else {
        Orientation::Vertical
    }
}

fn child<'v>(entries: &'v [Entry], key: &str) -> Option<&'v [Entry]> {
    match &entries.iter().find(|entry| entry.key == key)?.value {
        ConfigValue::Mapping(fields) => Some(fields),
        _ => None,
    }
}

fn integer(value: &ConfigValue, low: i64, high: i64) -> Option<i64> {
    let ConfigValue::Integer(text) = value else {
        return None;
    };
    text.parse::<i64>()
        .ok()
        .filter(|n| (low..=high).contains(n))
}

fn label_text(source: &Text) -> String {
    decode(&source.value).trim().to_owned()
}

struct PointSource<'a> {
    value: i64,
    span: Span,
    label: Option<&'a Text>,
}

fn point_from(span: Span, source: Option<PointSource<'_>>) -> Point {
    let Some(source) = source else {
        return Point {
            present: false,
            slot: None,
            has_x: false,
            x: 0,
            y: 0,
            label: String::new(),
            span,
        };
    };
    Point {
        present: true,
        slot: None,
        has_x: false,
        x: 0,
        y: source.value,
        label: source.label.map_or_else(String::new, label_text),
        span: source.span,
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
            self.read_chart(block);
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

    fn read_chart(&mut self, block: &ConfigValue) {
        let ConfigValue::Mapping(entries) = block else {
            return;
        };
        let Some(chart) = child(entries, CONFIG_KEY) else {
            return;
        };
        for field in chart {
            self.read_field(field);
        }
        for field in child(chart, "xAxis").unwrap_or_default() {
            self.read_axis_field(field);
        }
    }

    fn read_field(&mut self, field: &Entry) {
        if let (true, ConfigValue::String(value)) = (field.key == "chartOrientation", &field.value)
        {
            self.model.orientation = orientation_of(value);
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

    fn read_axis_field(&mut self, field: &Entry) {
        match (field.key.as_str(), &field.value) {
            ("labelFontSize", value) => {
                if let Some(n) = integer(value, 1, 256) {
                    self.model
                        .config
                        .insert("xAxis.labelFontSize".to_owned(), DumpValue::Integer(n));
                }
            }
            ("showLabel", ConfigValue::Bool(show)) => {
                self.model
                    .config
                    .insert("xAxis.showLabel".to_owned(), DumpValue::Bool(*show));
            }
            _ => {}
        }
    }

    fn statement(&mut self, kind: &StatementKind<'_>) {
        match kind {
            StatementKind::Title(title) => {
                self.model.title = label_text(&title.text);
                self.model.title_span = title.span;
            }
            StatementKind::Accessibility(accessibility) => {
                let value = accessibility.value.text.trim().to_owned();
                if accessibility.title {
                    self.model.acc_title = value;
                } else {
                    self.model.acc_descr = value;
                }
            }
            StatementKind::Axis(axis) => self.axis(axis),
            StatementKind::Plot(plot) => self.plot(plot),
        }
    }

    fn axis(&mut self, statement: &AxisStatement<'_>) {
        let title = statement
            .title
            .as_ref()
            .map_or_else(String::new, label_text);
        let axis = if statement.y {
            &mut self.model.y
        } else {
            &mut self.model.x
        };
        if let Some(band) = &statement.band {
            axis.band = true;
            axis.categories = band.categories.iter().map(label_text).collect();
            axis.spans = band.categories.iter().map(|c| c.span).collect();
            self.x_set = true;
        } else if let Some(range) = &statement.range {
            axis.band = false;
            axis.categories = Vec::new();
            axis.spans = Vec::new();
            axis.min = thousandths(range.min.text);
            axis.max = thousandths(range.max.text);
            if statement.y {
                self.y_set = true;
                self.y_observed = true;
            } else {
                self.x_set = true;
            }
        }
        axis.title = title;
        axis.span = statement.span;
    }

    fn plot(&mut self, statement: &PlotStatement<'_>) {
        let values: Vec<i64> = statement
            .data
            .points
            .iter()
            .map(|point| thousandths(point.number.text))
            .collect();
        self.fix_linear_domain(values.len());
        let band = self.model.x.band;
        let categories = self.model.x.categories.len();
        let kept = if band {
            values.len().min(categories)
        } else {
            values.len()
        };
        if !self.y_set {
            self.observe(&values[..kept]);
        }
        let slots = if band { categories } else { kept };
        let mut points = Vec::with_capacity(slots);
        let mut placed = Placement {
            band,
            names: Vec::new(),
            xs: Vec::new(),
        };
        for index in 0..slots {
            let source = (index < kept).then(|| {
                let data = &statement.data.points[index];
                PointSource {
                    value: values[index],
                    span: data.span,
                    label: data.label.as_ref().filter(|_| statement.line),
                }
            });
            points.push(point_from(statement.span, source));
            if band {
                placed.names.push(self.model.x.categories[index].clone());
            } else {
                placed.xs.push(linear_x(&self.model.x, index, slots));
            }
        }
        self.model.plots.push(Plot {
            line: statement.line,
            title: statement
                .title
                .as_ref()
                .map_or_else(String::new, label_text),
            span: statement.span,
            raw_point_count: values.len(),
            points,
        });
        self.placed.push(placed);
    }

    fn fix_linear_domain(&mut self, count: usize) {
        if self.x_set {
            return;
        }
        let x = &self.model.x;
        self.model.x = Axis {
            title: x.title.clone(),
            span: x.span,
            min: SCALE,
            max: i64::try_from(count).unwrap_or(i64::MAX) * SCALE,
            band: false,
            ..Axis::banded()
        };
        self.x_set = true;
    }

    fn observe(&mut self, values: &[i64]) {
        for value in values {
            let y = &mut self.model.y;
            if self.y_observed {
                y.min = y.min.min(*value);
                y.max = y.max.max(*value);
            } else {
                y.min = *value;
                y.max = *value;
                self.y_observed = true;
            }
        }
    }

    fn bind_placements(&mut self) {
        let x = &self.model.x;
        for (plot, placed) in self.model.plots.iter_mut().zip(&self.placed) {
            for (j, point) in plot.points.iter_mut().enumerate() {
                if placed.band && x.band {
                    point.slot = x.categories.iter().position(|c| *c == placed.names[j]);
                } else if !placed.band && !x.band {
                    point.has_x = true;
                    point.x = placed.xs[j];
                }
            }
        }
    }
}

fn linear_x(axis: &Axis, index: usize, count: usize) -> i64 {
    if count < 2 {
        return axis.min;
    }
    let numerator = i64::try_from(index).unwrap_or(i64::MAX) * (axis.max - axis.min);
    axis.min + floor_div(numerator, i64::try_from(count - 1).unwrap_or(i64::MAX))
}

fn digit(byte: u8) -> i64 {
    i64::from(byte.wrapping_sub(b'0'))
}

pub fn thousandths(literal: &str) -> i64 {
    let negative = literal.starts_with('-');
    let body = literal.trim_start_matches(['+', '-']);
    let (whole, fraction) = body.split_once('.').unwrap_or((body, ""));
    let mut value = 0i64;
    for byte in whole.bytes() {
        value = (value * 10 + digit(byte)).min(WHOLE_CAP);
    }
    value *= SCALE;
    let mut tail = 0i64;
    for index in 0..4 {
        tail *= 10;
        if let Some(byte) = fraction.as_bytes().get(index) {
            tail += digit(*byte);
        }
    }
    value += tail / 10;
    if tail % 10 >= 5 {
        value += 1;
    }
    if negative { -value } else { value }
}

#[cfg(test)]
mod tests;
