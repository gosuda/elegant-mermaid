//! Semantic resolution of the `quadrant` kind (`spec/grammar/quadrant.md`): axis and
//! quadrant texts, points in thousandths of the unit square, point classes and styles,
//! and the honoured config keys.

use crate::syntax::entities::decode_entities as decode;
use std::collections::BTreeMap;

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::preprocess::preprocess;
use crate::syntax::quadrant::ast::{
    AxisDetails, Points, Start, StatementKind, Style as StyleToken,
};
use crate::syntax::quadrant::diagnostic;

const SCALE: i64 = 1000;
const CONFIG_KEY: &str = "quadrantChart";
pub const NO_RADIUS: i64 = -1;
const MAX_RADIUS: i64 = 4096;
const MAX_PIXELS: i64 = 65536;
const MAX_SMALL_PX: i64 = 1024;
const MAX_FONT_PX: i64 = 256;
const DELIMITER_TAIL: &str = " \u{27f6} ";
const NO_SPAN: Span = Span { start: 0, end: 0 };

const INTEGER_KEYS: &[(&str, i64, i64)] = &[
    ("chartWidth", 1, MAX_PIXELS),
    ("chartHeight", 1, MAX_PIXELS),
    ("quadrantPadding", 0, MAX_SMALL_PX),
    ("titlePadding", 0, MAX_SMALL_PX),
    ("titleFontSize", 1, MAX_FONT_PX),
    ("xAxisLabelPadding", 0, MAX_SMALL_PX),
    ("yAxisLabelPadding", 0, MAX_SMALL_PX),
    ("xAxisLabelFontSize", 1, MAX_FONT_PX),
    ("yAxisLabelFontSize", 1, MAX_FONT_PX),
    ("pointRadius", 0, MAX_RADIUS),
    ("pointTextPadding", 0, MAX_SMALL_PX),
];

#[derive(Debug, Clone)]
pub struct Point {
    pub text: String,
    pub label_key: String,
    pub label_span: Span,
    pub class: String,
    pub x: i64,
    pub y: i64,
    pub radius: i64,
    pub color: String,
    pub stroke_color: String,
    pub stroke_width: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct QuadrantDeclaration {
    pub number: usize,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub header_span: Span,
    pub has_x_axis: bool,
    pub has_y_axis: bool,
    pub quadrant_declarations: Vec<QuadrantDeclaration>,
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub title_span: Span,
    pub quadrants: [String; 4],
    pub x_left: String,
    pub x_right: String,
    pub y_bottom: String,
    pub y_top: String,
    pub points: Vec<Point>,
    pub config: BTreeMap<String, i64>,
}

#[derive(Debug, Clone, Default)]
struct StyleSet {
    radius: Option<i64>,
    color: Option<String>,
    stroke_color: Option<String>,
    stroke_width: Option<String>,
}

impl StyleSet {
    fn over(self, base: &StyleSet) -> StyleSet {
        StyleSet {
            radius: self.radius.or(base.radius),
            color: self.color.or_else(|| base.color.clone()),
            stroke_color: self.stroke_color.or_else(|| base.stroke_color.clone()),
            stroke_width: self.stroke_width.or_else(|| base.stroke_width.clone()),
        }
    }
}

struct Resolver {
    model: Model,
    diagnostics: Vec<Diagnostic>,
    classes: BTreeMap<String, StyleSet>,
    inline: Vec<StyleSet>,
}

pub fn resolve(source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            header_span: document.header.span,
            has_x_axis: false,
            has_y_axis: false,
            quadrant_declarations: Vec::new(),
            acc_title: String::new(),
            acc_descr: String::new(),
            title: String::new(),
            title_span: NO_SPAN,
            quadrants: Default::default(),
            x_left: String::new(),
            x_right: String::new(),
            y_bottom: String::new(),
            y_top: String::new(),
            points: Vec::new(),
            config: BTreeMap::new(),
        },
        diagnostics: Vec::new(),
        classes: BTreeMap::new(),
        inline: Vec::new(),
    };
    resolver.read_config(source);
    for line in &document.document.lines {
        if let Some(kind) = &line.statement.kind {
            resolver.statement(kind);
        }
    }
    resolver.apply_classes();
    (resolver.model, resolver.diagnostics)
}

fn js_space(c: char) -> bool {
    matches!(
        c,
        '\t' | '\n'
            | '\u{b}'
            | '\u{c}'
            | '\r'
            | ' '
            | '\u{a0}'
            | '\u{1680}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
            | '\u{feff}'
            | '\u{2000}'..='\u{200a}'
    )
}

fn sanitize(text: &str) -> String {
    decode(text.trim_matches(js_space))
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
            self.read_chart(block);
        }
    }

    fn read_front_title(&mut self, root: &ConfigValue) {
        let ConfigValue::Mapping(entries) = root else {
            return;
        };
        for entry in entries.iter().filter(|entry| entry.key == "title") {
            if let ConfigValue::String(value) = &entry.value {
                self.model.title = sanitize(value);
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
            let Some((_, low, high)) = INTEGER_KEYS.iter().find(|(key, _, _)| *key == field.key)
            else {
                continue;
            };
            let ConfigValue::Integer(text) = &field.value else {
                continue;
            };
            if let Some(n) = text
                .parse::<i64>()
                .ok()
                .filter(|n| (*low..=*high).contains(n))
            {
                self.model.config.insert(field.key.clone(), n);
            }
        }
    }

    fn statement(&mut self, kind: &StatementKind<'_>) {
        match kind {
            StatementKind::Title(title) => {
                self.model.title = sanitize(title.value.text);
                self.model.title_span = title.span;
            }
            StatementKind::Accessibility(node) => {
                let value = node.value.text.trim_matches(js_space).to_owned();
                if node.title {
                    self.model.acc_title = value;
                } else {
                    self.model.acc_descr = value;
                }
            }
            StatementKind::AxisDetails(axis) => self.axis(axis),
            StatementKind::QuadrantDetails(details) => {
                self.model.quadrant_declarations.push(QuadrantDeclaration {
                    number: details.number,
                    span: details.span,
                });
                if let Some(slot) = details
                    .number
                    .checked_sub(1)
                    .and_then(|i| self.model.quadrants.get_mut(i))
                {
                    *slot = sanitize(&details.text.value);
                }
            }
            StatementKind::ClassDef(def) => {
                let styles = self.parse_styles(&def.styles.styles);
                self.classes.insert(def.name.text.clone(), styles);
            }
            StatementKind::Points(point) => self.point(point),
        }
    }

    fn axis(&mut self, axis: &AxisDetails<'_>) {
        if axis.y {
            self.model.has_y_axis = true;
        } else {
            self.model.has_x_axis = true;
        }
        let mut first = axis.first.value.clone();
        if axis.delimiter.is_some() && axis.second.is_none() {
            first.push_str(DELIMITER_TAIL);
        }
        let (low, high) = if axis.y {
            (&mut self.model.y_bottom, &mut self.model.y_top)
        } else {
            (&mut self.model.x_left, &mut self.model.x_right)
        };
        *low = sanitize(&first);
        if let Some(second) = &axis.second {
            *high = sanitize(&second.value);
        }
    }

    fn point(&mut self, node: &Points<'_>) {
        let styles = node
            .styles
            .as_ref()
            .map(|opt| self.parse_styles(&opt.styles))
            .unwrap_or_default();
        self.model.points.push(Point {
            text: sanitize(&node.text.value),
            label_key: node.text.value.clone(),
            label_span: node.text.span,
            class: node
                .class
                .as_ref()
                .map_or_else(String::new, |token| token.text.to_owned()),
            x: coordinate(node.point_x.text),
            y: coordinate(node.point_y.text),
            radius: NO_RADIUS,
            color: String::new(),
            stroke_color: String::new(),
            stroke_width: String::new(),
            span: node.span,
        });
        self.inline.push(styles);
    }

    fn apply_classes(&mut self) {
        for (point, inline) in self.model.points.iter_mut().zip(self.inline.drain(..)) {
            let styles = match self.classes.get(&point.class) {
                Some(class) if !point.class.is_empty() => inline.over(class),
                _ => inline,
            };
            point.radius = styles.radius.unwrap_or(NO_RADIUS);
            point.color = styles.color.unwrap_or_default();
            point.stroke_color = styles.stroke_color.unwrap_or_default();
            point.stroke_width = styles.stroke_width.unwrap_or_default();
        }
    }

    fn parse_styles(&mut self, styles: &[StyleToken]) -> StyleSet {
        let mut out = StyleSet::default();
        for style in styles {
            let entry = split_style(style);
            let Some(rule) = STYLE_RULES.iter().find(|rule| rule.key == entry.key) else {
                self.diagnostics.push(diagnostic(
                    "quadrant/unsupported-style",
                    format!("style named {} is not supported.", entry.key),
                    entry.key_span,
                ));
                continue;
            };
            if !entry.has_value || !(rule.valid)(&entry.value) {
                let shown = if entry.has_value {
                    entry.value.as_str()
                } else {
                    "undefined"
                };
                self.diagnostics.push(diagnostic(
                    rule.code,
                    format!(
                        "value for {} {shown} is invalid, please use a valid {}",
                        rule.key, rule.expectation
                    ),
                    entry.value_span,
                ));
                continue;
            }
            (rule.apply)(&mut out, &entry.value);
        }
        out
    }
}

fn coordinate(lexeme: &str) -> i64 {
    if lexeme.is_empty() || lexeme.starts_with('1') {
        return SCALE;
    }
    let rest = lexeme.get(1..).unwrap_or("");
    let size = rest.chars().next().map_or(0, char::len_utf8);
    let digits = lexeme.get(1 + size..).unwrap_or("").as_bytes();
    let mut tail = 0i64;
    for i in 0..4 {
        tail *= 10;
        if let Some(digit) = digits.get(i) {
            tail += i64::from(digit.saturating_sub(b'0'));
        }
    }
    let mut value = tail / 10;
    if tail % 10 >= 5 {
        value += 1;
    }
    value
}

struct StyleEntry {
    key: String,
    value: String,
    key_span: Span,
    value_span: Span,
    has_value: bool,
}

fn split_style(style: &StyleToken) -> StyleEntry {
    let trimmed = style.text.trim_matches(js_space);
    let start = style.span.start + style.text.len() - style.text.trim_start_matches(js_space).len();
    let Some(colon) = trimmed.find(':') else {
        let end = start + trimmed.len();
        return StyleEntry {
            key: trimmed.to_owned(),
            value: String::new(),
            key_span: Span { start, end },
            value_span: Span { start: end, end },
            has_value: false,
        };
    };
    let key = trimmed
        .get(..colon)
        .unwrap_or("")
        .trim_end_matches(js_space);
    let rest = trimmed.get(colon + 1..).unwrap_or("");
    let lead = rest.len() - rest.trim_start_matches(js_space).len();
    let mut value = rest.get(lead..).unwrap_or("");
    if let Some(next) = value.find(':') {
        value = value.get(..next).unwrap_or("").trim_end_matches(js_space);
    }
    let value_start = start + colon + 1 + lead;
    StyleEntry {
        key: key.to_owned(),
        value: value.to_owned(),
        key_span: Span {
            start,
            end: start + key.len(),
        },
        value_span: Span {
            start: value_start,
            end: value_start + value.len(),
        },
        has_value: true,
    }
}

fn all_digits(value: &str) -> bool {
    !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit())
}

fn hex_color(value: &str) -> bool {
    let digits = value.strip_prefix('#').unwrap_or(value);
    matches!(digits.len(), 3 | 6) && digits.bytes().all(|b| b.is_ascii_hexdigit())
}

fn pixels(value: &str) -> bool {
    value.strip_suffix("px").is_some_and(all_digits)
}

struct StyleRule {
    code: &'static str,
    key: &'static str,
    expectation: &'static str,
    valid: fn(&str) -> bool,
    apply: fn(&mut StyleSet, &str),
}

const STYLE_RULES: &[StyleRule] = &[
    StyleRule {
        code: "quadrant/invalid-radius",
        key: "radius",
        expectation: "number",
        valid: all_digits,
        apply: |styles, value| {
            styles.radius = Some(
                value
                    .parse::<i64>()
                    .map_or(MAX_RADIUS, |n| n.min(MAX_RADIUS)),
            );
        },
    },
    StyleRule {
        code: "quadrant/invalid-color",
        key: "color",
        expectation: "hex code",
        valid: hex_color,
        apply: |styles, value| styles.color = Some(value.to_owned()),
    },
    StyleRule {
        code: "quadrant/invalid-stroke-color",
        key: "stroke-color",
        expectation: "hex code",
        valid: hex_color,
        apply: |styles, value| styles.stroke_color = Some(value.to_owned()),
    },
    StyleRule {
        code: "quadrant/invalid-stroke-width",
        key: "stroke-width",
        expectation: "number of pixels (eg. 10px)",
        valid: pixels,
        apply: |styles, value| styles.stroke_width = Some(value.to_owned()),
    },
];

#[cfg(test)]
mod tests;
