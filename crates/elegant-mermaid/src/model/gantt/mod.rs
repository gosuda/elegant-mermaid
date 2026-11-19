//! Semantic resolution of the gantt model (`spec/grammar/gantt.md`, resolution).

mod compile;
mod dayjs;
mod duration;
mod fallback;
mod tasks;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::civil;
use crate::diag::Diagnostic;
use crate::scene::DumpValue;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::gantt::ast::{ClickStatement, Start, StatementKind};
use crate::syntax::gantt::lexer::Token;
use crate::syntax::gantt::{diagnostic, is_space};
use crate::syntax::preprocess::preprocess;

use crate::syntax::entities::decode_entities as label;

pub const DEFAULT_WEEKDAY: &str = "sunday";
pub const DEFAULT_WEEKEND: &str = "saturday";
pub const DEFAULT_AXIS_FORMAT: &str = "%Y-%m-%d";
const DAY_AXIS_FORMAT: &str = "%d";
const CONFIG_KEY: &str = "gantt";
const C_UNSAFE_URL: &str = "interaction/unsafe-url";
const C_CALLBACK_IGNORED: &str = "interaction/callback-ignored";
const C_TODAY: &str = "gantt/today-marker-ignored";
const C_TICK_UNSUPPORTED: &str = "gantt/tick-interval-unsupported";
const C_AXIS_UNSUPPORTED: &str = "gantt/axis-format-unsupported";

const INTEGER_KEYS: [(&str, i64, i64); 5] = [
    ("barHeight", 1, 1024),
    ("barGap", 0, 1024),
    ("topPadding", 0, 4096),
    ("leftPadding", 0, 4096),
    ("rightPadding", 0, 4096),
];

const WEEKDAY_IDS: [&str; 7] = [
    "monday",
    "tuesday",
    "wednesday",
    "thursday",
    "friday",
    "saturday",
    "sunday",
];

const TICK_UNITS: [&str; 7] = [
    "millisecond",
    "second",
    "minute",
    "hour",
    "day",
    "week",
    "month",
];

const NO_SPAN: Span = Span { start: 0, end: 0 };

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operand {
    pub text: String,
    pub span: Span,
}

impl Operand {
    fn none() -> Self {
        Self {
            text: String::new(),
            span: NO_SPAN,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section {
    pub name: String,
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowKind {
    Section,
    Task,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Row {
    pub kind: RowKind,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum StartKind {
    #[default]
    Operand,
    PrevEnd,
}

#[derive(Debug, Clone)]
pub struct Task {
    pub text: String,
    pub label: String,
    pub section: Option<usize>,
    pub id: String,
    pub generated: bool,
    pub active: bool,
    pub done: bool,
    pub crit: bool,
    pub milestone: bool,
    pub vert: bool,
    pub order: Option<usize>,
    pub start: Operand,
    pub end: Operand,
    pub span: Span,
    pub data_span: Span,
    pub(crate) prev_id: Option<String>,
    pub(crate) start_kind: StartKind,
    pub has_start: bool,
    pub has_end: bool,
    pub start_seconds: i64,
    pub end_seconds: i64,
    pub render_end: i64,
    pub has_render_end: bool,
    pub manual_end: bool,
    pub resolved: bool,
    pub failed: bool,
    pub link: Option<String>,
    pub owner: String,
}

impl Task {
    pub(crate) fn new(
        text: String,
        label: String,
        section: Option<usize>,
        span: Span,
        data_span: Span,
    ) -> Self {
        Self {
            text,
            label,
            section,
            id: String::new(),
            generated: false,
            active: false,
            done: false,
            crit: false,
            milestone: false,
            vert: false,
            order: None,
            start: Operand::none(),
            end: Operand::none(),
            span,
            data_span,
            prev_id: None,
            start_kind: StartKind::Operand,
            has_start: false,
            has_end: false,
            start_seconds: 0,
            end_seconds: 0,
            render_end: 0,
            has_render_end: false,
            manual_end: false,
            resolved: false,
            failed: false,
            link: None,
            owner: String::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Callback {
    pub name: String,
    pub args: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Click {
    pub ids: String,
    pub callback: Option<Callback>,
    pub href: Option<String>,
    pub href_span: Span,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub title_label: String,
    pub date_format: String,
    pub axis_format: String,
    pub axis_format_span: Span,
    pub tick_interval: String,
    pub tick_interval_span: Span,
    pub has_tick_interval: bool,
    pub today_marker: String,
    pub has_today_marker: bool,
    pub inclusive_end: bool,
    pub top_axis: bool,
    pub weekday: String,
    pub weekday_set: bool,
    pub weekend: String,
    pub includes: Vec<String>,
    pub excludes: Vec<String>,
    pub sections: Vec<Section>,
    pub tasks: Vec<Task>,
    pub rows: Vec<Row>,
    pub clicks: Vec<Click>,
    pub config: BTreeMap<String, DumpValue>,
}

impl Model {
    fn new() -> Self {
        Self {
            acc_title: String::new(),
            acc_descr: String::new(),
            title: String::new(),
            title_label: String::new(),
            date_format: String::new(),
            axis_format: String::new(),
            axis_format_span: NO_SPAN,
            tick_interval: String::new(),
            tick_interval_span: NO_SPAN,
            has_tick_interval: false,
            today_marker: String::new(),
            has_today_marker: false,
            inclusive_end: false,
            top_axis: false,
            weekday: DEFAULT_WEEKDAY.into(),
            weekday_set: false,
            weekend: DEFAULT_WEEKEND.into(),
            includes: Vec::new(),
            excludes: Vec::new(),
            sections: Vec::new(),
            tasks: Vec::new(),
            rows: Vec::new(),
            clicks: Vec::new(),
            config: BTreeMap::new(),
        }
    }
}

impl Model {
    pub fn config_integer(&self, key: &str) -> Option<i64> {
        match self.config.get(key) {
            Some(DumpValue::Integer(n)) => Some(*n),
            _ => None,
        }
    }

    pub fn config_string(&self, key: &str) -> Option<&str> {
        match self.config.get(key) {
            Some(DumpValue::String(text)) => Some(text),
            _ => None,
        }
    }

    pub fn config_bool(&self, key: &str) -> bool {
        matches!(self.config.get(key), Some(DumpValue::Bool(true)))
    }

    pub fn effective_weekday(&self) -> String {
        if self.weekday_set {
            return self.weekday.clone();
        }
        self.config_string("weekday")
            .map_or_else(|| self.weekday.clone(), str::to_owned)
    }

    pub fn effective_top_axis(&self) -> bool {
        self.top_axis || self.config_bool("topAxis")
    }

    pub fn effective_axis_format(&self) -> String {
        let mut format = self.axis_format.as_str();
        if format.is_empty() && self.date_format == "D" {
            format = DAY_AXIS_FORMAT;
        }
        if format.is_empty() {
            format = self.config_string("axisFormat").unwrap_or("");
        }
        if format.is_empty() {
            format = DEFAULT_AXIS_FORMAT;
        }
        if unsupported_axis_code(format).is_empty() {
            format.to_owned()
        } else {
            DEFAULT_AXIS_FORMAT.to_owned()
        }
    }

    pub fn tick_rule(&self) -> Option<(i64, &'static str)> {
        let mut text = self.tick_interval.as_str();
        if text.is_empty() {
            text = self.config_string("tickInterval").unwrap_or("");
        }
        parse_tick_interval(text).filter(|(_, unit)| *unit != "millisecond")
    }
}

struct ScanState {
    seen: BTreeSet<(usize, &'static str, usize)>,
    steps: usize,
    calendar: civil::Calendar,
}

pub(crate) struct Resolver {
    model: Model,
    ids: HashMap<String, usize>,
    diagnostics: Vec<Diagnostic>,
    last_id: Option<String>,
    counter: usize,
    order: usize,
    scans: ScanState,
}

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model::new(),
        ids: HashMap::new(),
        diagnostics: Vec::new(),
        last_id: None,
        counter: 0,
        order: 0,
        scans: ScanState {
            seen: BTreeSet::new(),
            steps: 0,
            calendar: civil::Calendar::new(&[], &[], DEFAULT_WEEKEND),
        },
    };
    resolver.read_config(source);
    for line in &document.document.lines {
        if let Some(statement) = &line.statement {
            resolver.statement(&statement.kind, statement.span);
        }
    }
    resolver.finish_directives();
    resolver.compile();
    (resolver.model, resolver.diagnostics)
}

pub(crate) fn trim(text: &str) -> &str {
    text.trim_matches(is_space)
}

fn description(text: &str) -> String {
    let mut out = String::new();
    let mut chars = trim(text).chars().peekable();
    while let Some(c) = chars.next() {
        out.push(c);
        if c == '\n' {
            while chars.next_if(|next| is_space(*next)).is_some() {}
        }
    }
    out
}

fn merge_tokens(existing: &mut Vec<String>, text: &str) {
    let lowered = text.to_ascii_lowercase();
    for token in lowered
        .split(|c: char| c == ',' || is_space(c))
        .filter(|token| !token.is_empty())
    {
        if !existing.iter().any(|known| known == token) {
            existing.push(token.to_owned());
        }
    }
}

fn unsupported_axis_code(format: &str) -> String {
    civil::format(0, format).1
}

fn parse_tick_interval(text: &str) -> Option<(i64, &'static str)> {
    let digits = text.bytes().take_while(u8::is_ascii_digit).count();
    if digits == 0 || text.starts_with('0') || digits > 9 {
        return None;
    }
    let every = text.get(..digits)?.parse::<i64>().ok()?;
    let name = text.get(digits..)?;
    TICK_UNITS
        .iter()
        .find(|unit| **unit == name)
        .map(|unit| (every, *unit))
}

impl Resolver {
    fn report(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn statement(&mut self, kind: &StatementKind, span: Span) {
        match kind {
            StatementKind::DateFormat(t) => self.model.date_format.clone_from(&t.value),
            StatementKind::InclusiveEndDates(_) => self.model.inclusive_end = true,
            StatementKind::TopAxis(_) => self.model.top_axis = true,
            StatementKind::AxisFormat(t) => {
                self.model.axis_format.clone_from(&t.value);
                self.model.axis_format_span = t.payload;
            }
            StatementKind::TickInterval(t) => {
                self.model.tick_interval.clone_from(&t.value);
                self.model.tick_interval_span = t.payload;
                self.model.has_tick_interval = true;
            }
            StatementKind::Excludes(t) => merge_tokens(&mut self.model.excludes, &t.value),
            StatementKind::Includes(t) => merge_tokens(&mut self.model.includes, &t.value),
            StatementKind::TodayMarker(t) => {
                self.model.today_marker.clone_from(&t.value);
                self.model.has_today_marker = true;
                self.report(C_TODAY, "today marker is ignored".into(), span);
            }
            StatementKind::Weekday(n) => {
                self.model.weekday = n.name.into();
                self.model.weekday_set = true;
            }
            StatementKind::Weekend(n) => self.model.weekend = n.name.into(),
            StatementKind::Title(t) => {
                self.model.title.clone_from(&t.value);
                self.model.title_label = label(trim(&t.value));
            }
            StatementKind::AccTitle(n) => self.model.acc_title = trim(&n.value.value).into(),
            StatementKind::AccDescr(n) => self.model.acc_descr = description(&n.value.value),
            StatementKind::AccDescrBlock(t) => self.model.acc_descr = description(&t.value),
            StatementKind::Section(t) => self.add_section(t),
            StatementKind::Click(c) => self.click(c, span),
            StatementKind::Task(t) => self.add_task(t, span),
        }
    }

    fn finish_directives(&mut self) {
        let m = &self.model;
        let axis = (!m.axis_format.is_empty())
            .then(|| unsupported_axis_code(&m.axis_format))
            .filter(|code| !code.is_empty())
            .map(|code| {
                (
                    format!(
                        "axis format contains unsupported code {code}; using {DEFAULT_AXIS_FORMAT}"
                    ),
                    m.axis_format_span,
                )
            });
        let tick = (m.has_tick_interval
            && matches!(
                parse_tick_interval(&m.tick_interval),
                Some((_, "millisecond"))
            ))
        .then_some((
            "millisecond tick interval is not supported; using automatic ticks".to_owned(),
            m.tick_interval_span,
        ));
        if let Some((message, span)) = axis {
            self.report(C_AXIS_UNSUPPORTED, message, span);
        }
        if let Some((message, span)) = tick {
            self.report(C_TICK_UNSUPPORTED, message, span);
        }
    }

    fn add_section(&mut self, token: &Token) {
        self.model.sections.push(Section {
            name: token.value.clone(),
            label: label(trim(&token.value)),
            span: token.payload,
        });
        self.model.rows.push(Row {
            kind: RowKind::Section,
            index: self.model.sections.len() - 1,
        });
    }

    fn click(&mut self, node: &ClickStatement, span: Span) {
        let mut click = Click {
            ids: node.click.value.clone(),
            callback: None,
            href: None,
            href_span: Span { start: 0, end: 0 },
            span,
        };
        if let Some(cb) = &node.callback {
            let name = trim(&cb.value).to_owned();
            let args = node
                .args
                .as_ref()
                .map(|args| split_callback_args(&args.value))
                .unwrap_or_default();
            self.report(
                C_CALLBACK_IGNORED,
                format!("callback {name} is ignored"),
                cb.payload,
            );
            click.callback = Some(Callback {
                name,
                args,
                span: cb.payload,
            });
        }
        if let Some(href) = &node.href {
            click.href = Some(href.value.clone());
            click.href_span = href.payload;
            self.link_tasks(&click.ids, &href.value, href.payload);
        }
        self.model.clicks.push(click);
    }

    fn link_tasks(&mut self, ids: &str, href: &str, span: Span) {
        let Some(url) = crate::interaction::SafeUrl::new(href).map(|u| u.as_str().to_owned())
        else {
            self.report(C_UNSAFE_URL, "link URL is not allowed".into(), span);
            return;
        };
        for id in ids.split(',') {
            if let Some(&at) = self.ids.get(id)
                && let Some(task) = self.model.tasks.get_mut(at)
            {
                task.link = Some(url.clone());
            }
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
            self.read_gantt(block);
        }
    }

    fn read_front_title(&mut self, root: &ConfigValue) {
        let ConfigValue::Mapping(entries) = root else {
            return;
        };
        for entry in entries.iter().filter(|entry| entry.key == "title") {
            if let ConfigValue::String(text) = &entry.value {
                self.model.title.clone_from(text);
                self.model.title_label = label(trim(text));
            }
        }
    }

    fn read_gantt(&mut self, block: &ConfigValue) {
        let ConfigValue::Mapping(entries) = block else {
            return;
        };
        let Some(Entry {
            value: ConfigValue::Mapping(fields),
            ..
        }) = entries.iter().find(|entry| entry.key == CONFIG_KEY)
        else {
            return;
        };
        for field in fields {
            self.read_field(field);
        }
    }

    fn read_field(&mut self, field: &Entry) {
        let value = INTEGER_KEYS
            .iter()
            .find(|(key, _, _)| *key == field.key)
            .map(|&(_, low, high)| integer_value(&field.value, low, high).map(DumpValue::Integer))
            .unwrap_or_else(|| text_field(field));
        if let Some(value) = value {
            self.model.config.insert(field.key.clone(), value);
        }
    }
}

fn integer_value(value: &ConfigValue, low: i64, high: i64) -> Option<i64> {
    let ConfigValue::Integer(text) = value else {
        return None;
    };
    let mut n = 0_i64;
    for byte in text.bytes() {
        if !byte.is_ascii_digit() || n > high {
            return None;
        }
        n = n * 10 + i64::from(byte - b'0');
    }
    (low..=high).contains(&n).then_some(n)
}

fn text_field(field: &Entry) -> Option<DumpValue> {
    match (field.key.as_str(), &field.value) {
        ("topAxis", ConfigValue::Bool(on)) => Some(DumpValue::Bool(*on)),
        ("axisFormat" | "tickInterval", ConfigValue::String(text)) => {
            Some(DumpValue::String(text.clone()))
        }
        ("weekday", ConfigValue::String(text)) if WEEKDAY_IDS.contains(&text.as_str()) => {
            Some(DumpValue::String(text.clone()))
        }
        _ => None,
    }
}

fn unquote(item: &str) -> String {
    if item.len() == 1 && item == "\"" {
        return String::new();
    }
    item.strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .unwrap_or(item)
        .to_owned()
}

fn split_callback_args(text: &str) -> Vec<String> {
    let bytes = text.as_bytes();
    let mut odd = vec![false; bytes.len() + 1];
    for i in (0..bytes.len()).rev() {
        odd[i] = odd[i + 1] != (bytes[i] == b'"');
    }
    let mut out = Vec::new();
    let mut from = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        if byte == b',' && !odd[i + 1] {
            out.push(unquote(trim(text.get(from..i).unwrap_or(""))));
            from = i + 1;
        }
    }
    out.push(unquote(trim(text.get(from..).unwrap_or(""))));
    out
}

#[cfg(test)]
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests;
