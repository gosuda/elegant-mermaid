//! Semantic resolution of the journey model (`spec/grammar/journey.md`, resolution).

use crate::diag::Diagnostic;
use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::source::Span;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::entities::decode_entities as decode;
use crate::syntax::journey::ast::{Field, Start, StatementKind, Task as TaskNode};
use crate::syntax::journey::{diagnostic, is_space, trim};
use crate::syntax::preprocess::preprocess;

const C_UNEXPECTED: &str = "journey/unexpected-token";
const C_OUT_OF_RANGE: &str = "journey/score-out-of-range";
const SCORE_MIN: &str = "vector.journey.score_min";
const SCORE_MAX: &str = "vector.journey.score_max";
const MAX_EXACT_DIGITS: usize = 18;
const NO_SPAN: Span = Span { start: 0, end: 0 };

#[derive(Debug, Clone)]
pub struct Section {
    pub name: String,
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Task {
    pub section: String,
    pub section_label: String,
    pub section_span: Span,
    pub name: String,
    pub label: String,
    pub score: i64,
    pub people: Vec<String>,
    pub span: Span,
    pub name_span: Span,
    pub score_span: Span,
    pub actor_span: Span,
    pub without_actor: bool,
}

#[derive(Debug, Clone, Default)]
pub struct Config {
    pub width: Option<i64>,
    pub height: Option<i64>,
    pub margin_x: Option<i64>,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub header_span: Span,
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub title_label: String,
    pub title_span: Option<Span>,
    pub sections: Vec<Section>,
    pub tasks: Vec<Task>,
    pub actors: Vec<String>,
    pub config: Config,
}

struct Resolver {
    model: Model,
    current: Option<Section>,
    low: i64,
    high: i64,
    diagnostics: Vec<Diagnostic>,
}

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            header_span: document.header.span,
            config: read_config(source),
            acc_title: String::new(),
            acc_descr: String::new(),
            title: String::new(),
            title_label: String::new(),
            title_span: None,
            sections: Vec::new(),
            tasks: Vec::new(),
            actors: Vec::new(),
        },
        current: None,
        low: score_bound(SCORE_MIN),
        high: score_bound(SCORE_MAX),
        diagnostics: Vec::new(),
    };
    for line in &document.document.lines {
        if let Some(statement) = &line.statement {
            resolver.statement(&statement.kind, statement.span);
        }
    }
    resolver.model.actors = actors(&resolver.model.tasks);
    (resolver.model, resolver.diagnostics)
}

fn score_bound(name: &str) -> i64 {
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == name)
        .map_or(0, |row| i64::from(row.value))
}

impl Resolver {
    fn statement(&mut self, kind: &StatementKind, span: Span) {
        let model = &mut self.model;
        match kind {
            StatementKind::Title(node) => {
                model.title.clone_from(&node.text.text);
                model.title_label = label(&node.text.text);
                model.title_span = Some(node.text.span);
            }
            StatementKind::AccTitle(node) => model.acc_title = trim(&node.value.text).into(),
            StatementKind::AccDescr(node) => model.acc_descr = description(&node.value.text),
            StatementKind::AccDescrMultiline(node) => {
                model.acc_descr = description(&node.value.text);
            }
            StatementKind::Section(node) => {
                let section = Section {
                    name: node.text.text.clone(),
                    label: label(&node.text.text),
                    span: node.text.span,
                };
                model.sections.push(section.clone());
                self.current = Some(section);
            }
            StatementKind::Task(node) => self.task(span, node),
        }
    }

    fn task(&mut self, span: Span, node: &TaskNode) {
        let (score, score_span) = self.score(&node.fields[0]);
        let (section, section_label, section_span) = self.current.as_ref().map_or_else(
            || (String::new(), String::new(), NO_SPAN),
            |s| (s.name.clone(), s.label.clone(), s.span),
        );
        let mut task = Task {
            section,
            section_label,
            section_span,
            name: node.name.text.clone(),
            label: label(&node.name.text),
            score,
            people: Vec::new(),
            span,
            name_span: node.name.span,
            score_span,
            actor_span: NO_SPAN,
            without_actor: node.fields.get(1).is_none_or(|field| {
                field
                    .raw
                    .text
                    .trim_matches([' ', ',', '\t', '\r', '\n'])
                    .is_empty()
            }),
        };
        if let Some(actors) = node.fields.get(1) {
            task.actor_span = actors.raw.span;
            task.people = actors
                .raw
                .text
                .split(',')
                .map(|n| trim(n).to_owned())
                .collect();
        }
        self.model.tasks.push(task);
    }

    fn score(&mut self, field: &Field) -> (i64, Span) {
        let text = field.trimmed.text.as_str();
        let span = field.trimmed.span;
        let digits = text.trim_start_matches(['+', '-']);
        let sign = &text[..text.len() - digits.len()];
        if sign.len() > 1 || digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            let message = format!("unexpected {text}, expected one of: integer");
            self.diagnostics
                .push(diagnostic(C_UNEXPECTED, message, span));
            return (0, span);
        }
        match integer_value(sign, digits) {
            Some(value) if (self.low..=self.high).contains(&value) => (value, span),
            _ => {
                let message = format!(
                    "score {text} is outside the range {} to {}",
                    self.low, self.high
                );
                self.diagnostics
                    .push(diagnostic(C_OUT_OF_RANGE, message, span));
                (0, span)
            }
        }
    }
}

fn integer_value(sign: &str, digits: &str) -> Option<i64> {
    let digits = digits.trim_start_matches('0');
    if digits.len() > MAX_EXACT_DIGITS {
        return None;
    }
    if digits.is_empty() {
        return Some(0);
    }
    let value: i64 = digits.parse().ok()?;
    Some(if sign == "-" { -value } else { value })
}

fn actors(tasks: &[Task]) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    for task in tasks {
        for name in &task.people {
            if !names.contains(name) {
                names.push(name.clone());
            }
        }
    }
    names.sort_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
    names
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
    let Some(entry) = entries.iter().find(|entry| entry.key == "journey") else {
        return;
    };
    let ConfigValue::Mapping(fields) = &entry.value else {
        return;
    };
    for field in fields {
        let ConfigValue::Integer(text) = &field.value else {
            continue;
        };
        let Some(value) = text.parse::<i64>().ok().filter(|value| *value >= 0) else {
            continue;
        };
        match field.key.as_str() {
            "width" => config.width = Some(value),
            "height" => config.height = Some(value),
            "diagramMarginX" => config.margin_x = Some(value),
            _ => {}
        }
    }
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

fn label(text: &str) -> String {
    decode(trim(text))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
