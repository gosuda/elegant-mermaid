//! Semantic resolution of the eventmodeling model (`spec/grammar/eventmodeling.md`,
//! resolution): frames, swimlane bands, relations, and unwrapped data payloads.

use std::collections::BTreeMap;

use crate::diag::{Diagnostic, Related};
use crate::source::Span;
use crate::syntax::eventmodeling::ast::{EmFrame, EventModel, FrameFields, Value};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Category {
    Ui,
    Command,
    ReadModel,
    Event,
    Processor,
}

impl Category {
    pub const fn as_str(self) -> &'static str {
        match self {
            Category::Ui => "ui",
            Category::Command => "command",
            Category::ReadModel => "readmodel",
            Category::Event => "event",
            Category::Processor => "processor",
        }
    }

    fn of(entity_type: &str) -> Category {
        match entity_type {
            "cmd" | "command" => Category::Command,
            "rmo" | "readmodel" => Category::ReadModel,
            "evt" | "event" => Category::Event,
            "pcr" | "processor" => Category::Processor,
            _ => Category::Ui,
        }
    }

    fn band(self) -> Band {
        match self {
            Category::Ui | Category::Processor => Band {
                first: 0,
                limit: 100,
                fallback: "UI/Automation",
                prefix: "UI/A: ",
            },
            Category::Command | Category::ReadModel => Band {
                first: 100,
                limit: 200,
                fallback: "Command/Read Model",
                prefix: "C/RM: ",
            },
            Category::Event => Band {
                first: 200,
                limit: 300,
                fallback: "Events",
                prefix: "Stream: ",
            },
        }
    }
}

struct Band {
    first: i64,
    limit: i64,
    fallback: &'static str,
    prefix: &'static str,
}

#[derive(Debug, Clone)]
pub struct Lane {
    pub index: i64,
    pub label: String,
}

#[derive(Debug, Clone)]
pub struct Frame {
    pub name: String,
    pub reset: bool,
    pub entity_type: String,
    pub category: Category,
    pub identifier: String,
    pub display: String,
    pub namespace: String,
    pub lane: i64,
    pub has_data: bool,
    pub data: String,
    pub data_type: String,
    pub span: Span,
    pub statement_span: Span,
    pub sources: Vec<Reference>,
}

#[derive(Debug, Clone, Copy)]
pub struct Relation {
    pub source: usize,
    pub target: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct Reference {
    pub source: Option<usize>,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub frames: Vec<Frame>,
    pub lanes: Vec<Lane>,
    pub relations: Vec<Relation>,
}

pub fn resolve(document: &EventModel) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        document,
        model: Model::default(),
        diagnostics: Vec::new(),
    };
    resolver.frames();
    resolver.relations();
    resolver.model.lanes.sort_by_key(|lane| lane.index);
    (resolver.model, resolver.diagnostics)
}

struct Resolver<'a> {
    document: &'a EventModel,
    model: Model,
    diagnostics: Vec<Diagnostic>,
}

fn split_identifier(identifier: &str) -> (&str, &str) {
    let mut parts = identifier.split('.');
    match (parts.next(), parts.next(), parts.next()) {
        (Some(namespace), Some(display), None) => (namespace, display),
        _ => ("", identifier),
    }
}

impl Resolver<'_> {
    fn frames(&mut self) {
        let mut names = BTreeMap::new();
        for node in &self.document.frames {
            let name = &node.fields().name;
            if let Some(&first) = names.get(name.text.as_str()) {
                let mut diagnostic = crate::syntax::eventmodeling::diagnostic(
                    crate::syntax::eventmodeling::C_DUPLICATE,
                    format!("frame {} already exists", name.text),
                    name.span,
                );
                diagnostic.related.push(Related {
                    span: first,
                    message: "first declared here".into(),
                });
                self.diagnostics.push(diagnostic);
            } else {
                names.insert(name.text.as_str(), name.span);
            }
            let frame = self.frame(node);
            self.model.frames.push(frame);
        }
    }

    fn frame(&mut self, node: &EmFrame) -> Frame {
        let fields = node.fields();
        let category = Category::of(&fields.model_entity_type.text);
        let (namespace, display) = split_identifier(&fields.entity_identifier.text);
        let (has_data, data) = self.payload(fields);
        Frame {
            name: fields.name.text.clone(),
            sources: Vec::new(),
            reset: node.is_reset(),
            entity_type: fields.model_entity_type.text.clone(),
            category,
            identifier: fields.entity_identifier.text.clone(),
            display: display.to_owned(),
            namespace: namespace.to_owned(),
            lane: self.lane(category, namespace),
            has_data,
            data,
            data_type: fields
                .data_type
                .as_ref()
                .map_or_else(String::new, |value| value.text.clone()),
            span: fields.name.span,
            statement_span: fields.span,
        }
    }

    fn lane(&mut self, category: Category, namespace: &str) -> i64 {
        let band = category.band();
        let (index, label) = if namespace.is_empty() {
            (band.first, band.fallback.to_owned())
        } else {
            (
                self.next_index(&band) + 1,
                format!("{}{namespace}", band.prefix),
            )
        };
        if !self.model.lanes.iter().any(|lane| lane.index == index) {
            self.model.lanes.push(Lane { index, label });
        }
        index
    }

    fn next_index(&self, band: &Band) -> i64 {
        self.model
            .lanes
            .iter()
            .map(|lane| lane.index)
            .filter(|&index| index > band.first && index < band.limit)
            .fold(band.first, i64::max)
    }

    fn payload(&self, fields: &FrameFields) -> (bool, String) {
        let inline = fields
            .data_inline_value
            .as_ref()
            .map(|value| unwrap_payload(&value.text, "{"));
        let Some(reference) = &fields.data_reference else {
            return (inline.is_some(), inline.unwrap_or_default());
        };
        let found = self
            .document
            .data_entities
            .iter()
            .find(|entity| entity.name.text == reference.text);
        match found {
            Some(entity) => {
                let text = normalize_lines(&entity.data_block_value.text);
                (true, unwrap_payload(&text, "{\n") + "\n")
            }
            None => (inline.is_some(), inline.unwrap_or_default()),
        }
    }

    fn relations(&mut self) {
        for (target, node) in self.document.frames.iter().enumerate() {
            let sources = &node.fields().source_frames;
            for reference in sources {
                let source = self
                    .model
                    .frames
                    .iter()
                    .position(|frame| frame.name == reference.text);
                self.model.frames[target].sources.push(Reference {
                    source,
                    span: reference.span,
                });
            }
            if sources.is_empty() {
                self.inferred(target);
            } else {
                self.explicit(target, sources);
            }
        }
    }

    fn explicit(&mut self, target: usize, sources: &[Value]) {
        for (source, frame) in self.model.frames.iter().enumerate() {
            let named = sources.iter().any(|value| value.text == frame.name);
            if named && source <= target {
                self.model.relations.push(Relation { source, target });
            }
        }
    }

    fn inferred(&mut self, target: usize) {
        let Some(frame) = self.model.frames.get(target) else {
            return;
        };
        if frame.reset {
            return;
        }
        let lane = frame.lane;
        let before = self.model.frames.get(..target).unwrap_or_default();
        if let Some(source) = before.iter().rposition(|earlier| earlier.lane != lane) {
            self.model.relations.push(Relation { source, target });
        }
    }
}

fn normalize_lines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

fn unwrap_payload(raw: &str, opener: &str) -> String {
    let units: Vec<u16> = raw.encode_utf16().collect();
    let opener_units: Vec<u16> = opener.encode_utf16().collect();
    let opener_len = to_index(opener_units.len());
    let from = index_of(&units, &opener_units) + opener_len;
    let body = substring(&units, from, to_index(units.len()));
    let close = body.iter().rposition(|&unit| unit == u16::from(b'}'));
    let to = close.map_or(-1, to_index) - 1;
    String::from_utf16_lossy(substring(body, 0, to))
}

fn to_index(value: usize) -> isize {
    isize::try_from(value).unwrap_or(isize::MAX)
}

fn substring(units: &[u16], from: isize, to: isize) -> &[u16] {
    let length = to_index(units.len());
    let (mut from, mut to) = (from.clamp(0, length), to.clamp(0, length));
    if from > to {
        (from, to) = (to, from);
    }
    let (from, to) = (from.unsigned_abs(), to.unsigned_abs());
    units.get(from..to).unwrap_or_default()
}

fn index_of(units: &[u16], needle: &[u16]) -> isize {
    units
        .windows(needle.len().max(1))
        .position(|window| window == needle)
        .map_or(-1, to_index)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
