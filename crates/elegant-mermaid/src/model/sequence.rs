//! Semantic resolution of the sequence model (`spec/grammar/sequence.md`, resolution).

use crate::syntax::entities::decode_entities as decode;
use std::collections::BTreeMap;

use crate::diag::{Diagnostic, Severity};
use crate::source::Span;
use crate::source::cleaned::Cleaned;
use crate::syntax::config_value::{self, ConfigValue};
use crate::syntax::preprocess::preprocess;
use crate::syntax::sequence::ast;
use crate::syntax::sequence::ast::StatementKind;
use crate::syntax::sequence::diagnostic;
use crate::syntax::sequence::lexer::Token;

pub const C_INACTIVE: &str = "sequence/inactive-participant";
pub const C_BOX_CONFLICT: &str = "sequence/participant-box-conflict";
pub const C_CREATE_EXISTS: &str = "sequence/create-existing-participant";
pub const C_CREATING_MISSING: &str = "sequence/creating-message-missing";
pub const C_DESTROYING_MISSING: &str = "sequence/destroying-message-missing";

pub const HONORED: &[&str] = &[
    "activationWidth",
    "actorMargin",
    "boxMargin",
    "boxTextMargin",
    "diagramMarginX",
    "diagramMarginY",
    "height",
    "labelBoxHeight",
    "labelBoxWidth",
    "look",
    "noteMargin",
    "theme",
    "width",
    "wrap",
    "wrapPadding",
];

pub const DRAW_KINDS: &[&str] = &[
    "actor",
    "boundary",
    "collections",
    "control",
    "database",
    "entity",
    "queue",
];

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub acc_title: String,
    pub acc_descr: String,
    pub title: Option<String>,
    pub actors: Vec<Actor>,
    pub events: Vec<Event>,
    pub boxes: Vec<ParticipantBox>,
    pub wrap: bool,
    pub config: BTreeMap<String, DumpValue>,
    pub declarations: Vec<ActorDeclaration>,
    pub activation_history: Vec<Activation>,
}

#[derive(Debug, Clone)]
pub struct ActorDeclaration {
    pub id: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Activation {
    pub actor: usize,
    pub open: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Actor {
    pub id: String,
    pub span: Span,
    pub label: String,
    pub kind: &'static str,
    pub wrap: Option<bool>,
    pub created: bool,
    pub created_at: Option<usize>,
    pub destroyed_at: Option<usize>,
    pub box_index: Option<usize>,
    pub links: Vec<(String, String)>,
    pub properties: Vec<(String, String)>,
}

#[derive(Debug, Clone)]
pub enum Event {
    Message(Message),
    Note(Note),
    FragmentStart(FragmentStart),
    FragmentElse(FragmentElse),
    FragmentEnd { start_event: usize },
    ActivateStart { actor: usize },
    ActivateEnd { actor: usize },
}

#[derive(Debug, Clone)]
pub struct Message {
    pub from: usize,
    pub to: usize,
    pub text: String,
    pub span: Span,
    pub dotted: bool,
    pub numbered: bool,
    pub head_start: &'static str,
    pub head_end: &'static str,
    pub central_start: bool,
    pub central_end: bool,
    pub creates: bool,
    pub destroys: bool,
    pub wrap: Option<bool>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Placement {
    LeftOf,
    RightOf,
    Over,
}

#[derive(Debug, Clone)]
pub struct Note {
    pub placement: Placement,
    pub actors: [usize; 2],
    pub text: String,
    pub span: Span,
    pub wrap: Option<bool>,
}

#[derive(Debug, Clone)]
pub struct FragmentStart {
    pub kind: &'static str,
    pub title: String,
    pub span: Span,
    pub wrap: Option<bool>,
}

#[derive(Debug, Clone)]
pub struct FragmentElse {
    pub start_event: usize,
    pub title: String,
    pub span: Span,
    pub wrap: Option<bool>,
}

#[derive(Debug, Clone)]
pub struct ParticipantBox {
    pub label: String,
    pub wrap: Option<bool>,
    pub color: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DumpValue {
    Bool(bool),
    Integer(i64),
    String(String),
}

pub fn resolve(source: &str, document: &ast::Start<'_>) -> (Model, Vec<Diagnostic>) {
    Resolver::new(source).run(document)
}

struct Resolver<'s> {
    cleaned: Cleaned<'s>,
    model: Model,
    diagnostics: Vec<Diagnostic>,
    indices: BTreeMap<String, usize>,
    activations: Vec<usize>,
    pending_create: Option<usize>,
    pending_destroy: Option<usize>,
    autonumber_start: i64,
    autonumber_step: i64,
    autonumber_on: bool,
    message_count: usize,
    current_box: Option<usize>,
    fragments: Vec<usize>,
}

impl<'s> Resolver<'s> {
    fn new(source: &'s str) -> Self {
        let preprocessed = preprocess(source);
        let cleaned = Cleaned::new(source, &preprocessed.removed);
        let mut config = BTreeMap::new();
        let mut wrap = preprocessed.wrap;
        for block in [
            preprocessed.frontmatter.and_then(|f| f.config),
            preprocessed.init_config,
        ]
        .into_iter()
        .flatten()
        {
            let ConfigValue::Mapping(entries) = &block else {
                continue;
            };
            let Some(sequence) = entries.iter().find(|entry| entry.key == "sequence") else {
                continue;
            };
            let ConfigValue::Mapping(fields) = &sequence.value else {
                continue;
            };
            for field in fields {
                if !HONORED.contains(&field.key.as_str()) {
                    continue;
                }
                if field.key == "wrap"
                    && let ConfigValue::Bool(value) = field.value
                {
                    wrap |= value;
                }
                if let Some(value) = dump_value(&field.value) {
                    config.insert(field.key.clone(), value);
                }
            }
        }
        Resolver {
            cleaned,
            model: Model {
                wrap,
                config,
                ..Model::default()
            },
            diagnostics: Vec::new(),
            indices: BTreeMap::new(),
            activations: Vec::new(),
            pending_create: None,
            pending_destroy: None,
            autonumber_start: 100,
            autonumber_step: 100,
            autonumber_on: false,
            message_count: 0,
            current_box: None,
            fragments: Vec::new(),
        }
    }

    fn run(mut self, document: &ast::Start<'_>) -> (Model, Vec<Diagnostic>) {
        self.lines(&document.document.lines);
        (self.model, self.diagnostics)
    }

    fn lines(&mut self, lines: &[ast::Line<'_>]) {
        for line in lines {
            let Some(statement) = line.statement.as_ref() else {
                continue;
            };
            self.statement(statement);
        }
    }

    fn statement(&mut self, statement: &ast::Statement<'_>) {
        match &statement.kind {
            StatementKind::Participant(participant) => self.participant(participant),
            StatementKind::Signal(signal) => self.signal(signal),
            StatementKind::Autonumber {
                start, step, off, ..
            } => self.autonumber(start.as_ref(), step.as_ref(), *off),
            StatementKind::Activate { actor, .. } => self.activate(actor),
            StatementKind::Deactivate { actor, .. } => self.deactivate(actor),
            StatementKind::Note(note) => self.note(note),
            StatementKind::Links { actor, text, .. } => {
                self.linked(actor, text, Linked::Links);
            }
            StatementKind::Link { actor, text, .. } => {
                self.linked(actor, text, Linked::Link);
            }
            StatementKind::Properties { actor, text, .. } => {
                self.linked(actor, text, Linked::Properties);
            }
            StatementKind::Details { actor, text, .. } => {
                self.linked(actor, text, Linked::Details);
            }
            StatementKind::Title { value, legacy, .. } => {
                let text = decode(if *legacy {
                    value.trim_start_matches(' ')
                } else {
                    value
                });
                self.model.title = Some(text);
            }
            StatementKind::Accessibility { title, value, .. } => {
                let text = self.text(*value).trim().to_string();
                if *title {
                    self.model.acc_title = text;
                } else {
                    self.model.acc_descr = text;
                }
            }
            StatementKind::Box(box_block) => self.box_block(box_block),
            StatementKind::Control(control) => self.control(control),
        }
    }

    fn text(&self, span: Span) -> String {
        self.cleaned.slice(span).into_owned()
    }

    fn participant(&mut self, participant: &ast::ParticipantStatement<'_>) {
        if participant.create.is_some() && self.indices.contains_key(&*participant.actor.text) {
            let message = format!(
                "cannot create existing participant {}",
                participant.actor.text
            );
            self.diagnostics
                .push(diagnostic(C_CREATE_EXISTS, message, participant.actor.span));
            return;
        }
        if participant.destroy && participant.create.is_none() {
            let index = self.absent_actor(&participant.actor);
            self.pending_destroy = Some(index);
            return;
        }
        let alias = participant
            .alias
            .as_ref()
            .map(|alias| strip_wrap(&alias.text.text));
        let metadata = participant
            .config
            .as_ref()
            .map(|config| self.metadata(config));
        let draw = participant.draw.unwrap_or("participant");
        let metadata_type = metadata
            .as_ref()
            .and_then(|fields| fields.iter().find(|(key, _)| key == "type"))
            .map(|(_, value)| value.as_str());
        let kind: &'static str = match metadata_type {
            Some(name) => DRAW_KINDS
                .iter()
                .find(|candidate| **candidate == name)
                .copied()
                .unwrap_or("participant"),
            None if draw == "actor" => "actor",
            None => "participant",
        };
        let wrap = text_override(alias.as_deref());
        let distinct_alias = alias
            .as_deref()
            .is_some_and(|text| text.trim() != participant.actor.text);
        let index = self.defined_actor(&participant.actor, alias.as_deref(), kind, wrap);
        if participant.create.is_some() {
            self.model.actors[index].created = true;
            self.pending_create = Some(index);
        }
        self.model.actors[index].links.clear();
        self.model.actors[index].properties.clear();
        if let Some(fields) = metadata {
            for (key, value) in fields {
                match key.as_str() {
                    "alias" if !distinct_alias && !value.is_empty() => {
                        self.model.actors[index].label = decode(&value);
                    }
                    "type" => {}
                    _ => self.model.actors[index].properties.push((key, value)),
                }
            }
        }
        if let Some(box_index) = self.current_box {
            let actor = &mut self.model.actors[index];
            match actor.box_index {
                None => actor.box_index = Some(box_index),
                Some(existing) if existing != box_index => {
                    let message = format!("participant {} belongs to more than one box", actor.id);
                    self.diagnostics.push(diagnostic(
                        C_BOX_CONFLICT,
                        message,
                        participant.actor.span,
                    ));
                }
                Some(_) => {}
            }
        }
    }

    fn defined_actor(
        &mut self,
        actor: &ast::Actor<'_>,
        alias: Option<&str>,
        kind: &'static str,
        wrap: Option<bool>,
    ) -> usize {
        self.model.declarations.push(ActorDeclaration {
            id: actor.text.to_string(),
            span: actor.span,
        });
        if let Some(index) = self.indices.get(&*actor.text).copied() {
            let record = &mut self.model.actors[index];
            if !record.created {
                record.label = decode(alias.unwrap_or(&actor.text));
                record.kind = kind;
                record.wrap = wrap;
            }
            return index;
        }
        let index = self.model.actors.len();
        self.model.actors.push(Actor {
            id: actor.text.to_string(),
            span: actor.span,
            label: decode(alias.unwrap_or(&actor.text)),
            kind,
            wrap,
            created: false,
            created_at: None,
            destroyed_at: None,
            box_index: self.current_box,
            links: Vec::new(),
            properties: Vec::new(),
        });
        self.activations.push(0);
        self.indices.insert(actor.text.to_string(), index);
        index
    }

    fn absent_actor(&mut self, actor: &ast::Actor<'_>) -> usize {
        if let Some(index) = self.indices.get(&*actor.text).copied() {
            return index;
        }
        let index = self.model.actors.len();
        self.model.actors.push(Actor {
            id: actor.text.to_string(),
            span: actor.span,
            label: decode(&actor.text),
            kind: "participant",
            wrap: None,
            created: false,
            created_at: None,
            destroyed_at: None,
            box_index: self.current_box,
            links: Vec::new(),
            properties: Vec::new(),
        });
        self.activations.push(0);
        self.indices.insert(actor.text.to_string(), index);
        index
    }

    fn signal(&mut self, signal: &ast::Signal<'_>) {
        let from = self.absent_actor(&signal.source);
        let to = self.absent_actor(&signal.target);
        let (text, wrap) = label_text(&signal.text.text);
        let dotted = dotted_arrow(signal.arrow.kind);
        let (head_start, head_end) = heads(signal.arrow.kind);
        if let Some(suffix) = signal.suffix.as_ref()
            && suffix.kind == "-"
            && self.activations[from] == 0
        {
            let message = format!("participant {} is not active", self.model.actors[from].id);
            self.diagnostics
                .push(diagnostic(C_INACTIVE, message, suffix.span));
        }
        let creates = self.take_pending_create(signal, to);
        let destroyed = if creates {
            None
        } else {
            self.take_pending_destroy(signal, from, to)
        };
        let destroys = destroyed.is_some();
        let numbered = self.autonumber_on;
        let label = if numbered {
            let number = self.autonumber_start
                + i64::try_from(self.message_count).unwrap_or(i64::MAX) * self.autonumber_step;
            let prefix = format!("({}) ", format_number(number));
            format!("{}{}", prefix, text)
        } else {
            text.clone()
        };
        let event = self.model.events.len();
        self.model.events.push(Event::Message(Message {
            from,
            to,
            text: label,
            span: signal.span,
            dotted,
            numbered,
            head_start,
            head_end,
            central_start: signal.central_start,
            central_end: signal.central_end,
            creates,
            destroys,
            wrap,
        }));
        self.message_count += 1;
        if creates {
            self.model.actors[to].created_at = Some(event);
        }
        if let Some(destroyed) = destroyed {
            self.model.actors[destroyed].destroyed_at = Some(event);
        }
        if let Some(suffix) = signal.suffix.as_ref() {
            self.model.activation_history.push(Activation {
                actor: if suffix.kind == "+" { to } else { from },
                open: suffix.kind == "+",
                span: suffix.span,
            });
            if suffix.kind == "+" {
                self.activations[to] += 1;
                self.model.events.push(Event::ActivateStart { actor: to });
            } else if self.activations[from] > 0 {
                self.activations[from] -= 1;
                self.model.events.push(Event::ActivateEnd { actor: from });
            }
        }
    }

    fn take_pending_create(&mut self, signal: &ast::Signal<'_>, to: usize) -> bool {
        let Some(created) = self.pending_create else {
            return false;
        };
        self.pending_create = None;
        if created == to {
            return true;
        }
        let message = format!(
            "next message must target created participant {}",
            self.model.actors[created].id
        );
        self.diagnostics
            .push(diagnostic(C_CREATING_MISSING, message, signal.target.span));
        false
    }

    fn take_pending_destroy(
        &mut self,
        signal: &ast::Signal<'_>,
        from: usize,
        to: usize,
    ) -> Option<usize> {
        let destroyed = self.pending_destroy?;
        self.pending_destroy = None;
        if destroyed != from && destroyed != to {
            let message = format!(
                "next message must involve destroyed participant {}",
                self.model.actors[destroyed].id
            );
            self.diagnostics
                .push(diagnostic(C_DESTROYING_MISSING, message, signal.span));
            return None;
        }
        Some(destroyed)
    }

    fn autonumber(&mut self, start: Option<&Token<'_>>, step: Option<&Token<'_>>, off: bool) {
        if off {
            self.autonumber_on = false;
            return;
        }
        self.autonumber_on = true;
        if let Some(token) = start
            && let Some(hundredths) = hundredths(&token.text)
            && hundredths != 0
        {
            self.autonumber_start = hundredths;
        }
        if let Some(token) = step
            && let Some(hundredths) = hundredths(&token.text)
            && hundredths != 0
        {
            self.autonumber_step = hundredths;
        }
    }

    fn activate(&mut self, actor: &ast::Actor<'_>) {
        let index = self.absent_actor(actor);
        self.model.activation_history.push(Activation {
            actor: index,
            open: true,
            span: actor.span,
        });
        self.activations[index] += 1;
        self.model
            .events
            .push(Event::ActivateStart { actor: index });
    }

    fn deactivate(&mut self, actor: &ast::Actor<'_>) {
        let index = self.absent_actor(actor);
        self.model.activation_history.push(Activation {
            actor: index,
            open: false,
            span: actor.span,
        });
        if self.activations[index] == 0 {
            let message = format!("participant {} is not active", self.model.actors[index].id);
            self.diagnostics
                .push(diagnostic(C_INACTIVE, message, actor.span));
            return;
        }
        self.activations[index] -= 1;
        self.model.events.push(Event::ActivateEnd { actor: index });
    }

    fn note(&mut self, note: &ast::NoteStatement<'_>) {
        let placement = match self.text(note.placement).to_ascii_lowercase() {
            text if text.starts_with("right") => Placement::RightOf,
            text if text.starts_with("left") => Placement::LeftOf,
            _ => Placement::Over,
        };
        let first = self.absent_actor(&note.actors[0]);
        let second = match note.actors.get(1) {
            Some(actor) => self.absent_actor(actor),
            None => first,
        };
        let (text, wrap) = label_text(&note.text.text);
        let placement = if note.over {
            Placement::Over
        } else {
            placement
        };
        self.model.events.push(Event::Note(Note {
            placement,
            actors: [first, second],
            text,
            span: note.span,
            wrap,
        }));
    }

    fn metadata(&mut self, config: &ast::ConfigObject<'_>) -> Vec<(String, String)> {
        let body = MetadataBody::new(config);
        let parsed = config_value::parse_yaml_doc(&body.text, 0, body.text.len());
        for mut diagnostic in parsed.diagnostics {
            diagnostic.span = Span {
                start: body.offset(diagnostic.span.start),
                end: body.offset(diagnostic.span.end),
            };
            self.diagnostics.push(diagnostic);
        }
        let mut fields = Vec::new();
        merge_pairs(&mut fields, mapping_entries(&parsed.value));
        fields
    }

    fn linked(&mut self, actor: &ast::Actor<'_>, text: &ast::Text2<'_>, target: Linked) {
        let index = self.absent_actor(actor);
        let raw = strip_wrap(text.text.strip_prefix(':').unwrap_or(&text.text))
            .trim()
            .to_string();
        let record = &mut self.model.actors[index];
        match target {
            Linked::Link => {
                let (label, url) = split_link(&raw);
                upsert(&mut record.links, label, url);
            }
            Linked::Links => merge_pairs(&mut record.links, &json_mapping(&raw)),
            Linked::Properties => merge_pairs(&mut record.properties, &json_mapping(&raw)),
            Linked::Details => {
                for member in json_mapping(&raw) {
                    let ConfigValue::Mapping(entries) = &member.value else {
                        continue;
                    };
                    match member.key.as_str() {
                        "properties" => merge_pairs(&mut record.properties, entries),
                        "links" => merge_pairs(&mut record.links, entries),
                        _ => {}
                    }
                }
            }
        }
    }

    fn box_block(&mut self, box_block: &ast::BoxBlock<'_>) {
        let raw = strip_wrap(&box_block.text.text).trim().to_string();
        let (color, label) = box_color_label(&raw);
        let index = self.model.boxes.len();
        let wrap = text_override(Some(&raw));
        self.model.boxes.push(ParticipantBox {
            label: decode(&label),
            wrap,
            color,
            span: box_block.keyword,
        });
        self.current_box = Some(index);
        self.box_lines(&box_block.section.lines);
        self.current_box = None;
    }

    fn box_lines(&mut self, lines: &[ast::Line<'_>]) {
        for line in lines {
            let Some(statement) = line.statement.as_ref() else {
                continue;
            };
            self.statement(statement);
        }
    }

    fn control(&mut self, control: &ast::ControlBlock<'_>) {
        let (title, wrap) = if control.kind == "rect" {
            (decode(control.text.text.trim()), None)
        } else {
            label_text(&control.text.text)
        };
        let event = self.model.events.len();
        self.model.events.push(Event::FragmentStart(FragmentStart {
            kind: control.kind,
            title,
            span: control.keyword,
            wrap,
        }));
        self.fragments.push(event);
        for section in &control.sections {
            if section.separator.is_some() {
                let (title, wrap) = label_text(&section.title.text);
                self.model.events.push(Event::FragmentElse(FragmentElse {
                    start_event: event,
                    title,
                    span: section
                        .separator
                        .as_ref()
                        .map_or(section.title.span, |token| token.span),
                    wrap,
                }));
            }
            self.lines(&section.document.lines);
        }
        self.fragments.pop();
        self.model
            .events
            .push(Event::FragmentEnd { start_event: event });
    }
}

#[derive(Debug, Clone, Copy)]
enum Linked {
    Links,
    Link,
    Properties,
    Details,
}

struct MetadataBody {
    text: String,
    start: usize,
    wrapped: bool,
    open: usize,
    close: usize,
}

impl MetadataBody {
    fn new(config: &ast::ConfigObject<'_>) -> Self {
        let trimmed = config.content.trim();
        let start = config.content_span.start + config.content.find(trimmed).unwrap_or(0);
        if trimmed.contains(['\n', '\r']) {
            return Self {
                text: trimmed.to_string(),
                start,
                wrapped: false,
                open: 0,
                close: 0,
            };
        }
        Self {
            text: format!("{{{trimmed}}}"),
            start,
            wrapped: true,
            open: config.span.start + 1,
            close: config.span.end - 1,
        }
    }

    fn offset(&self, at: usize) -> usize {
        if !self.wrapped {
            return self.start + at.min(self.text.len());
        }
        let inner = self.text.len() - 2;
        match at {
            0 => self.open,
            _ if at <= inner => self.start + at - 1,
            _ if at == inner + 1 => self.close,
            _ => self.close + 1,
        }
    }
}

fn mapping_entries(value: &ConfigValue) -> &[config_value::Entry] {
    match value {
        ConfigValue::Mapping(entries) => entries,
        _ => &[],
    }
}

fn json_mapping(text: &str) -> Vec<config_value::Entry> {
    let parsed = config_value::parse_json_doc(text, 0, text.len());
    mapping_entries(&parsed.value).to_vec()
}

fn merge_pairs(fields: &mut Vec<(String, String)>, entries: &[config_value::Entry]) {
    for entry in entries {
        if let Some(value) = plain_value(&entry.value) {
            upsert(fields, entry.key.clone(), value);
        }
    }
}

fn plain_value(value: &ConfigValue) -> Option<String> {
    match value {
        ConfigValue::String(text) => Some(text.clone()),
        ConfigValue::Integer(text) | ConfigValue::Decimal(text) => Some(text.clone()),
        ConfigValue::Bool(true) => Some(String::from("true")),
        ConfigValue::Bool(false) => Some(String::from("false")),
        _ => None,
    }
}

fn dump_value(value: &ConfigValue) -> Option<DumpValue> {
    match value {
        ConfigValue::Bool(flag) => Some(DumpValue::Bool(*flag)),
        ConfigValue::Integer(text) => text.parse::<i64>().ok().map(DumpValue::Integer),
        ConfigValue::Decimal(text) => text.parse::<i64>().ok().map(DumpValue::Integer),
        ConfigValue::String(text) => Some(DumpValue::String(text.clone())),
        _ => None,
    }
}

fn upsert(fields: &mut Vec<(String, String)>, key: String, value: String) {
    if let Some(existing) = fields.iter_mut().find(|(name, _)| *name == key) {
        existing.1 = value;
        return;
    }
    fields.push((key, value));
}

fn hundredths(text: &str) -> Option<i64> {
    let text = text.trim();
    let (whole, fraction) = match text.split_once('.') {
        Some((whole, fraction)) => (whole, fraction),
        None => (text, ""),
    };
    if whole.is_empty() && fraction.is_empty() {
        return None;
    }
    let mut value = whole.parse::<i64>().ok()?.checked_mul(100)?;
    let mut scale = 10;
    for digit in fraction.bytes().take(2) {
        if !digit.is_ascii_digit() {
            return None;
        }
        value += i64::from(digit - b'0') * scale;
        scale /= 10;
    }
    Some(value)
}

fn format_number(hundredths: i64) -> String {
    let whole = hundredths / 100;
    let fraction = hundredths % 100;
    if fraction == 0 {
        return whole.to_string();
    }
    if fraction % 10 == 0 {
        return format!("{whole}.{}", fraction / 10);
    }
    format!("{whole}.{fraction}")
}

fn label_text(token: &str) -> (String, Option<bool>) {
    let body = token.strip_prefix(':').unwrap_or(token);
    let (text, wrap) = strip_wrap_with(body);
    (decode(text.trim()), wrap)
}

fn strip_wrap(token: &str) -> String {
    strip_wrap_with(token).0
}

fn strip_wrap_with(token: &str) -> (String, Option<bool>) {
    let body = token.trim_start_matches([' ', '\t']);
    let folded = body.to_ascii_lowercase();
    for (marker, value) in [("nowrap:", Some(false)), ("wrap:", Some(true))] {
        if folded.starts_with(marker) {
            return (body[marker.len()..].to_string(), value);
        }
    }
    (body.to_string(), None)
}

fn text_override(token: Option<&str>) -> Option<bool> {
    let token = token?;
    let folded = token.trim_start_matches([' ', '\t']).to_ascii_lowercase();
    if folded.starts_with("nowrap:") {
        return Some(false);
    }
    if folded.starts_with("wrap:") {
        return Some(true);
    }
    None
}

fn dotted_arrow(kind: &str) -> bool {
    matches!(
        kind,
        "DOTTED_ARROW"
            | "BIDIRECTIONAL_DOTTED_ARROW"
            | "DOTTED_OPEN_ARROW"
            | "DOTTED_CROSS"
            | "DOTTED_POINT"
            | "SOLID_ARROW_TOP_DOTTED"
            | "SOLID_ARROW_BOTTOM_DOTTED"
            | "STICK_ARROW_TOP_DOTTED"
            | "STICK_ARROW_BOTTOM_DOTTED"
            | "SOLID_ARROW_TOP_REVERSE_DOTTED"
            | "SOLID_ARROW_BOTTOM_REVERSE_DOTTED"
            | "STICK_ARROW_TOP_REVERSE_DOTTED"
            | "STICK_ARROW_BOTTOM_REVERSE_DOTTED"
    )
}

fn heads(kind: &str) -> (&'static str, &'static str) {
    match kind {
        "SOLID_ARROW" | "DOTTED_ARROW" => ("", "arrowhead"),
        "BIDIRECTIONAL_SOLID_ARROW" | "BIDIRECTIONAL_DOTTED_ARROW" => ("arrowhead", "arrowhead"),
        "SOLID_OPEN_ARROW" | "DOTTED_OPEN_ARROW" => ("", "none"),
        "SOLID_CROSS" | "DOTTED_CROSS" => ("", "crosshead"),
        "SOLID_POINT" | "DOTTED_POINT" => ("", "filled-head"),
        "SOLID_ARROW_TOP" | "SOLID_ARROW_TOP_DOTTED" => ("", "solidTopArrowHead"),
        "SOLID_ARROW_BOTTOM" | "SOLID_ARROW_BOTTOM_DOTTED" => ("", "solidBottomArrowHead"),
        "STICK_ARROW_TOP" | "STICK_ARROW_TOP_DOTTED" => ("", "stickTopArrowHead"),
        "STICK_ARROW_BOTTOM" | "STICK_ARROW_BOTTOM_DOTTED" => ("", "stickBottomArrowHead"),
        "SOLID_ARROW_TOP_REVERSE" | "SOLID_ARROW_TOP_REVERSE_DOTTED" => {
            ("solidBottomArrowHead", "")
        }
        "SOLID_ARROW_BOTTOM_REVERSE" | "SOLID_ARROW_BOTTOM_REVERSE_DOTTED" => {
            ("solidTopArrowHead", "")
        }
        "STICK_ARROW_TOP_REVERSE" | "STICK_ARROW_TOP_REVERSE_DOTTED" => {
            ("stickBottomArrowHead", "")
        }
        "STICK_ARROW_BOTTOM_REVERSE" | "STICK_ARROW_BOTTOM_REVERSE_DOTTED" => {
            ("stickTopArrowHead", "")
        }
        _ => ("", ""),
    }
}

fn split_link(raw: &str) -> (String, String) {
    let chars: Vec<char> = raw.chars().collect();
    let (label_end, url_start) = match chars.iter().position(|c| *c == '@') {
        Some(0) => (chars.len().saturating_sub(1), 1),
        Some(at) => (at - 1, at + 1),
        None => (chars.len().saturating_sub(2), 0),
    };
    let part = |range: std::ops::Range<usize>| {
        chars
            .get(range)
            .unwrap_or_default()
            .iter()
            .collect::<String>()
            .trim()
            .to_string()
    };
    (part(0..label_end), part(url_start..chars.len()))
}

/// Splits box text into an optional colour and a title, as the upstream pattern
/// `^((?:rgba?|hsla?)\s*\(.*\)|\w*)(.*)$` does: a colour function runs to the last
/// closing parenthesis, any other colour is the leading word. Text whose colour part is
/// not a CSS colour is entirely the title.
fn box_color_label(raw: &str) -> (Option<String>, String) {
    let raw = raw.trim();
    let (color, rest) = color_prefix(raw);
    match color {
        Some(color) => (Some(color.to_string()), rest.trim().to_string()),
        None => (None, raw.to_string()),
    }
}

fn color_prefix(raw: &str) -> (Option<&str>, &str) {
    let word_end = raw
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(raw.len());
    let word = &raw[..word_end];
    if matches!(
        word.to_ascii_lowercase().as_str(),
        "rgb" | "rgba" | "hsl" | "hsla"
    ) {
        let after = raw[word_end..].trim_start();
        if let Some(body) = after.strip_prefix('(')
            && let Some(close) = body.rfind(')')
            && is_color_arguments(&body[..close])
        {
            let consumed = raw.len() - body.len() + close + 1;
            return (Some(raw[..consumed].trim()), &raw[consumed..]);
        }
        return (None, raw);
    }
    if is_named_color(word) {
        return (Some(word), &raw[word_end..]);
    }
    (None, raw)
}

fn is_color_arguments(arguments: &str) -> bool {
    !arguments.trim().is_empty()
        && arguments
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c.is_ascii_whitespace() || ",./%+-".contains(c))
}

/// CSS Color Module Level 4 named colours, plus `transparent` and `currentcolor`.
const NAMED_COLORS: &[&str] = &[
    "aliceblue",
    "antiquewhite",
    "aqua",
    "aquamarine",
    "azure",
    "beige",
    "bisque",
    "black",
    "blanchedalmond",
    "blue",
    "blueviolet",
    "brown",
    "burlywood",
    "cadetblue",
    "chartreuse",
    "chocolate",
    "coral",
    "cornflowerblue",
    "cornsilk",
    "crimson",
    "cyan",
    "darkblue",
    "darkcyan",
    "darkgoldenrod",
    "darkgray",
    "darkgreen",
    "darkgrey",
    "darkkhaki",
    "darkmagenta",
    "darkolivegreen",
    "darkorange",
    "darkorchid",
    "darkred",
    "darksalmon",
    "darkseagreen",
    "darkslateblue",
    "darkslategray",
    "darkslategrey",
    "darkturquoise",
    "darkviolet",
    "deeppink",
    "deepskyblue",
    "dimgray",
    "dimgrey",
    "dodgerblue",
    "firebrick",
    "floralwhite",
    "forestgreen",
    "fuchsia",
    "gainsboro",
    "ghostwhite",
    "gold",
    "goldenrod",
    "gray",
    "green",
    "greenyellow",
    "grey",
    "honeydew",
    "hotpink",
    "indianred",
    "indigo",
    "ivory",
    "khaki",
    "lavender",
    "lavenderblush",
    "lawngreen",
    "lemonchiffon",
    "lightblue",
    "lightcoral",
    "lightcyan",
    "lightgoldenrodyellow",
    "lightgray",
    "lightgreen",
    "lightgrey",
    "lightpink",
    "lightsalmon",
    "lightseagreen",
    "lightskyblue",
    "lightslategray",
    "lightslategrey",
    "lightsteelblue",
    "lightyellow",
    "lime",
    "limegreen",
    "linen",
    "magenta",
    "maroon",
    "mediumaquamarine",
    "mediumblue",
    "mediumorchid",
    "mediumpurple",
    "mediumseagreen",
    "mediumslateblue",
    "mediumspringgreen",
    "mediumturquoise",
    "mediumvioletred",
    "midnightblue",
    "mintcream",
    "mistyrose",
    "moccasin",
    "navajowhite",
    "navy",
    "oldlace",
    "olive",
    "olivedrab",
    "orange",
    "orangered",
    "orchid",
    "palegoldenrod",
    "palegreen",
    "paleturquoise",
    "palevioletred",
    "papayawhip",
    "peachpuff",
    "peru",
    "pink",
    "plum",
    "powderblue",
    "purple",
    "rebeccapurple",
    "red",
    "rosybrown",
    "royalblue",
    "saddlebrown",
    "salmon",
    "sandybrown",
    "seagreen",
    "seashell",
    "sienna",
    "silver",
    "skyblue",
    "slateblue",
    "slategray",
    "slategrey",
    "snow",
    "springgreen",
    "steelblue",
    "tan",
    "teal",
    "thistle",
    "tomato",
    "turquoise",
    "violet",
    "wheat",
    "white",
    "whitesmoke",
    "yellow",
    "yellowgreen",
    "transparent",
    "currentcolor",
];

fn is_named_color(word: &str) -> bool {
    let lowered = word.to_ascii_lowercase();
    NAMED_COLORS.contains(&lowered.as_str())
}

pub fn build_diagnostics(diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    diagnostics
        .into_iter()
        .map(|mut diagnostic| {
            diagnostic.severity = Severity::Error;
            diagnostic
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{Event, Model, Placement, box_color_label, preprocess, resolve};
    use crate::diag::Diagnostic;
    use crate::syntax::sequence::parse;

    fn model_of(source: &str) -> (Model, Vec<Diagnostic>) {
        let parsed = parse(source, &[]);
        resolve(source, &parsed.document)
    }

    fn pairs(fields: &[(String, String)]) -> Vec<(&str, &str)> {
        fields
            .iter()
            .map(|(key, value)| (key.as_str(), value.as_str()))
            .collect()
    }

    fn split(raw: &str) -> (Option<String>, String) {
        box_color_label(raw)
    }

    #[test]
    fn colour_function_runs_to_the_last_parenthesis() {
        assert_eq!(
            split("rgb(23, 124, 207) Profiles"),
            (
                Some("rgb(23, 124, 207)".to_string()),
                "Profiles".to_string()
            )
        );
        assert_eq!(
            split("rgb (1, 2, 3) T"),
            (Some("rgb (1, 2, 3)".to_string()), "T".to_string())
        );
    }

    #[test]
    fn named_colour_is_the_leading_word() {
        assert_eq!(
            split("Green New serwis"),
            (Some("Green".to_string()), "New serwis".to_string())
        );
        assert_eq!(split("Aqua"), (Some("Aqua".to_string()), String::new()));
    }

    #[test]
    fn other_text_is_the_whole_title() {
        assert_eq!(split("Group 1"), (None, "Group 1".to_string()));
        assert_eq!(split("\"Group\""), (None, "\"Group\"".to_string()));
        assert_eq!(split("rgb(1,2"), (None, "rgb(1,2".to_string()));
        assert_eq!(split("#fff Title"), (None, "#fff Title".to_string()));
    }

    #[test]
    fn note_placement_folds_ascii_case_of_the_keyword() {
        let source = "sequenceDiagram\nNote RIGHT OF A: x\nnote right of A: y\nnote over A,B: z\nNOTE Left Of A: w\nNote OVER A: v\n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let placements: Vec<Placement> = model
            .events
            .iter()
            .filter_map(|event| match event {
                Event::Note(note) => Some(note.placement),
                _ => None,
            })
            .collect();
        assert_eq!(
            placements,
            [
                Placement::RightOf,
                Placement::RightOf,
                Placement::Over,
                Placement::LeftOf,
                Placement::Over
            ]
        );
    }

    #[test]
    fn metadata_alias_and_properties_come_from_a_yaml_mapping() {
        let source = "sequenceDiagram\nparticipant R@{ alias: Jobs }\nparticipant S@{ x: 1 }\nparticipant L@{ label: Kept }\n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(model.actors[0].label, "Jobs");
        assert_eq!(pairs(&model.actors[1].properties), [("x", "1")]);
        assert_eq!(model.actors[2].label, "L", "only the alias key renames");
        assert_eq!(pairs(&model.actors[2].properties), [("label", "Kept")]);
    }

    #[test]
    fn metadata_on_one_line_holds_several_comma_separated_keys() {
        let source = "sequenceDiagram\nparticipant API@{ \"type\": \"boundary\", \"alias\": \"Public API\", \"x\": 1 }\nparticipant Q@{ type: queue, alias: Jobs }\n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(model.actors[0].kind, "boundary");
        assert_eq!(model.actors[0].label, "Public API");
        assert_eq!(pairs(&model.actors[0].properties), [("x", "1")]);
        assert_eq!(model.actors[1].kind, "queue");
        assert_eq!(model.actors[1].label, "Jobs");
    }

    #[test]
    fn explicit_alias_beats_metadata_alias_unless_it_equals_the_id() {
        let source = "sequenceDiagram\nparticipant API@{ \"alias\": \"Internal\" } as External\nparticipant DB@{ \"alias\": \"Store\" } as DB\n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(model.actors[0].label, "External");
        assert_eq!(pairs(&model.actors[0].properties), [("alias", "Internal")]);
        assert_eq!(model.actors[1].label, "Store");
    }

    #[test]
    fn metadata_on_several_lines_reads_a_block_mapping() {
        let source = "sequenceDiagram\nparticipant O@{\ntype: database\nalias: Oh\n}\n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(model.actors[0].kind, "database");
        assert_eq!(model.actors[0].label, "Oh");
    }

    #[test]
    fn indented_metadata_on_several_lines_is_rejected_like_upstream() {
        for (source, span) in [
            (
                "sequenceDiagram\nparticipant A@{\n  type: database\n  alias: Disk\n}\n",
                (51, 57),
            ),
            (
                "sequenceDiagram\nparticipant A@{\n  type: database\n  type: queue\n}\n",
                (51, 56),
            ),
        ] {
            let (model, diagnostics) = model_of(source);
            assert_eq!(diagnostics.len(), 1, "{source:?}: {diagnostics:?}");
            assert_eq!(diagnostics[0].code, "config/malformed");
            assert_eq!(diagnostics[0].message, "malformed config value");
            assert_eq!(
                (diagnostics[0].span.start, diagnostics[0].span.end),
                span,
                "{source:?}"
            );
            assert_eq!(
                model.actors[0].kind, "participant",
                "a rejected body has no model effect"
            );
        }
    }

    #[test]
    fn metadata_reader_diagnostics_reach_the_source_spans() {
        for (source, message, span) in [
            (
                "sequenceDiagram\nparticipant A@{ type: database, type: queue }\n",
                "duplicate key",
                (48, 52),
            ),
            (
                "sequenceDiagram\nparticipant A@{\ntype: database\ntype: queue\n}\n",
                "duplicate key",
                (47, 51),
            ),
            (
                "sequenceDiagram\nparticipant A@{ type: x, }\n",
                "malformed config value",
                (41, 42),
            ),
            (
                "sequenceDiagram\nparticipant A@{ type: x,\n}\n",
                "malformed config value",
                (41, 42),
            ),
            (
                "sequenceDiagram\nparticipant A@{ \"type: \"entity\" }\n",
                "malformed config value",
                (40, 49),
            ),
        ] {
            let (_, diagnostics) = model_of(source);
            assert_eq!(diagnostics.len(), 1, "{source:?}: {diagnostics:?}");
            assert_eq!(diagnostics[0].code, "config/malformed", "{source:?}");
            assert_eq!(diagnostics[0].message, message, "{source:?}");
            assert_eq!(
                (diagnostics[0].span.start, diagnostics[0].span.end),
                span,
                "{source:?}"
            );
        }
    }

    #[test]
    fn link_without_at_sign_keeps_the_whole_text_as_the_url() {
        let source = "sequenceDiagram\nlink A: foo\nlink B: @url\nlink C: éé@ u\nlink D: abc  \n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(pairs(&model.actors[0].links), [("f", "foo")]);
        assert_eq!(pairs(&model.actors[1].links), [("@ur", "url")]);
        assert_eq!(pairs(&model.actors[2].links), [("é", "u")]);
        assert_eq!(pairs(&model.actors[3].links), [("a", "abc")]);
    }

    #[test]
    fn repeated_link_label_replaces_the_earlier_url() {
        let source = "sequenceDiagram\nlink A: Docs @ https://one.dev\nlink A: Wiki @ https://wiki.dev\nlink A: Docs @ https://two.dev\nlinks A: {\"Wiki\": \"https://three.dev\"}\n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(
            pairs(&model.actors[0].links),
            [("Docs", "https://two.dev"), ("Wiki", "https://three.dev")]
        );
    }

    #[test]
    fn properties_and_details_json_forms_map_onto_properties_and_links() {
        let source = "sequenceDiagram\nproperties A: {\"p\": \"v\", \"q\": true, \"n\": null, \"o\": {\"x\": 1}, \"a\": [1], \"d\": 1.5}\ndetails B: {\"properties\": {\"k\": \"v\"}, \"links\": {\"L\": \"https://l.dev\"}, \"other\": 1}\ndetails B: {\"properties\": {\"k\": \"w\"}}\ndetails C: {\"k\": \"v\"}\ndetails D: element-id\nproperties E: [1]\n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(
            pairs(&model.actors[0].properties),
            [("p", "v"), ("q", "true"), ("d", "1.5")]
        );
        assert_eq!(pairs(&model.actors[1].properties), [("k", "w")]);
        assert_eq!(pairs(&model.actors[1].links), [("L", "https://l.dev")]);
        assert!(
            model.actors[2].properties.is_empty(),
            "flat details has no properties member"
        );
        assert!(
            model.actors[3].properties.is_empty(),
            "a reference that is not JSON has no effect"
        );
        assert!(
            model.actors[4].properties.is_empty(),
            "a JSON array has no effect"
        );
    }

    #[test]
    fn link_statements_drop_the_colon_before_their_text() {
        let source = "sequenceDiagram\nlink A: Dash @ https://x.dev\nlink B: wrap: Wrapped @ https://w.dev\nlinks C: {\"k\": \"https://k.dev\", \"n\": 2}\nproperties D: {\"p\": \"v\", \"q\": true}\nproperties D: {\"p\": \"w\"}\ndetails E: {\"properties\": {\"d\": \"v\"}}\nlinks F: not json\n";
        let (model, diagnostics) = model_of(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(pairs(&model.actors[0].links), [("Dash", "https://x.dev")]);
        assert_eq!(
            pairs(&model.actors[1].links),
            [("Wrapped", "https://w.dev")]
        );
        assert_eq!(
            pairs(&model.actors[2].links),
            [("k", "https://k.dev"), ("n", "2")]
        );
        assert_eq!(
            pairs(&model.actors[3].properties),
            [("p", "w"), ("q", "true")]
        );
        assert_eq!(pairs(&model.actors[4].properties), [("d", "v")]);
        assert!(
            model.actors[5].links.is_empty(),
            "malformed JSON has no model effect"
        );
    }

    #[test]
    fn accessibility_block_drops_removed_comment_lines() {
        let with_comment = "sequenceDiagram\naccDescr {\nfirst\n%% c\nsecond\n}\nA->>B: x\n";
        let removed = preprocess(with_comment).removed;
        let parsed = parse(with_comment, &removed);
        let (model, diagnostics) = resolve(with_comment, &parsed.document);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(model.acc_descr, "first\nsecond");
    }
}
