//! Semantic resolution of the packet model (`spec/grammar/packet.md`, resolution).
//!
//! Fields resolve in declaration order and stop at the first invalid field, as the
//! upstream database throws at the first one. A model without errors is then split into
//! row pieces by the upstream adapter rules.

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::packet::ast::{Metadata, PacketBlock, Start, Statement, StatementKind};
use crate::syntax::packet::diagnostic;
use crate::syntax::preprocess::preprocess;

const C_RANGE_REVERSED: &str = "packet/range-reversed";
const C_NON_CONTIGUOUS: &str = "packet/non-contiguous";
const C_ZERO_BIT_FIELD: &str = "packet/zero-bit-field";

pub const DEFAULT_BITS_PER_ROW: i64 = 32;
pub const MAX_WORDS: usize = 10_000;
pub const CONFIG_MAX: i64 = 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfigSetting {
    Integer(i64),
    Bool(bool),
    Text(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfigEntry {
    pub key: &'static str,
    pub setting: ConfigSetting,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub index: usize,
    pub start: i64,
    pub end: i64,
    pub bits: i64,
    pub label: String,
    pub span: Span,
    pub start_span: Span,
    pub end_span: Span,
    pub bits_span: Span,
    pub label_span: Span,
    pub has_start: bool,
    pub has_end: bool,
    pub has_bits: bool,
}

#[derive(Debug, Clone)]
pub struct Piece {
    pub field: usize,
    pub row: usize,
    pub start: i64,
    pub end: i64,
    pub bits: i64,
    pub label: String,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub fields: Vec<Field>,
    pub pieces: Vec<Piece>,
    pub rows: usize,
    pub bits_per_row: i64,
    pub show_bits: bool,
    pub descending: bool,
    pub config: Vec<ConfigEntry>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SettingKind {
    Integer,
    Bool,
    Text,
}

struct Setting {
    key: &'static str,
    kind: SettingKind,
    min: i64,
    max: i64,
}

const SETTINGS: &[Setting] = &[
    Setting {
        key: "bitOrder",
        kind: SettingKind::Text,
        min: 0,
        max: 0,
    },
    Setting {
        key: "bitWidth",
        kind: SettingKind::Integer,
        min: 1,
        max: CONFIG_MAX,
    },
    Setting {
        key: "bitsPerRow",
        kind: SettingKind::Integer,
        min: 1,
        max: CONFIG_MAX,
    },
    Setting {
        key: "paddingX",
        kind: SettingKind::Integer,
        min: 0,
        max: CONFIG_MAX,
    },
    Setting {
        key: "paddingY",
        kind: SettingKind::Integer,
        min: 0,
        max: CONFIG_MAX,
    },
    Setting {
        key: "rowHeight",
        kind: SettingKind::Integer,
        min: 1,
        max: CONFIG_MAX,
    },
    Setting {
        key: "showBits",
        kind: SettingKind::Bool,
        min: 0,
        max: 0,
    },
];

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        acc_title: String::new(),
        acc_descr: String::new(),
        title: String::new(),
        fields: Vec::new(),
        pieces: Vec::new(),
        rows: 0,
        bits_per_row: DEFAULT_BITS_PER_ROW,
        show_bits: true,
        descending: false,
        config: Vec::new(),
    };
    let preprocessed = preprocess(source);
    for block in [
        preprocessed.frontmatter.and_then(|f| f.config),
        preprocessed.init_config,
    ]
    .into_iter()
    .flatten()
    {
        read_config(&mut model, &block);
    }
    model.config.sort_by(|a, b| a.key.cmp(b.key));
    model.apply_config();
    let mut resolver = Resolver {
        model,
        diagnostics: Vec::new(),
        last: -1,
    };
    for statement in &document.statements {
        resolver.statement(statement);
    }
    let Resolver {
        mut model,
        diagnostics,
        ..
    } = resolver;
    if diagnostics.is_empty() {
        model.split();
    }
    (model, diagnostics)
}

fn read_config(model: &mut Model, block: &ConfigValue) {
    let ConfigValue::Mapping(entries) = block else {
        return;
    };
    let Some(packet) = entries.iter().find(|entry| entry.key == "packet") else {
        return;
    };
    let ConfigValue::Mapping(fields) = &packet.value else {
        return;
    };
    for field in fields {
        if let Some(entry) = config_entry(field) {
            model.upsert(entry);
        }
    }
}

fn config_entry(field: &Entry) -> Option<ConfigEntry> {
    let setting = SETTINGS.iter().find(|s| s.key == field.key)?;
    let value = &field.value;
    let parsed = match (setting.kind, value) {
        (SettingKind::Bool, ConfigValue::Bool(flag)) => ConfigSetting::Bool(*flag),
        (SettingKind::Text, ConfigValue::String(text))
            if text == "ascending" || text == "descending" =>
        {
            ConfigSetting::Text(text.clone())
        }
        (SettingKind::Integer, ConfigValue::Integer(text)) => {
            let n = text.parse::<i64>().ok()?;
            if n < setting.min || n > setting.max {
                return None;
            }
            ConfigSetting::Integer(n)
        }
        _ => return None,
    };
    Some(ConfigEntry {
        key: setting.key,
        setting: parsed,
    })
}

impl Model {
    fn upsert(&mut self, entry: ConfigEntry) {
        match self.config.iter_mut().find(|e| e.key == entry.key) {
            Some(existing) => *existing = entry,
            None => self.config.push(entry),
        }
    }

    fn apply_config(&mut self) {
        for entry in &self.config {
            match (entry.key, &entry.setting) {
                ("bitsPerRow", ConfigSetting::Integer(n)) => self.bits_per_row = *n,
                ("showBits", ConfigSetting::Bool(flag)) => self.show_bits = *flag,
                ("bitOrder", ConfigSetting::Text(text)) => self.descending = text == "descending",
                _ => {}
            }
        }
    }

    fn split(&mut self) {
        let mut word: Vec<Piece> = Vec::new();
        let mut words = 0usize;
        let mut row = 1i64;
        let fields = std::mem::take(&mut self.fields);
        for f in &fields {
            let mut current = Piece {
                field: f.index,
                row: 0,
                start: f.start,
                end: f.end,
                bits: f.bits,
                label: f.label.clone(),
            };
            while i64::try_from(word.len()).is_ok_and(|n| n <= self.bits_per_row + 1)
                && words < MAX_WORDS
            {
                let (piece, next) = self.fit(&current, row);
                let closes = piece.end + 1 == row * self.bits_per_row;
                word.push(piece);
                if closes {
                    self.flush(std::mem::take(&mut word), &mut words);
                    row += 1;
                }
                let Some(rest) = next else {
                    break;
                };
                current = rest;
            }
        }
        if !word.is_empty() {
            self.flush(word, &mut words);
        }
        self.fields = fields;
        self.rows = words;
    }

    fn flush(&mut self, word: Vec<Piece>, words: &mut usize) {
        for mut piece in word {
            piece.row = *words;
            self.pieces.push(piece);
        }
        *words += 1;
    }

    fn fit(&self, block: &Piece, row: i64) -> (Piece, Option<Piece>) {
        let limit = row * self.bits_per_row;
        if block.end < limit {
            return (block.clone(), None);
        }
        let first = Piece {
            field: block.field,
            row: 0,
            start: block.start,
            end: limit - 1,
            bits: limit - 1 - block.start,
            label: block.label.clone(),
        };
        let rest = Piece {
            field: block.field,
            row: 0,
            start: limit,
            end: block.end,
            bits: block.end - limit,
            label: block.label.clone(),
        };
        (first, Some(rest))
    }
}

struct Resolver {
    model: Model,
    diagnostics: Vec<Diagnostic>,
    last: i64,
}

impl Resolver {
    fn statement(&mut self, statement: &Statement) {
        if !self.diagnostics.is_empty() {
            return;
        }
        match &statement.kind {
            StatementKind::Metadata(node) => self.metadata(node),
            StatementKind::PacketBlock(node) => self.block(statement.span, node),
        }
    }

    fn metadata(&mut self, node: &Metadata) {
        match node.field {
            "title" => self.model.title.clone_from(&node.value),
            "accTitle" => self.model.acc_title.clone_from(&node.value),
            "accDescr" => self.model.acc_descr.clone_from(&node.value),
            _ => {}
        }
    }

    fn block(&mut self, span: Span, node: &PacketBlock) {
        let mut field = new_field(self.model.fields.len(), span, node);
        if let Some((code, message, at)) = self.check(&field) {
            self.diagnostics.push(diagnostic(code, message, at));
            return;
        }
        self.complete(&mut field);
        self.last = field.end;
        self.model.fields.push(field);
    }

    fn check(&self, f: &Field) -> Option<(&'static str, String, Span)> {
        if f.has_start && f.has_end && f.end < f.start {
            return Some((
                C_RANGE_REVERSED,
                format!(
                    "Packet block {} - {} is invalid. End must be greater than start.",
                    f.start, f.end
                ),
                Span {
                    start: f.start_span.start,
                    end: f.end_span.end,
                },
            ));
        }
        let next = self.last + 1;
        let start = if f.has_start { f.start } else { next };
        let shown = if f.has_end { f.end } else { start };
        if start != next {
            return Some((
                C_NON_CONTIGUOUS,
                format!(
                    "Packet block {start} - {shown} is not contiguous. It should start from {next}."
                ),
                f.start_span,
            ));
        }
        if f.has_bits && f.bits == 0 {
            return Some((
                C_ZERO_BIT_FIELD,
                format!("Packet block {start} is invalid. Cannot have a zero bit field."),
                f.bits_span,
            ));
        }
        None
    }

    fn complete(&self, f: &mut Field) {
        if !f.has_start {
            f.start = self.last + 1;
        }
        if !f.has_end {
            f.end = if f.has_bits {
                f.start + f.bits - 1
            } else {
                f.start
            };
        }
        if !f.has_bits {
            f.bits = f.end - f.start + 1;
        }
    }
}

fn new_field(index: usize, span: Span, node: &PacketBlock) -> Field {
    let mut field = Field {
        index,
        start: 0,
        end: 0,
        bits: 0,
        label: node.label.text.clone(),
        span,
        start_span: Span { start: 0, end: 0 },
        end_span: Span { start: 0, end: 0 },
        bits_span: Span { start: 0, end: 0 },
        label_span: node.label.span,
        has_start: false,
        has_end: false,
        has_bits: false,
    };
    if let Some(o) = node.start {
        field.start = o.value;
        field.start_span = o.span;
        field.has_start = true;
    }
    if let Some(o) = node.end {
        field.end = o.value;
        field.end_span = o.span;
        field.has_end = true;
    }
    if let Some(o) = node.bits {
        field.bits = o.value;
        field.bits_span = o.span;
        field.has_bits = true;
    }
    field
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
