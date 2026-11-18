//! Semantic resolution of the `venn` kind (`spec/grammar/venn.md`): subset, text, and
//! style records, set-count checks, and the honoured config keys. Numbers are integers
//! in thousandths.

use crate::syntax::entities::decode_entities as decode;
use std::collections::{BTreeMap, BTreeSet};

use crate::diag::{Diagnostic, Related};
use crate::scene::DumpValue;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::preprocess::preprocess;
use crate::syntax::venn::ast::{
    IdentifierList, IndentedText, Number, Set as SetStatement, Start, StatementKind, Style,
    StyleValue, Text as TextStatement, Union,
};
use crate::syntax::venn::lexer::{Token, js_space};
use crate::syntax::venn::{self, parser};

const SCALE: i64 = 1000;
const WHOLE_CAP: i64 = 1 << 32;
const CONFIG_KEY: &str = "venn";
const MAX_CANVAS_PX: i64 = 65536;
const MIN_CANVAS_PX: i64 = 4;
const MAX_SETS: usize = 3;
const TITLE_PREFIX: usize = "title".len();
const DEFAULT_SIZE_NUMERATOR: i64 = 10 * SCALE;
const NO_SPAN: Span = Span { start: 0, end: 0 };

const C_NO_SETS: &str = "venn/no-sets";
const C_TOO_MANY: &str = "venn/too-many-sets";
const C_UNION_SHORT: &str = "venn/union-requires-multiple-identifiers";
const C_UNKNOWN_SET: &str = "venn/unknown-set-identifier";
const C_TEXT_NO_SET: &str = "venn/text-requires-set";

#[derive(Debug, Clone)]
pub struct Subset {
    pub span: Span,
    pub sets: Vec<String>,
    pub label: String,
    pub display: String,
    pub size: i64,
}

#[derive(Debug, Clone)]
pub struct Text {
    pub span: Span,
    pub sets: Vec<String>,
    pub id: String,
    pub label: String,
    pub display: String,
}

#[derive(Debug, Clone)]
pub struct StyleEntry {
    pub key: String,
    pub value: String,
}

#[derive(Debug, Clone)]
pub struct StyleRecord {
    pub span: Span,
    pub targets: Vec<String>,
    pub entries: Vec<StyleEntry>,
}

#[derive(Debug, Clone)]
pub struct DistinctSet {
    pub id: String,
    pub display: String,
    pub size: i64,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Declaration {
    pub subset_index: Option<usize>,
    pub rejected_ids: Vec<String>,
    pub union: bool,
    pub span: Span,
    pub size_span: Option<Span>,
    pub non_positive: bool,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub title: String,
    pub title_span: Span,
    pub config: BTreeMap<String, DumpValue>,
    pub subsets: Vec<Subset>,
    pub texts: Vec<Text>,
    pub styles: Vec<StyleRecord>,
    pub header_span: Span,
    pub declarations: Vec<Declaration>,
}

impl Model {
    pub fn sets(&self) -> Vec<DistinctSet> {
        let mut out: Vec<DistinctSet> = Vec::new();
        for subset in &self.subsets {
            let [id] = subset.sets.as_slice() else {
                continue;
            };
            let mut set = DistinctSet {
                id: id.clone(),
                display: subset.display.clone(),
                size: subset.size,
                span: subset.span,
            };
            match out.iter_mut().find(|o| o.id == set.id) {
                Some(existing) => {
                    set.span = existing.span;
                    *existing = set;
                }
                None => out.push(set),
            }
        }
        out
    }

    pub fn integer(&self, key: &str) -> Option<i64> {
        match self.config.get(key) {
            Some(DumpValue::Integer(value)) => Some(*value),
            _ => None,
        }
    }
}

struct Resolver {
    model: Model,
    known: BTreeSet<String>,
    current: Option<Vec<String>>,
    diagnostics: Vec<Diagnostic>,
}

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model {
            title: String::new(),
            title_span: NO_SPAN,
            config: BTreeMap::new(),
            subsets: Vec::new(),
            texts: Vec::new(),
            styles: Vec::new(),
            header_span: document.header.as_ref().map_or(NO_SPAN, |token| token.span),
            declarations: Vec::new(),
        },
        known: BTreeSet::new(),
        current: None,
        diagnostics: Vec::new(),
    };
    resolver.read_config(source);
    for line in &document.document.lines {
        if let Some(statement) = &line.statement {
            resolver.statement(&statement.kind);
        }
    }
    let header = document.header.as_ref().map_or(NO_SPAN, |token| token.span);
    resolver.check_set_count(header);
    (resolver.model, resolver.diagnostics)
}

fn child<'v>(entries: &'v [Entry], key: &str) -> Option<&'v [Entry]> {
    match &entries.iter().find(|entry| entry.key == key)?.value {
        ConfigValue::Mapping(fields) => Some(fields),
        _ => None,
    }
}

fn normalize(text: &str) -> String {
    let trimmed = text.trim_matches(js_space);
    if trimmed.len() >= 2 && trimmed.starts_with('"') && trimmed.ends_with('"') {
        return trimmed[1..trimmed.len() - 1].to_owned();
    }
    trimmed.to_owned()
}

fn normalize_list(list: &IdentifierList) -> Vec<String> {
    list.ids.iter().map(|id| normalize(&id.text)).collect()
}

fn sorted(ids: &[String]) -> Vec<String> {
    let mut out = ids.to_vec();
    out.sort();
    out
}

fn optional_label(token: Option<&Token>) -> String {
    token
        .filter(|token| !token.text.is_empty())
        .map_or_else(String::new, |token| normalize(&token.text))
}

fn style_value(value: &StyleValue) -> String {
    if let Some(string) = &value.string {
        return normalize(&string.text);
    }
    let parts: Vec<&str> = value
        .tokens
        .iter()
        .flat_map(|tokens| tokens.tokens.iter().map(|t| t.text.as_str()))
        .collect();
    normalize(&parts.join(" "))
}

fn default_size(count: usize) -> i64 {
    let square = i64::try_from(count * count).unwrap_or(i64::MAX);
    (2 * DEFAULT_SIZE_NUMERATOR + square) / (2 * square)
}

impl Resolver {
    fn issue(&mut self, code: &'static str, message: String, span: Span, related: &[Span]) {
        let mut diagnostic = venn::diagnostic(code, message, span);
        diagnostic.related = related
            .iter()
            .map(|span| Related {
                span: *span,
                message: "also unknown".to_owned(),
            })
            .collect();
        self.diagnostics.push(diagnostic);
    }

    fn check_set_count(&mut self, header: Span) {
        let sets = self.model.sets();
        if sets.is_empty() {
            self.issue(
                C_NO_SETS,
                "venn diagram has no sets".to_owned(),
                header,
                &[],
            );
        } else if let Some(fourth) = sets.get(MAX_SETS) {
            let span = fourth.span;
            self.issue(
                C_TOO_MANY,
                "venn diagram has more than three sets".to_owned(),
                span,
                &[],
            );
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
            self.read_venn(block);
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

    fn read_venn(&mut self, block: &ConfigValue) {
        let ConfigValue::Mapping(entries) = block else {
            return;
        };
        let Some(venn) = child(entries, CONFIG_KEY) else {
            return;
        };
        for field in venn {
            let ConfigValue::Integer(text) = &field.value else {
                continue;
            };
            if field.key != "width" && field.key != "height" {
                continue;
            }
            if let Some(n) = text
                .parse::<i64>()
                .ok()
                .filter(|n| (MIN_CANVAS_PX..=MAX_CANVAS_PX).contains(n))
            {
                self.model
                    .config
                    .insert(field.key.clone(), DumpValue::Integer(n));
            }
        }
    }

    fn statement(&mut self, kind: &StatementKind) {
        match kind {
            StatementKind::Title(title) => {
                let tail = title.token.text.get(TITLE_PREFIX..).unwrap_or("");
                let skip = tail.chars().next().map_or(0, char::len_utf8);
                self.model.title = decode(tail.get(skip..).unwrap_or("")).trim().to_owned();
                self.model.title_span = title.span;
            }
            StatementKind::Set(set) => self.set(set),
            StatementKind::Union(union) => self.union(union),
            StatementKind::Text(text) => self.explicit_text(text),
            StatementKind::IndentedText(text) => self.indented_text(text),
            StatementKind::Style(style) => self.add_style(style),
        }
    }

    fn set(&mut self, set: &SetStatement) {
        let ids = vec![normalize(&set.id.text)];
        let declaration = self.declaration(false, set.id.span, set.size.as_ref());
        let subset = self.subset(set.span, ids, set.label.as_ref(), set.size.as_ref());
        self.model.declarations[declaration].subset_index = Some(subset);
    }

    fn union(&mut self, union: &Union) {
        let declaration = self.declaration(true, union.ids.span, union.size.as_ref());
        if union.ids.ids.len() < 2 {
            self.model.declarations[declaration].rejected_ids = sorted(&normalize_list(&union.ids));
            self.issue(
                C_UNION_SHORT,
                "union requires multiple identifiers".to_owned(),
                union.ids.span,
                &[],
            );
            return;
        }
        let names = normalize_list(&union.ids);
        let unknown: Vec<usize> = (0..names.len())
            .filter(|i| !self.known.contains(&names[*i]))
            .collect();
        if let Some((first, rest)) = unknown.split_first() {
            self.model.declarations[declaration].rejected_ids = sorted(&names);
            let listed: Vec<&str> = unknown.iter().map(|i| names[*i].as_str()).collect();
            let rest: Vec<Span> = rest.iter().map(|i| union.ids.ids[*i].span).collect();
            self.issue(
                C_UNKNOWN_SET,
                format!("unknown set identifier: {}", listed.join(", ")),
                union.ids.ids[*first].span,
                &rest,
            );
            return;
        }
        let subset = self.subset(union.span, names, union.label.as_ref(), union.size.as_ref());
        self.model.declarations[declaration].subset_index = Some(subset);
    }

    fn declaration(&mut self, union: bool, span: Span, size: Option<&Number>) -> usize {
        let index = self.model.declarations.len();
        self.model.declarations.push(Declaration {
            subset_index: None,
            rejected_ids: Vec::new(),
            union,
            span,
            size_span: size.map(|number| number.span),
            non_positive: size.is_some_and(|number| {
                number.text.starts_with('-')
                    || !number.text.bytes().any(|byte| matches!(byte, b'1'..=b'9'))
            }),
        });
        index
    }

    fn subset(
        &mut self,
        span: Span,
        ids: Vec<String>,
        label: Option<&Token>,
        size: Option<&Number>,
    ) -> usize {
        let count = ids.len();
        let sets = sorted(&ids);
        let mut subset = Subset {
            span,
            sets,
            label: optional_label(label),
            display: String::new(),
            size: size.map_or_else(|| default_size(count), |n| thousandths(&n.text)),
        };
        if !subset.label.is_empty() {
            subset.display = decode(&subset.label);
        }
        if let [only] = subset.sets.as_slice() {
            self.known.insert(only.clone());
            if subset.display.is_empty() {
                subset.display = decode(only);
            }
        }
        self.current = Some(subset.sets.clone());
        let index = self.model.subsets.len();
        self.model.subsets.push(subset);
        index
    }

    fn indented_text(&mut self, text: &IndentedText) {
        let Some(current) = self.current.clone() else {
            self.issue(
                C_TEXT_NO_SET,
                "text requires set".to_owned(),
                text.span,
                &[],
            );
            return;
        };
        self.add_text(
            text.span,
            current,
            &text.tail.id.text,
            text.tail.label.as_ref(),
        );
    }

    fn explicit_text(&mut self, text: &TextStatement) {
        let sets = sorted(&normalize_list(&text.targets));
        self.add_text(text.span, sets, &text.id.text, text.label.as_ref());
    }

    fn add_text(&mut self, span: Span, sets: Vec<String>, id: &str, label: Option<&Token>) {
        let id = normalize(id);
        let label = optional_label(label);
        let display = decode(if label.is_empty() { &id } else { &label });
        self.model.texts.push(Text {
            span,
            sets,
            id,
            label,
            display,
        });
    }

    fn add_style(&mut self, style: &Style) {
        let mut record = StyleRecord {
            span: style.span,
            targets: sorted(&normalize_list(&style.targets)),
            entries: Vec::new(),
        };
        for field in &style.styles.fields {
            let value = style_value(&field.value);
            match record.entries.iter_mut().find(|e| e.key == field.key.text) {
                Some(existing) => existing.value = value,
                None => record.entries.push(StyleEntry {
                    key: field.key.text.clone(),
                    value,
                }),
            }
        }
        self.model.styles.push(record);
    }
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

pub fn parse_and_resolve(source: &str, removed: &[Span]) -> (Model, Vec<Diagnostic>) {
    let parsed = parser::parse(source, removed);
    let (model, mut diagnostics) = resolve(source, &parsed.document);
    diagnostics.extend(parsed.diagnostics);
    (model, diagnostics)
}

#[cfg(test)]
mod tests;
