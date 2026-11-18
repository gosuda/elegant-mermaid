//! The `@{ ... }` node metadata of a kanban item: reading, conversion, and error spans.

use super::js::{convertible, js_string, truthy};
use super::{C_INVALID_SHAPE, C_MALFORMED_METADATA, Node, Resolver, decode};
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry, parse_config_yaml};
use crate::syntax::kanban::ast::ShapeData;
use crate::syntax::kanban::diagnostic;

const MALFORMED_MESSAGE: &str = "invalid node metadata";
type Setter = fn(&mut Node, String);

pub(super) struct Reading {
    input: String,
    at: Vec<usize>,
    span: Span,
    wrapped: bool,
}

impl Reading {
    fn new(data: &ShapeData) -> Self {
        let mut body = String::new();
        let mut at = Vec::new();
        for token in &data.tokens {
            let last = token.span.end.saturating_sub(1).max(token.span.start);
            at.extend((0..token.text.len()).map(|i| (token.span.start + i).min(last)));
            body.push_str(&token.text);
        }
        if body.contains(['\r', '\n']) {
            return Self {
                input: body,
                at,
                span: data.span,
                wrapped: false,
            };
        }
        let mut wrapped = Vec::with_capacity(at.len() + 2);
        wrapped.push(data.span.start);
        wrapped.extend(at);
        wrapped.push(data.span.end.saturating_sub(1).max(data.span.start));
        Self {
            input: format!("{{{body}}}"),
            at: wrapped,
            span: data.span,
            wrapped: true,
        }
    }

    fn blank(&self) -> bool {
        if self.wrapped {
            return false;
        }
        !self.input.split_inclusive('\n').any(|line| {
            let trimmed = line.trim_start_matches([' ', '\t', '\r', '\n']);
            !trimmed.is_empty() && !trimmed.starts_with('#')
        })
    }

    fn source_span(&self, start: usize, end: usize) -> Span {
        let Some(last) = self.at.len().checked_sub(1) else {
            return self.span;
        };
        let from = self
            .at
            .get(start.min(last))
            .copied()
            .unwrap_or(self.span.start);
        let to = if end > start {
            self.at
                .get(end.min(self.at.len()) - 1)
                .map_or(from, |at| at + 1)
        } else {
            from
        };
        Span {
            start: from,
            end: to.min(self.span.end).max(from),
        }
    }
}

impl Resolver<'_> {
    pub(super) fn apply_metadata(&mut self, node: &mut Node, data: &ShapeData) -> bool {
        let reading = Reading::new(data);
        let (document, diagnostics) = parse_config_yaml(&reading.input, 0, reading.input.len());
        if !diagnostics.is_empty() || reading.blank() || document == ConfigValue::Null {
            self.report(C_MALFORMED_METADATA, MALFORMED_MESSAGE, data.span);
            return false;
        }
        let ConfigValue::Mapping(entries) = &document else {
            return true;
        };
        if let Some(shape) = field(entries, "shape")
            && truthy(&shape.value)
            && invalid_shape(&shape.value)
        {
            self.invalid_shape(&reading, shape);
            return false;
        }
        self.convert(node, entries, data.span)
    }

    fn convert(&mut self, node: &mut Node, entries: &[Entry], span: Span) -> bool {
        let targets: [(&str, Setter); 4] = [
            ("label", |node, text| node.label = decode(&text)),
            ("icon", |node, text| node.icon = text),
            ("assigned", |node, text| node.assigned = text),
            ("ticket", |node, text| node.ticket = text),
        ];
        for (key, into) in targets {
            let Some(entry) = field(entries, key) else {
                continue;
            };
            if !truthy(&entry.value) {
                continue;
            }
            if !convertible(&entry.value) {
                self.report(C_MALFORMED_METADATA, MALFORMED_MESSAGE, span);
                return false;
            }
            into(node, js_string(&entry.value));
        }
        if let Some(entry) = field(entries, "priority")
            && truthy(&entry.value)
        {
            node.priority = js_string(&entry.value);
            node.has_priority = true;
        }
        true
    }

    fn invalid_shape(&mut self, reading: &Reading, shape: &Entry) {
        let (start, end) = value_span(&reading.input, shape.key_span.end);
        let span = self.snap(reading.source_span(start, end));
        let message = format!(
            "invalid shape {}; shape names must be lowercase without underscores",
            js_string(&shape.value)
        );
        self.report(C_INVALID_SHAPE, &message, span);
    }

    fn snap(&self, mut span: Span) -> Span {
        while span.start > 0
            && span.start < self.source.len()
            && !self.source.is_char_boundary(span.start)
        {
            span.start -= 1;
        }
        while span.end < self.source.len() && !self.source.is_char_boundary(span.end) {
            span.end += 1;
        }
        span
    }

    fn report(&mut self, code: &'static str, message: &str, span: Span) {
        self.diagnostics
            .push(diagnostic(code, message.to_owned(), span));
    }
}

fn field<'a>(entries: &'a [Entry], key: &str) -> Option<&'a Entry> {
    entries.iter().rfind(|entry| entry.key == key)
}

fn invalid_shape(value: &ConfigValue) -> bool {
    match value {
        ConfigValue::String(text) => text.to_lowercase() != *text || text.contains('_'),
        _ => true,
    }
}

fn value_span(input: &str, key_end: usize) -> (usize, usize) {
    let bytes = input.as_bytes();
    let colon = skip_blanks(bytes, key_end);
    if bytes.get(colon) != Some(&b':') {
        return (key_end, key_end);
    }
    let start = skip_blanks(bytes, colon + 1);
    if matches!(bytes.get(start), Some(b'"' | b'\'')) {
        return (start, quoted_end(bytes, start));
    }
    let mut end = start;
    while end < bytes.len() && !plain_ends(bytes, end) {
        end += 1;
    }
    while end > start && matches!(bytes.get(end - 1), Some(b' ' | b'\t')) {
        end -= 1;
    }
    (start, end)
}

fn skip_blanks(bytes: &[u8], mut at: usize) -> usize {
    while matches!(bytes.get(at), Some(b' ' | b'\t')) {
        at += 1;
    }
    at
}

fn plain_ends(bytes: &[u8], at: usize) -> bool {
    match bytes.get(at) {
        Some(b',' | b'\r' | b'\n' | b'}') => true,
        Some(b'#') => at > 0 && matches!(bytes.get(at - 1), Some(b' ' | b'\t')),
        _ => false,
    }
}

fn quoted_end(bytes: &[u8], start: usize) -> usize {
    let quote = bytes.get(start).copied().unwrap_or(b'"');
    let mut i = start + 1;
    while i < bytes.len() {
        let c = bytes.get(i).copied().unwrap_or(quote);
        if quote == b'"' && c == b'\\' {
            i += 2;
            continue;
        }
        if c == quote {
            if quote == b'\'' && bytes.get(i + 1) == Some(&quote) {
                i += 2;
                continue;
            }
            return i + 1;
        }
        i += 1;
    }
    bytes.len()
}
