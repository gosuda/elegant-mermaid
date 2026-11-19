use std::borrow::Cow;

use crate::source::{Span, cleaned::Cleaned};

pub const MODES: &[&str] = &[
    "INITIAL",
    "string",
    "token",
    "unqString",
    "style",
    "acc_title",
    "acc_descr",
    "acc_descr_multiline",
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: Cow<'a, str>,
    pub span: Span,
}

pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    lex_cleaned(&Cleaned::new(source, removed))
}

pub(crate) fn lex_cleaned<'a>(cleaned: &Cleaned<'a>) -> Vec<Token<'a>> {
    Scanner {
        cleaned,
        source: cleaned.text(),
        at: 0,
        mode: "INITIAL",
        header_seen: false,
        tokens: Vec::new(),
    }
    .run()
}

struct Scanner<'a, 't> {
    cleaned: &'t Cleaned<'a>,
    source: &'t str,
    at: usize,
    mode: &'static str,
    header_seen: bool,
    tokens: Vec<Token<'a>>,
}

impl<'a, 't> Scanner<'a, 't> {
    fn rest(&self) -> &'t str {
        self.source.get(self.at..).unwrap_or("")
    }
    fn emit(&mut self, kind: &'static str, length: usize, text: Cow<'a, str>) {
        self.emit_range(kind, self.at, self.at + length, text);
    }
    fn emit_range(&mut self, kind: &'static str, start: usize, end: usize, text: Cow<'a, str>) {
        self.tokens.push(Token {
            kind,
            text,
            span: self.cleaned.span(start, end),
        });
        self.at = end;
    }
    fn raw(&mut self, kind: &'static str, length: usize) {
        let end = (self.at + length).min(self.source.len());
        let text = self.cleaned.cow(self.at, end);
        self.emit(kind, length, text);
    }
    fn run(mut self) -> Vec<Token<'a>> {
        while self.at < self.source.len() {
            let before = self.at;
            self.next();
            if before == self.at {
                let n = self.rest().chars().next().map_or(1, char::len_utf8);
                self.raw("INVALID", n);
            }
        }
        self.raw("EOF", 0);
        self.tokens
    }
    fn next(&mut self) {
        if self.mode == "style" {
            self.style();
            return;
        }
        let s = self.rest();
        if self.title(s) || self.accessibility(s) {
            return;
        }
        let line = line_len(s);
        if let Some(kind) = direction(s.get(..line).unwrap_or("")) {
            self.raw(kind, line);
            return;
        }
        if self.space_or_comment(s) || self.header(s) || self.literal(s) {
            return;
        }
        if s.starts_with('"') {
            self.quoted();
            return;
        }
        self.unquoted(s);
    }
    fn title(&mut self, s: &'t str) -> bool {
        if !prefix(s, "title") {
            return false;
        }
        let tail = s.get(5..).unwrap_or("");
        let Some(c) = tail.chars().next().filter(|c| c.is_whitespace()) else {
            return false;
        };
        let value = tail.get(c.len_utf8()..).unwrap_or("");
        let n = value.find(['#', '\r', '\n', ';']).unwrap_or(value.len());
        if n == 0 {
            return false;
        }
        self.raw("title", 5 + c.len_utf8() + n);
        true
    }
    fn accessibility(&mut self, s: &'t str) -> bool {
        for (name, kind, value_kind) in [
            ("accTitle", "acc_title", "acc_title_value"),
            ("accDescr", "acc_descr", "acc_descr_value"),
        ] {
            if prefix(s, name) && self.accessibility_value(s, name, kind, value_kind) {
                return true;
            }
        }
        false
    }
    fn accessibility_value(
        &mut self,
        s: &'t str,
        name: &str,
        kind: &'static str,
        value_kind: &'static str,
    ) -> bool {
        let tail = s
            .get(name.len()..)
            .unwrap_or("")
            .trim_start_matches(char::is_whitespace);
        if let Some(value) = tail.strip_prefix(':') {
            let value = value.trim_start_matches(char::is_whitespace);
            self.raw(kind, s.len() - value.len());
            self.raw(value_kind, line_len(value));
            return true;
        }
        if kind != "acc_descr" || !tail.starts_with('{') {
            return false;
        }
        self.description_block(s.len() - tail.len());
        true
    }
    fn description_block(&mut self, brace: usize) {
        let s = self.rest();
        let content = s
            .get(brace + 1..)
            .unwrap_or("")
            .trim_start_matches(char::is_whitespace);
        let Some(n) = content.find('}') else {
            self.emit_range(
                "UNTERMINATED",
                self.at + brace,
                self.at + s.len(),
                self.cleaned.cow(self.at + brace, self.at + s.len()),
            );
            return;
        };
        let length = s.len() - content.len() + n + 1;
        let body = self.at + (s.len() - content.len());
        self.emit(
            "acc_descr_multiline_value",
            length,
            self.cleaned.cow(body, body + n),
        );
    }
    fn space_or_comment(&mut self, s: &'t str) -> bool {
        let n = newline_run(s);
        if n > 0 {
            self.raw("NEWLINE", n);
            return true;
        }
        let n = s
            .chars()
            .take_while(|c| c.is_whitespace() && !matches!(c, '\r' | '\n'))
            .map(char::len_utf8)
            .sum::<usize>();
        if n > 0 {
            self.at += n;
            return true;
        }
        if s.starts_with('#') || s.starts_with("%%") {
            self.at += line_len(s);
            return true;
        }
        false
    }
    fn header(&mut self, s: &'t str) -> bool {
        if !self.header_seen && keyword(s, "requirement") && s.starts_with("requirement") {
            self.header_seen = true;
            self.raw("RD", 11);
            return true;
        }
        if s.starts_with("requirementDiagram") && keyword(s, "requirementDiagram") {
            self.header_seen = true;
            self.raw("RD", 18);
            return true;
        }
        false
    }
    fn literal(&mut self, s: &'t str) -> bool {
        for (text, kind) in [
            ("{", "STRUCT_START"),
            ("}", "STRUCT_STOP"),
            (":::", "STYLE_SEPARATOR"),
            (":", "COLONSEP"),
            ("<-", "END_ARROW_L"),
            ("->", "END_ARROW_R"),
            ("-", "LINE"),
        ] {
            if s.starts_with(text) {
                self.raw(kind, text.len());
                return true;
            }
        }
        self.body_keyword(s)
    }
    fn body_keyword(&mut self, s: &'t str) -> bool {
        let Some((text, kind)) = KEYWORDS.iter().find(|(text, _)| keyword(s, text)) else {
            return false;
        };
        if matches!(*kind, "STYLE" | "CLASSDEF" | "CLASS") {
            self.mode = "style";
        }
        self.raw(kind, text.len());
        true
    }
    fn quoted(&mut self) {
        let s = self.rest();
        let content = s.get(1..).unwrap_or("");
        if let Some(n) = content.find('"') {
            self.emit(
                "qString",
                n + 2,
                self.cleaned.cow(self.at + 1, self.at + 1 + n),
            );
        } else {
            self.raw("UNTERMINATED", s.len());
        }
    }
    fn unquoted(&mut self, s: &'t str) {
        if s.as_bytes().first().is_none_or(|b| !word_byte(*b)) {
            self.universal(s);
            return;
        }
        let n = s
            .find([':', ',', '\r', '\n', '{', '<', '>', '-', '='])
            .unwrap_or(s.len());
        let trimmed = s.get(..n).unwrap_or("").trim();
        let lead = s.get(..n).unwrap_or("").len() - s.get(..n).unwrap_or("").trim_start().len();
        self.emit(
            "unqString",
            n,
            self.cleaned
                .cow(self.at + lead, self.at + lead + trimmed.len()),
        );
    }
    fn style(&mut self) {
        let s = self.rest();
        let n = s.bytes().take_while(|b| word_byte(*b)).count();
        if n > 0 {
            self.raw("ALPHA", n);
            return;
        }
        if s.starts_with('"') {
            self.quoted();
            return;
        }
        let n = ending_len(s);
        if n > 0 {
            self.at += n;
            self.mode = "INITIAL";
            return;
        }
        if s.starts_with(' ') {
            self.at += 1;
            return;
        }
        self.style_punctuation(s);
    }
    fn style_punctuation(&mut self, s: &'t str) {
        for (text, kind) in [
            (":", "COLON"),
            (";", "SEMICOLON"),
            ("%", "PERCENT"),
            ("-", "MINUS"),
            ("#", "BRKT"),
        ] {
            if s.starts_with(text) {
                self.raw(kind, 1);
                return;
            }
        }
        self.universal(s);
    }
    fn universal(&mut self, s: &'t str) {
        let n = s.bytes().take_while(|b| word_byte(*b)).count();
        if n > 0 {
            self.raw("ALPHA", n);
        } else if s.starts_with(',') {
            self.raw("COMMA", 1);
        }
    }
}

const KEYWORDS: &[(&str, &str)] = &[
    ("id", "ID"),
    ("text", "TEXT"),
    ("risk", "RISK"),
    ("verifyMethod", "VERIFYMTHD"),
    ("requirement", "REQUIREMENT"),
    ("functionalRequirement", "FUNCTIONAL_REQUIREMENT"),
    ("interfaceRequirement", "INTERFACE_REQUIREMENT"),
    ("performanceRequirement", "PERFORMANCE_REQUIREMENT"),
    ("physicalRequirement", "PHYSICAL_REQUIREMENT"),
    ("designConstraint", "DESIGN_CONSTRAINT"),
    ("low", "LOW_RISK"),
    ("medium", "MED_RISK"),
    ("high", "HIGH_RISK"),
    ("analysis", "VERIFY_ANALYSIS"),
    ("demonstration", "VERIFY_DEMONSTRATION"),
    ("inspection", "VERIFY_INSPECTION"),
    ("test", "VERIFY_TEST"),
    ("element", "ELEMENT"),
    ("contains", "CONTAINS"),
    ("copies", "COPIES"),
    ("derives", "DERIVES"),
    ("satisfies", "SATISFIES"),
    ("verifies", "VERIFIES"),
    ("refines", "REFINES"),
    ("traces", "TRACES"),
    ("type", "TYPE"),
    ("docref", "DOCREF"),
    ("style", "STYLE"),
    ("classDef", "CLASSDEF"),
    ("class", "CLASS"),
];

fn word_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}
fn prefix(s: &str, text: &str) -> bool {
    s.get(..text.len())
        .is_some_and(|p| p.eq_ignore_ascii_case(text))
}
fn keyword(s: &str, text: &str) -> bool {
    prefix(s, text) && s.as_bytes().get(text.len()).is_none_or(|b| !word_byte(*b))
}
fn line_len(s: &str) -> usize {
    s.find(['\r', '\n']).unwrap_or(s.len())
}
fn ending_len(s: &str) -> usize {
    if s.starts_with("\r\n") {
        2
    } else if s.starts_with(['\r', '\n']) {
        1
    } else {
        0
    }
}
fn direction(s: &str) -> Option<&'static str> {
    for (axis, kind) in [
        ("TB", "direction_tb"),
        ("BT", "direction_bt"),
        ("RL", "direction_rl"),
        ("LR", "direction_lr"),
    ] {
        if direction_axis(s, axis) {
            return Some(kind);
        }
    }
    None
}
fn direction_axis(s: &str, axis: &str) -> bool {
    s.char_indices().any(|(p, _)| {
        let text = s.get(p..).unwrap_or("");
        if !prefix(text, "direction") {
            return false;
        }
        let tail = text.get(9..).unwrap_or("");
        let value = tail.trim_start_matches(char::is_whitespace);
        value.len() < tail.len() && prefix(value, axis)
    })
}
fn newline_run(s: &str) -> usize {
    let mut length = 0;
    loop {
        let n = ending_len(s.get(length..).unwrap_or(""));
        if n == 0 {
            return length;
        }
        length += n;
    }
}
