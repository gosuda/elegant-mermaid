use std::borrow::Cow;

use crate::source::{Span, cleaned::Cleaned};

pub const MODES: &[&str] = &[
    "INITIAL",
    "block",
    "block_bq",
    "acc_title",
    "acc_descr",
    "acc_descr_multiline",
    "style",
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
        tokens: Vec::new(),
    }
    .run()
}

struct Scanner<'a, 't> {
    cleaned: &'t Cleaned<'a>,
    source: &'t str,
    at: usize,
    mode: &'static str,
    tokens: Vec<Token<'a>>,
}

impl<'a, 't> Scanner<'a, 't> {
    fn rest(&self) -> &'t str {
        self.source.get(self.at..).unwrap_or("")
    }
    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = self.at + length;
        self.tokens.push(Token {
            kind,
            text: self.cleaned.cow(self.at, end),
            span: self.cleaned.span(self.at, end),
        });
        self.at = end;
    }
    fn value(&mut self, kind: &'static str, start: usize, end: usize, text: Cow<'a, str>) {
        self.tokens.push(Token {
            kind,
            text,
            span: self.cleaned.span(start, end),
        });
        self.at = end;
    }
    fn run(mut self) -> Vec<Token<'a>> {
        while self.at < self.source.len() {
            self.next();
        }
        if matches!(self.mode, "acc_title" | "acc_descr") {
            self.accessibility_value();
        }
        self.emit("EOF", 0);
        self.tokens
    }
    fn next(&mut self) {
        match self.mode {
            "acc_title" | "acc_descr" => self.accessibility_value(),
            "style" => self.style(),
            "block" => self.block(),
            _ => self.initial(),
        }
    }
    fn initial(&mut self) {
        let s = self.rest();
        if self.accessibility() {
            return;
        }
        let line = line_len(s);
        if let Some(kind) = direction(s.get(..line).unwrap_or("")) {
            self.emit(kind, line);
            return;
        }
        if self.space_or_newline() || self.quoted() || self.initial_symbol() {
            return;
        }
        if self.keyword() || self.relationship() || self.number() {
            return;
        }
        let n = char_run(s, text_char);
        if n > 0 {
            self.emit("UNICODE_TEXT", n);
            return;
        }
        self.literal();
    }
    fn initial_symbol(&mut self) -> bool {
        for (text, kind) in [
            ("{", "BLOCK_START"),
            ("#", "BRKT"),
            (",", "COMMA"),
            (":::", "STYLE_SEPARATOR"),
            (":", "COLON"),
            ("[", "SQS"),
            ("]", "SQE"),
        ] {
            if self.rest().starts_with(text) {
                self.emit(kind, text.len());
                if kind == "BLOCK_START" {
                    self.mode = "block";
                }
                return true;
            }
        }
        false
    }
    fn keyword(&mut self) -> bool {
        for (text, kind) in [
            ("erDiagram", "ER_DIAGRAM"),
            ("style", "STYLE"),
            ("classDef", "CLASSDEF"),
            ("class", "CLASS"),
            ("subgraph", "SUBGRAPH"),
            ("end", "END"),
        ] {
            if !prefix(self.rest(), text) || !self.keyword_boundary(text, kind) {
                continue;
            }
            let mut n = text.len();
            if kind == "END" {
                n += char_run(self.rest().get(n..).unwrap_or(""), char::is_whitespace);
            }
            self.emit(kind, n);
            if matches!(kind, "STYLE" | "CLASSDEF") {
                self.mode = "style";
            }
            return true;
        }
        false
    }
    fn keyword_boundary(&self, text: &str, kind: &str) -> bool {
        let next = self.rest().get(text.len()..).unwrap_or("").chars().next();
        match kind {
            "ER_DIAGRAM" => {
                self.rest().starts_with(text)
                    && next.is_none_or(|c| !c.is_ascii_alphanumeric() && c != '-' && c != '_')
            }
            "END" => next.is_none_or(|c| !ascii_word(c)),
            _ => true,
        }
    }
    fn relationship(&mut self) -> bool {
        if self.cardinality_word() {
            return true;
        }
        if self.rest().starts_with('1') && contextual_one(self.rest()) {
            self.emit("ONLY_ONE", 1);
            return true;
        }
        if prefix(self.rest(), "u")
            && self
                .rest()
                .get(1..)
                .is_some_and(|s| s.starts_with(['.', '-', '|']))
        {
            self.emit("MD_PARENT", 1);
            return true;
        }
        for (text, kind) in [
            ("..", "NON_IDENTIFYING"),
            ("--", "IDENTIFYING"),
            ("to", "IDENTIFYING"),
            ("optionally to", "NON_IDENTIFYING"),
            (".-", "NON_IDENTIFYING"),
            ("-.", "NON_IDENTIFYING"),
        ] {
            if relationship_prefix(self.rest(), text) {
                self.emit(kind, text.len());
                return true;
            }
        }
        false
    }
    fn cardinality_word(&mut self) -> bool {
        for (text, kind) in [
            ("one or zero", "ZERO_OR_ONE"),
            ("one or more", "ONE_OR_MORE"),
            ("one or many", "ONE_OR_MORE"),
            ("1+", "ONE_OR_MORE"),
            ("|o", "ZERO_OR_ONE"),
            ("zero or one", "ZERO_OR_ONE"),
            ("zero or more", "ZERO_OR_MORE"),
            ("zero or many", "ZERO_OR_MORE"),
            ("0+", "ZERO_OR_MORE"),
            ("}o", "ZERO_OR_MORE"),
            ("many(0)", "ZERO_OR_MORE"),
            ("many(1)", "ONE_OR_MORE"),
            ("many", "ZERO_OR_MORE"),
            ("}|", "ONE_OR_MORE"),
            ("one", "ONLY_ONE"),
            ("only one", "ONLY_ONE"),
            ("||", "ONLY_ONE"),
            ("o|", "ZERO_OR_ONE"),
            ("o{", "ZERO_OR_MORE"),
            ("|{", "ONE_OR_MORE"),
        ] {
            if prefix(self.rest(), text) {
                self.emit(kind, text.len());
                return true;
            }
        }
        false
    }
    fn number(&mut self) -> bool {
        let s = self.rest();
        let n = s.bytes().take_while(u8::is_ascii_digit).count();
        if n == 0 {
            return false;
        }
        let fraction = s
            .get(n + 1..)
            .unwrap_or("")
            .bytes()
            .take_while(u8::is_ascii_digit)
            .count();
        if s.get(n..).is_some_and(|s| s.starts_with('.')) && fraction > 0 {
            self.emit("DECIMAL_NUM", n + 1 + fraction);
        } else if s.starts_with('1') {
            self.emit("ENTITY_ONE", 1);
        } else {
            self.emit("NUM", n);
        }
        true
    }
    fn space_or_newline(&mut self) -> bool {
        let s = self.rest();
        let n = char_run(s, |c| matches!(c, ' ' | '\t'));
        if n > 0 {
            self.at += n;
            return true;
        }
        let n = newline_run(s);
        if n == 0 {
            return false;
        }
        self.emit("NEWLINE", n);
        true
    }
    fn quoted(&mut self) -> bool {
        let s = self.rest();
        let Some(tail) = s.strip_prefix('"') else {
            return false;
        };
        let Some(n) = tail.find('"') else {
            self.value(
                "UNTERMINATED",
                self.at,
                self.source.len(),
                Cow::Borrowed("\""),
            );
            return true;
        };
        let value = tail.get(..n).unwrap_or("");
        let kind = if self.mode == "block" {
            "COMMENT"
        } else if !value.is_empty() && !value.contains(['%', '\r', '\n', '\u{b}', '\u{8}', '\\']) {
            "ENTITY_NAME"
        } else {
            "WORD"
        };
        self.value(
            kind,
            self.at,
            self.at + n + 2,
            self.cleaned.cow(self.at + 1, self.at + 1 + n),
        );
        true
    }
    fn accessibility(&mut self) -> bool {
        for (name, kind) in [("accTitle", "acc_title"), ("accDescr", "acc_descr")] {
            let s = self.rest();
            if !prefix(s, name) {
                continue;
            }
            let tail = s.get(name.len()..).unwrap_or("");
            let ws = char_run(tail, char::is_whitespace);
            let tail = tail.get(ws..).unwrap_or("");
            if tail.starts_with(':') {
                let after = tail.get(1..).unwrap_or("");
                self.emit(
                    kind,
                    name.len() + ws + 1 + char_run(after, char::is_whitespace),
                );
                self.mode = kind;
                return true;
            }
            if kind == "acc_descr" && tail.starts_with('{') {
                self.accessibility_block(name.len() + ws);
                return true;
            }
        }
        false
    }
    fn accessibility_value(&mut self) {
        let kind = if self.mode == "acc_title" {
            "acc_title_value"
        } else {
            "acc_descr_value"
        };
        self.mode = "INITIAL";
        self.emit(kind, line_len(self.rest()));
    }
    fn accessibility_block(&mut self, brace: usize) {
        self.mode = "acc_descr_multiline";
        let start = self.at;
        let body = self.rest().get(brace + 1..).unwrap_or("");
        if let Some(n) = body.find('}') {
            let trimmed = body.get(..n).unwrap_or("").trim_start();
            let body_at = start + brace + 1;
            self.value(
                "acc_descr_multiline_value",
                start,
                start + brace + n + 2,
                self.cleaned.cow(body_at + n - trimmed.len(), body_at + n),
            );
        } else {
            self.value(
                "UNTERMINATED",
                start + brace,
                self.source.len(),
                Cow::Borrowed("{"),
            );
        }
        self.mode = "INITIAL";
    }
    fn block(&mut self) {
        let s = self.rest();
        let ws = char_run(s, char::is_whitespace);
        if ws > 0 {
            self.at += ws;
            return;
        }
        if self.attribute_key() || self.generic_word() {
            return;
        }
        let first = s.chars().next();
        if first.is_some_and(attribute_start) {
            self.emit("ATTRIBUTE_WORD", char_run(s, attribute_char));
            return;
        }
        if s.starts_with('`') {
            self.backtick();
            return;
        }
        if self.quoted() {
            return;
        }
        if s.starts_with('}') {
            self.emit("BLOCK_STOP", 1);
            self.mode = "INITIAL";
            return;
        }
        self.literal();
    }
    fn attribute_key(&mut self) -> bool {
        let before = self.source.get(..self.at).unwrap_or("").chars().next_back();
        if before.is_some_and(ascii_word) {
            return false;
        }
        for key in ["PK", "FK", "UK"] {
            let s = self.rest();
            if prefix(s, key)
                && s.get(2..)
                    .unwrap_or("")
                    .chars()
                    .next()
                    .is_none_or(|c| !ascii_word(c))
            {
                self.emit("ATTRIBUTE_KEY", 2);
                return true;
            }
        }
        false
    }
    fn generic_word(&mut self) -> bool {
        let s = self.rest();
        let line = s.get(..line_len(s)).unwrap_or("");
        let Some(first) = line.find('~') else {
            return false;
        };
        if line
            .get(..first)
            .unwrap_or("")
            .contains(char::is_whitespace)
        {
            return false;
        }
        let Some(last) = line.rfind('~').filter(|last| *last > first) else {
            return false;
        };
        let suffix = char_run(line.get(last + 1..).unwrap_or(""), |c| !c.is_whitespace());
        self.emit("ATTRIBUTE_WORD", last + 1 + suffix);
        true
    }
    fn backtick(&mut self) {
        self.mode = "block_bq";
        let start = self.at;
        let body = self.rest().get(1..).unwrap_or("");
        if let Some(n) = body.find('`') {
            if n == 0 {
                self.at += 2;
            } else {
                self.value(
                    "ATTRIBUTE_WORD",
                    start,
                    start + n + 2,
                    self.cleaned.cow(start + 1, start + 1 + n),
                );
            }
        } else {
            self.value("UNTERMINATED", start, self.source.len(), Cow::Borrowed("`"));
        }
        self.mode = "block";
    }
    fn style(&mut self) {
        let s = self.rest();
        let n = newline_run(s);
        if n > 0 {
            self.emit("NEWLINE", n);
            self.mode = "INITIAL";
            return;
        }
        let ws = char_run(s, char::is_whitespace);
        if ws > 0 {
            self.at += ws;
            return;
        }
        for (text, kind) in [(":", "COLON"), (",", "COMMA"), ("#", "BRKT"), (";", "SEMI")] {
            if s.starts_with(text) {
                self.emit(kind, 1);
                return;
            }
        }
        let n = char_run(s, style_char);
        if n > 0 {
            self.emit("STYLE_TEXT", n);
        } else {
            self.literal();
        }
    }
    fn literal(&mut self) {
        let c = self.rest().chars().next().unwrap_or('\0');
        let kind = [
            "?", ",", ";", "{", "}", "(", ")", "[", "]", "%", ":", "#", "|", "+", "=", "/", "\\",
            "\"", "'", "`", "!", "@", "$", "&", "^", "~", "<", ">", ".", "-",
        ]
        .into_iter()
        .find(|text| self.rest().starts_with(*text))
        .unwrap_or("INVALID");
        self.emit(kind, c.len_utf8());
    }
}

fn prefix(s: &str, text: &str) -> bool {
    s.get(..text.len())
        .is_some_and(|s| s.eq_ignore_ascii_case(text))
}
fn char_run(s: &str, predicate: fn(char) -> bool) -> usize {
    s.char_indices()
        .take_while(|(_, c)| predicate(*c))
        .last()
        .map_or(0, |(i, c)| i + c.len_utf8())
}
fn ascii_word(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}
fn style_char(c: char) -> bool {
    !c.is_ascii() || ascii_word(c) || matches!(c, '-' | '*')
}
fn text_char(c: char) -> bool {
    style_char(c) || c == '.'
}
fn attribute_start(c: char) -> bool {
    c.is_ascii_alphabetic() || matches!(c, '*' | '_') || ('\u{c0}'..='\u{ffff}').contains(&c)
}
fn attribute_char(c: char) -> bool {
    attribute_start(c) || c.is_ascii_digit() || matches!(c, '-' | '[' | ']' | '(' | ')' | '.' | ',')
}
fn line_len(s: &str) -> usize {
    s.find(['\r', '\n']).unwrap_or(s.len())
}
fn newline_run(s: &str) -> usize {
    s.bytes()
        .take_while(|b| matches!(*b, b'\r' | b'\n'))
        .count()
}
fn contextual_one(s: &str) -> bool {
    let tail = s.get(1..).unwrap_or("");
    if ["--", "..", ".-", "-."]
        .iter()
        .any(|line| tail.starts_with(*line))
    {
        return true;
    }
    let n = char_run(tail, char::is_whitespace);
    n > 0
        && tail
            .get(n..)
            .unwrap_or("")
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '"' | '\''))
}
fn direction(line: &str) -> Option<&'static str> {
    for (axis, kind) in [
        ("TB", "direction_tb"),
        ("BT", "direction_bt"),
        ("RL", "direction_rl"),
        ("LR", "direction_lr"),
    ] {
        if direction_axis(line, axis) {
            return Some(kind);
        }
    }
    None
}
fn direction_axis(line: &str, axis: &str) -> bool {
    line.char_indices().any(|(i, _)| {
        let tail = line.get(i..).unwrap_or("");
        if !prefix(tail, "direction") {
            return false;
        }
        let tail = tail.get(9..).unwrap_or("");
        let ws = char_run(tail, char::is_whitespace);
        ws > 0 && prefix(tail.get(ws..).unwrap_or(""), axis)
    })
}

fn relationship_prefix(source: &str, text: &str) -> bool {
    if !prefix(source, text) {
        return false;
    }
    if !text.ends_with("to") {
        return true;
    }
    source
        .get(text.len()..)
        .unwrap_or("")
        .chars()
        .next()
        .is_none_or(|c| !ascii_word(c))
}
