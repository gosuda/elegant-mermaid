use super::lexer_rules::{
    ascii_id, header_boundary, label_structure, line_len, newline_len, unicode_letter,
    word_boundary,
};

use std::borrow::Cow;

use crate::source::{Span, cleaned::Cleaned};

pub const MODES: &[&str] = &[
    "INITIAL",
    "acc_title",
    "acc_descr",
    "acc_descr_multiline",
    "dir",
    "string",
    "md_string",
    "edgeText",
    "text",
    "ellipseText",
    "trapText",
    "click",
    "callbackname",
    "callbackargs",
    "shapeData",
    "shapeDataStr",
    "vertex",
    "href",
    "shapeDataEndBracket",
];
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: Cow<'a, str>,
    pub span: Span,
}
struct Frame {
    mode: &'static str,
    opening: usize,
}
struct Scanner<'a, 'c> {
    cleaned: &'a Cleaned<'c>,
    source: &'a str,
    at: usize,
    modes: Vec<Frame>,
    tokens: Vec<Token<'c>>,
    first_graph: bool,
}
pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    lex_cleaned(&Cleaned::new(source, removed))
}
pub(crate) fn lex_cleaned<'c>(cleaned: &Cleaned<'c>) -> Vec<Token<'c>> {
    Scanner {
        cleaned,
        source: cleaned.text(),
        at: 0,
        modes: Vec::new(),
        tokens: Vec::new(),
        first_graph: true,
    }
    .run()
}
impl<'a, 'c> Scanner<'a, 'c> {
    fn mode(&self) -> &'static str {
        self.modes.last().map_or("INITIAL", |f| f.mode)
    }
    fn push(&mut self, mode: &'static str) {
        self.modes.push(Frame {
            mode,
            opening: self.at,
        });
    }
    fn raw(&mut self, kind: &'static str, n: usize) {
        let len = self.source.len();
        let start = self.at.min(len);
        let text = self.cleaned.cow(start, (self.at + n).min(len));
        self.emit(kind, n, text);
    }
    fn text_of(&self, value: &str) -> Cow<'c, str> {
        let from = value
            .as_ptr()
            .addr()
            .checked_sub(self.source.as_ptr().addr());
        match from {
            Some(from) if !value.is_empty() && from + value.len() <= self.source.len() => {
                self.cleaned.cow(from, from + value.len())
            }
            _ => Cow::Owned(value.to_owned()),
        }
    }
    fn emit(&mut self, kind: &'static str, n: usize, text: Cow<'c, str>) {
        self.tokens.push(Token {
            kind,
            text,
            span: Span {
                start: self.at,
                end: self.at + n,
            },
        });
        self.at += n;
    }
    fn run(mut self) -> Vec<Token<'c>> {
        while self.at < self.source.len() {
            if !self.next() {
                let n = self.tail().chars().next().map_or(1, char::len_utf8);
                self.raw("INVALID", n);
            }
        }
        self.finish();
        let cleaned = self.cleaned;
        for token in &mut self.tokens {
            token.span = cleaned.span(token.span.start, token.span.end);
        }
        self.tokens
    }
    fn tail(&self) -> &'a str {
        self.source.get(self.at..).unwrap_or("")
    }
    fn finish(&mut self) {
        if let Some(f) = self.modes.iter().rev().find(|f| f.mode != "dir") {
            let span = Span {
                start: f.opening,
                end: self.source.len(),
            };
            self.tokens.push(Token {
                kind: "UNTERMINATED",
                text: self.cleaned.cow(span.start, span.end),
                span,
            });
        }
        self.raw("EOF", 0);
    }
    fn next(&mut self) -> bool {
        match self.mode() {
            "dir" => self.header_direction(),
            "string" | "md_string" => self.quoted_value(),
            "edgeText" => self.edge_text(),
            "text" | "ellipseText" | "trapText" => self.label(),
            _ => self.initial(),
        }
    }
    fn initial(&mut self) -> bool {
        let s = self.tail();
        if self.accessibility() || self.metadata() || self.callback() || self.quoted() {
            return true;
        }
        if self.keywords() || self.whole_direction() || self.link_id() || self.punctuation() {
            return true;
        }
        if self.link() || self.open_label() || self.comment() || self.identifier() {
            return true;
        }
        if s.starts_with(['\r', '\n']) {
            self.raw("NEWLINE", newline_len(s));
            return true;
        }
        let Some(c) = s.chars().next().filter(|c| c.is_whitespace()) else {
            return false;
        };
        self.raw("SPACE", c.len_utf8());
        true
    }
    fn accessibility(&mut self) -> bool {
        for (name, kind, value) in [
            ("accTitle", "acc_title", "acc_title_value"),
            ("accDescr", "acc_descr", "acc_descr_value"),
        ] {
            let Some(rest) = self.tail().strip_prefix(name) else {
                continue;
            };
            let rest = rest.trim_start_matches(char::is_whitespace);
            if rest.starts_with(':') {
                let text = rest
                    .get(1..)
                    .unwrap_or("")
                    .trim_start_matches(char::is_whitespace);
                let prefix = self.tail().len() - text.len();
                self.raw(kind, prefix);
                self.raw(value, line_len(self.tail()));
                return true;
            }
            if name == "accDescr" && rest.starts_with('{') {
                let prefix = self.tail().len() - rest.len() + 1;
                self.delimited("acc_descr_multiline_value", prefix, "}");
                return true;
            }
        }
        false
    }
    fn delimited(&mut self, kind: &'static str, prefix: usize, close: &str) {
        let body = self.tail().get(prefix..).unwrap_or("");
        if let Some(n) = body.find(close) {
            let text = self.text_of(body.get(..n).unwrap_or(""));
            self.emit(kind, prefix + n + close.len(), text);
        } else {
            self.raw("UNTERMINATED", self.tail().len());
        }
    }
    fn quoted(&mut self) -> bool {
        if self.tail().starts_with("\"`") {
            self.push("md_string");
            self.at += 2;
            return true;
        }
        if self.tail().starts_with('"') {
            self.push("string");
            self.at += 1;
            return true;
        }
        false
    }
    fn quoted_value(&mut self) -> bool {
        let mode = self.mode();
        let s = self.tail();
        let close = if mode == "md_string" { "`\"" } else { "\"" };
        if mode == "string" && s.starts_with("\"`") {
            return self.quoted();
        }
        if s.starts_with(close) {
            let opening = self.modes.pop().map_or(self.at, |f| f.opening);
            self.at += close.len();
            if let Some(token) = self.tokens.last_mut()
                && token.span.start == opening
            {
                token.span.end = self.at;
            }
            return true;
        }
        let n = if mode == "md_string" {
            s.find(['`', '"']).unwrap_or(s.len())
        } else {
            s.find('"').unwrap_or(s.len())
        };
        if n == 0 {
            return self.quoted();
        }
        let opening = self.modes.last().map_or(self.at, |f| f.opening);
        let start = self.at;
        self.raw(if mode == "md_string" { "MD_STR" } else { "STR" }, n);
        if let Some(token) = self.tokens.last_mut() {
            token.span.start = opening.min(start);
        }
        true
    }
    fn metadata(&mut self) -> bool {
        if !self.tail().starts_with("@{") {
            return false;
        }
        let opening = self.at;
        self.emit("SHAPE_DATA", 2, Cow::Borrowed(""));
        while self.at < self.source.len() {
            if self.metadata_piece() {
                return true;
            }
        }
        self.tokens.push(Token {
            kind: "UNTERMINATED",
            text: self.cleaned.cow(opening, self.source.len()),
            span: Span {
                start: opening,
                end: self.at,
            },
        });
        true
    }
    fn metadata_piece(&mut self) -> bool {
        let s = self.tail();
        if s.starts_with('}') {
            self.at += 1;
            if let Some(t) = self.tokens.last_mut() {
                t.span.end = self.at;
            }
            return true;
        }
        if s.starts_with('"') {
            self.metadata_string();
            return false;
        }
        let n = s.find(['}', '^', '"']).unwrap_or(s.len());
        if n > 0 {
            self.raw("SHAPE_DATA", n);
        } else {
            self.raw("INVALID", 1);
        }
        false
    }
    fn metadata_string(&mut self) {
        self.raw("SHAPE_DATA", 1);
        let n = self.tail().find('"').unwrap_or(self.tail().len());
        if n > 0 {
            self.raw("SHAPE_DATA", n);
        }
        if self.tail().starts_with('"') {
            self.raw("SHAPE_DATA", 1);
        }
    }
    fn callback(&mut self) -> bool {
        let s = self.tail();
        let Some(tail) = s.strip_prefix("call") else {
            return false;
        };
        if !tail.starts_with(char::is_whitespace) {
            return false;
        }
        let name = tail.trim_start_matches(char::is_whitespace);
        let prefix = s.len() - name.len();
        let n = name.find('(').unwrap_or(name.len());
        let text = self.text_of(name.get(..n).unwrap_or(""));
        self.emit("CALLBACKNAME", prefix + n, text);
        if !self.tail().starts_with('(') {
            return true;
        }
        let rest = self.tail().get(1..).unwrap_or("");
        let Some(n) = rest.find(')') else {
            self.raw("UNTERMINATED", self.tail().len());
            return true;
        };
        let value = rest.get(..n).unwrap_or("");
        if value.trim().is_empty() {
            self.at += n + 2;
        } else {
            let text = self.text_of(value);
            self.emit("CALLBACKARGS", n + 2, text);
        }
        true
    }
    fn keywords(&mut self) -> bool {
        let s = self.tail();
        for (literal, kind) in [
            ("style", "STYLE"),
            ("default", "DEFAULT"),
            ("linkStyle", "LINKSTYLE"),
            ("interpolate", "INTERPOLATE"),
            ("classDef", "CLASSDEF"),
            ("class", "CLASS"),
        ] {
            if s.starts_with(literal) && word_boundary(s.get(literal.len()..).unwrap_or("")) {
                self.raw(kind, literal.len());
                return true;
            }
        }
        if self.href_or_click() {
            return true;
        }
        if s.starts_with("agentflow-beta") && header_boundary(s.get(14..).unwrap_or("")) {
            if self.first_graph {
                self.push("dir");
                self.first_graph = false;
            }
            self.raw("GRAPH", 14);
            return true;
        }
        self.remaining_keywords()
    }
    fn href_or_click(&mut self) -> bool {
        let s = self.tail();
        if let Some(t) = s.strip_prefix("href")
            && t.starts_with(char::is_whitespace)
        {
            self.raw("HREF", 4 + t.chars().next().map_or(0, char::len_utf8));
            return true;
        }
        let Some(t) = s.strip_prefix("click") else {
            return false;
        };
        if !t.starts_with(char::is_whitespace) {
            return false;
        }
        let id = t.trim_start_matches(char::is_whitespace);
        let n = id.find(char::is_whitespace).unwrap_or(id.len());
        let text = self.text_of(id.get(..n).unwrap_or(""));
        self.emit("CLICK", s.len() - id.len() + n, text);
        let ws = self
            .tail()
            .chars()
            .next()
            .filter(|c| c.is_whitespace())
            .map_or(0, char::len_utf8);
        self.at += ws;
        true
    }
    fn remaining_keywords(&mut self) -> bool {
        let s = self.tail();
        for (literal, kind) in [
            ("flow", "flow"),
            ("connector", "connector"),
            ("global", "global"),
            ("end", "end"),
            ("_self", "LINK_TARGET"),
            ("_blank", "LINK_TARGET"),
            ("_parent", "LINK_TARGET"),
            ("_top", "LINK_TARGET"),
        ] {
            if !s.starts_with(literal) {
                continue;
            }
            let tail = s.get(literal.len()..).unwrap_or("");
            if !word_boundary(tail) {
                continue;
            }
            let n = if matches!(kind, "global" | "end") {
                literal.len() + tail.len() - tail.trim_start_matches([' ', '\t']).len()
            } else {
                literal.len()
            };
            self.raw(kind, n);
            return true;
        }
        false
    }
    fn header_direction(&mut self) -> bool {
        let s = self.tail();
        let t = s.trim_start_matches(char::is_whitespace);
        let whitespace = s.len() - t.len();
        if s.get(..whitespace)
            .is_some_and(|w| w.contains(['\r', '\n']))
        {
            self.modes.pop();
            self.raw("NODIR", whitespace);
            return true;
        }
        for d in ["LR", "RL", "TB", "BT", "TD", "BR", "<", ">", "^", "v"] {
            if t.starts_with(d) {
                self.modes.pop();
                self.raw("DIR", whitespace + d.len());
                return true;
            }
        }
        false
    }
    fn whole_direction(&mut self) -> bool {
        let s = self.tail();
        let line = s.get(..line_len(s)).unwrap_or("");
        for (axis, kind) in [
            ("TB", "direction_tb"),
            ("BT", "direction_bt"),
            ("RL", "direction_rl"),
            ("LR", "direction_lr"),
            ("TD", "direction_td"),
        ] {
            if line.match_indices("direction").any(|(p, _)| {
                let t = line.get(p + 9..).unwrap_or("");
                t.starts_with(char::is_whitespace)
                    && t.trim_start_matches(char::is_whitespace).starts_with(axis)
            }) {
                self.raw(kind, line.len());
                return true;
            }
        }
        false
    }
    fn link_id(&mut self) -> bool {
        let s = self.tail();
        let n = s.find([' ', '\t', '\r', '\n', '"']).unwrap_or(s.len());
        let run = s.get(..n).unwrap_or("");
        let Some(p) = run.rfind('@') else {
            return false;
        };
        let next = s.get(p + 1..).and_then(|t| t.chars().next());
        if p == 0 || next.is_none_or(|c| matches!(c, '{' | '"')) {
            return false;
        }
        self.raw("LINK_ID", p + 1);
        true
    }
    fn punctuation(&mut self) -> bool {
        let s = self.tail();
        let n = s.bytes().take_while(u8::is_ascii_digit).count();
        if n > 0 {
            self.raw("NUM", n);
            return true;
        }
        for (literal, kind) in [
            ("#", "BRKT"),
            (":::", "STYLE_SEPARATOR"),
            (":", "COLON"),
            ("&", "AMP"),
            (";", "SEMI"),
            (",", "COMMA"),
            ("*", "MULT"),
        ] {
            if s.starts_with(literal) {
                self.raw(kind, literal.len());
                return true;
            }
        }
        false
    }
    fn link(&mut self) -> bool {
        let s = self.tail();
        let t = s.trim_start_matches(char::is_whitespace);
        let prefix = s.len() - t.len();
        let hyphens = t.bytes().take_while(|b| *b == b'-').count();
        let suffix = t.get(hyphens..).unwrap_or("");
        if hyphens >= 2 && suffix.starts_with(['x', '>']) {
            self.modes.pop();
            let rest = suffix.get(1..).unwrap_or("");
            self.raw(
                "LINK",
                prefix + hyphens + 1 + rest.len()
                    - rest.trim_start_matches(char::is_whitespace).len(),
            );
            return true;
        }
        if t.starts_with("--") {
            self.modes.push(Frame {
                mode: "edgeText",
                opening: self.at + prefix,
            });
            let rest = t.get(2..).unwrap_or("");
            self.raw(
                "START_LINK",
                prefix + 2 + rest.len() - rest.trim_start_matches(char::is_whitespace).len(),
            );
            return true;
        }
        self.dotted_link(prefix, t)
    }
    fn dotted_link(&mut self, prefix: usize, t: &str) -> bool {
        let Some(rest) = t.strip_prefix('-') else {
            return false;
        };
        let dots = rest.bytes().take_while(|b| *b == b'.').count();
        let tail = rest.get(dots..).unwrap_or("");
        if dots == 0 || !tail.starts_with('-') {
            return false;
        }
        let after = tail.get(1..).unwrap_or("");
        self.raw(
            "LINK",
            prefix + dots + 2 + after.len() - after.trim_start_matches(char::is_whitespace).len(),
        );
        true
    }
    fn edge_text(&mut self) -> bool {
        let s = self.tail();
        let t = s.trim_start_matches(char::is_whitespace);
        let n = t.bytes().take_while(|b| *b == b'-').count();
        if n >= 2 && t.get(n..).is_some_and(|v| v.starts_with(['x', '>'])) {
            return self.link();
        }
        if self.quoted() || self.open_label() {
            return true;
        }
        if s.starts_with("--") {
            return false;
        }
        self.raw("EDGE_TEXT", s.chars().next().map_or(1, char::len_utf8));
        true
    }
    fn open_label(&mut self) -> bool {
        let s = self.tail();
        if self.mode() == "INITIAL" && s.starts_with("[|") {
            self.raw("VERTEX_WITH_PROPS_START", 2);
            return true;
        }
        if self.mode() == "INITIAL" && s.starts_with('>') {
            self.push("text");
            self.raw("TAGEND", 1);
            return true;
        }
        for (literal, kind, mode) in [
            ("(-", "(-", "ellipseText"),
            ("([", "STADIUMSTART", "text"),
            ("[[", "SUBROUTINESTART", "text"),
            ("[(", "CYLINDERSTART", "text"),
            ("(((", "DOUBLECIRCLESTART", "text"),
            ("[/", "TRAPSTART", "trapText"),
            ("[\\", "INVTRAPSTART", "trapText"),
            ("|", "PIPE", "text"),
            ("(", "PS", "text"),
            ("[", "SQS", "text"),
            ("{", "DIAMOND_START", "text"),
        ] {
            if s.starts_with(literal) {
                self.push(mode);
                self.raw(kind, literal.len());
                return true;
            }
        }
        false
    }
    fn label(&mut self) -> bool {
        if self.label_close() || self.quoted() || self.label_comment() {
            return true;
        }
        if self.open_label() {
            return true;
        }
        let n = self.label_text_len();
        if n == 0 {
            return false;
        }
        self.raw("TEXT", n);
        true
    }
    fn label_close(&mut self) -> bool {
        let choices: &[(&str, &str)] = match self.mode() {
            "ellipseText" => &[("-)", "-)"), ("/)", "-)"), ("))", "-)")],
            "trapText" => &[("\\]", "TRAPEND"), (")]", "TRAPEND"), ("/]", "INVTRAPEND")],
            _ => &[
                ("])", "STADIUMEND"),
                ("]]", "SUBROUTINEEND"),
                (")]", "CYLINDEREND"),
                (")))", "DOUBLECIRCLEEND"),
                ("|", "PIPE"),
                (")", "PE"),
                ("]", "SQE"),
                ("}", "DIAMOND_STOP"),
            ],
        };
        for &(literal, kind) in choices {
            if self.tail().starts_with(literal) {
                self.modes.pop();
                self.raw(kind, literal.len());
                return true;
            }
        }
        false
    }
    fn label_text_len(&self) -> usize {
        let s = self.tail();
        if self.mode() == "ellipseText" {
            return s
                .chars()
                .next()
                .filter(|c| !label_structure("ellipseText", *c))
                .map_or(0, char::len_utf8);
        }
        if self.mode() == "trapText" && s.starts_with(['/', '\\']) {
            return 1;
        }
        s.char_indices()
            .take_while(|(p, c)| {
                !label_structure(self.mode(), *c)
                    && !s.get(*p..).is_some_and(|t| t.starts_with("%%"))
            })
            .last()
            .map_or(0, |(p, c)| p + c.len_utf8())
    }
    fn label_comment(&mut self) -> bool {
        if !self.tail().starts_with("%%") || self.tail().starts_with("%%{") {
            return false;
        }
        self.at += line_len(self.tail());
        true
    }
    fn comment(&mut self) -> bool {
        let s = self.tail();
        let t = s.trim_start_matches([' ', '\t']);
        if !t.starts_with("%%") || t.starts_with("%%{") {
            return false;
        }
        self.raw("COMMENT", line_len(s));
        true
    }
    fn identifier(&mut self) -> bool {
        let s = self.tail();
        for (literal, kind) in [("<", "TAGSTART"), ("^", "UP"), ("v", "DOWN")] {
            if s.starts_with(literal) && (literal != "v" || word_boundary(s.get(1..).unwrap_or("")))
            {
                self.raw(kind, 1);
                return true;
            }
        }
        let n = s
            .char_indices()
            .take_while(|(p, c)| ascii_id(*c, s.get(*p + c.len_utf8()..).unwrap_or("")))
            .last()
            .map_or(0, |(p, c)| p + c.len_utf8());
        if n > 0 {
            self.raw("NODE_STRING", n);
            return true;
        }
        if s.starts_with('-') {
            self.raw("MINUS", 1);
            return true;
        }
        let Some(c) = s.chars().next().filter(|c| unicode_letter(*c)) else {
            return false;
        };
        self.raw("UNICODE_TEXT", c.len_utf8());
        true
    }
}
