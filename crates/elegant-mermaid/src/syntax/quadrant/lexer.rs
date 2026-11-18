//! Lexer for the quadrant grammar of `spec/grammar/quadrant.md`.
//!
//! Modes follow the authority's start conditions. Within a mode the first rule whose
//! pattern matches wins. Keywords match with ASCII case folding.

use std::collections::BTreeSet;

use crate::source::Span;

use super::entities::{deleted_semicolons, entity_end};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: &'a str,
    pub span: Span,
    pub content: Span,
}

pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    Scanner {
        source,
        removed,
        deleted: deleted_semicolons(source),
        at: 0,
        opener: 0,
        modes: vec![Mode::Initial],
        tokens: Vec::new(),
    }
    .run()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Initial,
    Str,
    Markdown,
    Title,
    AccTitle,
    AccDescr,
    AccMulti,
    PointStart,
    PointX,
    PointY,
    ClassName,
}

const OTHER_PUNCTUATION: &[u8] = b"!$%'`?\\/";

fn punctuation(c: u8) -> Option<&'static str> {
    Some(match c {
        b':' => "COLON",
        b'+' => "PLUS",
        b',' => "COMMA",
        b'=' => "EQUALS",
        b'*' => "MULT",
        b'#' => "BRKT",
        b'_' => "UNDERSCORE",
        b'.' => "DOT",
        b'&' => "AMP",
        b'-' => "MINUS",
        b';' => "SEMI",
        _ => return None,
    })
}

pub(super) fn is_word_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn is_line_byte(c: u8) -> bool {
    c == b'\n' || c == b'\r'
}

pub(super) fn js_space(c: char) -> bool {
    matches!(
        c,
        '\t' | '\n'
            | '\u{b}'
            | '\u{c}'
            | '\r'
            | ' '
            | '\u{a0}'
            | '\u{1680}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
            | '\u{feff}'
            | '\u{2000}'..='\u{200a}'
    )
}

fn js_line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

struct Scanner<'a, 'r> {
    source: &'a str,
    removed: &'r [Span],
    deleted: BTreeSet<usize>,
    at: usize,
    opener: usize,
    modes: Vec<Mode>,
    tokens: Vec<Token<'a>>,
}

impl<'a> Scanner<'a, '_> {
    fn bytes(&self) -> &'a [u8] {
        self.source.as_bytes()
    }

    fn byte(&self, at: usize) -> Option<u8> {
        self.bytes().get(at).copied()
    }

    fn rest(&self) -> &'a str {
        self.source.get(self.at..).unwrap_or("")
    }

    fn slice(&self, from: usize, to: usize) -> &'a str {
        self.source.get(from..to).unwrap_or("")
    }

    fn mode(&self) -> Mode {
        self.modes.last().copied().unwrap_or(Mode::Initial)
    }

    fn pop(&mut self) {
        if self.modes.len() > 1 {
            self.modes.pop();
        }
    }

    fn push(&mut self, mode: Mode) {
        self.modes.push(mode);
    }

    fn rune_len(&self) -> usize {
        self.rest().chars().next().map_or(1, char::len_utf8)
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = (self.at + length).min(self.source.len());
        let span = Span {
            start: self.at,
            end,
        };
        self.tokens.push(Token {
            kind,
            text: self.slice(self.at, end),
            span,
            content: span,
        });
        self.at = end;
    }

    fn quoted(&mut self, kind: &'static str, text: &'a str, span: Span, content: Span) {
        self.tokens.push(Token {
            kind,
            text,
            span,
            content,
        });
    }

    fn run(mut self) -> Vec<Token<'a>> {
        while self.at < self.source.len() {
            if let Some(end) = self.removed_end(self.at) {
                self.at = end;
                continue;
            }
            if self.deleted.contains(&self.at) {
                self.at += 1;
                continue;
            }
            self.step();
        }
        self.finish();
        let end = self.source.len();
        let span = Span { start: end, end };
        self.tokens.push(Token {
            kind: "EOF",
            text: "",
            span,
            content: span,
        });
        self.tokens
    }

    fn finish(&mut self) {
        match self.mode() {
            Mode::Title => self.emit("title_value", 0),
            Mode::Str => self.unterminated("\"", self.opener),
            Mode::Markdown => self.unterminated("\"`", self.opener),
            Mode::AccMulti => self.unterminated("{", self.opener),
            Mode::PointStart | Mode::PointX | Mode::PointY => self.unterminated("[", self.opener),
            Mode::ClassName => self.unterminated(":::", self.opener),
            _ => {}
        }
    }

    fn removed_end(&self, at: usize) -> Option<usize> {
        self.removed
            .iter()
            .find(|span| span.start <= at && at < span.end)
            .map(|span| span.end)
    }

    fn unterminated(&mut self, opener: &'static str, start: usize) {
        let span = Span {
            start,
            end: self.source.len(),
        };
        self.tokens.push(Token {
            kind: "UNTERMINATED",
            text: opener,
            span,
            content: span,
        });
        self.at = self.source.len();
        self.modes = vec![Mode::Initial];
    }

    fn invalid(&mut self) {
        self.modes = vec![Mode::Initial];
        let width = if self.byte(self.at).is_some_and(is_line_byte) {
            0
        } else {
            self.rune_len()
        };
        self.emit("INVALID", width);
    }

    fn step(&mut self) {
        match self.mode() {
            Mode::Str => self.lex_string(),
            Mode::Markdown => self.lex_markdown(),
            Mode::Title => self.lex_line_value("title_value"),
            Mode::AccTitle => self.lex_line_value("acc_title_value"),
            Mode::AccDescr => self.lex_line_value("acc_descr_value"),
            Mode::AccMulti => self.lex_accessibility_block(),
            Mode::PointStart => self.lex_point_start(),
            Mode::PointX => self.lex_point_x(),
            Mode::PointY => self.lex_point_y(),
            Mode::ClassName => self.lex_class_name(),
            Mode::Initial => self.lex_initial(),
        }
    }

    fn lex_string(&mut self) {
        let rest = self.rest();
        let Some(i) = rest.find('"') else {
            self.unterminated("\"", self.opener);
            return;
        };
        if i > 0 {
            self.quoted(
                "STR",
                rest.get(..i).unwrap_or(""),
                Span {
                    start: self.opener,
                    end: self.at + i + 1,
                },
                Span {
                    start: self.at,
                    end: self.at + i,
                },
            );
        }
        self.at += i + 1;
        self.pop();
    }

    fn lex_markdown(&mut self) {
        let bytes = self.bytes();
        for (j, byte) in bytes.iter().enumerate().skip(self.at) {
            match *byte {
                b'`' if bytes.get(j + 1) == Some(&b'"') => {
                    self.close_markdown(j);
                    return;
                }
                b'`' | b'"' => {
                    self.at = j;
                    self.invalid();
                    return;
                }
                _ => {}
            }
        }
        self.unterminated("\"`", self.opener);
    }

    fn close_markdown(&mut self, close: usize) {
        if close > self.at {
            self.quoted(
                "MD_STR",
                self.slice(self.at, close),
                Span {
                    start: self.opener,
                    end: close + 2,
                },
                Span {
                    start: self.at,
                    end: close,
                },
            );
        }
        self.at = close + 2;
        self.pop();
    }

    fn lex_line_value(&mut self, kind: &'static str) {
        let rest = self.rest();
        let n = rest.find(['\n', '\r']).unwrap_or(rest.len());
        self.emit(kind, n);
        self.pop();
    }

    fn lex_accessibility_block(&mut self) {
        if self.byte(self.at) == Some(b'}') {
            self.at += 1;
            self.pop();
            return;
        }
        let Some(i) = self.rest().find('}') else {
            self.unterminated("{", self.opener);
            return;
        };
        self.emit("acc_descr_multiline_value", i);
    }

    fn spaces(&self, at: usize) -> usize {
        self.source.get(at..).map_or(0, |rest| {
            rest.chars()
                .take_while(|c| js_space(*c))
                .map(char::len_utf8)
                .sum()
        })
    }

    fn blanks(&self, at: usize) -> usize {
        self.bytes()
            .get(at..)
            .map_or(0, |rest| rest.iter().take_while(|b| **b == b' ').count())
    }

    fn match_fold(&self, at: usize, word: &str) -> bool {
        self.bytes()
            .get(at..at + word.len())
            .is_some_and(|head| head.eq_ignore_ascii_case(word.as_bytes()))
    }

    fn word(&self, word: &str) -> bool {
        if !self.match_fold(self.at, word) {
            return false;
        }
        self.byte(self.at + word.len())
            .is_none_or(|b| !is_word_byte(b))
    }

    fn padded(&self, word: &str) -> usize {
        let lead = self.blanks(self.at);
        if !self.match_fold(self.at + lead, word) {
            return 0;
        }
        let end = self.at + lead + word.len();
        end + self.blanks(end) - self.at
    }

    fn delimiter(&self) -> usize {
        let at = self.at + self.blanks(self.at);
        let dashes = self
            .bytes()
            .get(at..)
            .map_or(0, |rest| rest.iter().take_while(|b| **b == b'-').count());
        if dashes < 2 || self.byte(at + dashes) != Some(b'>') {
            return 0;
        }
        let end = at + dashes + 1;
        end + self.blanks(end) - self.at
    }

    fn accessibility_opener(&self, word: &str, separator: u8) -> usize {
        if !self.match_fold(self.at, word) {
            return 0;
        }
        let mut at = self.at + word.len();
        at += self.spaces(at);
        if self.byte(at) != Some(separator) {
            return 0;
        }
        at += 1;
        at += self.spaces(at);
        at - self.at
    }

    fn lex_initial(&mut self) {
        if self.lex_skip()
            || self.lex_newline()
            || self.lex_accessibility()
            || self.lex_keyword()
            || self.lex_quote()
            || self.lex_point()
            || self.lex_text()
        {
            return;
        }
        let width = self.rune_len();
        self.emit("INVALID", width);
    }

    fn skip_line(&mut self, from: usize) {
        let rest = self.source.get(from..).unwrap_or("");
        self.at = from + rest.find(['\n', '\r']).unwrap_or(rest.len());
    }

    fn lex_skip(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with("%%") {
            self.skip_line(self.at + 2);
            return true;
        }
        let Some(first) = rest.chars().next() else {
            return false;
        };
        let size = first.len_utf8();
        let hidden = self.removed_end(self.at + size).is_some();
        if first != '}' && !hidden && rest.get(size..).is_some_and(|tail| tail.starts_with("%%")) {
            self.skip_line(self.at + size + 2);
            return true;
        }
        false
    }

    fn lex_newline(&mut self) -> bool {
        if !self.byte(self.at).is_some_and(is_line_byte) {
            return false;
        }
        let n = self.rest().bytes().take_while(|b| is_line_byte(*b)).count();
        self.emit("NEWLINE", n);
        true
    }

    fn open(&mut self, kind: &'static str, length: usize, mode: Mode) -> bool {
        self.emit(kind, length);
        self.push(mode);
        true
    }

    fn lex_accessibility(&mut self) -> bool {
        if self.word("title") {
            return self.open("title", "title".len(), Mode::Title);
        }
        let n = self.accessibility_opener("acctitle", b':');
        if n > 0 {
            return self.open("acc_title", n, Mode::AccTitle);
        }
        let n = self.accessibility_opener("accdescr", b':');
        if n > 0 {
            return self.open("acc_descr", n, Mode::AccDescr);
        }
        let n = self.accessibility_opener("accdescr", b'{');
        if n == 0 {
            return false;
        }
        let head = self.slice(self.at, self.at + n);
        self.opener = self.at + head.find('{').unwrap_or(0);
        self.at += n;
        self.push(Mode::AccMulti);
        true
    }

    fn lex_keyword(&mut self) -> bool {
        for (word, kind) in [("x-axis", "X-AXIS"), ("y-axis", "Y-AXIS")] {
            let n = self.padded(word);
            if n > 0 {
                self.emit(kind, n);
                return true;
            }
        }
        let n = self.delimiter();
        if n > 0 {
            self.emit("AXIS-TEXT-DELIMITER", n);
            return true;
        }
        for (word, kind) in [
            ("quadrant-1", "QUADRANT_1"),
            ("quadrant-2", "QUADRANT_2"),
            ("quadrant-3", "QUADRANT_3"),
            ("quadrant-4", "QUADRANT_4"),
        ] {
            let n = self.padded(word);
            if n > 0 {
                self.emit(kind, n);
                return true;
            }
        }
        if self.word("classDef") {
            self.emit("CLASSDEF", "classDef".len());
            return true;
        }
        false
    }

    fn lex_quote(&mut self) -> bool {
        if self.byte(self.at) != Some(b'"') {
            return false;
        }
        self.opener = self.at;
        if self.byte(self.at + 1) == Some(b'`') {
            self.at += 2;
            self.push(Mode::Markdown);
            return true;
        }
        self.at += 1;
        self.push(Mode::Str);
        true
    }

    fn lex_point(&mut self) -> bool {
        if self.rest().starts_with(":::") {
            self.opener = self.at;
            self.at += 3;
            self.push(Mode::ClassName);
            return true;
        }
        let mut at = self.at + self.spaces(self.at);
        if self.byte(at) != Some(b':') {
            return self.lex_header();
        }
        at += 1;
        at += self.spaces(at);
        if self.byte(at) != Some(b'[') {
            return self.lex_header();
        }
        self.opener = at;
        at += 1;
        at += self.spaces(at);
        self.open("point_start", at - self.at, Mode::PointStart)
    }

    fn lex_header(&mut self) -> bool {
        let n = self.padded("quadrantChart");
        if n == 0 {
            return false;
        }
        self.emit("QUADRANT", n);
        true
    }

    fn lex_text(&mut self) -> bool {
        let Some(c) = self.byte(self.at) else {
            return false;
        };
        let entity = entity_end(self.source, &self.deleted, self.at);
        if c.is_ascii_alphabetic() {
            let n = self.run_of(|b| b.is_ascii_alphabetic());
            self.emit("ALPHA", n);
        } else if c >= 0x80 {
            let n = self.rest().bytes().take_while(|b| *b >= 0x80).count();
            self.emit("UNICODE_TEXT", n);
        } else if c.is_ascii_digit() {
            let n = self.run_of(|b| b.is_ascii_digit());
            self.emit("NUM", n);
        } else if entity > 0 {
            self.emit("UNICODE_TEXT", entity);
        } else {
            return self.lex_single(c);
        }
        true
    }

    fn run_of(&self, member: impl Fn(u8) -> bool) -> usize {
        1 + self
            .bytes()
            .get(self.at + 1..)
            .map_or(0, |rest| rest.iter().take_while(|b| member(**b)).count())
    }

    fn lex_single(&mut self, c: u8) -> bool {
        if let Some(kind) = punctuation(c) {
            self.emit(kind, 1);
            return true;
        }
        if matches!(c, b' ' | b'\t' | 0x0b | 0x0c) {
            self.emit("SPACE", 1);
        } else if OTHER_PUNCTUATION.contains(&c) {
            self.emit("PUNCTUATION", 1);
        } else {
            return false;
        }
        true
    }

    fn coordinate(&self, at: usize) -> usize {
        match self.byte(at) {
            Some(b'1') => 1,
            Some(b'0') => 1 + self.fraction(at + 1),
            _ => 0,
        }
    }

    fn fraction(&self, at: usize) -> usize {
        let Some(first) = self.source.get(at..).and_then(|rest| rest.chars().next()) else {
            return 0;
        };
        if js_line_terminator(first) || u32::from(first) > 0xffff {
            return 0;
        }
        let size = first.len_utf8();
        let digits = self.bytes().get(at + size..).map_or(0, |rest| {
            rest.iter().take_while(|b| b.is_ascii_digit()).count()
        });
        if digits == 0 { 0 } else { size + digits }
    }

    fn lex_point_start(&mut self) {
        let n = self.coordinate(self.at);
        if n > 0 {
            self.emit("point_x", n);
            self.push(Mode::PointX);
            return;
        }
        let mut at = self.at + self.spaces(self.at);
        if self.byte(at) != Some(b']') {
            self.invalid();
            return;
        }
        at += 1;
        self.at = at + self.blanks(at);
        self.pop();
    }

    fn lex_point_x(&mut self) {
        let mut at = self.at + self.spaces(self.at);
        if self.byte(at) != Some(b',') {
            self.invalid();
            return;
        }
        at += 1;
        self.at = at + self.spaces(at);
        self.pop();
        self.push(Mode::PointY);
    }

    fn lex_point_y(&mut self) {
        let n = self.coordinate(self.at);
        if n == 0 {
            self.invalid();
            return;
        }
        self.pop();
        self.emit("point_y", n);
    }

    fn lex_class_name(&mut self) {
        if !self.byte(self.at).is_some_and(is_word_byte) {
            self.invalid();
            return;
        }
        let n = self.run_of(is_word_byte);
        self.pop();
        self.emit("class_name", n);
    }
}
