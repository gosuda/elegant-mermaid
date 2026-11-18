//! Lexer for the sequence grammar of `spec/grammar/sequence.md`.
//!
//! One pass in source order; the first rule whose pattern matches at the cursor wins.
//! Keyword rules are INITIAL-only and end at a word boundary. LF, CRLF, and a lone CR
//! all return NEWLINE. Keyword folding is ASCII; actor and label text keep their case.

use std::borrow::Cow;

use crate::source::{Span, cleaned::Cleaned};

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
        opener: 0,
        modes: vec![Mode::Initial],
        tokens: Vec::new(),
    }
    .run()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Initial,
    Id,
    Alias,
    Line,
    Config,
    AccTitle,
    AccDescr,
    AccDescrMultiline,
}

const ARROWS: &[(&str, &str)] = &[
    ("->>", "SOLID_ARROW"),
    ("<<->>", "BIDIRECTIONAL_SOLID_ARROW"),
    ("-->>", "DOTTED_ARROW"),
    ("<<-->>", "BIDIRECTIONAL_DOTTED_ARROW"),
    ("->", "SOLID_OPEN_ARROW"),
    ("-->", "DOTTED_OPEN_ARROW"),
    ("-x", "SOLID_CROSS"),
    ("--x", "DOTTED_CROSS"),
    ("-)", "SOLID_POINT"),
    ("--)", "DOTTED_POINT"),
    ("--|\\", "SOLID_ARROW_TOP_DOTTED"),
    ("--|/", "SOLID_ARROW_BOTTOM_DOTTED"),
    ("--\\\\", "STICK_ARROW_TOP_DOTTED"),
    ("--//", "STICK_ARROW_BOTTOM_DOTTED"),
    ("/|--", "SOLID_ARROW_TOP_REVERSE_DOTTED"),
    ("\\|--", "SOLID_ARROW_BOTTOM_REVERSE_DOTTED"),
    ("//--", "STICK_ARROW_TOP_REVERSE_DOTTED"),
    ("\\\\--", "STICK_ARROW_BOTTOM_REVERSE_DOTTED"),
    ("-|\\", "SOLID_ARROW_TOP"),
    ("-|/", "SOLID_ARROW_BOTTOM"),
    ("-\\\\", "STICK_ARROW_TOP"),
    ("-//", "STICK_ARROW_BOTTOM"),
    ("/|-", "SOLID_ARROW_TOP_REVERSE"),
    ("\\|-", "SOLID_ARROW_BOTTOM_REVERSE"),
    ("//-", "STICK_ARROW_TOP_REVERSE"),
    ("\\\\-", "STICK_ARROW_BOTTOM_REVERSE"),
];

const LOOP_LOOKAHEAD: &[&str] = &[
    "-x", "--x", "-)", "--)", "-|\\", "-\\", "-/", "-//", "-|/", "/|-", "\\|-", "//-", "\\\\-",
    "/|-", "--|\\", "--", "()",
];

const KEYWORDS: &[(&str, &str, Option<Mode>)] = &[
    ("loop", "loop", Some(Mode::Line)),
    ("rect", "rect", Some(Mode::Line)),
    ("opt", "opt", Some(Mode::Line)),
    ("alt", "alt", Some(Mode::Line)),
    ("else", "else", Some(Mode::Line)),
    ("par", "par", Some(Mode::Line)),
    ("par_over", "par_over", Some(Mode::Line)),
    ("and", "and", Some(Mode::Line)),
    ("critical", "critical", Some(Mode::Line)),
    ("option", "option", Some(Mode::Line)),
    ("break", "break", Some(Mode::Line)),
    ("end", "end", None),
    ("left of", "left_of", None),
    ("right of", "right_of", None),
    ("links", "links", None),
    ("link", "link", None),
    ("properties", "properties", None),
    ("details", "details", None),
    ("over", "over", None),
    ("note", "note", None),
    ("activate", "activate", Some(Mode::Id)),
    ("deactivate", "deactivate", Some(Mode::Id)),
    ("sequencediagram", "SD", None),
    ("autonumber", "autonumber", None),
    ("off", "off", None),
    ("box", "box", Some(Mode::Line)),
    ("participant", "participant", Some(Mode::Id)),
    ("actor", "actor_kw", Some(Mode::Id)),
    ("create", "create", None),
    ("destroy", "destroy", Some(Mode::Id)),
];

struct Scanner<'a, 't> {
    cleaned: &'t Cleaned<'a>,
    source: &'t str,
    at: usize,
    opener: usize,
    modes: Vec<Mode>,
    tokens: Vec<Token<'a>>,
}

fn fold(text: &str) -> String {
    text.bytes()
        .take(24)
        .map(|byte| char::from(byte.to_ascii_lowercase()))
        .collect()
}

fn word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

impl<'a, 't> Scanner<'a, 't> {
    fn mode(&self) -> Mode {
        *self.modes.last().unwrap_or(&Mode::Initial)
    }
    fn rest(&self) -> &'t str {
        self.source.get(self.at..).unwrap_or("")
    }
    fn bytes(&self) -> &'t [u8] {
        &self.source.as_bytes()[self.at.min(self.source.len())..]
    }
    fn line_len(&self) -> usize {
        let bytes = self.bytes();
        bytes
            .iter()
            .position(|b| matches!(b, b'\n' | b'\r'))
            .unwrap_or(bytes.len())
    }
    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = (self.at + length).min(self.source.len());
        let text = self.cleaned.cow(self.at, end);
        self.value(kind, length, text);
    }
    fn value(&mut self, kind: &'static str, length: usize, text: Cow<'a, str>) {
        let end = (self.at + length).min(self.source.len());
        self.tokens.push(Token {
            kind,
            text,
            span: self.cleaned.span(self.at, end),
        });
        self.at = end;
    }
    fn trim_spaces(&self, s: &str) -> Cow<'a, str> {
        let lead = s.len() - s.trim_start_matches([' ', '\t']).len();
        let kept = s.trim_matches([' ', '\t']).len();
        self.cleaned.cow(self.at + lead, self.at + lead + kept)
    }
    fn run(mut self) -> Vec<Token<'a>> {
        while self.at < self.source.len() {
            if !self.next() {
                self.invalid_byte();
            }
        }
        let end = self.source.len();
        for kind in ["NEWLINE", "EOF"] {
            self.tokens.push(Token {
                kind,
                text: Cow::Borrowed(""),
                span: self.cleaned.span(end, end),
            });
        }
        self.tokens
    }
    fn invalid_byte(&mut self) {
        let rest = self.rest();
        let length = rest.chars().next().map_or(1, char::len_utf8);
        self.emit("INVALID", length);
    }
    fn next(&mut self) -> bool {
        match self.mode() {
            Mode::AccTitle | Mode::AccDescr => {
                let line = self.line_len();
                self.emit("acc_value", line);
                self.modes.pop();
                true
            }
            Mode::AccDescrMultiline => self.accessibility_block(),
            Mode::Config => self.config(),
            Mode::Id => self.id_mode(),
            Mode::Alias => self.alias_mode(),
            Mode::Line => self.line_mode(),
            Mode::Initial => self.initial_mode(),
        }
    }
    fn accessibility_block(&mut self) -> bool {
        let rest = self.rest();
        match rest.find('}') {
            Some(n) => {
                if n > 0 {
                    self.emit("acc_multiline_value", n);
                }
                self.at += 1;
                self.modes.pop();
                true
            }
            None => {
                self.unterminated("accessibility description");
                true
            }
        }
    }
    fn unterminated(&mut self, what: &'static str) {
        let end = self.source.len();
        self.tokens.push(Token {
            kind: "UNTERMINATED",
            text: Cow::Borrowed(what),
            span: self.cleaned.span(self.opener.min(end), end),
        });
        self.at = end;
    }
    fn config(&mut self) -> bool {
        let rest = self.rest();
        let Some(close) = rest.find('}') else {
            self.unterminated("metadata object");
            return true;
        };
        if close > 0 {
            self.emit("CONFIG_CONTENT", close);
            return true;
        }
        if alias_follows(&rest[1..]) {
            self.emit("CONFIG_END", 1);
            self.modes.pop();
            self.modes.push(Mode::Alias);
            return true;
        }
        self.emit("CONFIG_END", 1);
        self.modes.pop();
        self.modes.pop();
        true
    }
    fn id_mode(&mut self) -> bool {
        if self.space_tab() || self.hash_comment() {
            return true;
        }
        if self.bytes().starts_with(b"@{") {
            self.opener = self.at;
            self.emit("CONFIG_START", 2);
            self.modes.push(Mode::Config);
            return true;
        }
        let rest = self.rest();
        let line = self.line_len();
        let head = &rest[..line];
        if let Some((n, after)) = id_actor_end(head) {
            let text = self.trim_spaces(&head[..n]);
            self.value("ACTOR", n, text);
            match after {
                IdAfter::KeepId => {}
                IdAfter::Alias => self.modes.push(Mode::Alias),
                IdAfter::Pop => {
                    self.modes.pop();
                }
            }
            return true;
        }
        if line > 0 {
            let text = self.trim_spaces(head);
            self.value("INVALID", line, text);
            self.modes.pop();
            return true;
        }
        self.value("INVALID", 0, Cow::Borrowed(""));
        self.modes.pop();
        true
    }
    fn alias_mode(&mut self) -> bool {
        if self.space_tab() || self.hash_comment() {
            return true;
        }
        let rest = self.rest();
        if fold(rest.get(..2).unwrap_or("")).as_str() == "as"
            && rest.as_bytes().get(2).is_none_or(|b| !word_byte(*b))
        {
            self.modes.pop();
            self.modes.pop();
            self.modes.push(Mode::Line);
            self.emit("AS", 2);
            return true;
        }
        self.modes.pop();
        self.modes.pop();
        self.emit("NEWLINE", 0);
        true
    }
    fn line_mode(&mut self) -> bool {
        if self.space_tab() {
            return true;
        }
        let rest = self.rest();
        let line = self.line_len();
        let stop = rest[..line].find(['#', ';']).unwrap_or(line);
        self.modes.pop();
        self.value(
            "restOfLine",
            stop,
            self.cleaned.cow(self.at, self.at + stop),
        );
        true
    }
    fn initial_mode(&mut self) -> bool {
        if self.newline() || self.space_tab() || self.hash_comment() || self.percent_comment() {
            return true;
        }
        if self.number() || self.keyword() || self.accessibility() {
            return true;
        }
        if self.actor() || self.arrow() || self.punct() {
            return true;
        }
        false
    }
    fn newline(&mut self) -> bool {
        let b = self.bytes();
        match b.first() {
            Some(b'\n') => {
                let mut n = 1;
                while b.get(n) == Some(&b'\n') {
                    n += 1;
                }
                self.emit("NEWLINE", n);
                true
            }
            Some(b'\r') => {
                let n = if b.get(1) == Some(&b'\n') { 2 } else { 1 };
                self.emit("NEWLINE", n);
                true
            }
            _ => false,
        }
    }
    fn space_tab(&mut self) -> bool {
        let n = self
            .bytes()
            .iter()
            .take_while(|b| matches!(b, b' ' | b'\t'))
            .count();
        self.at += n;
        n > 0
    }
    fn hash_comment(&mut self) -> bool {
        if self.bytes().first() != Some(&b'#') {
            return false;
        }
        self.at += self.line_len();
        true
    }
    fn percent_comment(&mut self) -> bool {
        let b = self.bytes();
        let skip = if b.starts_with(b"%%") && b.get(2) != Some(&b'{') {
            2
        } else if b.first() != Some(&b'}') && b.len() >= 3 && &b[1..3] == b"%%" {
            1
        } else {
            0
        };
        if skip == 0 {
            return false;
        }
        self.at += self.line_len();
        true
    }
    fn number(&mut self) -> bool {
        let Some(length) = number_length(self.bytes()) else {
            return false;
        };
        self.emit("NUM", length);
        true
    }
    fn keyword(&mut self) -> bool {
        let rest = self.rest();
        let folded = fold(rest);
        for (pattern, kind, mode) in KEYWORDS {
            if !folded.starts_with(pattern) {
                continue;
            }
            let length = pattern.len();
            if rest.as_bytes().get(length).is_some_and(|b| word_byte(*b)) {
                continue;
            }
            if matches!(*kind, "links" | "link" | "properties" | "details")
                && !link_follows(rest.get(length..).unwrap_or(""))
            {
                continue;
            }
            self.emit(kind, length);
            if let Some(mode) = mode {
                self.modes.push(*mode);
            }
            return true;
        }
        self.keyword_title(rest, "title", "title")
            || self.keyword_title(rest, "title:", "legacy_title")
    }
    fn keyword_title(&mut self, rest: &'t str, pattern: &str, kind: &'static str) -> bool {
        if !fold(rest).starts_with(pattern) {
            return false;
        }
        if !matches!(rest.as_bytes().get(pattern.len()), Some(b' ') | Some(b'\t')) {
            return false;
        }
        let line = self.line_len();
        let tail = rest.get(pattern.len() + 1..line).unwrap_or("");
        let stop = tail.find(['#', ';']).unwrap_or(tail.len());
        if stop == 0 {
            return false;
        }
        self.emit(kind, pattern.len() + 1 + stop);
        true
    }
    fn accessibility(&mut self) -> bool {
        let rest = self.rest();
        let folded = fold(rest);
        for (pattern, kind, mode) in [
            ("acctitle", "acc_title", Mode::AccTitle),
            ("accdescr", "acc_descr", Mode::AccDescr),
        ] {
            if !folded.starts_with(pattern) {
                continue;
            }
            let Some(length) = accessibility_length(rest, pattern.len()) else {
                continue;
            };
            self.emit(kind, length);
            self.modes.push(mode);
            return true;
        }
        if folded.starts_with("accdescr")
            && let Some(length) = brace_length(rest, "accdescr".len())
        {
            self.opener = self.at;
            self.at += length;
            self.modes.push(Mode::AccDescrMultiline);
            return true;
        }
        false
    }
    fn actor(&mut self) -> bool {
        let rest = self.rest();
        let line = self.line_len();
        let head = &rest[..line];
        let Some(end) = actor_end(head) else {
            return false;
        };
        let text = self.trim_spaces(&head[..end]);
        self.value("ACTOR", end, text);
        true
    }
    fn arrow(&mut self) -> bool {
        let rest = self.rest();
        for (pattern, kind) in ARROWS {
            if rest.starts_with(pattern) {
                self.emit(kind, pattern.len());
                return true;
            }
        }
        false
    }
    fn punct(&mut self) -> bool {
        let b = self.bytes();
        match b.first() {
            Some(b':') => {
                let line = self.line_len();
                let rest = self.rest();
                let stop = rest[..line].find(['#', ';']).unwrap_or(line);
                self.emit("TXT", stop);
                true
            }
            Some(b'+') => {
                self.emit("+", 1);
                true
            }
            Some(b'-') => {
                self.emit("-", 1);
                true
            }
            Some(b'(') if b.get(1) == Some(&b')') => {
                self.emit("()", 2);
                true
            }
            Some(b',') => {
                self.emit(",", 1);
                true
            }
            Some(b';') => {
                self.emit("NEWLINE", 1);
                true
            }
            _ => false,
        }
    }
}

fn number_length(bytes: &[u8]) -> Option<usize> {
    let digits = |from: usize| -> usize {
        let mut n = 0;
        while bytes.get(from + n).is_some_and(u8::is_ascii_digit) {
            n += 1;
        }
        n
    };
    let whole = digits(0);
    let fraction = |from: usize| -> usize {
        if bytes.get(from) == Some(&b'.') && bytes.get(from + 1).is_some_and(u8::is_ascii_digit) {
            1 + digits(from + 1).min(2)
        } else {
            0
        }
    };
    let mut length = if whole > 0 {
        whole + fraction(whole)
    } else {
        0
    };
    if length == 0 && bytes.first() == Some(&b'.') {
        let tail = digits(1);
        if tail > 0 {
            length = 1 + tail;
        }
    }
    if length == 0 {
        return None;
    }
    if !matches!(bytes.get(length), Some(b' ') | Some(b'\n') | Some(b'\r')) {
        return None;
    }
    Some(length)
}

fn id_actor_end(head: &str) -> Option<(usize, IdAfter)> {
    let tight = plain_id_run(head);
    if tight > 0 {
        if config_follows(&head[tight..]) {
            return Some((tight, IdAfter::KeepId));
        }
        if alias_follows(&head[tight..]) {
            return Some((tight, IdAfter::Alias));
        }
    }
    let run = spaced_id_run(head);
    if run == 0 {
        return None;
    }
    if head[run..].is_empty() || head[run..].starts_with(';') {
        return Some((run, IdAfter::Pop));
    }
    head[..run]
        .rfind('#')
        .filter(|at| *at > 0)
        .map(|at| (at, IdAfter::Pop))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IdAfter {
    KeepId,
    Alias,
    Pop,
}

fn plain_id_run(head: &str) -> usize {
    run_until(head, |c| {
        matches!(c, '<' | '>' | ':' | ',' | ';' | '@' | '\r' | '\n') || c == ' ' || c == '\t'
    })
}

fn spaced_id_run(head: &str) -> usize {
    run_until(head, |c| {
        matches!(c, '<' | '>' | ':' | ',' | ';' | '@' | '\r' | '\n')
    })
}

fn run_until(text: &str, stop: impl Fn(char) -> bool) -> usize {
    let mut n = 0;
    for (index, character) in text.char_indices() {
        if stop(character) {
            break;
        }
        n = index + character.len_utf8();
    }
    n
}

fn actor_end(head: &str) -> Option<usize> {
    let mut n = 0;
    for (index, character) in head.char_indices() {
        if matches!(
            character,
            '/' | '\\' | '+' | '(' | ')' | '<' | '-' | '>' | ':' | ',' | ';' | '\r'
        ) || character == '\n'
        {
            break;
        }
        n = index + character.len_utf8();
    }
    if n == 0 {
        return None;
    }
    let mut end = n;
    while end < head.len() {
        let tail = &head[end..];
        if arrow_ahead(tail) {
            break;
        }
        let bytes = tail.as_bytes();
        let mut hyphens = 0;
        while bytes.get(hyphens) == Some(&b'-') {
            hyphens += 1;
        }
        let run = plain_run(&tail[hyphens..]);
        if run == 0 {
            break;
        }
        end += hyphens + run;
    }
    Some(end)
}

fn plain_run(text: &str) -> usize {
    let mut n = 0;
    for (index, character) in text.char_indices() {
        if matches!(character, '+' | '<' | '-' | '>' | ':' | ',' | ';' | '\r') || character == '\n'
        {
            break;
        }
        n = index + character.len_utf8();
    }
    n
}

fn arrow_ahead(text: &str) -> bool {
    LOOP_LOOKAHEAD
        .iter()
        .any(|pattern| text.starts_with(pattern))
}

fn alias_follows(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut index = 0;
    while bytes.get(index).is_some_and(|b| matches!(b, b' ' | b'\t')) {
        index += 1;
    }
    if index == 0 || fold(text.get(index..index + 2).unwrap_or("")) != "as" {
        return false;
    }
    bytes
        .get(index + 2)
        .is_none_or(|b| matches!(b, b' ' | b'\t' | b'\n' | b'\r'))
}

fn config_follows(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut index = 0;
    while bytes.get(index).is_some_and(|b| matches!(b, b' ' | b'\t')) {
        index += 1;
    }
    text.get(index..).is_some_and(|tail| tail.starts_with("@{"))
}

fn skip_space(bytes: &[u8], from: usize) -> usize {
    let mut index = from;
    while bytes
        .get(index)
        .is_some_and(|b| matches!(b, b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c))
    {
        index += 1;
    }
    index
}

fn accessibility_length(rest: &str, from: usize) -> Option<usize> {
    let bytes = rest.as_bytes();
    let index = skip_space(bytes, from);
    if bytes.get(index) != Some(&b':') {
        return None;
    }
    Some(skip_space(bytes, index + 1))
}

fn brace_length(rest: &str, from: usize) -> Option<usize> {
    let bytes = rest.as_bytes();
    let index = skip_space(bytes, from);
    if bytes.get(index) != Some(&b'{') {
        return None;
    }
    Some(skip_space(bytes, index + 1))
}

fn link_follows(text: &str) -> bool {
    let trimmed = text.trim_start_matches([' ', '\t']);
    if trimmed.len() == text.len() {
        return false;
    }
    trimmed.chars().next().is_some_and(|c| {
        !c.is_whitespace()
            && !matches!(
                c,
                '/' | '\\' | '+' | '(' | ')' | '<' | '>' | ':' | ',' | ';' | '-'
            )
    })
}
