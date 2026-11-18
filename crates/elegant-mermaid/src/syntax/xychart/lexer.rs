//! Lexer for the xychart grammar of `spec/grammar/xychart.md`.
//!
//! Modes follow the authority's start conditions. Within a mode the first rule whose
//! pattern matches wins, and a keyword that ends in a word character ends at a word
//! boundary. A line end pops `axis_data` and `data`.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: &'a str,
    pub span: Span,
}

pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    Scanner {
        source,
        removed,
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
    AccTitle,
    AccDescr,
    AccMulti,
    AxisData,
    AxisBand,
    Data,
    DataInner,
}

const PUNCTUATION: &[(u8, &str)] = &[
    (b'[', "SQUARE_BRACES_START"),
    (b']', "SQUARE_BRACES_END"),
    (b':', "COLON"),
    (b'+', "PLUS"),
    (b',', "COMMA"),
    (b'=', "EQUALS"),
    (b'*', "MULT"),
    (b'#', "BRKT"),
    (b'_', "UNDERSCORE"),
    (b'.', "DOT"),
    (b'&', "AMP"),
    (b'-', "MINUS"),
    (b';', "SEMI"),
];

const KEYWORDS: &[(&str, &str, Option<Mode>)] = &[
    ("xychart-beta", "XYCHART", None),
    ("xychart", "XYCHART", None),
    ("x-axis", "X_AXIS", Some(Mode::AxisData)),
    ("y-axis", "Y_AXIS", Some(Mode::AxisData)),
];

fn is_word_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn is_line_byte(c: u8) -> bool {
    c == b'\n' || c == b'\r'
}

fn js_space(c: char) -> bool {
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

struct Scanner<'a, 'r> {
    source: &'a str,
    removed: &'r [Span],
    at: usize,
    opener: usize,
    modes: Vec<Mode>,
    tokens: Vec<Token<'a>>,
}

impl<'a> Scanner<'a, '_> {
    fn bytes(&self) -> &'a [u8] {
        self.source.as_bytes()
    }

    fn mode(&self) -> Mode {
        self.modes.last().copied().unwrap_or(Mode::Initial)
    }

    fn pop(&mut self) {
        self.modes.pop();
    }

    fn push(&mut self, mode: Mode) {
        self.modes.push(mode);
    }

    fn rest(&self) -> &'a str {
        self.source.get(self.at..).unwrap_or("")
    }

    fn slice(&self, from: usize, to: usize) -> &'a str {
        self.source.get(from..to).unwrap_or("")
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = (self.at + length).min(self.source.len());
        self.tokens.push(Token {
            kind,
            text: self.slice(self.at, end),
            span: Span {
                start: self.at,
                end,
            },
        });
        self.at = end;
    }

    fn value(&mut self, kind: &'static str, text: &'a str, start: usize, end: usize) {
        self.tokens.push(Token {
            kind,
            text,
            span: Span { start, end },
        });
    }

    fn run(mut self) -> Vec<Token<'a>> {
        while self.at < self.source.len() {
            if let Some(end) = self.removed_end() {
                self.at = end;
                continue;
            }
            self.step();
        }
        let end = self.source.len();
        self.tokens.push(Token {
            kind: "EOF",
            text: "",
            span: Span { start: end, end },
        });
        self.tokens
    }

    fn removed_end(&self) -> Option<usize> {
        self.removed
            .iter()
            .find(|span| span.start <= self.at && self.at < span.end)
            .map(|span| span.end)
    }

    fn unterminated(&mut self, opener: &'static str, start: usize) {
        self.value("UNTERMINATED", opener, start, self.source.len());
        self.at = self.source.len();
    }

    fn step(&mut self) {
        match self.mode() {
            Mode::Str => self.lex_string(),
            Mode::Markdown => self.lex_markdown(),
            Mode::AccTitle => self.lex_accessibility_value("acc_title_value"),
            Mode::AccDescr => self.lex_accessibility_value("acc_descr_value"),
            Mode::AccMulti => self.lex_accessibility_block(),
            _ => self.lex_inclusive(),
        }
    }

    fn lex_string(&mut self) {
        let rest = self.rest();
        let Some(i) = rest.find('"') else {
            self.unterminated("\"", self.opener);
            return;
        };
        if i > 0 {
            self.value("STR", &rest[..i], self.opener, self.at + i + 1);
        }
        self.at += i + 1;
        self.pop();
    }

    fn lex_markdown(&mut self) {
        let rest = self.rest();
        let line = rest
            .find(['\n', '\r', '\u{2028}', '\u{2029}'])
            .unwrap_or(rest.len());
        let Some(i) = rest[..line].find("`\"") else {
            self.unterminated("\"`", self.opener);
            return;
        };
        if i > 0 {
            self.value("MD_STR", &rest[..i], self.opener, self.at + i + 2);
        }
        self.at += i + 2;
        self.pop();
    }

    fn line_end(&self) -> usize {
        let rest = self.rest();
        rest.find(['\n', '\r']).unwrap_or(rest.len())
    }

    fn lex_accessibility_value(&mut self, kind: &'static str) {
        let n = self.line_end();
        self.emit(kind, n);
        self.pop();
    }

    fn lex_accessibility_block(&mut self) {
        if self.bytes()[self.at] == b'}' {
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
        self.source
            .get(at..)
            .unwrap_or("")
            .chars()
            .take_while(|c| js_space(*c))
            .map(char::len_utf8)
            .sum()
    }

    fn match_fold(&self, at: usize, word: &str) -> bool {
        self.bytes()
            .get(at..at + word.len())
            .is_some_and(|window| window.eq_ignore_ascii_case(word.as_bytes()))
    }

    fn word(&self, word: &str) -> bool {
        self.match_fold(self.at, word)
            && self
                .bytes()
                .get(self.at + word.len())
                .is_none_or(|c| !is_word_byte(*c))
    }

    fn accessibility_opener(&self, word: &str, separator: u8) -> usize {
        if !self.match_fold(self.at, word) {
            return 0;
        }
        let mut at = self.at + word.len();
        at += self.spaces(at);
        if self.bytes().get(at) != Some(&separator) {
            return 0;
        }
        at += 1;
        at += self.spaces(at);
        at - self.at
    }

    fn digits(&self, at: usize) -> usize {
        self.bytes()
            .get(at..)
            .unwrap_or(&[])
            .iter()
            .take_while(|c| c.is_ascii_digit())
            .count()
    }

    fn fraction(&self, at: usize) -> usize {
        let bytes = self.bytes();
        if bytes.get(at) == Some(&b'.') && bytes.get(at + 1).is_some_and(u8::is_ascii_digit) {
            1 + self.digits(at + 1)
        } else {
            0
        }
    }

    fn number(&self, at: usize) -> usize {
        let start = at;
        let mut at = at;
        if matches!(self.bytes().get(at), Some(b'+' | b'-')) {
            at += 1;
        }
        let whole = self.digits(at);
        at += whole;
        let fraction = self.fraction(at);
        if whole == 0 && fraction == 0 {
            return 0;
        }
        at + fraction - start
    }

    fn lex_inclusive(&mut self) {
        let c = self.bytes()[self.at];
        let mode = self.mode();
        if is_line_byte(c) {
            self.lex_line_end(c, mode);
            return;
        }
        if self.lex_keyword() || self.lex_data(mode, c) || self.lex_quote(c) || self.lex_plain(c) {
            return;
        }
        let length = self.rest().chars().next().map_or(1, char::len_utf8);
        self.emit("INVALID", length);
    }

    fn lex_line_end(&mut self, c: u8, mode: Mode) {
        if matches!(mode, Mode::AxisData | Mode::Data) {
            let n = if c == b'\r' && self.bytes().get(self.at + 1) == Some(&b'\n') {
                2
            } else {
                1
            };
            self.pop();
            self.emit("NEWLINE", n);
            return;
        }
        let n = self.bytes()[self.at..]
            .iter()
            .take_while(|b| is_line_byte(**b))
            .count();
        self.emit("NEWLINE", n);
    }

    fn lex_keyword(&mut self) -> bool {
        if self.word("title") {
            self.emit("title", "title".len());
            return true;
        }
        self.lex_accessibility() || self.lex_chart_keyword()
    }

    fn open_value(&mut self, length: usize, kind: &'static str, mode: Mode) -> bool {
        self.emit(kind, length);
        self.push(mode);
        true
    }

    fn lex_accessibility(&mut self) -> bool {
        let title = self.accessibility_opener("acctitle", b':');
        if title > 0 {
            return self.open_value(title, "acc_title", Mode::AccTitle);
        }
        let line = self.accessibility_opener("accdescr", b':');
        if line > 0 {
            return self.open_value(line, "acc_descr", Mode::AccDescr);
        }
        let block = self.accessibility_opener("accdescr", b'{');
        if block == 0 {
            return false;
        }
        self.opener = self.at + self.slice(self.at, self.at + block).find('{').unwrap_or(0);
        self.at += block;
        self.push(Mode::AccMulti);
        true
    }

    fn lex_chart_keyword(&mut self) -> bool {
        for (text, kind, mode) in KEYWORDS {
            if !self.word(text) {
                continue;
            }
            self.emit(kind, text.len());
            if let Some(mode) = mode {
                self.push(*mode);
            }
            return true;
        }
        for orientation in ["vertical", "horizontal"] {
            if self.match_fold(self.at, orientation) {
                self.emit("CHART_ORIENTATION", orientation.len());
                return true;
            }
        }
        false
    }

    fn lex_data(&mut self, mode: Mode, c: u8) -> bool {
        self.lex_opener(mode, c) || self.lex_number(mode) || self.lex_close(mode, c)
    }

    fn lex_opener(&mut self, mode: Mode, c: u8) -> bool {
        if mode == Mode::AxisData && c == b'[' {
            self.emit("SQUARE_BRACES_START", 1);
            self.push(Mode::AxisBand);
        } else if mode == Mode::AxisData && self.rest().starts_with("-->") {
            self.emit("ARROW_DELIMITER", 3);
        } else if self.word("line") {
            self.open_value("line".len(), "LINE", Mode::Data);
        } else if self.word("bar") {
            self.open_value("bar".len(), "BAR", Mode::Data);
        } else if mode == Mode::Data && c == b'[' {
            self.emit("SQUARE_BRACES_START", 1);
            self.push(Mode::DataInner);
        } else {
            return false;
        }
        true
    }

    fn lex_number(&mut self, mode: Mode) -> bool {
        if !matches!(mode, Mode::AxisData | Mode::DataInner) {
            return false;
        }
        let n = self.number(self.at);
        if n > 0 {
            self.emit("NUMBER_WITH_DECIMAL", n);
        }
        n > 0
    }

    fn lex_close(&mut self, mode: Mode, c: u8) -> bool {
        if c == b']' && matches!(mode, Mode::DataInner | Mode::AxisBand) {
            self.emit("SQUARE_BRACES_END", 1);
            self.pop();
            return true;
        }
        false
    }

    fn lex_quote(&mut self, c: u8) -> bool {
        if c != b'"' {
            return false;
        }
        self.opener = self.at;
        if self.bytes().get(self.at + 1) == Some(&b'`') {
            self.at += 2;
            self.push(Mode::Markdown);
        } else {
            self.at += 1;
            self.push(Mode::Str);
        }
        true
    }

    fn lex_plain(&mut self, c: u8) -> bool {
        if let Some((_, kind)) = PUNCTUATION.iter().find(|(byte, _)| *byte == c) {
            self.emit(kind, 1);
            return true;
        }
        if c.is_ascii_alphabetic() {
            let n = self.bytes()[self.at..]
                .iter()
                .take_while(|b| b.is_ascii_alphabetic())
                .count();
            self.emit("ALPHA", n);
        } else if c.is_ascii_digit() {
            let n = self.digits(self.at);
            self.emit("NUM", n);
        } else {
            let n = self.spaces(self.at);
            if n == 0 {
                return false;
            }
            self.at += n;
        }
        true
    }
}
