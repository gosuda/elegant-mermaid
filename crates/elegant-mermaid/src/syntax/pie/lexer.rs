//! Lexer for the pie grammar of `spec/grammar/pie.md`.
//!
//! One pass in source order. Keywords come first and yield to a longer ID; the terminals
//! follow in the authority order. LF, CRLF, and a lone CR each make one NEWLINE. Hidden
//! terminals (whitespace, comments, removed spans) emit nothing.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

const KEYWORDS: &[&str] = &["showData", "pie", ":"];

pub fn lex(source: &str, removed: &[Span]) -> Vec<Token> {
    Scanner {
        source,
        removed,
        at: 0,
        tokens: Vec::new(),
    }
    .run()
}

struct Scanner<'a> {
    source: &'a str,
    removed: &'a [Span],
    at: usize,
    tokens: Vec<Token>,
}

fn horizontal(byte: u8) -> bool {
    byte == b' ' || byte == b'\t'
}

fn horizontal_run(text: &str) -> usize {
    text.bytes().take_while(|&byte| horizontal(byte)).count()
}

fn line_length(text: &str) -> usize {
    text.find(['\n', '\r']).unwrap_or(text.len())
}

fn comment_cut(line: &str) -> usize {
    line.find("%%").unwrap_or(line.len())
}

fn is_space_byte(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c)
}

fn is_word(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn line_end_char(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

fn collapse_runs(value: &str) -> String {
    let bytes = value.as_bytes();
    let mut out = String::with_capacity(value.len());
    let mut i = 0;
    while i < bytes.len() {
        let run = horizontal_run(value.get(i..).unwrap_or(""));
        match run {
            0 => {
                let step = value
                    .get(i..)
                    .and_then(|rest| rest.chars().next())
                    .map_or(1, char::len_utf8);
                out.push_str(value.get(i..i + step).unwrap_or(""));
                i += step;
            }
            1 => {
                out.push(char::from(bytes.get(i).copied().unwrap_or(b' ')));
                i += 1;
            }
            _ => {
                out.push(' ');
                i += run;
            }
        }
    }
    out
}

fn collapse_line(value: &str) -> String {
    collapse_runs(value.trim_matches(char::is_whitespace))
}

fn collapse_block(value: &str) -> String {
    value
        .split(['\n', '\r'])
        .map(|line| line.trim_matches(char::is_whitespace))
        .filter(|line| !line.is_empty())
        .map(collapse_runs)
        .collect::<Vec<_>>()
        .join("\n")
}

fn id_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    if !bytes.first().copied().is_some_and(is_word) {
        return 0;
    }
    let mut run = 1;
    while bytes.get(run).is_some_and(|&b| is_word(b) || b == b'-') {
        run += 1;
    }
    while run > 1 && bytes.get(run - 1) == Some(&b'-') {
        run -= 1;
    }
    run
}

fn digit_run(text: &str) -> usize {
    text.bytes().take_while(u8::is_ascii_digit).count()
}

fn not_dot(text: &str, at: usize) -> bool {
    text.as_bytes().get(at) != Some(&b'.')
}

fn sign_length(text: &str) -> usize {
    usize::from(text.starts_with('-'))
}

pub(crate) fn float_length(text: &str) -> usize {
    let sign = sign_length(text);
    let rest = text.get(sign..).unwrap_or("");
    let whole = digit_run(rest);
    if whole == 0 || rest.as_bytes().get(whole) != Some(&b'.') {
        return 0;
    }
    let fraction = digit_run(rest.get(whole + 1..).unwrap_or(""));
    if fraction == 0 {
        return 0;
    }
    let end = sign + whole + 1 + fraction;
    if not_dot(text, end) {
        return end;
    }
    if fraction == 1 { 0 } else { end - 1 }
}

pub(crate) fn integer_length(text: &str) -> usize {
    let sign = sign_length(text);
    let rest = text.get(sign..).unwrap_or("");
    match rest.as_bytes().first() {
        Some(b'0') => {
            if not_dot(rest, 1) {
                sign + 1
            } else {
                0
            }
        }
        Some(b'1'..=b'9') => {
            let digits = digit_run(rest);
            if not_dot(rest, digits) {
                sign + digits
            } else if digits == 1 {
                0
            } else {
                sign + digits - 1
            }
        }
        _ => 0,
    }
}

fn escaped(c: char) -> String {
    match c {
        'b' => "\u{8}".into(),
        'f' => "\u{c}".into(),
        'n' => "\n".into(),
        'r' => "\r".into(),
        't' => "\t".into(),
        'v' => "\u{b}".into(),
        '0' => "\0".into(),
        other => other.to_string(),
    }
}

impl Scanner<'_> {
    fn run(mut self) -> Vec<Token> {
        while self.at < self.source.len() {
            if let Some(end) = self.removed_end() {
                self.at = end;
                continue;
            }
            if !self.next() {
                self.emit_char("INVALID");
            }
        }
        let end = self.source.len();
        self.tokens.push(Token {
            kind: "EOF",
            text: String::new(),
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

    fn rest(&self) -> &str {
        self.source.get(self.at..).unwrap_or("")
    }

    fn next(&mut self) -> bool {
        self.newline()
            || self.metadata()
            || self.keyword()
            || self.number()
            || self.string_literal()
            || self.space()
            || self.comment()
            || self.word()
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = self.at + length;
        let text = self.source.get(self.at..end).unwrap_or("").to_owned();
        self.tokens.push(Token {
            kind,
            text,
            span: Span {
                start: self.at,
                end,
            },
        });
        self.at = end;
    }

    fn emit_value(&mut self, kind: &'static str, length: usize, text: String) {
        let end = self.at + length;
        self.tokens.push(Token {
            kind,
            text,
            span: Span {
                start: self.at,
                end,
            },
        });
        self.at = end;
    }

    fn emit_char(&mut self, kind: &'static str) {
        let size = self.rest().chars().next().map_or(1, char::len_utf8);
        self.emit(kind, size);
    }

    fn unterminated(&mut self, opener: usize, length: usize) {
        let end = self.source.len();
        let text = self
            .source
            .get(opener..opener + length)
            .unwrap_or("")
            .to_owned();
        self.tokens.push(Token {
            kind: "UNTERMINATED",
            text,
            span: Span { start: opener, end },
        });
        self.at = end;
    }

    fn newline(&mut self) -> bool {
        match self.rest().as_bytes().first() {
            Some(b'\n') => self.emit("NEWLINE", 1),
            Some(b'\r') => {
                let length = if self.rest().as_bytes().get(1) == Some(&b'\n') {
                    2
                } else {
                    1
                };
                self.emit("NEWLINE", length);
            }
            _ => return false,
        }
        true
    }

    fn metadata(&mut self) -> bool {
        let lead = horizontal_run(self.rest());
        let rest = self.rest().get(lead..).unwrap_or("").to_owned();
        if let Some(after) = rest.strip_prefix("accDescr") {
            return self.acc_descr(lead, after);
        }
        if let Some(after) = rest.strip_prefix("accTitle") {
            let colon = horizontal_run(after);
            if after.as_bytes().get(colon) != Some(&b':') {
                return false;
            }
            let prefix = lead + "accTitle".len() + colon + 1;
            return self.line("ACC_TITLE", prefix, after.get(colon + 1..).unwrap_or(""));
        }
        if let Some(after) = rest.strip_prefix("title") {
            if after.as_bytes().first().copied().is_some_and(horizontal) {
                return self.line("TITLE", lead + "title".len(), after);
            }
            self.emit_value("TITLE", lead + "title".len(), String::new());
            return true;
        }
        false
    }

    fn line(&mut self, kind: &'static str, prefix: usize, value: &str) -> bool {
        let line = value.get(..line_length(value)).unwrap_or("");
        let value = line.get(..comment_cut(line)).unwrap_or("");
        self.emit_value(kind, prefix + value.len(), collapse_line(value));
        true
    }

    fn acc_descr(&mut self, lead: usize, after: &str) -> bool {
        let colon = horizontal_run(after);
        if after.as_bytes().get(colon) == Some(&b':') {
            let prefix = lead + "accDescr".len() + colon + 1;
            return self.line("ACC_DESCR", prefix, after.get(colon + 1..).unwrap_or(""));
        }
        let space = after.bytes().take_while(|&b| is_space_byte(b)).count();
        if after.as_bytes().get(space) != Some(&b'{') {
            return false;
        }
        let body = after.get(space + 1..).unwrap_or("");
        let Some(closing) = body.find('}') else {
            self.unterminated(self.at + lead + "accDescr".len() + space, 1);
            return true;
        };
        let length = lead + "accDescr".len() + space + 1 + closing + 1;
        self.emit_value(
            "ACC_DESCR",
            length,
            collapse_block(body.get(..closing).unwrap_or("")),
        );
        true
    }

    fn keyword(&mut self) -> bool {
        let rest = self.rest();
        let found = KEYWORDS
            .iter()
            .copied()
            .find(|keyword| rest.starts_with(keyword) && id_length(rest) <= keyword.len());
        let Some(keyword) = found else {
            return false;
        };
        self.emit(keyword, keyword.len());
        true
    }

    fn number(&mut self) -> bool {
        let length = match float_length(self.rest()) {
            0 => integer_length(self.rest()),
            float => float,
        };
        if length == 0 {
            return false;
        }
        self.emit("NUMBER_PIE", length);
        true
    }

    fn string_literal(&mut self) -> bool {
        let quote = match self.rest().as_bytes().first() {
            Some(&q @ (b'"' | b'\'')) => q,
            _ => return false,
        };
        let mut value = String::new();
        let mut i = self.at + 1;
        while i < self.source.len() {
            let byte = self.source.as_bytes().get(i).copied().unwrap_or(0);
            if byte == quote {
                self.emit_value("STRING", i + 1 - self.at, value);
                return true;
            }
            let rest = self.source.get(i..).unwrap_or("");
            if byte == b'\\' {
                let Some(next) = rest.get(1..).and_then(|r| r.chars().next()) else {
                    break;
                };
                if line_end_char(next) {
                    self.emit("INVALID", 1);
                    return true;
                }
                value.push_str(&escaped(next));
                i += 1 + next.len_utf8();
                continue;
            }
            let Some(c) = rest.chars().next() else {
                break;
            };
            value.push(c);
            i += c.len_utf8();
        }
        self.unterminated(self.at, 1);
        true
    }

    fn space(&mut self) -> bool {
        let run = horizontal_run(self.rest());
        self.at += run;
        run > 0
    }

    fn comment(&mut self) -> bool {
        if !self.rest().starts_with("%%") {
            return false;
        }
        self.at += line_length(self.rest());
        true
    }

    fn word(&mut self) -> bool {
        let length = id_length(self.rest());
        if length == 0 {
            return false;
        }
        self.emit("ID", length);
        true
    }
}
