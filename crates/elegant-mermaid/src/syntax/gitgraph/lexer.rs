//! Lexer for the gitgraph grammar of `spec/grammar/gitgraph.md`.
//!
//! One pass in source order. Keywords come first and yield to a longer REFERENCE;
//! the terminals follow in the authority order. LF, CRLF, and a lone CR each make one
//! NEWLINE. Hidden terminals (whitespace, comments, removed spans) emit nothing.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

const KEYWORDS: &[&str] = &[
    "cherry-pick",
    "HIGHLIGHT",
    "gitGraph:",
    "checkout",
    "gitGraph",
    "REVERSE",
    "parent:",
    "NORMAL",
    "branch",
    "commit",
    "order:",
    "switch",
    "merge",
    "type:",
    "msg:",
    "tag:",
    "id:",
    "BT",
    "LR",
    "TB",
    ":",
];

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

fn header_guard(after: &str) -> bool {
    after.is_empty()
        || after.starts_with("%%")
        || after.chars().next().is_some_and(char::is_whitespace)
}

fn word_like(keyword: &str) -> bool {
    !keyword.contains(':')
}

fn reference_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    if !bytes.first().copied().is_some_and(is_word) {
        return 0;
    }
    let mut run = 1;
    while bytes
        .get(run)
        .is_some_and(|&b| is_word(b) || b == b'-' || b == b'.' || b == b'/')
    {
        run += 1;
    }
    while run > 1
        && bytes
            .get(run - 1)
            .is_some_and(|&b| b != b'-' && !is_word(b))
    {
        run -= 1;
    }
    run
}

fn integer_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    match bytes.first() {
        Some(b'0') => 1,
        Some(b'1'..=b'9') => {
            let mut digits = 1;
            while bytes.get(digits).is_some_and(u8::is_ascii_digit) {
                digits += 1;
            }
            if bytes.get(digits) == Some(&b'.') {
                digits -= 1;
            }
            digits
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
            || self.integer()
            || self.string_literal()
            || self.space()
            || self.comment()
            || self.reference()
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
        let found = KEYWORDS.iter().copied().find(|keyword| {
            rest.starts_with(keyword)
                && !(*keyword == "gitGraph"
                    && !header_guard(rest.get(keyword.len()..).unwrap_or("")))
                && !(word_like(keyword) && reference_length(rest) > keyword.len())
        });
        let Some(keyword) = found else {
            return false;
        };
        self.emit(keyword, keyword.len());
        true
    }

    fn integer(&mut self) -> bool {
        let length = integer_length(self.rest());
        if length == 0 {
            return false;
        }
        self.emit("INT", length);
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

    fn reference(&mut self) -> bool {
        let length = reference_length(self.rest());
        if length == 0 {
            return false;
        }
        self.emit("REFERENCE", length);
        true
    }
}

#[cfg(test)]
pub(crate) fn lengths(text: &str) -> (usize, usize) {
    (integer_length(text), reference_length(text))
}
