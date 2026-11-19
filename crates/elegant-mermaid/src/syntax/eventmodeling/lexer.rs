//! Lexer for the eventmodeling grammar of `spec/grammar/eventmodeling.md`.
//!
//! One pass in source order. A word is a keyword token unless it is the header word
//! without a boundary. Whitespace, comments, `---` blocks, and removed spans emit
//! nothing; the byte offsets of LF and CR are recorded so the parser can find line ends.

use crate::source::Span;

pub(crate) const K_ID: &str = "EM_ID";
pub(crate) const K_FID: &str = "EM_FID";
pub(crate) const K_INLINE: &str = "EM_DATA_INLINE";
pub(crate) const K_BLOCK: &str = "EM_DATA_BLOCK";
pub(crate) const K_INVALID: &str = "INVALID";
pub(crate) const K_UNCLOSED: &str = "UNTERMINATED";
pub(crate) const K_EOF: &str = "EOF";
pub(crate) const HEADER: &str = "eventmodeling";
const MAX_FRAME_ID: usize = 3;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

const KEYWORDS: &[&str] = &[
    HEADER,
    "rmo",
    "readmodel",
    "ui",
    "cmd",
    "command",
    "evt",
    "event",
    "pcr",
    "processor",
    "json",
    "jsobj",
    "figma",
    "salt",
    "uri",
    "md",
    "html",
    "text",
    "tf",
    "timeframe",
    "rf",
    "resetframe",
    "entity",
    "data",
    "note",
    "gwt",
    "given",
    "when",
    "then",
];

pub fn lex(source: &str, removed: &[Span]) -> (Vec<Token>, Vec<usize>) {
    let mut scanner = Scanner {
        source,
        removed,
        at: 0,
        tokens: Vec::new(),
        breaks: Vec::new(),
    };
    scanner.run();
    (scanner.tokens, scanner.breaks)
}

struct Scanner<'a> {
    source: &'a str,
    removed: &'a [Span],
    at: usize,
    tokens: Vec<Token>,
    breaks: Vec<usize>,
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

fn is_word(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphanumeric()
}

fn line_length(text: &str) -> usize {
    text.find(['\n', '\r']).unwrap_or(text.len())
}

fn header_boundary(after: &str) -> bool {
    after.is_empty() || after.starts_with("%%") || after.chars().next().is_some_and(js_space)
}

fn newline_length(text: &str, at: usize) -> usize {
    let rest = text.as_bytes().get(at..).unwrap_or_default();
    if rest.starts_with(b"\r\n") {
        2
    } else if matches!(rest.first(), Some(b'\n' | b'\r')) {
        1
    } else {
        0
    }
}

fn inline_end(rest: &str, closing: u8) -> Option<usize> {
    let bytes = rest.as_bytes();
    let line = rest
        .get(1..)
        .and_then(|tail| tail.find(['\n', '\r', '\u{2028}', '\u{2029}']))
        .map_or(bytes.len(), |i| 1 + i);
    let inner = bytes.get(1..line)?;
    inner
        .iter()
        .rposition(|&byte| byte == closing)
        .map(|i| 1 + i + 1)
}

fn block_tail(rest: &str, at: usize) -> Option<usize> {
    if at >= rest.len() {
        return Some(at);
    }
    let n = newline_length(rest, at);
    if n > 0 {
        return Some(at + n);
    }
    rest.get(at..)
        .and_then(|tail| tail.chars().next())
        .filter(|&c| js_space(c))
        .map(|_| at)
}

fn block_end(rest: &str, open: &str, closing: &str) -> Option<usize> {
    let bytes = rest.as_bytes();
    if !rest.starts_with(open) {
        return None;
    }
    let mut i = open.len();
    while matches!(bytes.get(i), Some(b' ' | b'\t')) {
        i += 1;
    }
    let n = newline_length(rest, i);
    if n == 0 {
        return None;
    }
    let first = i + n;
    for k in first + 1..bytes.len() {
        let after_break = matches!(bytes.get(k - 1), Some(b'\n' | b'\r'));
        if !after_break
            || !bytes
                .get(k..)
                .is_some_and(|tail| tail.starts_with(closing.as_bytes()))
        {
            continue;
        }
        if let Some(end) = block_tail(rest, k + closing.len()) {
            return Some(end);
        }
    }
    if bytes
        .get(first..)
        .is_some_and(|tail| tail.starts_with(closing.as_bytes()))
    {
        return block_tail(rest, first + closing.len());
    }
    None
}

impl Scanner<'_> {
    fn rest(&self) -> &str {
        self.source.get(self.at..).unwrap_or("")
    }

    fn run(&mut self) {
        while self.at < self.source.len() {
            if let Some(end) = self.removed_end() {
                self.at = end;
                continue;
            }
            if !self.next() {
                self.emit_char(K_INVALID);
            }
        }
        let end = self.source.len();
        self.tokens.push(Token {
            kind: K_EOF,
            text: String::new(),
            span: Span { start: end, end },
        });
    }

    fn removed_end(&self) -> Option<usize> {
        self.removed
            .iter()
            .find(|span| span.start <= self.at && self.at < span.end)
            .map(|span| span.end)
    }

    fn next(&mut self) -> bool {
        let Some(&byte) = self.source.as_bytes().get(self.at) else {
            return false;
        };
        if self.whitespace() {
            return true;
        }
        match byte {
            b'/' => self.slash(),
            b'%' => self.percent(),
            b'_' | b'a'..=b'z' | b'A'..=b'Z' => {
                self.word();
                true
            }
            b'0'..=b'9' => {
                self.frame_id();
                true
            }
            b'{' => {
                self.brace();
                true
            }
            b'"' | b'\'' => {
                self.quoted(byte);
                true
            }
            b'-' => self.dash(),
            b'`' => {
                self.emit("`", 1);
                true
            }
            b'.' => {
                self.emit(".", 1);
                true
            }
            b'[' | b']' => self.bracket(byte),
            _ => false,
        }
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = self.at + length;
        self.tokens.push(Token {
            kind,
            text: self.source.get(self.at..end).unwrap_or("").to_owned(),
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
        self.tokens.push(Token {
            kind: K_UNCLOSED,
            text: self
                .source
                .get(opener..opener + length)
                .unwrap_or("")
                .to_owned(),
            span: Span { start: opener, end },
        });
        self.at = end;
    }

    fn whitespace(&mut self) -> bool {
        let start = self.at;
        while let Some(c) = self.rest().chars().next() {
            if !js_space(c) {
                break;
            }
            let mut size = c.len_utf8();
            match c {
                '\n' => self.breaks.push(self.at),
                '\r' => {
                    self.breaks.push(self.at);
                    if self.source.as_bytes().get(self.at + 1) == Some(&b'\n') {
                        size += 1;
                    }
                }
                _ => {}
            }
            self.at += size;
        }
        self.at > start
    }

    fn slash(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with("//") {
            self.at += line_length(rest);
        } else if rest.starts_with("/*") {
            match rest.get(2..).and_then(|tail| tail.find("*/")) {
                Some(closing) => self.at += 2 + closing + 2,
                None => self.unterminated(self.at, 2),
            }
        } else {
            return false;
        }
        true
    }

    fn percent(&mut self) -> bool {
        let rest = self.rest();
        if !rest.starts_with("%%") {
            return false;
        }
        self.at += line_length(rest);
        true
    }

    fn word(&mut self) {
        let rest = self.rest();
        let n = 1 + rest
            .as_bytes()
            .get(1..)
            .unwrap_or_default()
            .iter()
            .take_while(|&&byte| is_word(byte))
            .count();
        let word = rest.get(..n).unwrap_or("");
        let after = rest.get(n..).unwrap_or("");
        let keyword = KEYWORDS
            .iter()
            .find(|&&k| k == word)
            .filter(|&&k| k != HEADER || header_boundary(after));
        self.emit(keyword.copied().unwrap_or(K_ID), n);
    }

    fn frame_id(&mut self) {
        let n = 1 + self
            .rest()
            .as_bytes()
            .get(1..MAX_FRAME_ID.min(self.rest().len()))
            .unwrap_or_default()
            .iter()
            .take_while(|byte| byte.is_ascii_digit())
            .count();
        self.emit(K_FID, n);
    }

    fn brace(&mut self) {
        let rest = self.rest();
        if let Some(end) = inline_end(rest, b'}') {
            self.emit(K_INLINE, end);
        } else if let Some(end) = block_end(rest, "{", "}") {
            self.emit(K_BLOCK, end);
        } else {
            self.unterminated(self.at, 1);
        }
    }

    fn quoted(&mut self, quote: u8) {
        match inline_end(self.rest(), quote) {
            Some(end) => self.emit(K_INLINE, end),
            None => self.unterminated(self.at, 1),
        }
    }

    fn dash(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with("->>") {
            self.emit("->>", 3);
            return true;
        }
        match block_end(rest, "---", "---") {
            Some(end) => {
                self.at += end;
                true
            }
            None => false,
        }
    }

    fn bracket(&mut self, byte: u8) -> bool {
        if self.rest().as_bytes().get(1) != Some(&byte) {
            return false;
        }
        self.emit(if byte == b'[' { "[[" } else { "]]" }, 2);
        true
    }
}
