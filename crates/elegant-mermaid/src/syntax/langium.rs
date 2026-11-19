//! The lexer and parser cursor shared by the Langium kinds (`spec/grammar/info.md`,
//! `spec/grammar/cynefin.md`): the common terminals of `common.langium`, keywords before
//! imported terminals, and statement-level recovery.

use crate::diag::{Diagnostic, Severity};
use crate::source::Span;

pub const EOF: &str = "EOF";
pub const NEWLINE: &str = "NEWLINE";
pub const INVALID: &str = "INVALID";
pub const UNTERMINATED: &str = "UNTERMINATED";
pub const STRING: &str = "STRING";
pub const ACC_DESCR: &str = "ACC_DESCR";
pub const ACC_TITLE: &str = "ACC_TITLE";
pub const TITLE: &str = "TITLE";

const ACC_DESCR_WORD: &str = "accDescr";
const ACC_TITLE_WORD: &str = "accTitle";
const TITLE_WORD: &str = "title";
const COMMENT: &str = "%%";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub struct Keyword {
    pub text: &'static str,
    pub guard: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct Terminal {
    pub kind: &'static str,
    pub matcher: fn(&str) -> usize,
}

#[derive(Debug, Clone, Copy)]
pub struct Grammar {
    pub keywords: &'static [Keyword],
    pub locals: &'static [Terminal],
}

pub fn lex(src: &str, removed: &[Span], grammar: Grammar) -> Vec<Token> {
    let mut scanner = Scanner {
        src,
        removed,
        grammar,
        at: 0,
        tokens: Vec::new(),
    };
    scanner.run();
    let end = src.len();
    scanner.tokens.push(Token {
        kind: EOF,
        text: String::new(),
        span: Span { start: end, end },
    });
    scanner.tokens
}

struct Scanner<'a> {
    src: &'a str,
    removed: &'a [Span],
    grammar: Grammar,
    at: usize,
    tokens: Vec<Token>,
}

impl<'a> Scanner<'a> {
    fn run(&mut self) {
        while self.at < self.src.len() {
            if let Some(end) = self.removed_end() {
                self.at = end;
            } else if !self.src.is_char_boundary(self.at) {
                self.at += 1;
            } else if !self.next() {
                self.emit_char(INVALID);
            }
        }
    }

    fn removed_end(&self) -> Option<usize> {
        self.removed
            .iter()
            .find(|span| span.start <= self.at && self.at < span.end)
            .map(|span| span.end)
    }

    fn rest(&self) -> &'a str {
        self.src.get(self.at..).unwrap_or("")
    }

    fn slice(&self, from: usize, to: usize) -> &'a str {
        self.src.get(from..to).unwrap_or("")
    }

    fn next(&mut self) -> bool {
        self.structural() || self.literal() || self.hidden()
    }

    fn structural(&mut self) -> bool {
        self.newline() || self.keyword() || self.local() || self.boolean() || self.metadata()
    }

    fn literal(&mut self) -> bool {
        self.number() || self.string_literal() || self.id()
    }

    fn hidden(&mut self) -> bool {
        self.space() || self.comment()
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = self.at + length;
        let text = self.slice(self.at, end).to_owned();
        self.emit_value(kind, length, text);
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
        let end = self.src.len();
        let text = self.slice(opener, opener + length).to_owned();
        self.tokens.push(Token {
            kind: UNTERMINATED,
            text,
            span: Span { start: opener, end },
        });
        self.at = end;
    }

    fn newline(&mut self) -> bool {
        let length = super::eol_len(self.src.as_bytes(), self.at);
        if length > 0 {
            self.emit(NEWLINE, length);
        }
        length > 0
    }

    fn keyword(&mut self) -> bool {
        let found = self.grammar.keywords.iter().find(|keyword| {
            let rest = self.rest();
            rest.starts_with(keyword.text)
                && (!keyword.guard || header_guard(rest.get(keyword.text.len()..).unwrap_or("")))
        });
        let Some(keyword) = found.copied() else {
            return false;
        };
        self.emit(keyword.text, keyword.text.len());
        true
    }

    fn local(&mut self) -> bool {
        let rest = self.rest();
        let found = self
            .grammar
            .locals
            .iter()
            .map(|terminal| (terminal.kind, (terminal.matcher)(rest)))
            .find(|(_, length)| *length > 0);
        let Some((kind, length)) = found else {
            return false;
        };
        self.emit(kind, length);
        true
    }

    fn boolean(&mut self) -> bool {
        let rest = self.rest();
        let Some(word) = ["true", "false"]
            .into_iter()
            .find(|word| rest.starts_with(word))
        else {
            return false;
        };
        self.emit("BOOLEAN", word.len());
        true
    }

    fn number(&mut self) -> bool {
        let rest = self.rest();
        let (kind, length) = match float_length(rest) {
            0 => ("INT", integer_length(rest)),
            n => ("FLOAT", n),
        };
        if length > 0 {
            self.emit(kind, length);
        }
        length > 0
    }

    fn id(&mut self) -> bool {
        let length = id_length(self.rest());
        if length > 0 {
            self.emit("ID", length);
        }
        length > 0
    }

    fn space(&mut self) -> bool {
        let length = horizontal_run(self.rest());
        self.at += length;
        length > 0
    }

    fn comment(&mut self) -> bool {
        if !self.rest().starts_with(COMMENT) {
            return false;
        }
        self.at += line_length(self.rest());
        true
    }

    fn metadata(&mut self) -> bool {
        let lead = horizontal_run(self.rest());
        let rest = self.slice(self.at + lead, self.src.len());
        if let Some(after) = rest.strip_prefix(ACC_DESCR_WORD) {
            return self.acc_descr(lead, after);
        }
        if let Some(after) = rest.strip_prefix(ACC_TITLE_WORD) {
            let colon = horizontal_run(after);
            if after.as_bytes().get(colon) != Some(&b':') {
                return false;
            }
            let prefix = lead + ACC_TITLE_WORD.len() + colon + 1;
            return self.line(ACC_TITLE, prefix, after.get(colon + 1..).unwrap_or(""));
        }
        let Some(after) = rest.strip_prefix(TITLE_WORD) else {
            return false;
        };
        let prefix = lead + TITLE_WORD.len();
        if after.as_bytes().first().is_some_and(|b| is_horizontal(*b)) {
            return self.line(TITLE, prefix, after);
        }
        self.emit_value(TITLE, prefix, String::new());
        true
    }

    fn line(&mut self, kind: &'static str, prefix: usize, value: &str) -> bool {
        let content = value.get(..line_length(value)).unwrap_or("");
        let value = value.get(..comment_cut(content)).unwrap_or("");
        self.emit_value(kind, prefix + value.len(), collapse_runs(value.trim()));
        true
    }

    fn acc_descr(&mut self, lead: usize, after: &str) -> bool {
        let colon = horizontal_run(after);
        if after.as_bytes().get(colon) == Some(&b':') {
            let prefix = lead + ACC_DESCR_WORD.len() + colon + 1;
            return self.line(ACC_DESCR, prefix, after.get(colon + 1..).unwrap_or(""));
        }
        let space = after.bytes().take_while(|b| is_space(*b)).count();
        if after.as_bytes().get(space) != Some(&b'{') {
            return false;
        }
        let body = after.get(space + 1..).unwrap_or("");
        let base = lead + ACC_DESCR_WORD.len() + space;
        let Some(closing) = body.find('}') else {
            self.unterminated(self.at + base, 1);
            return true;
        };
        let value = collapse_block(body.get(..closing).unwrap_or(""));
        self.emit_value(ACC_DESCR, base + 1 + closing + 1, value);
        true
    }

    fn string_literal(&mut self) -> bool {
        let quote = match self.src.as_bytes().get(self.at) {
            Some(&q) if q == b'"' || q == b'\'' => q,
            _ => return false,
        };
        let mut value = String::new();
        let mut i = self.at + 1;
        while let Some(c) = self.slice(i, self.src.len()).chars().next() {
            if c == char::from(quote) {
                self.emit_value(STRING, i + 1 - self.at, value);
                return true;
            }
            if c != '\\' {
                value.push(c);
                i += c.len_utf8();
                continue;
            }
            let Some(next) = self.slice(i + 1, self.src.len()).chars().next() else {
                break;
            };
            value.push(escaped(next));
            i += 1 + next.len_utf8();
        }
        self.unterminated(self.at, 1);
        true
    }
}

fn escaped(c: char) -> char {
    match c {
        'b' => '\u{8}',
        'f' => '\u{c}',
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        'v' => '\u{b}',
        '0' => '\0',
        other => other,
    }
}

fn is_horizontal(c: u8) -> bool {
    c == b' ' || c == b'\t'
}

fn is_space(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c)
}

fn horizontal_run(text: &str) -> usize {
    text.bytes().take_while(|b| is_horizontal(*b)).count()
}

fn line_length(text: &str) -> usize {
    text.find(['\n', '\r']).unwrap_or(text.len())
}

fn comment_cut(line: &str) -> usize {
    line.find(COMMENT).unwrap_or(line.len())
}

fn js_space(c: char) -> bool {
    match c {
        '\u{85}' => false,
        '\u{feff}' => true,
        other => other.is_whitespace(),
    }
}

fn header_guard(after: &str) -> bool {
    after.is_empty() || after.starts_with(COMMENT) || after.chars().next().is_some_and(js_space)
}

fn is_word(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

pub fn id_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    if !bytes.first().is_some_and(|b| is_word(*b)) {
        return 0;
    }
    let mut run = bytes
        .iter()
        .skip(1)
        .take_while(|b| is_word(**b) || **b == b'-')
        .count()
        + 1;
    while run > 1 && bytes.get(run - 1) == Some(&b'-') {
        run -= 1;
    }
    run
}

fn digit_run(text: &str) -> usize {
    text.bytes().take_while(u8::is_ascii_digit).count()
}

fn float_length(text: &str) -> usize {
    let whole = digit_run(text);
    if whole == 0 || text.as_bytes().get(whole) != Some(&b'.') {
        return 0;
    }
    let mut fraction = digit_run(text.get(whole + 1..).unwrap_or(""));
    if fraction == 0 {
        return 0;
    }
    let mut end = whole + 1 + fraction;
    if text.as_bytes().get(end) == Some(&b'.') {
        fraction -= 1;
        end -= 1;
        if fraction == 0 {
            return 0;
        }
    }
    end
}

fn integer_length(text: &str) -> usize {
    match text.as_bytes().first() {
        Some(b'0') => 1,
        Some(b'1'..=b'9') => {
            let digits = digit_run(text);
            if text.as_bytes().get(digits) == Some(&b'.') {
                digits - 1
            } else {
                digits
            }
        }
        _ => 0,
    }
}

fn collapse_runs(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    let mut chars = value.chars().peekable();
    while let Some(c) = chars.next() {
        if c != ' ' && c != '\t' {
            out.push(c);
            continue;
        }
        let mut run = 1;
        while chars
            .next_if(|next| *next == ' ' || *next == '\t')
            .is_some()
        {
            run += 1;
        }
        out.push(if run == 1 { c } else { ' ' });
    }
    out
}

fn collapse_block(value: &str) -> String {
    value
        .split(['\n', '\r'])
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(collapse_runs)
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn is_metadata(kind: &str) -> bool {
    kind == ACC_DESCR || kind == ACC_TITLE || kind == TITLE
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Field {
    AccDescr,
    AccTitle,
    Title,
}

pub fn metadata_field(kind: &str) -> Field {
    match kind {
        ACC_DESCR => Field::AccDescr,
        ACC_TITLE => Field::AccTitle,
        _ => Field::Title,
    }
}

pub fn diagnostic(
    code: &'static str,
    severity: Severity,
    message: String,
    span: Span,
) -> Diagnostic {
    Diagnostic {
        code,
        severity,
        message,
        span,
        related: Vec::new(),
        help: crate::r#gen::diagnostics::DIAGNOSTICS
            .iter()
            .find(|row| row.code == code)
            .map_or("", |row| row.help)
            .into(),
        fixes: Vec::new(),
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Codes {
    pub unexpected: &'static str,
    pub unknown: &'static str,
    pub unterminated: &'static str,
}

pub struct Cursor<'a> {
    pub src: &'a str,
    tokens: Vec<Token>,
    pub at: usize,
    pub end: usize,
    pub diags: Vec<Diagnostic>,
    codes: Codes,
}

impl<'a> Cursor<'a> {
    pub fn new(src: &'a str, removed: &[Span], grammar: Grammar, codes: Codes) -> Cursor<'a> {
        Cursor {
            src,
            tokens: lex(src, removed, grammar),
            at: 0,
            end: 0,
            diags: Vec::new(),
            codes,
        }
    }

    fn eof(&self) -> Token {
        let end = self.src.len();
        Token {
            kind: EOF,
            text: String::new(),
            span: Span { start: end, end },
        }
    }

    pub fn token(&self) -> Token {
        self.ahead(0)
    }

    pub fn ahead(&self, n: usize) -> Token {
        self.tokens
            .get(self.at + n)
            .cloned()
            .unwrap_or_else(|| self.eof())
    }

    pub fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or(EOF, |token| token.kind)
    }

    pub fn kind_ahead(&self, n: usize) -> &'static str {
        self.tokens.get(self.at + n).map_or(EOF, |token| token.kind)
    }

    pub fn take(&mut self) -> Token {
        let token = self.token();
        if self.at < self.tokens.len() {
            self.at += 1;
        }
        token
    }

    pub fn skip_newlines(&mut self) {
        while self.kind() == NEWLINE {
            self.at += 1;
        }
    }

    fn content_end(&self) -> usize {
        self.tokens
            .iter()
            .take(self.at)
            .rev()
            .find(|token| token.kind != NEWLINE)
            .map_or(0, |token| token.span.end)
    }

    fn describe(&self, token: &Token) -> String {
        if token.span.start == token.span.end {
            return "end of input".into();
        }
        self.src
            .get(token.span.start..token.span.end)
            .unwrap_or("")
            .to_owned()
    }

    pub fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        if token.kind == UNTERMINATED {
            return;
        }
        let mut names = expected.to_vec();
        names.sort_unstable();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.describe(&token),
            names.join(", ")
        );
        self.diags.push(diagnostic(
            self.codes.unexpected,
            Severity::Error,
            message,
            token.span,
        ));
    }

    fn line_end(&self) -> usize {
        self.tokens
            .iter()
            .skip(self.at)
            .find(|token| matches!(token.kind, NEWLINE | EOF | UNTERMINATED))
            .map_or(self.src.len(), |token| token.span.start)
    }

    pub fn skip_line(&mut self) {
        loop {
            match self.kind() {
                EOF | UNTERMINATED => return,
                NEWLINE => {
                    self.take();
                    return;
                }
                _ => {
                    self.take();
                }
            }
        }
    }

    pub fn unknown(&mut self) {
        let first = self.token();
        let text = self.describe(&first);
        let span = Span {
            start: first.span.start,
            end: self.line_end().max(first.span.end),
        };
        self.diags.push(diagnostic(
            self.codes.unknown,
            Severity::Error,
            format!("unknown statement {text}"),
            span,
        ));
        self.skip_line();
    }

    pub fn unterminated(&mut self) {
        let token = self.token();
        self.diags.push(diagnostic(
            self.codes.unterminated,
            Severity::Error,
            format!("unterminated {}", token.text),
            token.span,
        ));
    }

    pub fn finish(&mut self, expected: &[&str]) -> bool {
        let end = self.content_end();
        match self.kind() {
            NEWLINE => {
                self.take();
            }
            EOF => {}
            _ => {
                let mut names = expected.to_vec();
                names.extend([EOF, NEWLINE]);
                self.unexpected(&names);
                self.skip_line();
                return false;
            }
        }
        self.end = end;
        true
    }

    pub fn metadata(&mut self) -> Option<(Field, Token)> {
        let token = self.take();
        if !self.finish(&[]) {
            return None;
        }
        Some((metadata_field(token.kind), token))
    }
}
