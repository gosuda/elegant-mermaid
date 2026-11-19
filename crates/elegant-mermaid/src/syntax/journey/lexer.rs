//! Lexer for the journey grammar of `spec/grammar/journey.md`.
//!
//! The lexer reads a body view of the source: removed spans are cut out, and LF, CRLF,
//! and a lone CR each become one LF. Token spans map back to the original bytes. In the
//! initial mode the first matching rule of the authority order wins; the three
//! accessibility modes are exclusive.

use std::rc::Rc;

use crate::source::Span;

use super::ast::{Field, Value};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
    pub value: Value,
    pub fields: Vec<Field>,
    pub(crate) end: usize,
}

pub const JOURNEY: &str = "journey";
pub const NEWLINE: &str = "NEWLINE";
pub const TITLE: &str = "title";
pub const ACC_TITLE: &str = "acc_title";
pub const ACC_TITLE_VALUE: &str = "acc_title_value";
pub const ACC_DESCR: &str = "acc_descr";
pub const ACC_DESCR_VALUE: &str = "acc_descr_value";
pub const OPEN: &str = "acc_descr_open";
pub const MULTILINE: &str = "acc_descr_multiline_value";
pub const CLOSE: &str = "acc_descr_close";
pub const SECTION: &str = "section";
pub const TASK_NAME: &str = "taskName";
pub const TASK_DATA: &str = "taskData";
pub const COLON: &str = ":";
pub const EOF: &str = "EOF";
pub const INVALID: &str = "INVALID";
pub const UNTERMINATED: &str = "UNTERMINATED";

pub fn is_space(c: char) -> bool {
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
    ) || ('\u{2000}'..='\u{200a}').contains(&c)
}

pub fn trim(text: &str) -> &str {
    let (lo, hi) = trim_bounds(text);
    &text[lo..hi]
}

fn trim_bounds(text: &str) -> (usize, usize) {
    let tail = text.trim_start_matches(is_space);
    let lo = text.len() - tail.len();
    (lo, lo + tail.trim_end_matches(is_space).len())
}

fn space_run(text: &str) -> usize {
    text.len() - text.trim_start_matches(is_space).len()
}

fn fold_prefix(text: &str, word: &str) -> bool {
    text.as_bytes()
        .get(..word.len())
        .is_some_and(|head| head.eq_ignore_ascii_case(word.as_bytes()))
}

fn is_word(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn entity_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    let mut n = 1;
    while n < bytes.len() && is_word(bytes[n]) {
        n += 1;
    }
    if n == 1 || bytes.get(n) != Some(&b';') {
        return 0;
    }
    n + 1
}

fn run_until(text: &str, stop: &str) -> usize {
    let protect = stop.contains('#');
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if protect && bytes[i] == b'#' {
            let n = entity_length(&text[i..]);
            if n > 0 {
                i += n;
                continue;
            }
        }
        if stop.as_bytes().contains(&bytes[i]) {
            return i;
        }
        i += 1;
    }
    bytes.len()
}

struct View {
    text: Rc<str>,
    from: Vec<usize>,
    to: Vec<usize>,
    length: usize,
}

impl View {
    fn new(source: &str, removed: &[Span]) -> View {
        let mut text = String::with_capacity(source.len());
        let mut from = Vec::with_capacity(source.len());
        let mut to = Vec::with_capacity(source.len());
        let mut next = 0;
        let mut chars = source.char_indices().peekable();
        while let Some((i, c)) = chars.next() {
            while next < removed.len() && removed[next].end <= i {
                next += 1;
            }
            if next < removed.len() && removed[next].start <= i {
                continue;
            }
            let mut width = c.len_utf8();
            let mut kept = c;
            if c == '\r' {
                kept = '\n';
                if chars.peek().is_some_and(|(_, after)| *after == '\n') {
                    chars.next();
                    width = 2;
                }
            }
            text.push(kept);
            for k in 0..kept.len_utf8() {
                from.push(i + k);
                to.push(i + width.max(k + 1));
            }
        }
        View {
            text: text.into(),
            from,
            to,
            length: source.len(),
        }
    }

    fn offset(&self, at: usize) -> usize {
        self.from.get(at).copied().unwrap_or(self.length)
    }

    fn span(&self, from: usize, to: usize) -> Span {
        if to > from {
            return Span {
                start: self.from[from],
                end: self.to[to - 1],
            };
        }
        let at = self.offset(from);
        Span { start: at, end: at }
    }

    fn value(&self, from: usize, to: usize) -> Value {
        Value {
            text: self.text[from..to].to_owned(),
            span: self.span(from, to),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Initial,
    AccTitle,
    AccDescr,
    Multiline,
}

struct Scanner {
    view: View,
    at: usize,
    mode: Mode,
    opener: usize,
    line_end: Option<usize>,
    tokens: Vec<Token>,
}

pub fn lex(source: &str, removed: &[Span]) -> Vec<Token> {
    let mut scanner = Scanner {
        view: View::new(source, removed),
        at: 0,
        mode: Mode::Initial,
        opener: 0,
        line_end: None,
        tokens: Vec::new(),
    };
    while scanner.step() {}
    scanner.tokens
}

fn keyword_line(rest: &str, word: &str, stop: &str) -> Option<(usize, usize)> {
    if !fold_prefix(rest, word) {
        return None;
    }
    let c = rest[word.len()..].chars().next()?;
    if !is_space(c) {
        return None;
    }
    let lead = word.len() + c.len_utf8();
    match run_until(&rest[lead..], stop) {
        0 => None,
        n => Some((lead, lead + n)),
    }
}

fn access_lead(rest: &str, word: &str, delimiter: u8) -> Option<(usize, usize)> {
    if !fold_prefix(rest, word) {
        return None;
    }
    let head = word.len() + space_run(&rest[word.len()..]);
    if rest.as_bytes().get(head) != Some(&delimiter) {
        return None;
    }
    Some((head, head + 1 + space_run(&rest[head + 1..])))
}

impl Scanner {
    fn step(&mut self) -> bool {
        match self.mode {
            Mode::AccTitle => self.acc_value(ACC_TITLE_VALUE),
            Mode::AccDescr => self.acc_value(ACC_DESCR_VALUE),
            Mode::Multiline => return self.multiline(),
            Mode::Initial => {
                if self.at >= self.view.text.len() {
                    self.emit(EOF, self.at, self.at);
                    return false;
                }
                self.initial();
            }
        }
        true
    }

    fn physical_end(&mut self, at: usize) -> usize {
        let end = match self.line_end {
            Some(end) if end >= at => end,
            _ => at + run_until(&self.view.text[at..], "\n"),
        };
        self.line_end = Some(end);
        self.view.offset(end)
    }

    fn push(
        &mut self,
        kind: &'static str,
        from: usize,
        to: usize,
        value: Value,
        fields: Vec<Field>,
    ) {
        let whole = self.view.value(from, to);
        let end = self.physical_end(from);
        self.tokens.push(Token {
            kind,
            text: whole.text,
            span: whole.span,
            value,
            fields,
            end,
        });
        self.at = to;
    }

    fn emit(&mut self, kind: &'static str, from: usize, to: usize) {
        let value = self.view.value(from, to);
        self.push(kind, from, to, value, Vec::new());
    }

    fn acc_value(&mut self, kind: &'static str) {
        let text = Rc::clone(&self.view.text);
        let n = run_until(&text[self.at..], "\n");
        self.emit(kind, self.at, self.at + n);
        self.mode = Mode::Initial;
    }

    fn multiline(&mut self) -> bool {
        let text = Rc::clone(&self.view.text);
        let rest = &text[self.at..];
        match rest.as_bytes().first() {
            None => {
                let start = self.view.offset(self.opener);
                self.tokens.push(Token {
                    kind: UNTERMINATED,
                    text: "{".to_owned(),
                    span: Span {
                        start,
                        end: self.view.length,
                    },
                    value: Value {
                        text: String::new(),
                        span: Span { start: 0, end: 0 },
                    },
                    fields: Vec::new(),
                    end: self.view.length,
                });
                return false;
            }
            Some(b'}') => {
                self.emit(CLOSE, self.at, self.at + 1);
                self.mode = Mode::Initial;
            }
            Some(_) => {
                let n = run_until(rest, "}");
                self.emit(MULTILINE, self.at, self.at + n);
            }
        }
        true
    }

    fn initial(&mut self) {
        let text = Rc::clone(&self.view.text);
        let rest = &text[self.at..];
        if self.comment(rest)
            || self.newline(rest)
            || self.whitespace(rest)
            || self.hash_comment(rest)
        {
            return;
        }
        if self.header(rest)
            || self.title_line(rest)
            || self.accessibility(rest)
            || self.section_line(rest)
            || self.task(rest)
        {
            return;
        }
        let size = rest.chars().next().map_or(1, char::len_utf8);
        self.emit(INVALID, self.at, self.at + size);
    }

    fn comment(&mut self, rest: &str) -> bool {
        if let Some(tail) = rest.strip_prefix("%%")
            && !tail.starts_with('{')
        {
            self.at += 2 + run_until(tail, "\n");
            return true;
        }
        let Some(first) = rest.chars().next() else {
            return false;
        };
        if first == '}' || u32::from(first) >= 0x10000 {
            return false;
        }
        let size = first.len_utf8();
        let Some(tail) = rest[size..].strip_prefix("%%") else {
            return false;
        };
        self.at += size + 2 + run_until(tail, "\n");
        true
    }

    fn newline(&mut self, rest: &str) -> bool {
        if !rest.starts_with('\n') {
            return false;
        }
        let n = rest.bytes().take_while(|b| *b == b'\n').count();
        self.emit(NEWLINE, self.at, self.at + n);
        true
    }

    fn whitespace(&mut self, rest: &str) -> bool {
        let n = space_run(rest);
        self.at += n;
        n > 0
    }

    fn hash_comment(&mut self, rest: &str) -> bool {
        if !rest.starts_with('#') || entity_length(rest) > 0 {
            return false;
        }
        self.at += run_until(rest, "\n");
        true
    }

    fn header(&mut self, rest: &str) -> bool {
        if !fold_prefix(rest, JOURNEY)
            || rest
                .as_bytes()
                .get(JOURNEY.len())
                .is_some_and(|c| is_word(*c))
        {
            return false;
        }
        self.emit(JOURNEY, self.at, self.at + JOURNEY.len());
        true
    }

    fn value_token(&mut self, kind: &'static str, lead: usize, total: usize) {
        let from = self.at;
        let value = self.view.value(from + lead, from + total);
        self.push(kind, from, from + total, value, Vec::new());
    }

    fn title_line(&mut self, rest: &str) -> bool {
        let Some((lead, total)) = keyword_line(rest, "title", "#\n;") else {
            return false;
        };
        self.value_token(TITLE, lead, total);
        true
    }

    fn section_line(&mut self, rest: &str) -> bool {
        let Some((lead, total)) = keyword_line(rest, "section", "#:\n;") else {
            return false;
        };
        self.value_token(SECTION, lead, total);
        true
    }

    fn accessibility(&mut self, rest: &str) -> bool {
        if let Some((_, total)) = access_lead(rest, "acctitle", b':') {
            self.emit(ACC_TITLE, self.at, self.at + total);
            self.mode = Mode::AccTitle;
            return true;
        }
        if let Some((_, total)) = access_lead(rest, "accdescr", b':') {
            self.emit(ACC_DESCR, self.at, self.at + total);
            self.mode = Mode::AccDescr;
            return true;
        }
        if let Some((head, total)) = access_lead(rest, "accdescr", b'{') {
            self.opener = self.at + head;
            self.emit(OPEN, self.opener, self.opener + 1);
            self.at += total - head - 1;
            self.mode = Mode::Multiline;
            return true;
        }
        false
    }

    fn task(&mut self, rest: &str) -> bool {
        let n = run_until(rest, "#:\n;");
        if n > 0 {
            self.emit(TASK_NAME, self.at, self.at + n);
            return true;
        }
        if !rest.starts_with(':') {
            return false;
        }
        self.task_data(rest);
        true
    }

    fn task_data(&mut self, rest: &str) {
        let n = run_until(&rest[1..], "#\n;");
        if n == 0 {
            self.emit(COLON, self.at, self.at + 1);
            return;
        }
        let start = self.at;
        let to = start + 1 + n;
        let fields = self.fields(start + 1, to);
        let value = self.view.value(start, to);
        self.push(TASK_DATA, start, to, value, fields);
    }

    fn fields(&self, mut from: usize, to: usize) -> Vec<Field> {
        let mut out = Vec::new();
        loop {
            let end = from + run_until(&self.view.text[from..to], ":");
            out.push(self.field(from, end));
            if end >= to {
                return out;
            }
            from = end + 1;
        }
    }

    fn field(&self, from: usize, to: usize) -> Field {
        let raw = self.view.value(from, to);
        let (lo, hi) = trim_bounds(&self.view.text[from..to]);
        if lo == hi {
            let at = raw.span.start;
            return Field {
                raw,
                trimmed: Value {
                    text: String::new(),
                    span: Span { start: at, end: at },
                },
            };
        }
        let trimmed = self.view.value(from + lo, from + hi);
        Field { raw, trimmed }
    }
}
