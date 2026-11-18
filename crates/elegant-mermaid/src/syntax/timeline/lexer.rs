//! Lexer for the timeline grammar of `spec/grammar/timeline.md`.
//!
//! The scanner pulls one token at a time over the source with removed spans dropped, each
//! line end written as one LF, and a synthetic LF appended. Every text byte maps back to
//! the host byte range it came from. Hidden text (blanks, comments, removed spans) emits
//! nothing.

use crate::source::Span;

pub const TIMELINE: &str = "timeline";
pub const TIMELINE_LR: &str = "timeline_lr";
pub const TIMELINE_TD: &str = "timeline_td";
pub const NEWLINE: &str = "NEWLINE";
pub const TITLE: &str = "title";
pub const ACC_TITLE: &str = "acc_title";
pub const ACC_TITLE_VALUE: &str = "acc_title_value";
pub const ACC_DESCR: &str = "acc_descr";
pub const ACC_DESCR_VALUE: &str = "acc_descr_value";
pub const ACC_BLOCK_VALUE: &str = "acc_descr_multiline_value";
pub const SECTION: &str = "section";
pub const EVENT: &str = "event";
pub const PERIOD: &str = "period";
pub const EOF: &str = "EOF";
pub const INVALID: &str = "INVALID";
pub const UNTERMINATED: &str = "UNTERMINATED";

const NONE: Span = Span { start: 0, end: 0 };

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub value: String,
    pub span: Span,
    pub payload: Span,
    pub open: Span,
    pub close: Span,
}

impl Token {
    fn new(kind: &'static str, text: String, span: Span) -> Self {
        Self {
            kind,
            text,
            value: String::new(),
            span,
            payload: NONE,
            open: NONE,
            close: NONE,
        }
    }

    pub fn empty() -> Self {
        Self::new("", String::new(), NONE)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Initial,
    AccTitle,
    AccDescr,
    Block,
}

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
            | '\u{2000}'..='\u{200a}'
    )
}

fn word_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn decode_rune(bytes: &[u8]) -> (char, usize) {
    if bytes.is_empty() {
        return ('\u{fffd}', 0);
    }
    let head = bytes.get(..bytes.len().min(4)).unwrap_or(&[]);
    for len in 1..=head.len() {
        let decoded = head
            .get(..len)
            .and_then(|part| std::str::from_utf8(part).ok());
        if let Some(c) = decoded.and_then(|text| text.chars().next()) {
            return (c, len);
        }
    }
    ('\u{fffd}', 1)
}

pub(super) struct Scanner {
    text: Vec<u8>,
    start: Vec<usize>,
    end: Vec<usize>,
    length: usize,
    at: usize,
    mode: Mode,
    open: Span,
    brace: usize,
    crossed: bool,
    pending: Option<Token>,
}

impl Scanner {
    pub fn new(source: &str, removed: &[Span]) -> Self {
        let bytes = source.as_bytes();
        let mut skip = vec![false; bytes.len()];
        for span in removed {
            for flag in skip
                .iter_mut()
                .take(span.end.min(bytes.len()))
                .skip(span.start)
            {
                *flag = true;
            }
        }
        let kept: Vec<usize> = skip
            .iter()
            .enumerate()
            .filter(|(_, hidden)| !**hidden)
            .map(|(index, _)| index)
            .collect();
        let mut text = Vec::with_capacity(kept.len() + 1);
        let mut start = Vec::with_capacity(kept.len() + 2);
        let mut end = Vec::with_capacity(kept.len() + 2);
        let mut k = 0;
        while let Some(&i) = kept.get(k) {
            let mut last = i;
            let mut c = bytes.get(i).copied().unwrap_or(0);
            if c == b'\r' {
                if let Some(&next) = kept.get(k + 1)
                    && bytes.get(next) == Some(&b'\n')
                {
                    k += 1;
                    last = next;
                }
                c = b'\n';
            }
            text.push(c);
            start.push(i);
            end.push(last + 1);
            k += 1;
        }
        text.push(b'\n');
        start.extend([bytes.len(), bytes.len()]);
        end.extend([bytes.len(), bytes.len()]);
        Self {
            text,
            start,
            end,
            length: bytes.len(),
            at: 0,
            mode: Mode::Initial,
            open: NONE,
            brace: 0,
            crossed: false,
            pending: None,
        }
    }

    fn byte(&self, at: usize) -> u8 {
        self.text.get(at).copied().unwrap_or(0)
    }

    fn slice(&self, from: usize, to: usize) -> &[u8] {
        self.text.get(from..to).unwrap_or(&[])
    }

    fn string(&self, from: usize, to: usize) -> String {
        String::from_utf8_lossy(self.slice(from, to)).into_owned()
    }

    fn rune(&self, at: usize) -> (char, usize) {
        decode_rune(self.text.get(at..).unwrap_or(&[]))
    }

    fn space_run(&self, mut at: usize) -> usize {
        while at < self.text.len() {
            let (r, n) = self.rune(at);
            if !is_space(r) {
                break;
            }
            at += n;
        }
        at
    }

    fn line_end(&self, at: usize) -> usize {
        self.text
            .get(at..)
            .and_then(|rest| rest.iter().position(|&c| c == b'\n'))
            .map_or(self.text.len(), |i| at + i)
    }

    fn fold(&self, at: usize, word: &str) -> bool {
        let Some(part) = self.text.get(at..at + word.len()) else {
            return false;
        };
        part.eq_ignore_ascii_case(word.as_bytes())
    }

    fn span(&self, from: usize, to: usize) -> Span {
        if from >= to {
            let at = self
                .start
                .get(from.min(self.text.len()))
                .copied()
                .unwrap_or(self.length);
            return Span { start: at, end: at };
        }
        Span {
            start: self.start.get(from).copied().unwrap_or(self.length),
            end: self.end.get(to - 1).copied().unwrap_or(self.length),
        }
    }

    fn token(&mut self, kind: &'static str, from: usize, to: usize) -> Token {
        self.at = to;
        if self.slice(from, to).contains(&b'\n') {
            self.crossed = true;
        }
        Token::new(kind, self.string(from, to), self.span(from, to))
    }

    fn payload_token(
        &mut self,
        kind: &'static str,
        from: usize,
        value_from: usize,
        to: usize,
    ) -> Token {
        let mut t = self.token(kind, from, to);
        t.value = self.string(value_from, to);
        t.payload = self.span(value_from, to);
        t
    }

    fn skip(&mut self, to: usize) {
        if self.slice(self.at, to).contains(&b'\n') {
            self.crossed = true;
        }
        self.at = to;
    }

    pub fn next(&mut self) -> Token {
        if let Some(t) = self.pending.take() {
            return t;
        }
        loop {
            if let Some(t) = self.step() {
                return t;
            }
        }
    }

    fn step(&mut self) -> Option<Token> {
        if self.at >= self.text.len() {
            return Some(self.finish());
        }
        match self.mode {
            Mode::AccTitle => Some(self.value(ACC_TITLE_VALUE)),
            Mode::AccDescr => Some(self.value(ACC_DESCR_VALUE)),
            Mode::Block => self.block(),
            Mode::Initial => self.initial(),
        }
    }

    fn finish(&mut self) -> Token {
        if self.mode == Mode::Block {
            self.mode = Mode::Initial;
            self.at = self.text.len();
            let begin = self.start.get(self.brace).copied().unwrap_or(self.length);
            return Token::new(
                UNTERMINATED,
                "{".into(),
                Span {
                    start: begin,
                    end: self.length,
                },
            );
        }
        self.mode = Mode::Initial;
        let zero = Span {
            start: self.length,
            end: self.length,
        };
        let mut t = Token::new(EOF, String::new(), zero);
        t.payload = zero;
        t
    }

    fn value(&mut self, kind: &'static str) -> Token {
        let at = self.at;
        let end = self.line_end(at);
        self.mode = Mode::Initial;
        let mut t = self.token(kind, at, end);
        t.value = t.text.clone();
        t.payload = t.span;
        t
    }

    fn block(&mut self) -> Option<Token> {
        let at = self.at;
        let Some(rel) = self
            .text
            .get(at..)
            .and_then(|rest| rest.iter().position(|&c| c == b'}'))
        else {
            return Some(self.finish());
        };
        let end = at + rel;
        self.mode = Mode::Initial;
        self.at = end + 1;
        if rel == 0 {
            return None;
        }
        let value = self.string(at, end);
        let span = self.span(at, end);
        let mut t = Token::new(ACC_BLOCK_VALUE, value.clone(), span);
        t.value = value;
        t.payload = span;
        t.open = self.open;
        t.close = self.span(end, end + 1);
        Some(t)
    }

    fn initial(&mut self) -> Option<Token> {
        if self.trivia() {
            return None;
        }
        let at = self.at;
        if self.byte(at) == b'\n' {
            let mut end = at;
            while end < self.text.len() && self.byte(end) == b'\n' {
                end += 1;
            }
            return Some(self.token(NEWLINE, at, end));
        }
        if let Some(t) = self.header(at) {
            return Some(t);
        }
        self.statement(at)
    }

    fn line_len(&self, from: usize) -> usize {
        self.text
            .get(from..)
            .and_then(|rest| rest.iter().position(|&c| c == b'\n'))
            .unwrap_or_else(|| self.text.len().saturating_sub(from))
    }

    fn starts_with(&self, at: usize, prefix: &[u8]) -> bool {
        self.text
            .get(at..)
            .is_some_and(|rest| rest.starts_with(prefix))
    }

    fn trivia(&mut self) -> bool {
        let at = self.at;
        let (r, n) = self.rune(at);
        let to = if self.starts_with(at, b"%%") && !self.starts_with(at, b"%%{") {
            at + self.line_len(at)
        } else if r != '}' && self.starts_with(at + n, b"%%") {
            at + n + 2 + self.line_len(at + n + 2)
        } else if self.byte(at) == b'\n' {
            return false;
        } else if self.space_run(at) > at {
            self.space_run(at)
        } else if self.byte(at) == b'#' && self.entity_len(at) == 0 {
            at + self.line_len(at)
        } else {
            return false;
        };
        self.skip(to);
        true
    }

    fn boundary(&self, at: usize) -> bool {
        at >= self.text.len() || !word_byte(self.byte(at))
    }

    fn header(&mut self, at: usize) -> Option<Token> {
        if !self.fold(at, "timeline") {
            return None;
        }
        let word = at + "timeline".len();
        let mut gap = word;
        while gap < self.text.len() && matches!(self.byte(gap), b' ' | b'\t') {
            gap += 1;
        }
        if gap > word && self.boundary(gap + 2) {
            if self.fold(gap, "lr") {
                return Some(self.token(TIMELINE_LR, at, gap + 2));
            }
            if self.fold(gap, "td") {
                return Some(self.token(TIMELINE_TD, at, gap + 2));
            }
        }
        if !self.boundary(word) {
            return None;
        }
        Some(self.token(TIMELINE, at, word))
    }

    fn keyword_payload(
        &self,
        at: usize,
        word: &str,
        stop: impl Fn(u8) -> bool,
    ) -> Option<(usize, usize)> {
        if !self.fold(at, word) {
            return None;
        }
        let gap = at + word.len();
        if gap >= self.text.len() {
            return None;
        }
        let (r, n) = self.rune(gap);
        if !is_space(r) {
            return None;
        }
        let from = gap + n;
        let mut end = from;
        while end < self.text.len() && !stop(self.byte(end)) {
            end += 1;
        }
        (end > from).then_some((from, end))
    }

    fn statement(&mut self, at: usize) -> Option<Token> {
        if let Some((from, end)) = self.keyword_payload(at, "title", |c| c == b'\n') {
            return Some(self.payload_token(TITLE, at, from, end));
        }
        if let Some(handled) = self.accessibility(at) {
            return handled;
        }
        if let Some((from, end)) = self.keyword_payload(at, "section", |c| c == b'\n' || c == b':')
        {
            return Some(self.payload_token(SECTION, at, from, end));
        }
        if let Some((from, end)) = self.event(at) {
            return Some(self.payload_token(EVENT, at, from, end));
        }
        let end = self.period_end(at);
        if end > at {
            return Some(self.payload_token(PERIOD, at, at, end));
        }
        let (_, n) = self.rune(at);
        Some(self.token(INVALID, at, at + n))
    }

    fn accessibility(&mut self, at: usize) -> Option<Option<Token>> {
        let title = self.fold(at, "acctitle");
        let descr = self.fold(at, "accdescr");
        if !title && !descr {
            return None;
        }
        let colon = self.space_run(at + "acctitle".len());
        let found = (colon < self.text.len()).then(|| self.byte(colon));
        if found == Some(b':') {
            let after = self.space_run(colon + 1);
            if title {
                self.mode = Mode::AccTitle;
                return Some(Some(self.token(ACC_TITLE, at, after)));
            }
            self.mode = Mode::AccDescr;
            return Some(Some(self.token(ACC_DESCR, at, after)));
        }
        if descr && found == Some(b'{') {
            let after = self.space_run(colon + 1);
            self.open = self.span(at, after);
            self.brace = colon;
            self.mode = Mode::Block;
            self.at = after;
            return Some(None);
        }
        None
    }

    fn event(&self, at: usize) -> Option<(usize, usize)> {
        if self.byte(at) != b':' || at + 1 >= self.text.len() {
            return None;
        }
        let (r, n) = self.rune(at + 1);
        if !is_space(r) {
            return None;
        }
        let from = at + 1 + n;
        let mut end = from;
        while end < self.text.len() {
            let c = self.byte(end);
            if c == b'\n' {
                break;
            }
            if c == b':' && end + 1 < self.text.len() && is_space(self.rune(end + 1).0) {
                break;
            }
            end += self.rune(end).1;
        }
        (end > from).then_some((from, end))
    }

    fn entity_len(&self, at: usize) -> usize {
        let mut end = at + 1;
        while end < self.text.len() && word_byte(self.byte(end)) {
            end += 1;
        }
        if end == at + 1 || end >= self.text.len() || self.byte(end) != b';' {
            return 0;
        }
        end + 1 - at
    }

    fn period_end(&self, at: usize) -> usize {
        let mut end = at;
        while end < self.text.len() {
            let c = self.byte(end);
            if c == b'#' {
                let n = self.entity_len(end);
                if n == 0 {
                    break;
                }
                end += n;
                continue;
            }
            if c == b':' || c == b'\n' {
                break;
            }
            end += 1;
        }
        end
    }

    pub fn skip_line(&mut self, mut content_end: usize) -> usize {
        loop {
            self.crossed = false;
            if let Some(t) = self.step() {
                match t.kind {
                    EOF | UNTERMINATED => {
                        self.pending = Some(t);
                        return content_end;
                    }
                    NEWLINE => {}
                    _ => content_end = content_end.max(t.span.end),
                }
            }
            if self.crossed && self.mode == Mode::Initial {
                return content_end;
            }
        }
    }
}
