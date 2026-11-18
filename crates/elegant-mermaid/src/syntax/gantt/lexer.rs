//! Lexer for the gantt grammar of `spec/grammar/gantt.md`.
//!
//! The scanner pulls one token at a time over the source with removed spans dropped, each
//! line end written as one LF, and a synthetic LF appended. Every text byte maps back to
//! the host byte range it came from. Hidden text (blanks, comments, removed spans) emits
//! nothing.

use crate::source::Span;

pub const GANTT: &str = "gantt";
pub const NEWLINE: &str = "NL";
pub const DATE_FORMAT: &str = "dateFormat";
pub const INCLUSIVE_END_DATES: &str = "inclusiveEndDates";
pub const TOP_AXIS: &str = "topAxis";
pub const AXIS_FORMAT: &str = "axisFormat";
pub const TICK_INTERVAL: &str = "tickInterval";
pub const INCLUDES: &str = "includes";
pub const EXCLUDES: &str = "excludes";
pub const TODAY_MARKER: &str = "todayMarker";
pub const WEEKDAY_PREFIX: &str = "weekday_";
pub const WEEKEND_PREFIX: &str = "weekend_";
pub const DATE: &str = "date";
pub const TITLE: &str = "title";
pub const ACC_DESCRIPTION: &str = "accDescription";
pub const SECTION: &str = "section";
pub const TASK_TEXT: &str = "taskTxt";
pub const TASK_DATA: &str = "taskData";
pub const COLON: &str = ":";
pub const ACC_TITLE: &str = "acc_title";
pub const ACC_TITLE_VALUE: &str = "acc_title_value";
pub const ACC_DESCR: &str = "acc_descr";
pub const ACC_DESCR_VALUE: &str = "acc_descr_value";
pub const ACC_BLOCK_VALUE: &str = "acc_descr_multiline_value";
pub const CLICK: &str = "click";
pub const HREF: &str = "href";
pub const CALLBACK_NAME: &str = "callbackname";
pub const CALLBACK_ARGS: &str = "callbackargs";
pub const EOF: &str = "EOF";
pub const INVALID: &str = "INVALID";
pub const UNTERMINATED: &str = "UNTERMINATED";

const WEEKDAYS: [(&str, &str); 7] = [
    ("monday", "weekday_monday"),
    ("tuesday", "weekday_tuesday"),
    ("wednesday", "weekday_wednesday"),
    ("thursday", "weekday_thursday"),
    ("friday", "weekday_friday"),
    ("saturday", "weekday_saturday"),
    ("sunday", "weekday_sunday"),
];

const WEEKENDS: [(&str, &str); 2] = [
    ("friday", "weekend_friday"),
    ("saturday", "weekend_saturday"),
];

type Stop = fn(u8) -> bool;

fn stop_line(c: u8) -> bool {
    c == b'\n'
}

fn stop_hash_line(c: u8) -> bool {
    c == b'#' || c == b'\n' || c == b';'
}

fn stop_line_semi(c: u8) -> bool {
    c == b'\n' || c == b';'
}

const PAYLOAD_RULES: [(&str, &str, Stop); 6] = [
    ("dateformat", DATE_FORMAT, stop_hash_line),
    ("axisformat", AXIS_FORMAT, stop_hash_line),
    ("tickinterval", TICK_INTERVAL, stop_hash_line),
    ("includes", INCLUDES, stop_hash_line),
    ("excludes", EXCLUDES, stop_hash_line),
    ("todaymarker", TODAY_MARKER, stop_line_semi),
];

const FLAGS: [(&str, &str); 2] = [
    ("inclusiveenddates", INCLUSIVE_END_DATES),
    ("topaxis", TOP_AXIS),
];

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
    Click,
    Href,
    CallName,
    CallArgs,
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
    delim: usize,
    keyword: usize,
    click_read: bool,
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
            delim: 0,
            keyword: 0,
            click_read: false,
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
            Mode::Click => self.click(),
            Mode::Href => self.href(),
            Mode::CallName => self.call_name(),
            Mode::CallArgs => self.call_args(),
            Mode::Initial => self.initial(),
        }
    }

    fn unterminated(&mut self, text: &str, at: usize) -> Token {
        self.mode = Mode::Initial;
        self.at = self.text.len();
        let begin = self.start.get(at).copied().unwrap_or(self.length);
        Token::new(
            UNTERMINATED,
            text.into(),
            Span {
                start: begin,
                end: self.length,
            },
        )
    }

    fn finish(&mut self) -> Token {
        match self.mode {
            Mode::Block => return self.unterminated("{", self.delim),
            Mode::Href => return self.unterminated("\"", self.delim),
            Mode::CallArgs => return self.unterminated("(", self.delim),
            Mode::CallName => return self.unterminated("call", self.keyword),
            _ => {}
        }
        let zero = Span {
            start: self.length,
            end: self.length,
        };
        let was_click = self.mode == Mode::Click;
        self.mode = Mode::Initial;
        if was_click && !self.click_read {
            let mut t = Token::new(
                CLICK,
                String::new(),
                self.span(self.keyword, self.text.len()),
            );
            t.payload = zero;
            return t;
        }
        let mut t = Token::new(EOF, String::new(), zero);
        t.payload = zero;
        t
    }

    fn value(&mut self, kind: &'static str) -> Token {
        let at = self.at;
        let end = at + self.line_len(at);
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

    fn click(&mut self) -> Option<Token> {
        let (r, n) = self.rune(self.at);
        if is_space(r) {
            self.mode = Mode::Initial;
            self.skip(self.at + n);
            return None;
        }
        let mut end = self.at;
        while end < self.text.len() {
            let (c, w) = self.rune(end);
            if is_space(c) {
                break;
            }
            end += w;
        }
        self.click_read = true;
        Some(self.payload_token(CLICK, self.keyword, self.at, end))
    }

    fn href(&mut self) -> Option<Token> {
        let at = self.at;
        if self.byte(at) == b'"' {
            self.mode = Mode::Initial;
            self.skip(at + 1);
            return None;
        }
        let Some(rel) = self
            .text
            .get(at..)
            .and_then(|rest| rest.iter().position(|&c| c == b'"'))
        else {
            return Some(self.finish());
        };
        let end = at + rel;
        self.mode = Mode::Initial;
        let mut t = self.payload_token(HREF, self.keyword, at, end);
        t.span = self.span(self.keyword, end + 1);
        self.at = end + 1;
        Some(t)
    }

    fn empty_args_end(&self, at: usize) -> Option<usize> {
        if at >= self.text.len() || self.byte(at) != b'(' {
            return None;
        }
        let ws = self.space_run(at + 1);
        (ws < self.text.len() && self.byte(ws) == b')').then_some(ws + 1)
    }

    fn call_name(&mut self) -> Option<Token> {
        let at = self.at;
        if let Some(end) = self.empty_args_end(at) {
            self.mode = Mode::Initial;
            self.skip(end);
            return None;
        }
        if self.byte(at) == b'(' {
            self.delim = at;
            self.mode = Mode::CallArgs;
            self.at = at + 1;
            return None;
        }
        let Some(rel) = self
            .text
            .get(at..)
            .and_then(|rest| rest.iter().position(|&c| c == b'('))
        else {
            return Some(self.finish());
        };
        let end = at + rel;
        let mut t = self.payload_token(CALLBACK_NAME, self.keyword, at, end);
        if let Some(closed) = self.empty_args_end(end) {
            t.span = self.span(self.keyword, closed);
            self.at = closed;
            self.mode = Mode::Initial;
        }
        Some(t)
    }

    fn call_args(&mut self) -> Option<Token> {
        let at = self.at;
        if self.byte(at) == b')' {
            self.mode = Mode::Initial;
            self.skip(at + 1);
            return None;
        }
        let Some(rel) = self
            .text
            .get(at..)
            .and_then(|rest| rest.iter().position(|&c| c == b')'))
        else {
            return Some(self.finish());
        };
        let end = at + rel;
        self.mode = Mode::Initial;
        let mut t = self.payload_token(CALLBACK_ARGS, self.delim, at, end);
        t.span = self.span(self.delim, end + 1);
        self.at = end + 1;
        Some(t)
    }

    fn newline_run(&self, from: usize) -> usize {
        let mut end = from;
        while end < self.text.len() && self.byte(end) == b'\n' {
            end += 1;
        }
        end
    }

    fn trivia(&mut self, at: usize) -> Option<Option<Token>> {
        let (r, n) = self.rune(at);
        let c = self.byte(at);
        if self.starts_with(at, b"%%") {
            self.skip(at + self.line_len(at));
        } else if r != '}' && self.byte(at + n) == b'%' && at + n < self.text.len() {
            self.skip(at + n + self.line_len(at + n));
        } else if c == b'%' {
            self.skip(self.newline_run(at + self.line_len(at)));
        } else if c == b'\n' {
            return Some(Some(self.token(NEWLINE, at, self.newline_run(at))));
        } else if is_space(r) {
            self.skip(self.space_run(at));
        } else {
            return None;
        }
        Some(None)
    }

    fn initial(&mut self) -> Option<Token> {
        let at = self.at;
        if let Some(handled) = self.accessibility(at) {
            return handled;
        }
        if let Some(handled) = self.trivia(at) {
            return handled;
        }
        self.statement(at)
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
            self.delim = colon;
            self.mode = Mode::Block;
            self.at = after;
            return Some(None);
        }
        None
    }

    fn word_then_space(&self, at: usize, word: &str) -> Option<usize> {
        if !self.fold(at, word) {
            return None;
        }
        let after = at + word.len();
        let run = self.space_run(after);
        (run > after).then_some(run)
    }

    fn statement(&mut self, at: usize) -> Option<Token> {
        if let Some(run) = self.word_then_space(at, "href")
            && run < self.text.len()
            && self.byte(run) == b'"'
        {
            self.keyword = at;
            self.delim = run;
            self.mode = Mode::Href;
            self.at = run + 1;
            return None;
        }
        if let Some(run) = self.word_then_space(at, "call") {
            self.keyword = at;
            self.mode = Mode::CallName;
            self.at = run;
            return None;
        }
        if let Some(run) = self.word_then_space(at, "click") {
            self.keyword = at;
            self.mode = Mode::Click;
            self.at = run;
            self.click_read = false;
            return None;
        }
        self.keyword_token(at)
    }

    fn keyword_payload(&self, at: usize, word: &str, stop: Stop) -> Option<(usize, usize)> {
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

    fn keyword_token(&mut self, at: usize) -> Option<Token> {
        if self.fold(at, GANTT) {
            return Some(self.token(GANTT, at, at + GANTT.len()));
        }
        for (word, kind, stop) in PAYLOAD_RULES {
            if let Some((from, end)) = self.keyword_payload(at, word, stop) {
                return Some(self.payload_token(kind, at, from, end));
            }
        }
        for (word, kind) in FLAGS {
            if self.fold(at, word) {
                return Some(self.token(kind, at, at + word.len()));
            }
        }
        if let Some((kind, end)) = self.day_rule(at) {
            return Some(self.token(kind, at, end));
        }
        self.line_rules(at)
    }

    fn day_rule(&self, at: usize) -> Option<(&'static str, usize)> {
        let groups: [(&str, &[(&'static str, &'static str)]); 2] =
            [("weekday", &WEEKDAYS), ("weekend", &WEEKENDS)];
        for (word, names) in groups {
            let Some(run) = self.word_then_space(at, word) else {
                continue;
            };
            for (name, kind) in names {
                if self.fold(run, name) {
                    return Some((kind, run + name.len()));
                }
            }
        }
        None
    }

    fn date_at(&self, at: usize) -> bool {
        const SHAPE: &[u8; 10] = b"dddd-dd-dd";
        if at + SHAPE.len() > self.text.len() {
            return false;
        }
        SHAPE.iter().enumerate().all(|(i, &shape)| {
            let c = self.byte(at + i);
            if shape == b'-' {
                c == b'-'
            } else {
                c.is_ascii_digit()
            }
        })
    }

    fn line_rules(&mut self, at: usize) -> Option<Token> {
        if self.date_at(at) {
            return Some(self.token(DATE, at, at + 10));
        }
        if let Some((from, end)) = self.keyword_payload(at, "title", stop_line) {
            return Some(self.payload_token(TITLE, at, from, end));
        }
        if let Some((from, end)) = self.keyword_payload(at, "accdescription", stop_hash_line) {
            return Some(self.payload_token(ACC_DESCRIPTION, at, from, end));
        }
        if let Some((from, end)) = self.keyword_payload(at, "section", stop_line) {
            return Some(self.payload_token(SECTION, at, from, end));
        }
        let mut end = at;
        while end < self.text.len() && self.byte(end) != b':' && self.byte(end) != b'\n' {
            end += 1;
        }
        if end > at {
            return Some(self.payload_token(TASK_TEXT, at, at, end));
        }
        Some(self.colon(at))
    }

    fn colon(&mut self, at: usize) -> Token {
        if self.byte(at) != b':' {
            let (_, n) = self.rune(at);
            return self.token(INVALID, at, at + n);
        }
        let mut end = at + 1;
        while end < self.text.len() && !stop_hash_line(self.byte(end)) {
            end += 1;
        }
        if end > at + 1 {
            return self.payload_token(TASK_DATA, at, at, end);
        }
        self.token(COLON, at, at + 1)
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
