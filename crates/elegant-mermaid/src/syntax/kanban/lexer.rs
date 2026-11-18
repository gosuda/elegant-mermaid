use super::ast::{Description, Token};
use crate::source::Span;

const HEADER_WORD: &str = "kanban";
const ICON_OPENER: &str = "::icon(";
const DATA_OPENER: &str = "@{";
const LINE_BREAK: &str = "<br/>";

pub(super) const K_SPACE_LINE: &str = "SPACELINE";
pub(super) const K_KANBAN: &str = "KANBAN";
pub(super) const K_CLASS: &str = "CLASS";
pub(super) const K_ICON: &str = "ICON";
pub(super) const K_NL: &str = "NL";
pub(super) const K_NODE_START: &str = "NODE_DSTART";
pub(super) const K_SPACE_LIST: &str = "SPACELIST";
pub(super) const K_NODE_ID: &str = "NODE_ID";
pub(super) const K_EOF: &str = "EOF";
pub(super) const K_NODE_DESCR: &str = "NODE_DESCR";
pub(super) const K_NODE_END: &str = "NODE_DEND";
pub(super) const K_INVALID: &str = "INVALID";
pub(super) const K_UNTERMINATED: &str = "UNTERMINATED";
pub(super) const K_END: &str = "END";
pub(super) const K_SHAPE_DATA: &str = "SHAPE_DATA";

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Initial,
    Node,
    Quoted,
    Markdown,
    Icon,
    Class,
    Data,
    DataString,
}

#[derive(Clone)]
struct Frame {
    mode: Mode,
    opener: usize,
    text: String,
}

const NODE_OPENERS: [&str; 8] = ["-)", "(-", "))", ")", "((", "{{", "(", "["];
const NODE_CLOSERS: [&str; 8] = ["))", ")", "]", "}}", "(-", "-)", "((", "("];

pub(super) struct Scanner {
    text: String,
    orig: Vec<usize>,
    end: usize,
    at: usize,
    frames: Vec<Frame>,
    eof_sent: bool,
    pub(super) crossed: bool,
    pending: Option<Token>,
    pub(super) closed_at: usize,
}

impl Scanner {
    pub(super) fn new(src: &str, removed: &[Span]) -> Self {
        let (filtered, orig) = filter_removed(src, removed);
        let mut start = 0;
        while start < filtered.len() {
            let (r, n) = unit(&filtered, start);
            if !is_space(r) {
                break;
            }
            start += n;
        }
        let mut text = filtered.get(start..).unwrap_or("").to_owned();
        text.push('\n');
        Self {
            text,
            orig: orig.get(start..).unwrap_or(&[]).to_vec(),
            end: src.len(),
            at: 0,
            frames: vec![Frame {
                mode: Mode::Initial,
                opener: 0,
                text: String::new(),
            }],
            eof_sent: false,
            crossed: false,
            pending: None,
            closed_at: 0,
        }
    }

    fn mode(&self) -> Mode {
        self.frames.last().map_or(Mode::Initial, |f| f.mode)
    }

    fn top(&self) -> Frame {
        self.frames.last().cloned().unwrap_or(Frame {
            mode: Mode::Initial,
            opener: 0,
            text: String::new(),
        })
    }

    fn push(&mut self, mode: Mode, opener: usize, text: &str) {
        self.frames.push(Frame {
            mode,
            opener,
            text: text.to_owned(),
        });
    }

    fn pop(&mut self) {
        if self.frames.len() > 1 {
            self.frames.pop();
        }
    }

    fn reset(&mut self) {
        self.frames.truncate(1);
    }

    fn start(&self, at: usize) -> usize {
        self.orig.get(at).copied().unwrap_or(self.end)
    }

    fn finish(&self, at: usize) -> usize {
        if at == 0 {
            return self.start(0);
        }
        if at > self.orig.len() {
            return self.end;
        }
        self.orig.get(at - 1).map_or(self.end, |o| o + 1)
    }

    fn span(&self, from: usize, to: usize) -> Span {
        let start = self.start(from);
        Span {
            start,
            end: self.finish(to).max(start),
        }
    }

    fn slice(&self, from: usize, to: usize) -> &str {
        self.text.get(from..to).unwrap_or("")
    }

    fn rest(&self, at: usize) -> &[u8] {
        self.text.as_bytes().get(at..).unwrap_or(&[])
    }

    fn token(&mut self, kind: &'static str, from: usize, to: usize) -> Token {
        self.at = to;
        Token::new(kind, self.slice(from, to), self.span(from, to))
    }

    fn run(&self, mut at: usize, keep: impl Fn(char) -> bool) -> usize {
        while at < self.text.len() {
            let (r, n) = unit(&self.text, at);
            if !keep(r) {
                break;
            }
            at += n;
        }
        at
    }

    fn fold(&self, at: usize, word: &str) -> bool {
        let Some(window) = self.text.as_bytes().get(at..at + word.len()) else {
            return false;
        };
        window
            .iter()
            .zip(word.bytes())
            .all(|(c, w)| c.to_ascii_lowercase() == w)
    }

    pub(super) fn next(&mut self) -> Token {
        if let Some(token) = self.pending.take() {
            return token;
        }
        loop {
            if let Some(token) = self.step() {
                return token;
            }
        }
    }

    pub(super) fn step(&mut self) -> Option<Token> {
        if self.at >= self.text.len() {
            return self.finish_input();
        }
        match self.mode() {
            Mode::Node => self.node(),
            Mode::Quoted => self.quoted(),
            Mode::Markdown => self.markdown(),
            Mode::Icon => self.icon(),
            Mode::Class => self.class(),
            Mode::Data => self.data(),
            Mode::DataString => self.data_string(),
            Mode::Initial => self.initial(),
        }
    }

    fn finish_input(&mut self) -> Option<Token> {
        let zero = Span {
            start: self.end,
            end: self.end,
        };
        match self.mode() {
            Mode::Initial => {
                let kind = if self.eof_sent { K_END } else { K_EOF };
                self.eof_sent = true;
                Some(Token::new(kind, "", zero))
            }
            Mode::Class => {
                self.pop();
                None
            }
            _ => {
                let open = self.top();
                self.reset();
                self.eof_sent = true;
                Some(Token::new(
                    K_UNTERMINATED,
                    &open.text,
                    Span {
                        start: self.start(open.opener),
                        end: self.end,
                    },
                ))
            }
        }
    }

    fn descr(&mut self, from: usize, to: usize, quote: Description) -> Token {
        let mut token = self.token(K_NODE_DESCR, from, to);
        token.quote = quote;
        token
    }

    fn invalid(&mut self) -> Option<Token> {
        let (_, n) = unit(&self.text, self.at);
        Some(self.token(K_INVALID, self.at, self.at + n))
    }

    fn comment_end(&self, at: usize) -> Option<usize> {
        let j = self.run(at, is_space);
        if !self.rest(j).starts_with(b"%%") {
            return None;
        }
        Some(self.run(j + 2, is_dot))
    }

    fn space_line_end(&self, at: usize) -> Option<usize> {
        let mut last = None;
        let mut j = at;
        while j < self.text.len() {
            let (r, n) = unit(&self.text, j);
            if !is_space(r) {
                break;
            }
            if r == '\n' && j > at {
                last = Some(j + n);
            }
            j += n;
        }
        last
    }

    fn header_at(&self, at: usize) -> bool {
        let end = at + HEADER_WORD.len();
        if !self.fold(at, HEADER_WORD) {
            return false;
        }
        self.text
            .as_bytes()
            .get(end)
            .is_none_or(|c| !is_word_byte(*c))
    }

    fn initial(&mut self) -> Option<Token> {
        let at = self.at;
        if self.rest(at).starts_with(DATA_OPENER.as_bytes()) {
            self.push(Mode::Data, at, DATA_OPENER);
            let mut token = self.token(K_SHAPE_DATA, at, at + DATA_OPENER.len());
            token.text.clear();
            return Some(token);
        }
        if let Some(end) = self.comment_end(at) {
            return Some(self.token(K_SPACE_LINE, at, end));
        }
        if self.header_at(at) {
            return Some(self.token(K_KANBAN, at, at + HEADER_WORD.len()));
        }
        if self.rest(at).starts_with(b":::") {
            self.push(Mode::Class, at, ":::");
            self.at = at + 3;
            return None;
        }
        if self.fold(at, ICON_OPENER) {
            let opener = self.slice(at, at + ICON_OPENER.len()).to_owned();
            self.push(Mode::Icon, at, &opener);
            self.at = at + ICON_OPENER.len();
            return None;
        }
        self.initial_lines(at)
    }

    fn initial_lines(&mut self, at: usize) -> Option<Token> {
        if let Some(end) = self.space_line_end(at) {
            self.crossed = true;
            return Some(self.token(K_SPACE_LINE, at, end));
        }
        let end = self.run(at, |r| r == '\n');
        if end > at {
            self.crossed = true;
            return Some(self.token(K_NL, at, end));
        }
        for opener in NODE_OPENERS {
            if self.rest(at).starts_with(opener.as_bytes()) {
                self.push(Mode::Node, at, opener);
                return Some(self.token(K_NODE_START, at, at + opener.len()));
            }
        }
        let end = self.run(at, is_space);
        if end > at {
            return Some(self.token(K_SPACE_LIST, at, end));
        }
        let end = self.run(at, is_id_char);
        if end > at {
            return Some(self.token(K_NODE_ID, at, end));
        }
        self.invalid()
    }

    fn node(&mut self) -> Option<Token> {
        let at = self.at;
        if self.rest(at).starts_with(b"\"`") {
            self.push(Mode::Markdown, at, "\"`");
            self.at = at + 2;
            return None;
        }
        if self.rest(at).first() == Some(&b'"') {
            self.push(Mode::Quoted, at, "\"");
            self.at = at + 1;
            return None;
        }
        for closer in NODE_CLOSERS {
            if self.rest(at).starts_with(closer.as_bytes()) {
                self.pop();
                return Some(self.token(K_NODE_END, at, at + closer.len()));
            }
        }
        let end = self.run(at, is_descr_char);
        if end > at {
            return Some(self.descr(at, end, Description::Plain));
        }
        let end = self.run(at, is_dot);
        if end > at {
            return Some(self.descr(at, end, Description::Plain));
        }
        self.invalid()
    }

    fn quoted(&mut self) -> Option<Token> {
        let at = self.at;
        if self.rest(at).first() == Some(&b'"') {
            self.pop();
            self.at = at + 1;
            return None;
        }
        let end = self.run(at, |r| r != '"');
        Some(self.descr(at, end, Description::Quoted))
    }

    fn markdown(&mut self) -> Option<Token> {
        let at = self.at;
        if self.rest(at).starts_with(b"`\"") {
            self.pop();
            self.at = at + 2;
            return None;
        }
        let end = self.run(at, |r| r != '`' && r != '"');
        if end > at {
            return Some(self.descr(at, end, Description::Markdown));
        }
        self.invalid()
    }

    fn icon(&mut self) -> Option<Token> {
        let at = self.at;
        if self.rest(at).first() == Some(&b')') {
            self.pop();
            self.at = at + 1;
            return None;
        }
        let end = self.run(at, |r| r != ')');
        let closed = if end < self.text.len() { end + 1 } else { end };
        let token = Token::new(
            K_ICON,
            self.slice(at, end),
            self.span(self.top().opener, closed),
        );
        self.at = end;
        Some(token)
    }

    fn class(&mut self) -> Option<Token> {
        let at = self.at;
        let (r, n) = unit(&self.text, at);
        if r == '\n' {
            self.crossed = true;
            self.pop();
            self.at = at + n;
            return None;
        }
        let end = self.run(at, is_dot);
        if end == at {
            return self.invalid();
        }
        let opener = self.top().opener;
        self.pop();
        let token = Token::new(K_CLASS, self.slice(at, end), self.span(opener, end));
        self.at = end;
        Some(token)
    }

    fn data(&mut self) -> Option<Token> {
        let at = self.at;
        match self.rest(at).first() {
            Some(b'}') => {
                self.pop();
                self.at = at + 1;
                self.closed_at = self.finish(at + 1);
                return None;
            }
            Some(b'"') => {
                let open = self.top();
                self.push(Mode::DataString, open.opener, &open.text);
                return Some(self.token(K_SHAPE_DATA, at, at + 1));
            }
            _ => {}
        }
        let end = self.run(at, is_data_char);
        if end > at {
            return Some(self.token(K_SHAPE_DATA, at, end));
        }
        self.invalid()
    }

    fn data_string(&mut self) -> Option<Token> {
        let at = self.at;
        if self.rest(at).first() == Some(&b'"') {
            self.pop();
            return Some(self.token(K_SHAPE_DATA, at, at + 1));
        }
        let end = self.run(at, |r| r != '"');
        let mut token = self.token(K_SHAPE_DATA, at, end);
        token.text = fold_breaks(&token.text);
        Some(token)
    }

    /// Skips the rest of the current line and returns the end of its content.
    pub(super) fn skip_line(&mut self, mut content_end: usize) -> usize {
        loop {
            self.crossed = false;
            if let Some(token) = self.step() {
                if matches!(token.kind, K_EOF | K_END | K_UNTERMINATED) {
                    self.pending = Some(token);
                    return content_end;
                }
                if !is_separator(token.kind) {
                    content_end = content_end.max(token.span.end);
                }
            }
            if self.crossed {
                self.reset();
                return content_end;
            }
        }
    }
}

pub(super) fn is_separator(kind: &str) -> bool {
    matches!(kind, K_NL | K_SPACE_LINE | K_EOF | K_END)
}

fn fold_breaks(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut at = 0;
    while at < text.len() {
        let (r, n) = unit(text, at);
        if r != '\n' {
            out.push_str(text.get(at..at + n).unwrap_or(""));
            at += n;
            continue;
        }
        out.push_str(LINE_BREAK);
        at += n;
        while at < text.len() {
            let (next, width) = unit(text, at);
            if !is_space(next) {
                break;
            }
            at += width;
        }
    }
    out
}

fn filter_removed(src: &str, removed: &[Span]) -> (String, Vec<usize>) {
    let mut text = String::with_capacity(src.len());
    let mut orig = Vec::with_capacity(src.len());
    let mut at = 0;
    for span in removed {
        let from = span.start.max(at);
        let to = span.end.min(src.len());
        if from >= to {
            continue;
        }
        let Some(kept) = src.get(at..from) else {
            continue;
        };
        orig.extend(at..from);
        text.push_str(kept);
        at = to;
    }
    orig.extend(at..src.len());
    text.push_str(src.get(at..).unwrap_or(""));
    (text, orig)
}

/// The scalar at `at` and its byte length; CR and CRLF read as one LF.
fn unit(text: &str, at: usize) -> (char, usize) {
    let bytes = text.as_bytes();
    match bytes.get(at) {
        Some(b'\r') => {
            if bytes.get(at + 1) == Some(&b'\n') {
                ('\n', 2)
            } else {
                ('\n', 1)
            }
        }
        Some(c) if *c < 0x80 => (char::from(*c), 1),
        _ => text
            .get(at..)
            .and_then(|rest| rest.chars().next())
            .map_or(('\u{fffd}', 1), |ch| (ch, ch.len_utf8())),
    }
}

fn is_space(r: char) -> bool {
    matches!(
        r,
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

fn is_dot(r: char) -> bool {
    !matches!(r, '\n' | '\u{2028}' | '\u{2029}')
}

fn is_id_char(r: char) -> bool {
    !matches!(r, '(' | '[' | '\n' | ')' | '{' | '}' | '@')
}

fn is_data_char(r: char) -> bool {
    !matches!(r, '}' | '^' | '"')
}

fn is_descr_char(r: char) -> bool {
    !matches!(r, ')' | ']' | '(' | '}')
}

fn is_word_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}
