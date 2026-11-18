use super::ast::Token;
use crate::source::Span;

const HEADER_WORDS: [&str; 2] = ["ishikawa-beta", "ishikawa"];

pub(super) const K_SPACE_LINE: &str = "SPACELINE";
pub(super) const K_ISHIKAWA: &str = "ISHIKAWA";
pub(super) const K_NL: &str = "NL";
pub(super) const K_SPACE_LIST: &str = "SPACELIST";
pub(super) const K_TEXT: &str = "TEXT";
pub(super) const K_EOF: &str = "EOF";
pub(super) const K_END: &str = "END";

pub(super) struct Scanner {
    text: String,
    orig: Vec<usize>,
    end: usize,
    at: usize,
    eof_sent: bool,
    crossed: bool,
    pending: Option<Token>,
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
            eof_sent: false,
            crossed: false,
            pending: None,
        }
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
        match self.pending.take() {
            Some(token) => token,
            None => self.step(),
        }
    }

    fn step(&mut self) -> Token {
        if self.at >= self.text.len() {
            let zero = Span {
                start: self.end,
                end: self.end,
            };
            let kind = if self.eof_sent { K_END } else { K_EOF };
            self.eof_sent = true;
            return Token::new(kind, "", zero);
        }
        self.initial()
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

    fn header_end(&self, at: usize) -> Option<usize> {
        HEADER_WORDS.iter().find_map(|word| {
            let end = at + word.len();
            let bounded = self
                .text
                .as_bytes()
                .get(end)
                .is_none_or(|c| !is_word_byte(*c));
            (self.fold(at, word) && bounded).then_some(end)
        })
    }

    fn initial(&mut self) -> Token {
        let at = self.at;
        if let Some(end) = self.comment_end(at) {
            return self.token(K_SPACE_LINE, at, end);
        }
        if let Some(end) = self.header_end(at) {
            return self.token(K_ISHIKAWA, at, end);
        }
        if let Some(end) = self.space_line_end(at) {
            self.crossed = true;
            return self.token(K_SPACE_LINE, at, end);
        }
        let end = self.run(at, |r| r == '\n');
        if end > at {
            self.crossed = true;
            return self.token(K_NL, at, end);
        }
        let end = self.run(at, is_space);
        if end > at {
            return self.token(K_SPACE_LIST, at, end);
        }
        let end = self.run(at, |r| r != '\n');
        self.token(K_TEXT, at, end)
    }

    /// Skips the rest of the current line and returns the end of its content.
    pub(super) fn skip_line(&mut self, mut content_end: usize) -> usize {
        loop {
            self.crossed = false;
            let token = self.step();
            if matches!(token.kind, K_EOF | K_END) {
                self.pending = Some(token);
                return content_end;
            }
            if !is_separator(token.kind) {
                content_end = content_end.max(token.span.end);
            }
            if self.crossed {
                return content_end;
            }
        }
    }
}

pub(super) fn is_separator(kind: &str) -> bool {
    matches!(kind, K_NL | K_SPACE_LINE | K_EOF | K_END)
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

/// The ECMAScript whitespace and line terminator set of the authority lexer.
pub fn is_space(r: char) -> bool {
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

fn is_word_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}
