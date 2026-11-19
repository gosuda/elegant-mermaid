//! Lexer for the venn grammar of `spec/grammar/venn.md`.
//!
//! The lexer reads the text without the preprocessing spans, as the authority does, and
//! maps each token back to the source. Rules follow the authority's order, a keyword
//! ends at a word boundary, and the indent flag that the parser sets after a `set` or
//! `union` statement decides whether an indented `text` line is a statement of its own.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Initial,
    Bol,
}

enum Step {
    Token(Token),
    Skip,
    Pass,
}

struct Fragment {
    eff: usize,
    orig: usize,
}

pub(super) struct Lexer {
    src: String,
    size: usize,
    frags: Vec<Fragment>,
    at: usize,
    mode: Mode,
    pub(super) indent: bool,
    consume: bool,
}

const KEYWORDS: &[(&str, &str)] = &[
    ("venn-beta", "VENN"),
    ("set", "SET"),
    ("union", "UNION"),
    ("text", "TEXT"),
    ("style", "STYLE"),
];

fn is_word_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn is_line_byte(c: u8) -> bool {
    c == b'\n' || c == b'\r'
}

fn is_blank(c: u8) -> bool {
    c == b' ' || c == b'\t'
}

pub fn js_space(c: char) -> bool {
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

fn keep(kept: &mut String, frags: &mut Vec<Fragment>, source: &str, from: usize, to: usize) {
    if to > from {
        frags.push(Fragment {
            eff: kept.len(),
            orig: from,
        });
        kept.push_str(source.get(from..to).unwrap_or(""));
    }
}

impl Lexer {
    pub(super) fn new(source: &str, removed: &[Span]) -> Lexer {
        let mut kept = String::new();
        let mut frags = Vec::new();
        let mut at = 0;
        for span in removed {
            if span.start < at || span.end > source.len() {
                continue;
            }
            keep(&mut kept, &mut frags, source, at, span.start);
            at = span.end;
        }
        keep(&mut kept, &mut frags, source, at, source.len());
        Lexer {
            src: kept,
            size: source.len(),
            frags,
            at: 0,
            mode: Mode::Initial,
            indent: false,
            consume: false,
        }
    }

    fn origin(&self, at: usize) -> usize {
        if at >= self.src.len() {
            return self.size;
        }
        let i = self
            .frags
            .partition_point(|f| f.eff <= at)
            .saturating_sub(1);
        self.frags.get(i).map_or(self.size, |f| f.orig + at - f.eff)
    }

    fn span(&self, start: usize, end: usize) -> Span {
        if end <= start {
            let at = self.origin(start);
            return Span { start: at, end: at };
        }
        Span {
            start: self.origin(start),
            end: self.origin(end - 1) + 1,
        }
    }

    fn bytes(&self) -> &[u8] {
        self.src.as_bytes()
    }

    fn rest(&self) -> &str {
        self.src.get(self.at..).unwrap_or("")
    }

    fn byte_at(&self, at: usize) -> Option<u8> {
        self.bytes().get(at).copied()
    }

    fn match_fold(&self, at: usize, word: &str) -> bool {
        self.bytes()
            .get(at..at + word.len())
            .is_some_and(|window| window.eq_ignore_ascii_case(word.as_bytes()))
    }

    fn word_at(&self, at: usize, word: &str) -> bool {
        self.match_fold(at, word)
            && self
                .byte_at(at + word.len())
                .is_none_or(|c| !is_word_byte(c))
    }

    fn token(&mut self, kind: &'static str, length: usize) -> Token {
        let end = (self.at + length).min(self.src.len());
        let token = Token {
            kind,
            text: self.src.get(self.at..end).unwrap_or("").to_owned(),
            span: self.span(self.at, end),
        };
        self.at = end;
        token
    }

    fn valued(&mut self, kind: &'static str, text: &str, length: usize) -> Token {
        let end = (self.at + length).min(self.src.len());
        let token = Token {
            kind,
            text: text.to_owned(),
            span: self.span(self.at, end),
        };
        self.at = end;
        token
    }

    fn unterminated(&mut self, opener: &str) -> Token {
        let start = self.at;
        self.at = self.src.len();
        Token {
            kind: "UNTERMINATED",
            text: opener.to_owned(),
            span: self.span(start, self.src.len()),
        }
    }

    pub(super) fn next(&mut self) -> Token {
        loop {
            if self.at >= self.src.len() {
                return Token {
                    kind: "EOF",
                    text: String::new(),
                    span: Span {
                        start: self.size,
                        end: self.size,
                    },
                };
            }
            if let Step::Token(token) = self.step() {
                return token;
            }
        }
    }

    fn step(&mut self) -> Step {
        if self.comment() {
            return Step::Skip;
        }
        if self.mode == Mode::Bol {
            match self.line_start() {
                Step::Pass => {}
                other => return other,
            }
        }
        let c = self.byte_at(self.at).unwrap_or(b' ');
        self.body(c)
    }

    fn to_line_end(&self, from: usize) -> usize {
        self.src
            .get(from..)
            .and_then(|tail| tail.find(['\r', '\n']))
            .map_or(self.src.len(), |i| from + i)
    }

    fn comment(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with("%%") && !rest.starts_with("%%{") {
            self.at = self.to_line_end(self.at);
            return true;
        }
        let Some(first) = rest.chars().next() else {
            return false;
        };
        if first != '}' && rest[first.len_utf8()..].starts_with("%%") {
            self.at = self.to_line_end(self.at + first.len_utf8() + 2);
            return true;
        }
        false
    }

    fn blanks(&self, at: usize) -> usize {
        self.bytes()
            .get(at..)
            .unwrap_or_default()
            .iter()
            .take_while(|c| is_blank(**c))
            .count()
    }

    fn line_start(&mut self) -> Step {
        let n = self.blanks(self.at);
        if n > 0 {
            return self.indented_line(n);
        }
        if self.byte_at(self.at).is_some_and(is_line_byte) {
            return Step::Pass;
        }
        self.indent = false;
        self.mode = Mode::Initial;
        Step::Skip
    }

    fn indented_line(&mut self, n: usize) -> Step {
        if self.indent && self.word_at(self.at + n, "text") {
            self.consume = true;
            self.mode = Mode::Initial;
            return Step::Token(self.token("INDENT_TEXT", n));
        }
        self.at += n;
        Step::Skip
    }

    fn body(&mut self, c: u8) -> Step {
        if is_line_byte(c) {
            return Step::Token(self.newline());
        }
        if self.rest().starts_with("%%") {
            self.at = self.to_line_end(self.at);
            return Step::Skip;
        }
        if is_blank(c) {
            self.at += self.blanks(self.at);
            return Step::Skip;
        }
        self.word(c)
    }

    fn newline(&mut self) -> Token {
        let n = self.bytes()[self.at..]
            .iter()
            .take_while(|c| is_line_byte(**c))
            .count();
        self.mode = Mode::Bol;
        self.token("NEWLINE", n)
    }

    fn word(&mut self, c: u8) -> Step {
        if let Some(token) = self.title() {
            return Step::Token(token);
        }
        for (text, kind) in KEYWORDS {
            if !self.word_at(self.at, text) {
                continue;
            }
            if *kind == "TEXT" && self.consume {
                self.consume = false;
                self.at += text.len();
                return Step::Skip;
            }
            return Step::Token(self.token(kind, text.len()));
        }
        Step::Token(self.value(c))
    }

    fn title(&mut self) -> Option<Token> {
        if !self.match_fold(self.at, "title") {
            return None;
        }
        let at = self.at + "title".len();
        let space = self
            .src
            .get(at..)?
            .chars()
            .next()
            .filter(|c| js_space(*c))?;
        let start = at + space.len_utf8();
        let n = self.bytes()[start..]
            .iter()
            .take_while(|c| !matches!(**c, b'#' | b'\r' | b'\n' | b';'))
            .count();
        if n == 0 {
            return None;
        }
        Some(self.token("TITLE", start + n - self.at))
    }

    fn value(&mut self, c: u8) -> Token {
        match c {
            b'[' => self.bracket(),
            b'"' => self.quoted(),
            b',' => self.token("COMMA", 1),
            b':' => self.token("COLON", 1),
            _ => self.literal(),
        }
    }

    fn literal(&mut self) -> Token {
        let rules: [(&'static str, usize); 5] = [
            ("NUMERIC", self.number(self.at)),
            ("HEXCOLOR", self.hex_colour()),
            ("RGBACOLOR", self.colour("rgba", 4)),
            ("RGBCOLOR", self.colour("rgb", 3)),
            ("IDENTIFIER", self.identifier()),
        ];
        for (kind, n) in rules {
            if n > 0 {
                return self.token(kind, n);
            }
        }
        let size = self.rest().chars().next().map_or(1, char::len_utf8);
        self.token("INVALID", size)
    }

    fn hex_colour(&self) -> usize {
        if self.byte_at(self.at) != Some(b'#') {
            return 0;
        }
        let n = self
            .bytes()
            .get(self.at + 1..)
            .unwrap_or_default()
            .iter()
            .take(8)
            .take_while(|c| c.is_ascii_hexdigit())
            .count();
        if n < 3 { 0 } else { 1 + n }
    }

    fn identifier(&self) -> usize {
        let Some(first) = self.byte_at(self.at) else {
            return 0;
        };
        if first != b'_' && !first.is_ascii_alphabetic() {
            return 0;
        }
        1 + self
            .bytes()
            .get(self.at + 1..)
            .unwrap_or_default()
            .iter()
            .take_while(|c| is_word_byte(**c) || **c == b'-')
            .count()
    }

    fn quoted(&mut self) -> Token {
        match self.rest().get(1..).and_then(|tail| tail.find('"')) {
            Some(i) => self.token("STRING", i + 2),
            None => self.unterminated("\""),
        }
    }

    fn bracket(&mut self) -> Token {
        let rest = self.rest().get(1..).unwrap_or("").to_owned();
        if let Some(after_quote) = rest.strip_prefix('"') {
            return self.quoted_bracket(after_quote);
        }
        match rest.find([']', '"']) {
            None => self.unterminated("["),
            Some(0) => self.token("INVALID", 1),
            Some(i) if rest.as_bytes()[i] == b'"' => self.token("INVALID", 1),
            Some(i) => {
                let label = rest[..i].trim_matches(js_space);
                self.valued("BRACKET_LABEL", label, i + 2)
            }
        }
    }

    fn quoted_bracket(&mut self, after_quote: &str) -> Token {
        let Some(i) = after_quote.find('"') else {
            return self.unterminated("[");
        };
        match after_quote.as_bytes().get(i + 1) {
            None => self.unterminated("["),
            Some(b']') => self.valued("BRACKET_LABEL", &after_quote[..i], i + 4),
            Some(_) => self.token("INVALID", 1),
        }
    }

    fn digits(&self, at: usize) -> usize {
        self.bytes()
            .get(at..)
            .unwrap_or_default()
            .iter()
            .take_while(|c| c.is_ascii_digit())
            .count()
    }

    fn fraction(&self, at: usize) -> usize {
        match (self.byte_at(at), self.byte_at(at + 1)) {
            (Some(b'.'), Some(d)) if d.is_ascii_digit() => 1 + self.digits(at + 1),
            _ => 0,
        }
    }

    fn number(&self, at: usize) -> usize {
        let start = at;
        let mut at = at;
        if matches!(self.byte_at(at), Some(b'+' | b'-')) {
            at += 1;
        }
        let whole = self.digits(at);
        at += whole;
        let frac = self.fraction(at);
        if whole == 0 && frac == 0 {
            return 0;
        }
        at + frac - start
    }

    fn spaces(&self, at: usize) -> usize {
        self.src
            .get(at..)
            .unwrap_or("")
            .chars()
            .take_while(|c| js_space(*c))
            .map(char::len_utf8)
            .sum()
    }

    fn colour_part(&self, at: usize, want: u8) -> Option<usize> {
        let at = at + self.spaces(at);
        let digits = self
            .bytes()
            .get(at..)
            .unwrap_or_default()
            .iter()
            .take_while(|c| c.is_ascii_digit() || **c == b'.')
            .count();
        if digits == 0 {
            return None;
        }
        let at = at + digits;
        let at = at + self.spaces(at);
        (self.byte_at(at) == Some(want)).then_some(at + 1)
    }

    fn colour(&self, name: &str, parts: usize) -> usize {
        if !self.match_fold(self.at, name) || self.byte_at(self.at + name.len()) != Some(b'(') {
            return 0;
        }
        let mut at = self.at + name.len() + 1;
        for i in 0..parts {
            let want = if i == parts - 1 { b')' } else { b',' };
            match self.colour_part(at, want) {
                Some(next) => at = next,
                None => return 0,
            }
        }
        at - self.at
    }
}
