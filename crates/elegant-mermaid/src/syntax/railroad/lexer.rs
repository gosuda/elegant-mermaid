use super::ast::{Notation, Token};
use super::text::{is_js_space, is_line_terminator};
use crate::source::Span;

const WORD_KEYWORDS: [&str; 8] = [
    "nonterminal",
    "zeroOrMore",
    "oneOrMore",
    "terminal",
    "optional",
    "sequence",
    "special",
    "choice",
];

pub(super) const fn header_of(notation: Notation) -> &'static str {
    match notation {
        Notation::Constructor => "railroad-beta",
        Notation::Ebnf => "railroad-ebnf-beta",
        Notation::Abnf => "railroad-abnf-beta",
        Notation::Peg => "railroad-peg-beta",
    }
}

const fn punctuation(notation: Notation) -> &'static [&'static str] {
    match notation {
        Notation::Constructor => &["=", ";", "(", ",", ")"],
        Notation::Ebnf => &[
            "::=", "=", ";", "|", ",", "(", ")", "[", "]", "{", "}", "?", "*", "+", "-",
        ],
        Notation::Abnf => &["=", ";", "/", "(", ")", "[", "]"],
        Notation::Peg => &["<-", ";", "/", "(", ")", "&", "!", "?", "*", "+", "."],
    }
}

pub(super) fn equal_fold_ascii(a: &[u8], b: &str) -> bool {
    a.eq_ignore_ascii_case(b.as_bytes())
}

pub(super) fn decode(bytes: &[u8]) -> (char, usize) {
    let Some(&first) = bytes.first() else {
        return ('\u{fffd}', 0);
    };
    let width = match first {
        0x00..=0x7f => 1,
        0xc2..=0xdf => 2,
        0xe0..=0xef => 3,
        0xf0..=0xf4 => 4,
        _ => return ('\u{fffd}', 1),
    };
    bytes
        .get(..width)
        .and_then(|prefix| std::str::from_utf8(prefix).ok())
        .and_then(|text| text.chars().next())
        .map_or(('\u{fffd}', 1), |c| (c, width))
}

struct Scanner<'a> {
    orig: &'a [u8],
    src: Vec<u8>,
    removed: &'a [Span],
    n: Notation,
    at: usize,
    tokens: Vec<Token>,
    no_yaml_close: bool,
}

pub(super) fn lex(text: &str, removed: &[Span], n: Notation) -> Vec<Token> {
    let mut scanner = Scanner {
        orig: text.as_bytes(),
        src: blank(text, removed),
        removed,
        n,
        at: 0,
        tokens: Vec::new(),
        no_yaml_close: false,
    };
    scanner.run();
    scanner.tokens
}

fn blank(text: &str, removed: &[Span]) -> Vec<u8> {
    let mut bytes = text.as_bytes().to_vec();
    for span in removed {
        let end = span.end.min(bytes.len());
        for byte in bytes.iter_mut().take(end).skip(span.start) {
            *byte = b' ';
        }
    }
    bytes
}

fn is_digit(c: u8) -> bool {
    c.is_ascii_digit()
}

impl Scanner<'_> {
    fn len(&self) -> usize {
        self.src.len()
    }

    fn byte(&self, i: usize) -> Option<u8> {
        self.src.get(i).copied()
    }

    fn rest(&self) -> &[u8] {
        self.src.get(self.at..).unwrap_or(&[])
    }

    fn starts_with(&self, prefix: &str) -> bool {
        self.rest().starts_with(prefix.as_bytes())
    }

    fn slice(&self, start: usize, end: usize) -> String {
        let bytes: Vec<u8> = (start..end)
            .filter(|&i| !self.in_removed(i))
            .filter_map(|i| self.orig.get(i).copied())
            .collect();
        String::from_utf8_lossy(&bytes).into_owned()
    }

    fn in_removed(&self, i: usize) -> bool {
        self.removed
            .iter()
            .any(|span| span.start <= i && i < span.end)
    }

    fn emit(&mut self, kind: &str, end: usize) {
        let token = Token {
            kind: kind.to_owned(),
            text: self.slice(self.at, end),
            span: Span {
                start: self.at,
                end,
            },
        };
        self.tokens.push(token);
        self.at = end;
    }

    fn terminate(&mut self, opener: &str, from: usize) {
        self.tokens.push(Token {
            kind: "UNTERMINATED".to_owned(),
            text: opener.to_owned(),
            span: Span {
                start: from,
                end: self.len(),
            },
        });
        self.at = self.len();
    }

    fn run(&mut self) {
        while let Some(c) = self.byte(self.at) {
            if matches!(c, b' ' | b'\t' | b'\r' | b'\n') {
                self.at += 1;
                continue;
            }
            if self.hidden() {
                continue;
            }
            self.token();
        }
        let end = self.len();
        self.tokens.push(Token {
            kind: "EOF".to_owned(),
            text: String::new(),
            span: Span { start: end, end },
        });
    }

    fn line_end(&self, from: usize) -> usize {
        (from..self.len())
            .find(|&i| matches!(self.byte(i), Some(b'\n' | b'\r')))
            .unwrap_or(self.len())
    }

    fn value_end(&self, from: usize) -> usize {
        let end = self.line_end(from);
        (from..end.saturating_sub(1))
            .find(|&i| self.byte(i) == Some(b'%') && self.byte(i + 1) == Some(b'%'))
            .unwrap_or(end)
    }

    fn hidden(&mut self) -> bool {
        self.percent_comment()
            || self.frontmatter_block()
            || self.block_comment()
            || self.iso_comment()
            || self.abnf_comment()
            || self.peg_comment()
    }

    fn percent_comment(&mut self) -> bool {
        if !self.starts_with("%%") {
            return false;
        }
        self.at = self.line_end(self.at);
        true
    }

    fn frontmatter_block(&mut self) -> bool {
        if !self.starts_with("---") {
            return false;
        }
        let Some(end) = self.yaml() else {
            return false;
        };
        self.at = end;
        true
    }

    fn find_from(&self, from: usize, needle: &str) -> Option<usize> {
        let haystack = self.src.get(from..)?;
        let needle = needle.as_bytes();
        haystack
            .windows(needle.len())
            .position(|window| window == needle)
    }

    fn block_comment(&mut self) -> bool {
        if !self.starts_with("/*") || (self.n != Notation::Constructor && self.n != Notation::Ebnf)
        {
            return false;
        }
        let Some(idx) = self.find_from(self.at + 2, "*/") else {
            self.terminate("/*", self.at);
            return true;
        };
        self.at += 2 + idx + 2;
        true
    }

    fn abnf_comment(&mut self) -> bool {
        if self.n != Notation::Abnf || self.byte(self.at) != Some(b';') {
            return false;
        }
        if matches!(self.byte(self.at + 1), None | Some(b'\n' | b'\r')) {
            return false;
        }
        self.at = self.line_end(self.at);
        true
    }

    fn peg_comment(&mut self) -> bool {
        if self.n != Notation::Peg || self.byte(self.at) != Some(b'#') {
            return false;
        }
        self.at = self.line_end(self.at);
        true
    }

    fn iso_comment(&mut self) -> bool {
        if self.n != Notation::Ebnf || !self.starts_with("(*") {
            return false;
        }
        let Some(idx) = self.find_from(self.at + 2, "*)") else {
            return false;
        };
        self.at += 2 + idx + 2;
        true
    }

    fn yaml_body_start(&self) -> Option<usize> {
        let mut i = self.horizontal(self.at + 3);
        if self.byte(i) == Some(b'\r') {
            i += 1;
        }
        (self.byte(i) == Some(b'\n')).then_some(i + 1)
    }

    fn yaml(&mut self) -> Option<usize> {
        if self.no_yaml_close {
            return None;
        }
        let mut line = Some(self.yaml_body_start()?);
        while let Some(start) = line {
            if let Some(end) = self.yaml_closes_at(start) {
                return Some(end);
            }
            line = self.next_line(start);
        }
        self.no_yaml_close = true;
        None
    }

    fn yaml_closes_at(&self, line: usize) -> Option<usize> {
        if !self.src.get(line..)?.starts_with(b"---") {
            return None;
        }
        self.yaml_close(line + 3)
    }

    fn next_line(&self, from: usize) -> Option<usize> {
        let tail = self.src.get(from..)?;
        tail.iter().position(|&c| c == b'\n').map(|i| from + i + 1)
    }

    fn yaml_close(&self, after: usize) -> Option<usize> {
        if self.byte(after) == Some(b'\n') {
            return Some(after + 1);
        }
        let tail = self.src.get(after..).unwrap_or(&[]);
        if tail.starts_with(b"\r\n") {
            return Some(after + 2);
        }
        if after >= self.len() {
            return Some(after);
        }
        let (r, _) = decode(tail);
        is_js_space(r).then_some(after)
    }

    fn token(&mut self) {
        let matched = self.header()
            || self.word_keyword()
            || self.special()
            || self.punct()
            || self.meta()
            || self.identifier()
            || self.quoted()
            || self.numval()
            || self.repeat();
        if matched {
            return;
        }
        let (_, size) = decode(self.rest());
        self.emit("INVALID", self.at + size);
    }

    fn meta(&mut self) -> bool {
        if self.starts_with("title") {
            let end = self.title_end();
            self.emit("TITLE", end);
            return true;
        }
        if self.starts_with("accTitle") {
            return self.acc_title();
        }
        if self.starts_with("accDescr") {
            return self.acc_descr();
        }
        false
    }

    fn identifier(&mut self) -> bool {
        let length = self.id_len();
        if length == 0 {
            return false;
        }
        self.emit("ID", self.at + length);
        true
    }

    fn quoted(&mut self) -> bool {
        match self.byte(self.at) {
            Some(b'"') => {}
            Some(b'\'') if self.n != Notation::Abnf => {}
            _ => return false,
        }
        self.string();
        true
    }

    fn header(&mut self) -> bool {
        let keyword = header_of(self.n);
        let end = self.at + keyword.len();
        let Some(candidate) = self.src.get(self.at..end) else {
            return false;
        };
        if !equal_fold_ascii(candidate, keyword) {
            return false;
        }
        let tail = self.src.get(end..).unwrap_or(&[]);
        if !tail.is_empty() && !tail.starts_with(b"%%") && !is_js_space(decode(tail).0) {
            return false;
        }
        self.emit("HEADER", end);
        true
    }

    fn word_keyword(&mut self) -> bool {
        if self.n != Notation::Constructor {
            return false;
        }
        for keyword in WORD_KEYWORDS {
            if self.starts_with(keyword) {
                if self.id_len() > keyword.len() {
                    return false;
                }
                self.emit(keyword, self.at + keyword.len());
                return true;
            }
        }
        false
    }

    fn special(&mut self) -> bool {
        if self.n != Notation::Ebnf || self.byte(self.at) != Some(b'?') {
            return false;
        }
        let mut i = self.at + 1;
        while let Some(c) = self.byte(i) {
            if c == b'?' || c == b';' {
                break;
            }
            i += 1;
        }
        if self.byte(i) != Some(b'?') {
            return false;
        }
        let body = self.src.get(self.at + 1..i).unwrap_or(&[]);
        if all_js_space(body) {
            return false;
        }
        self.emit("SPECIAL", i + 1);
        true
    }

    fn punct(&mut self) -> bool {
        for p in punctuation(self.n) {
            if self.starts_with(p) {
                self.emit(p, self.at + p.len());
                return true;
            }
        }
        false
    }

    fn title_end(&self) -> usize {
        let i = self.at + "title".len();
        if matches!(self.byte(i), Some(b' ' | b'\t')) {
            return self.value_end(i + 1);
        }
        i
    }

    fn horizontal(&self, mut from: usize) -> usize {
        while matches!(self.byte(from), Some(b' ' | b'\t')) {
            from += 1;
        }
        from
    }

    fn acc_title(&mut self) -> bool {
        let i = self.horizontal(self.at + "accTitle".len());
        if self.byte(i) != Some(b':') {
            return false;
        }
        let end = self.value_end(i + 1);
        self.emit("ACC_TITLE", end);
        true
    }

    fn acc_descr(&mut self) -> bool {
        let after = self.at + "accDescr".len();
        let colon = self.horizontal(after);
        if self.byte(colon) == Some(b':') {
            let end = self.value_end(colon + 1);
            self.emit("ACC_DESCR", end);
            return true;
        }
        let mut i = after;
        while i < self.len() {
            let (r, size) = decode(self.src.get(i..).unwrap_or(&[]));
            if !is_js_space(r) {
                break;
            }
            i += size;
        }
        if self.byte(i) != Some(b'{') {
            return false;
        }
        let Some(idx) = self
            .src
            .get(i..)
            .and_then(|tail| tail.iter().position(|&c| c == b'}'))
        else {
            self.terminate("{", i);
            return true;
        };
        self.emit("ACC_DESCR", i + idx + 1);
        true
    }

    fn id_start(&self, c: u8) -> bool {
        c.is_ascii_alphabetic() || (c == b'_' && self.n != Notation::Abnf)
    }

    fn id_part(&self, c: u8) -> bool {
        self.id_start(c) || is_digit(c) || c == b'-'
    }

    fn id_len(&self) -> usize {
        match self.byte(self.at) {
            Some(c) if self.id_start(c) => {}
            _ => return 0,
        }
        let mut i = self.at + 1;
        while self.byte(i).is_some_and(|c| self.id_part(c)) {
            i += 1;
        }
        i - self.at
    }

    fn string(&mut self) {
        let Some(quote) = self.byte(self.at) else {
            return;
        };
        let quote_text = char::from(quote).to_string();
        let mut i = self.at + 1;
        while let Some(c) = self.byte(i) {
            if c == quote {
                self.emit("STRING", i + 1);
                return;
            }
            if c != b'\\' || self.n == Notation::Abnf {
                i += 1;
                continue;
            }
            let Some(tail) = self.src.get(i + 1..).filter(|tail| !tail.is_empty()) else {
                self.terminate(&quote_text, self.at);
                return;
            };
            let (r, size) = decode(tail);
            if is_line_terminator(r) {
                self.emit("INVALID", self.at + 1);
                return;
            }
            i += 1 + size;
        }
        self.terminate(&quote_text, self.at);
    }

    fn hex_run(&self, mut from: usize) -> usize {
        while self.byte(from).is_some_and(|c| c.is_ascii_hexdigit()) {
            from += 1;
        }
        from
    }

    fn numval(&mut self) -> bool {
        let i = self.at + 1;
        if !self
            .byte(i)
            .is_some_and(|c| matches!(c, b'x' | b'X' | b'd' | b'D' | b'b' | b'B'))
        {
            return false;
        }
        let mut end = self.hex_run(i + 1);
        if end == i + 1 {
            return false;
        }
        while matches!(self.byte(end), Some(b'-' | b'.')) {
            let next = self.hex_run(end + 1);
            if next == end + 1 {
                break;
            }
            end = next;
        }
        self.emit("NUMVAL", end);
        true
    }

    fn repeat(&mut self) -> bool {
        let mut digits = self.at;
        while self.byte(digits).is_some_and(is_digit) {
            digits += 1;
        }
        if self.byte(digits) == Some(b'*') {
            let mut end = digits + 1;
            while self.byte(end).is_some_and(is_digit) {
                end += 1;
            }
            self.emit("REPEAT", end);
            return true;
        }
        if digits > self.at {
            self.emit("EXACT_REPEAT", digits);
            return true;
        }
        false
    }
}

fn all_js_space(mut bytes: &[u8]) -> bool {
    while !bytes.is_empty() {
        let (r, size) = decode(bytes);
        if !is_js_space(r) {
            return false;
        }
        bytes = bytes.get(size..).unwrap_or(&[]);
    }
    true
}
