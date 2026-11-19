use super::ast::Token;
use super::boxdraw::convert_box;
use super::prepare::prepare;
use super::text::{
    acc_descr_value, acc_title_value, bare_name_value, blank, class_value, desc_value, icon_value,
    js_space, quoted_name_value, title_value, word_char,
};
use crate::diag::Diagnostic;
use crate::source::Span;

pub(super) const HEADER_WORD: &str = "treeView-beta";

pub(super) const K_HEADER: &str = HEADER_WORD;
pub(super) const K_ACC_DESCR: &str = "ACC_DESCR";
pub(super) const K_ACC_TITLE: &str = "ACC_TITLE";
pub(super) const K_TITLE: &str = "TITLE";
pub(super) const K_CLASS: &str = "CLASS_ANNOTATION";
pub(super) const K_ICON: &str = "ICON_ANNOTATION";
pub(super) const K_DESC: &str = "DESC_ANNOTATION";
pub(super) const K_INDENT: &str = "INDENTATION";
pub(super) const K_QUOTED: &str = "QUOTED_NAME";
pub(super) const K_BARE: &str = "BARE_NAME";
pub(super) const K_EOF: &str = "EOF";
pub(super) const K_INVALID: &str = "INVALID";
pub(super) const K_UNTERMINATED: &str = "UNTERMINATED";

type Matcher = fn(&Scanner, usize) -> Option<usize>;

struct Rule {
    kind: &'static str,
    hidden: bool,
    matcher: Matcher,
}

const RULES: [Rule; 12] = [
    Rule {
        kind: K_HEADER,
        hidden: false,
        matcher: Scanner::header,
    },
    Rule {
        kind: K_ACC_DESCR,
        hidden: false,
        matcher: Scanner::acc_descr,
    },
    Rule {
        kind: K_ACC_TITLE,
        hidden: false,
        matcher: Scanner::acc_title,
    },
    Rule {
        kind: K_TITLE,
        hidden: false,
        matcher: Scanner::title,
    },
    Rule {
        kind: K_CLASS,
        hidden: false,
        matcher: Scanner::class,
    },
    Rule {
        kind: K_ICON,
        hidden: false,
        matcher: Scanner::icon,
    },
    Rule {
        kind: K_DESC,
        hidden: false,
        matcher: Scanner::desc,
    },
    Rule {
        kind: K_INDENT,
        hidden: false,
        matcher: Scanner::indent,
    },
    Rule {
        kind: K_QUOTED,
        hidden: false,
        matcher: Scanner::quoted,
    },
    Rule {
        kind: "",
        hidden: true,
        matcher: Scanner::comment,
    },
    Rule {
        kind: "",
        hidden: true,
        matcher: Scanner::newline,
    },
    Rule {
        kind: K_BARE,
        hidden: false,
        matcher: Scanner::bare,
    },
];

pub(super) struct Scanner {
    pub(super) text: String,
    orig: Vec<usize>,
    end: usize,
    pub(super) at: usize,
}

fn token_value(kind: &str, text: &str) -> String {
    match kind {
        K_ACC_DESCR => acc_descr_value(text),
        K_ACC_TITLE => acc_title_value(text),
        K_TITLE => title_value(text),
        K_CLASS => class_value(text),
        K_ICON => icon_value(text),
        K_DESC => desc_value(text),
        K_QUOTED => quoted_name_value(text),
        K_BARE => bare_name_value(text),
        _ => text.to_owned(),
    }
}

fn is_class_start(c: u8) -> bool {
    c == b'_' || c.is_ascii_alphabetic()
}

impl Scanner {
    pub(super) fn new(src: &str, removed: &[Span]) -> (Self, Vec<Diagnostic>) {
        let (text, orig) = prepare(src, removed);
        let (text, orig, diags) = convert_box(&text, orig, src.len());
        (
            Self {
                text,
                orig,
                end: src.len(),
                at: 0,
            },
            diags,
        )
    }

    fn bytes(&self) -> &[u8] {
        self.text.as_bytes()
    }

    fn byte(&self, at: usize) -> Option<u8> {
        self.bytes().get(at).copied()
    }

    pub(super) fn start(&self, at: usize) -> usize {
        self.orig.get(at).copied().unwrap_or(self.end)
    }

    pub(super) fn finish(&self, at: usize) -> usize {
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

    fn token(&mut self, kind: &'static str, from: usize, to: usize) -> Token {
        self.at = to;
        let text = self.text.get(from..to).unwrap_or("").to_owned();
        Token {
            kind,
            value: token_value(kind, &text),
            text,
            span: self.span(from, to),
            from,
            to,
        }
    }

    pub(super) fn next(&mut self) -> Token {
        while self.at < self.text.len() {
            if let Some(token) = self.attempt(self.at) {
                return token;
            }
        }
        let end = Span {
            start: self.end,
            end: self.end,
        };
        Token::end_of(end, self.text.len())
    }

    fn attempt(&mut self, at: usize) -> Option<Token> {
        for rule in &RULES {
            let Some(end) = (rule.matcher)(self, at) else {
                continue;
            };
            if rule.hidden {
                self.at = end;
                return None;
            }
            return Some(self.token(rule.kind, at, end));
        }
        Some(self.reject(at))
    }

    fn rune_at(&self, at: usize) -> char {
        self.text
            .get(at..)
            .and_then(|s| s.chars().next())
            .unwrap_or('\u{fffd}')
    }

    fn reject(&mut self, at: usize) -> Token {
        let c = self.byte(at).unwrap_or(0);
        if c == b'"' || c == b'\'' {
            let to = self.text.len();
            self.at = to;
            return Token {
                kind: K_UNTERMINATED,
                text: char::from(c).to_string(),
                value: String::new(),
                span: Span {
                    start: self.start(at),
                    end: self.end,
                },
                from: at,
                to,
            };
        }
        let size = self
            .text
            .get(at..)
            .map_or(1, |s| s.chars().next().map_or(1, char::len_utf8));
        self.token(K_INVALID, at, at + size)
    }

    pub(super) fn line_end(&self, from: usize) -> usize {
        let from = from.min(self.text.len());
        self.bytes()
            .get(from..)
            .and_then(|rest| rest.iter().position(|c| *c == b'\n'))
            .map_or(self.text.len(), |end| from + end)
    }

    fn has(&self, at: usize, literal: &str) -> bool {
        self.bytes()
            .get(at..)
            .is_some_and(|rest| rest.starts_with(literal.as_bytes()))
    }

    fn blanks(&self, mut at: usize) -> usize {
        while self.byte(at).is_some_and(blank) {
            at += 1;
        }
        at
    }

    fn tail(&self, mut at: usize) -> usize {
        while let Some(c) = self.byte(at) {
            if c == b'\n' || c == b'\r' || self.has(at, "%%") {
                break;
            }
            at += 1;
        }
        at
    }

    fn header(&self, at: usize) -> Option<usize> {
        let end = at + HEADER_WORD.len();
        if !self.has(at, HEADER_WORD) {
            return None;
        }
        if end < self.text.len() && !self.has(end, "%%") && !js_space(self.rune_at(end)) {
            return None;
        }
        if self.bare(at).is_some_and(|stop| stop > end) {
            return None;
        }
        Some(end)
    }

    fn acc_descr(&self, at: usize) -> Option<usize> {
        let q = self.blanks(at);
        if !self.has(q, "accDescr") {
            return None;
        }
        let q = q + "accDescr".len();
        let r = self.blanks(q);
        if self.byte(r) == Some(b':') {
            return Some(self.tail(r + 1));
        }
        let mut r = q;
        while r < self.text.len() {
            let c = self.rune_at(r);
            if !js_space(c) {
                break;
            }
            r += c.len_utf8();
        }
        if self.byte(r) != Some(b'{') {
            return None;
        }
        let closing = self.bytes().get(r + 1..)?.iter().position(|c| *c == b'}')?;
        Some(r + 1 + closing + 1)
    }

    fn acc_title(&self, at: usize) -> Option<usize> {
        let q = self.blanks(at);
        if !self.has(q, "accTitle") {
            return None;
        }
        let q = self.blanks(q + "accTitle".len());
        if self.byte(q) != Some(b':') {
            return None;
        }
        Some(self.tail(q + 1))
    }

    fn title(&self, at: usize) -> Option<usize> {
        let q = self.blanks(at);
        if !self.has(q, "title") {
            return None;
        }
        let q = q + "title".len();
        if self.byte(q).is_some_and(blank) {
            return Some(self.tail(q + 1));
        }
        Some(q)
    }

    fn annotation(&self, at: usize) -> Option<usize> {
        let q = self.blanks(at);
        (q != at).then_some(q)
    }

    fn word_run(&self, mut at: usize) -> usize {
        while self.byte(at).is_some_and(|c| word_char(c) || c == b'-') {
            at += 1;
        }
        at
    }

    fn class(&self, at: usize) -> Option<usize> {
        let q = self.annotation(at)?;
        if !self.has(q, ":::") {
            return None;
        }
        let q = self.blanks(q + ":::".len());
        if !self.byte(q).is_some_and(is_class_start) {
            return None;
        }
        Some(self.word_run(q + 1))
    }

    fn icon(&self, at: usize) -> Option<usize> {
        let q = self.annotation(at)?;
        if !self.has(q, "icon(") {
            return None;
        }
        let mut q = self.word_run(q + "icon(".len());
        if self.byte(q) == Some(b':') {
            let name = self.word_run(q + 1);
            if name == q + 1 {
                return None;
            }
            q = name;
        }
        (self.byte(q) == Some(b')')).then_some(q + 1)
    }

    fn desc(&self, at: usize) -> Option<usize> {
        let q = self.annotation(at)?;
        if !self.has(q, "##") {
            return None;
        }
        Some(self.line_end_or_carriage(q + "##".len()))
    }

    fn line_end_or_carriage(&self, mut at: usize) -> usize {
        while self.byte(at).is_some_and(|c| c != b'\n' && c != b'\r') {
            at += 1;
        }
        at
    }

    fn indent(&self, at: usize) -> Option<usize> {
        self.annotation(at)
    }

    fn quoted(&self, at: usize) -> Option<usize> {
        let c = self.byte(at)?;
        if c != b'"' && c != b'\'' {
            return None;
        }
        let closing = self.bytes().get(at + 1..)?.iter().position(|b| *b == c)?;
        Some(at + 1 + closing + 1)
    }

    fn comment(&self, at: usize) -> Option<usize> {
        self.has(at, "%%").then(|| self.line_end(at))
    }

    fn newline(&self, at: usize) -> Option<usize> {
        (self.byte(at) == Some(b'\n')).then_some(at + 1)
    }

    fn marker(&self, at: usize) -> bool {
        let q = self.blanks(at);
        if q == at {
            return false;
        }
        if self.has(q, "icon(") || self.has(q, "##") {
            return true;
        }
        self.has(q, ":::")
            && self
                .byte(self.blanks(q + ":::".len()))
                .is_some_and(is_class_start)
    }

    fn bare(&self, at: usize) -> Option<usize> {
        let c = self.byte(at)?;
        if matches!(c, b' ' | b'\t' | b'\n' | b'\r' | b'"' | b'\'') {
            return None;
        }
        if self.has(at, ":::") || self.has(at, "icon(") || self.has(at, "##") {
            return None;
        }
        let mut q = at
            + self
                .text
                .get(at..)
                .map_or(1, |s| s.chars().next().map_or(1, char::len_utf8));
        while self
            .byte(q)
            .is_some_and(|b| b != b'\n' && b != b'\r' && !self.marker(q))
        {
            q += 1;
        }
        Some(q)
    }
}
