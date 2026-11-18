use std::borrow::Cow;

use crate::source::{Span, cleaned::Cleaned};

pub const MODES: &[&str] = &["defaultMode", "jsonBody", "stereotype"];
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: Cow<'a, str>,
    pub span: Span,
}

pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    lex_cleaned(&Cleaned::new(source, removed))
}

pub(crate) fn lex_cleaned<'a>(cleaned: &Cleaned<'a>) -> Vec<Token<'a>> {
    let mut scanner = Scanner {
        cleaned,
        source: cleaned.text(),
        at: 0,
        mode: "defaultMode",
        tokens: Vec::new(),
    };
    while scanner.at < scanner.source.len() {
        scanner.next();
    }
    scanner.tokens
}
struct Scanner<'a, 't> {
    cleaned: &'t Cleaned<'a>,
    source: &'t str,
    at: usize,
    mode: &'static str,
    tokens: Vec<Token<'a>>,
}
impl<'a, 't> Scanner<'a, 't> {
    fn emit(&mut self, kind: &'static str, n: usize) {
        let end = (self.at + n).min(self.source.len());
        self.tokens.push(Token {
            kind,
            text: self.cleaned.cow(self.at, end),
            span: self.cleaned.span(self.at, end),
        });
        self.at = end;
    }
    fn next(&mut self) {
        let s = self.source.get(self.at..).unwrap_or("");
        if self.mode == "jsonBody" {
            self.json(s);
            return;
        }
        if self.mode == "stereotype" {
            self.stereotype(s);
            return;
        }
        let ws = s.bytes().take_while(|b| matches!(b, b' ' | b'\t')).count();
        if ws > 0 {
            self.at += ws;
            return;
        }
        if self.special(s) || self.keyword(s) || self.operator(s) || self.atom(s) {
            return;
        }
        self.emit("INVALID", s.chars().next().map_or(1, char::len_utf8));
    }
    fn special(&mut self, s: &str) -> bool {
        if s.starts_with("\"`") {
            self.markdown_string(s);
            return true;
        }
        if s.starts_with("%%") && self.line_start() {
            self.emit("COMMENT", line_len(s));
            return true;
        }
        if s.starts_with(['\r', '\n']) {
            self.emit("NEWLINE", if s.starts_with("\r\n") { 2 } else { 1 });
            return true;
        }
        if self.accessibility(s) {
            return true;
        }
        if let Some(n) = json_header(s) {
            self.emit("JSON_DECLARATION_START", n);
            self.mode = "jsonBody";
            return true;
        }
        false
    }
    fn markdown_string(&mut self, s: &str) {
        let n = s.get(2..).and_then(|t| t.find("`\"")).map(|n| n + 4);
        let kind = if n.is_some() {
            "MARKDOWN_STRING"
        } else {
            "UNCLOSED_MARKDOWN_STRING"
        };
        self.emit(kind, n.unwrap_or(s.len()));
    }
    fn line_start(&self) -> bool {
        self.source
            .get(..self.at)
            .unwrap_or("")
            .chars()
            .rev()
            .take_while(|c| !matches!(c, '\r' | '\n'))
            .all(|c| matches!(c, ' ' | '\t'))
    }
    fn accessibility(&mut self, s: &str) -> bool {
        if !self.line_start() {
            return false;
        }
        for (name, kind) in [
            ("accTitle", "ACC_TITLE_LINE"),
            ("accDescr", "ACC_DESCR_LINE"),
        ] {
            let Some(tail) = s.strip_prefix(name) else {
                continue;
            };
            let tail = tail.trim_start_matches([' ', '\t']);
            if tail.starts_with(':') {
                self.emit(kind, line_len(s));
                return true;
            }
            if name == "accDescr" && tail.starts_with('{') {
                self.accessibility_block(s, tail);
                return true;
            }
        }
        false
    }
    fn accessibility_block(&mut self, s: &str, tail: &str) {
        let n = tail.find('}').map(|n| s.len() - tail.len() + n + 1);
        let kind = if n.is_some() {
            "ACC_DESCR_BLOCK"
        } else {
            "UNCLOSED_ACC_DESCR_BLOCK"
        };
        self.emit(kind, n.unwrap_or(s.len()));
    }
    fn keyword(&mut self, s: &str) -> bool {
        for (text, kind) in KEYWORDS {
            let Some(prefix) = s.get(..text.len()) else {
                continue;
            };
            let matches = if matches!(*kind, "INCLUDE" | "EXTEND") {
                prefix.eq_ignore_ascii_case(text)
            } else {
                prefix == *text
            };
            if matches && word_len(s) <= text.len() {
                self.emit(kind, text.len());
                return true;
            }
        }
        false
    }
    fn operator(&mut self, s: &str) -> bool {
        for &(text, kind) in OPERATORS {
            if !s.starts_with(text) {
                continue;
            }
            self.emit(kind, text.len());
            if kind == "STEREOTYPE_START" {
                self.mode = "stereotype";
            }
            return true;
        }
        if self.solid_arrow(s) {
            return true;
        }
        for &(text, kind) in MARKED_ASSOCIATIONS {
            if s.starts_with(text) {
                self.emit(kind, 3);
                return true;
            }
        }
        let n = s.bytes().take_while(|b| *b == b'-').count();
        if n >= 2 {
            self.emit("MARKERLESS_SOLID", n);
            return true;
        }
        false
    }
    fn solid_arrow(&mut self, s: &str) -> bool {
        let n = s.bytes().take_while(|b| *b == b'-').count();
        if n >= 2 && s.get(n..).is_some_and(|t| t.starts_with('>')) {
            self.emit("FORWARD_SOLID", n + 1);
            return true;
        }
        if !s.starts_with("<--") {
            return false;
        }
        let n = s.bytes().skip(1).take_while(|b| *b == b'-').count();
        self.emit("BACKWARD_SOLID", n + 1);
        true
    }
    fn atom(&mut self, s: &str) -> bool {
        for &(text, kind) in DELIMITERS {
            if s.starts_with(text) {
                self.emit(kind, text.len());
                return true;
            }
        }
        let hex = s.bytes().skip(1).take_while(u8::is_ascii_hexdigit).count();
        if s.starts_with('#') && hex > 0 {
            self.emit("HASH_COLOR", hex + 1);
            return true;
        }
        if s.starts_with(['\'', '"']) {
            self.plain_string(s);
            return true;
        }
        let css = css_len(s);
        if css > 0 {
            self.emit("CSS_IDENTIFIER", css);
            return true;
        }
        let word = word_len(s);
        let number = number_len(s);
        if word > 0 || number > 0 {
            let kind = if number > word {
                "NUMBER"
            } else {
                "IDENTIFIER"
            };
            self.emit(kind, word.max(number));
            return true;
        }
        self.punctuation(s)
    }
    fn plain_string(&mut self, s: &str) {
        let quote = s.chars().next().unwrap_or('"');
        let n = s
            .get(1..line_len(s))
            .and_then(|t| t.find(quote))
            .map(|n| n + 2);
        let kind = if n.is_some() {
            "PLAIN_STRING"
        } else {
            "UNCLOSED_PLAIN_STRING"
        };
        self.emit(kind, n.unwrap_or(line_len(s)));
    }
    fn punctuation(&mut self, s: &str) -> bool {
        for (text, kind) in [
            ("\\,", "CSS_ESCAPED_COMMA"),
            ("-", "DASH"),
            (".", "DOT"),
            ("%", "PERCENT"),
        ] {
            if s.starts_with(text) {
                self.emit(kind, text.len());
                return true;
            }
        }
        let c = s.chars().next().unwrap_or('\0');
        let kind = if "!#$&*+/=?^_|~".contains(c) {
            "CSS_PUNCTUATION"
        } else if ";<>\\`".contains(c) {
            "LABEL_PUNCTUATION"
        } else {
            ""
        };
        if !kind.is_empty() {
            self.emit(kind, c.len_utf8());
            return true;
        }
        let n = s
            .char_indices()
            .take_while(|(_, c)| !matches!(c, '\t' | '\r' | '\n' | ' '..='~'))
            .last()
            .map_or(0, |(i, c)| i + c.len_utf8());
        if n > 0 {
            self.emit("LABEL_SYMBOL", n);
            return true;
        }
        false
    }
    fn stereotype(&mut self, s: &str) {
        if s.starts_with(">>") {
            self.emit("STEREOTYPE_END", 2);
            self.mode = "defaultMode";
            return;
        }
        let line = line_len(s);
        if let Some(n) = s.get(..line).and_then(|t| t.find(">>"))
            && !s.get(..n).unwrap_or("").trim().is_empty()
        {
            self.emit("STEREOTYPE_TEXT", n);
            return;
        }
        self.mode = "defaultMode";
        if line == 0 {
            self.next();
        } else {
            self.emit("UNCLOSED_STEREOTYPE_TEXT", line);
        }
    }
    fn json(&mut self, s: &str) {
        let mut balance = JsonBalance {
            depth: 0,
            quote: JsonQuote::Outside,
        };
        let end = s
            .bytes()
            .enumerate()
            .find_map(|(i, b)| balance.advance(b).then_some(i + 1));
        let kind = if end.is_some() {
            "JSON_OBJECT_LITERAL"
        } else {
            "UNCLOSED_JSON_OBJECT_LITERAL"
        };
        self.emit(kind, end.unwrap_or(s.len()));
        self.mode = "defaultMode";
    }
}
enum JsonQuote {
    Outside,
    Inside,
    Escaped,
}
struct JsonBalance {
    depth: usize,
    quote: JsonQuote,
}
impl JsonBalance {
    fn advance(&mut self, byte: u8) -> bool {
        match self.quote {
            JsonQuote::Escaped => self.quote = JsonQuote::Inside,
            JsonQuote::Inside => match byte {
                b'\\' => self.quote = JsonQuote::Escaped,
                b'"' => self.quote = JsonQuote::Outside,
                _ => {}
            },
            JsonQuote::Outside => return self.outside(byte),
        }
        false
    }
    fn outside(&mut self, byte: u8) -> bool {
        match byte {
            b'"' => self.quote = JsonQuote::Inside,
            b'{' => self.depth += 1,
            b'}' => {
                self.depth = self.depth.saturating_sub(1);
                return self.depth == 0;
            }
            _ => {}
        }
        false
    }
}
const KEYWORDS: &[(&str, &str)] = &[
    ("usecase-beta", "USECASE"),
    ("actor", "ACTOR"),
    ("systemBoundary", "SYSTEM_BOUNDARY"),
    ("end", "END"),
    ("direction", "DIRECTION"),
    ("TD", "TD"),
    ("TB", "TB"),
    ("BT", "BT"),
    ("LR", "LR"),
    ("RL", "RL"),
    ("note", "NOTE"),
    ("for", "FOR"),
    ("json", "JSON"),
    ("classDef", "CLASS_DEF"),
    ("class", "CLASS"),
    ("style", "STYLE"),
    ("include", "INCLUDE"),
    ("extend", "EXTEND"),
    ("true", "TRUE"),
    ("false", "FALSE"),
];
pub(crate) fn is_word(kind: &str) -> bool {
    kind == "IDENTIFIER" || KEYWORDS.iter().any(|(_, k)| *k == kind)
}
pub(crate) fn is_label(kind: &str) -> bool {
    is_word(kind)
        || matches!(
            kind,
            "NUMBER"
                | "AT"
                | "COMMA"
                | "COLON"
                | "HASH_COLOR"
                | "CSS_IDENTIFIER"
                | "CSS_ESCAPED_COMMA"
                | "DASH"
                | "DOT"
                | "PERCENT"
                | "CSS_PUNCTUATION"
                | "LABEL_PUNCTUATION"
                | "LABEL_SYMBOL"
        )
}
fn line_len(s: &str) -> usize {
    s.find(['\r', '\n']).unwrap_or(s.len())
}
fn word_len(s: &str) -> usize {
    s.bytes()
        .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
        .count()
}
fn number_len(s: &str) -> usize {
    let digits = s.bytes().take_while(u8::is_ascii_digit).count();
    let tail = s.get(digits..).unwrap_or("");
    let fraction = tail
        .strip_prefix('.')
        .map_or(0, |t| t.bytes().take_while(u8::is_ascii_digit).count());
    let n = digits + if fraction > 0 { 1 + fraction } else { 0 };
    if n == 0 {
        return 0;
    }
    n + s
        .get(n..)
        .unwrap_or("")
        .bytes()
        .take_while(u8::is_ascii_alphabetic)
        .count()
}
fn css_len(s: &str) -> usize {
    if !s
        .bytes()
        .next()
        .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
    {
        return 0;
    }
    let first = word_len(s);
    let mut n = first;
    while s.get(n..).is_some_and(|t| t.starts_with('-')) {
        let part = word_len(s.get(n + 1..).unwrap_or(""));
        if part == 0 {
            break;
        }
        n += 1 + part;
    }
    if n > first { n } else { 0 }
}
fn json_header(s: &str) -> Option<usize> {
    let tail = s.strip_prefix("json")?;
    let t = tail.trim_start_matches([' ', '\t']);
    if t.len() == tail.len() {
        return None;
    }
    let n = word_len(t);
    if n == 0 {
        return None;
    }
    let tail = t
        .get(n..)?
        .trim_start_matches([' ', '\t'])
        .strip_prefix('@')?
        .trim_start_matches([' ', '\t']);
    tail.starts_with('{').then_some(s.len() - tail.len())
}

const OPERATORS: &[(&str, &str)] = &[
    ("--|>", "GENERALIZATION"),
    ("..>", "DEPENDENCY_ARROW"),
    ("<<", "STEREOTYPE_START"),
    (":::", "CLASS_SEPARATOR"),
];
const MARKED_ASSOCIATIONS: &[(&str, &str)] = &[
    ("--o", "FORWARD_CIRCLE"),
    ("o--", "BACKWARD_CIRCLE"),
    ("--x", "FORWARD_CROSS"),
    ("x--", "BACKWARD_CROSS"),
];
const DELIMITERS: &[(&str, &str)] = &[
    ("@{", "METADATA_START"),
    ("@", "AT"),
    ("{", "LBRACE"),
    ("}", "RBRACE"),
    ("[", "LBRACKET"),
    ("]", "RBRACKET"),
    ("(", "LPAREN"),
    (")", "RPAREN"),
    (",", "COMMA"),
    (":", "COLON"),
];
