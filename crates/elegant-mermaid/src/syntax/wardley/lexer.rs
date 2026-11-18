//! Lexer for the wardley grammar of `spec/grammar/wardley.md`.
//!
//! Terminals follow the authority's order: whitespace, punctuation keywords, then the
//! terminal rules in declaration order. The first rule that matches at a position wins.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

const KEYWORDS: &[(&str, &str)] = &[
    ("wardley-beta", "KW_WARDLEY"),
    ("size", "KW_SIZE"),
    ("evolution", "KW_EVOLUTION"),
    ("anchor", "KW_ANCHOR"),
    ("component", "KW_COMPONENT"),
    ("label", "KW_LABEL"),
    ("inertia", "KW_INERTIA"),
    ("evolve", "KW_EVOLVE"),
    ("pipeline", "KW_PIPELINE"),
    ("note", "KW_NOTE"),
    ("annotations", "KW_ANNOTATIONS"),
    ("annotation", "KW_ANNOTATION"),
    ("accelerator", "KW_ACCELERATOR"),
    ("deaccelerator", "KW_DEACCELERATOR"),
];

const STRATEGIES: &[&str] = &["build", "buy", "outsource", "market"];
const LINK_PORTS: &[&str] = &["+<>", "+>", "+<"];
const LINK_ARROWS: &[&str] = &["-->", "-.->", ">"];
const QUOTED_FLOWS: &[&str] = &["<>", "<", ">"];
const DASH_ARROWS: &[(&str, &str)] = &[
    ("->", "ARROW"),
    ("-->", "LINK_ARROW"),
    ("-.->", "LINK_ARROW"),
];
const PUNCTUATION: &[(u8, &str)] = &[
    (b'[', "["),
    (b',', ","),
    (b']', "]"),
    (b'@', "@"),
    (b'/', "/"),
    (b'-', "-"),
    (b'(', "("),
    (b')', ")"),
    (b'{', "{"),
    (b'}', "}"),
];

pub fn lex(source: &str, removed: &[Span]) -> Vec<Token> {
    Scanner {
        source,
        removed,
        at: 0,
        tokens: Vec::new(),
    }
    .run()
}

struct Scanner<'a, 'r> {
    source: &'a str,
    removed: &'r [Span],
    at: usize,
    tokens: Vec<Token>,
}

fn horizontal(c: u8) -> bool {
    c == b' ' || c == b'\t'
}

fn horizontal_run(text: &str) -> usize {
    text.bytes().take_while(|c| horizontal(*c)).count()
}

fn line_length(text: &str) -> usize {
    text.find(['\n', '\r']).unwrap_or(text.len())
}

fn is_word(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn js_space(c: char) -> bool {
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

pub(crate) fn trim_js(text: &str) -> &str {
    text.trim_matches(js_space)
}

impl<'a> Scanner<'a, '_> {
    fn rest(&self) -> &'a str {
        self.source.get(self.at..).unwrap_or("")
    }

    fn run(mut self) -> Vec<Token> {
        while self.at < self.source.len() {
            if let Some(end) = self.removed_end() {
                self.at = end;
                continue;
            }
            if !self.hidden() && !self.next() {
                self.emit_char("INVALID");
            }
        }
        let end = self.source.len();
        self.tokens.push(Token {
            kind: "EOF",
            text: String::new(),
            span: Span { start: end, end },
        });
        self.tokens
    }

    fn removed_end(&self) -> Option<usize> {
        self.removed
            .iter()
            .find(|span| span.start <= self.at && self.at < span.end)
            .map(|span| span.end)
    }

    fn hidden(&mut self) -> bool {
        let rest = self.rest();
        let blanks = horizontal_run(rest);
        if blanks > 0 {
            self.at += blanks;
            return true;
        }
        if rest.starts_with("%%") {
            self.at += line_length(rest);
            return true;
        }
        false
    }

    fn next(&mut self) -> bool {
        self.newline()
            || self.punctuation()
            || self.number()
            || self.link_port()
            || self.link_arrow()
            || self.link_label()
            || self.strategy()
            || self.keyword()
            || self.name()
            || self.metadata()
            || self.integer()
            || self.string_literal()
            || self.identifier()
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = self.at + length;
        let text = self.source.get(self.at..end).unwrap_or("").to_owned();
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

    fn unterminated(&mut self, opener: usize, text: &str) {
        let end = self.source.len();
        self.tokens.push(Token {
            kind: "UNTERMINATED",
            text: text.to_owned(),
            span: Span { start: opener, end },
        });
        self.at = end;
    }

    fn newline(&mut self) -> bool {
        let rest = self.rest().as_bytes();
        match rest.first() {
            Some(b'\n') => self.emit("NEWLINE", 1),
            Some(b'\r') => {
                let length = if rest.get(1) == Some(&b'\n') { 2 } else { 1 };
                self.emit("NEWLINE", length);
            }
            _ => return false,
        }
        true
    }

    fn punctuation(&mut self) -> bool {
        let rest = self.rest();
        let Some(first) = rest.bytes().next() else {
            return false;
        };
        let Some((_, kind)) = PUNCTUATION.iter().find(|(c, _)| *c == first) else {
            return false;
        };
        if first == b'-'
            && let Some((prefix, token)) = DASH_ARROWS
                .iter()
                .find(|(prefix, _)| rest.starts_with(*prefix))
        {
            self.emit(token, prefix.len());
            return true;
        }
        self.emit(kind, 1);
        true
    }

    fn number(&mut self) -> bool {
        let rest = self.rest().as_bytes();
        let whole = rest.iter().take_while(|c| c.is_ascii_digit()).count();
        if whole == 0 || rest.get(whole) != Some(&b'.') {
            return false;
        }
        let fraction = rest[whole + 1..]
            .iter()
            .take_while(|c| c.is_ascii_digit())
            .count();
        if fraction == 0 {
            return false;
        }
        self.emit("WARDLEY_NUMBER", whole + 1 + fraction);
        true
    }

    fn link_port(&mut self) -> bool {
        let rest = self.rest();
        let Some(port) = LINK_PORTS.iter().find(|port| rest.starts_with(**port)) else {
            return false;
        };
        self.emit("LINK_PORT", port.len());
        true
    }

    fn link_arrow(&mut self) -> bool {
        let rest = self.rest();
        if let Some(arrow) = LINK_ARROWS.iter().find(|arrow| rest.starts_with(**arrow)) {
            self.emit("LINK_ARROW", arrow.len());
            return true;
        }
        let Some(tail) = rest.strip_prefix("+'") else {
            return false;
        };
        let Some(closing) = tail.find('\'') else {
            return false;
        };
        let head = 2 + closing + 1;
        let after = &rest[head..];
        let Some(flow) = QUOTED_FLOWS.iter().find(|flow| after.starts_with(**flow)) else {
            return false;
        };
        self.emit("LINK_ARROW", head + flow.len());
        true
    }

    fn link_label(&mut self) -> bool {
        let rest = self.rest();
        let Some(body) = rest.strip_prefix(';') else {
            return false;
        };
        let length = line_length(body);
        if length == 0 {
            return false;
        }
        let text = trim_js(&body[..length]).to_owned();
        self.emit_value("LINK_LABEL", 1 + length, text);
        true
    }

    fn strategy(&mut self) -> bool {
        let rest = self.rest();
        let Some(strategy) = STRATEGIES.iter().find(|s| rest.starts_with(**s)) else {
            return false;
        };
        self.emit("STRATEGY", strategy.len());
        true
    }

    fn header_position(&self) -> bool {
        self.tokens.iter().all(|t| t.kind == "NEWLINE")
    }

    fn keyword(&mut self) -> bool {
        let rest = self.rest();
        if self.header_position() && fold_prefix(rest, "wardley-beta") {
            self.emit("KW_WARDLEY", "wardley-beta".len());
            return true;
        }
        let Some((word, kind)) = KEYWORDS.iter().find(|(word, _)| rest.starts_with(*word)) else {
            return false;
        };
        self.emit(kind, word.len());
        true
    }

    fn name(&mut self) -> bool {
        let length = name_length(self.rest());
        if length == 0 {
            return false;
        }
        self.emit("NAME_WITH_SPACES", length);
        true
    }

    fn metadata(&mut self) -> bool {
        let rest = self.rest();
        if let Some(after) = rest.strip_prefix("accDescr") {
            return self.acc_descr(after);
        }
        if let Some(after) = rest.strip_prefix("accTitle") {
            let colon = horizontal_run(after);
            if after.as_bytes().get(colon) != Some(&b':') {
                return false;
            }
            return self.line(
                "ACC_TITLE",
                "accTitle".len() + colon + 1,
                &after[colon + 1..],
            );
        }
        let Some(after) = rest.strip_prefix("title") else {
            return false;
        };
        if after.bytes().next().is_none_or(|c| !horizontal(c)) {
            self.emit_value("TITLE", "title".len(), String::new());
            return true;
        }
        self.line("TITLE", "title".len(), after)
    }

    fn line(&mut self, kind: &'static str, prefix: usize, value: &str) -> bool {
        let value = &value[..line_length(value)];
        let value = &value[..value.find("%%").unwrap_or(value.len())];
        self.emit_value(kind, prefix + value.len(), collapse_line(value));
        true
    }

    fn acc_descr(&mut self, after: &str) -> bool {
        let colon = horizontal_run(after);
        if after.as_bytes().get(colon) == Some(&b':') {
            return self.line(
                "ACC_DESCR",
                "accDescr".len() + colon + 1,
                &after[colon + 1..],
            );
        }
        let space = after.len() - after.trim_start_matches(js_space).len();
        if after.as_bytes().get(space) != Some(&b'{') {
            return false;
        }
        let body = &after[space + 1..];
        let Some(closing) = body.find('}') else {
            self.unterminated(self.at + "accDescr".len() + space, "{");
            return true;
        };
        let length = "accDescr".len() + space + 1 + closing + 1;
        self.emit_value("ACC_DESCR", length, collapse_block(&body[..closing]));
        true
    }

    fn integer(&mut self) -> bool {
        let length = integer_length(self.rest());
        if length == 0 {
            return false;
        }
        self.emit("INT", length);
        true
    }

    fn string_literal(&mut self) -> bool {
        let rest = self.rest();
        let Some(quote) = rest.chars().next().filter(|c| *c == '"' || *c == '\'') else {
            return false;
        };
        let mut value = String::new();
        let mut chars = rest.char_indices().skip(1);
        while let Some((i, c)) = chars.next() {
            if c == quote {
                self.emit_value("STRING", i + 1, value);
                return true;
            }
            if c != '\\' {
                value.push(c);
                continue;
            }
            let Some((_, escape)) = chars.next() else {
                break;
            };
            if line_terminator(escape) {
                break;
            }
            value.push_str(&escaped(escape));
        }
        self.unterminated(self.at, &quote.to_string());
        true
    }

    fn identifier(&mut self) -> bool {
        let rest = self.rest().as_bytes();
        if rest.first().is_none_or(|c| !is_word(*c)) {
            return false;
        }
        let mut length = 1;
        while length < rest.len() && (is_word(rest[length]) || rest[length] == b'-') {
            length += 1;
        }
        while length > 1 && rest[length - 1] == b'-' {
            length -= 1;
        }
        self.emit("ID", length);
        true
    }
}

fn fold_prefix(text: &str, word: &str) -> bool {
    text.len() >= word.len()
        && text.as_bytes()[..word.len()]
            .iter()
            .zip(word.bytes())
            .all(|(c, w)| c.to_ascii_lowercase() == w)
}

fn is_name_byte(c: u8) -> bool {
    is_word(c) || c == b'(' || c == b')' || c == b'&'
}

fn name_run(text: &str, from: usize) -> usize {
    let bytes = text.as_bytes();
    let mut i = from;
    while i < bytes.len() {
        let c = bytes[i];
        let continues = is_name_byte(c) || (c == b'-' && bytes.get(i + 1) != Some(&b'>'));
        if !continues {
            return i;
        }
        i += 1;
    }
    i
}

fn excluded_name(text: &str) -> bool {
    if text.starts_with("accTitle") || text.starts_with("accDescr") {
        return true;
    }
    text.strip_prefix("title")
        .and_then(|after| after.chars().next())
        .is_some_and(js_space)
}

fn name_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    if bytes.first().is_none_or(|c| !c.is_ascii_alphabetic()) || excluded_name(text) {
        return 0;
    }
    let mut end = name_run(text, 1);
    loop {
        let blanks = horizontal_run(&text[end..]);
        let next = end + blanks;
        let starts_word = bytes
            .get(next)
            .is_some_and(|c| c.is_ascii_alphabetic() || *c == b'(');
        if blanks == 0 || !starts_word {
            return end;
        }
        end = name_run(text, next + 1);
    }
}

fn collapse_line(value: &str) -> String {
    collapse_runs(trim_js(value))
}

fn collapse_runs(value: &str) -> String {
    let mut out = String::new();
    let mut at = 0;
    while at < value.len() {
        let blanks = horizontal_run(&value[at..]);
        if blanks > 0 {
            out.push(if blanks == 1 {
                char::from(value.as_bytes()[at])
            } else {
                ' '
            });
            at += blanks;
            continue;
        }
        let c = value[at..].chars().next().unwrap_or(' ');
        out.push(c);
        at += c.len_utf8();
    }
    out
}

fn collapse_block(value: &str) -> String {
    value
        .split(['\n', '\r'])
        .map(trim_js)
        .filter(|line| !line.is_empty())
        .map(collapse_runs)
        .collect::<Vec<_>>()
        .join("\n")
}

fn integer_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    match bytes.first() {
        None => 0,
        Some(b'0') => 1,
        Some(c) if !(b'1'..=b'9').contains(c) => 0,
        Some(_) => {
            let mut digits = 1;
            while digits < bytes.len() && bytes[digits].is_ascii_digit() {
                digits += 1;
            }
            if bytes.get(digits) == Some(&b'.') {
                digits -= 1;
            }
            digits
        }
    }
}

fn line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

fn escaped(c: char) -> String {
    match c {
        'b' => "\u{8}".to_owned(),
        'f' => "\u{c}".to_owned(),
        'n' => "\n".to_owned(),
        'r' => "\r".to_owned(),
        't' => "\t".to_owned(),
        'v' => "\u{b}".to_owned(),
        '0' => "\0".to_owned(),
        other => other.to_string(),
    }
}
