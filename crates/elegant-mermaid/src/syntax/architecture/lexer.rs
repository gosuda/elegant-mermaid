//! Lexer for the architecture grammar of `spec/grammar/architecture.md`.
//!
//! One pass in source order; the first rule that matches at the cursor wins. Keyword
//! rules end at a word boundary, and removed spans (comments, directives) are skipped.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

const KEYWORDS: [&str; 9] = [
    "architecture-beta",
    "architecture",
    "junction",
    "service",
    "column",
    "group",
    "align",
    "row",
    "in",
];

pub fn lex(source: &str, removed: &[Span]) -> Vec<Token> {
    Scanner {
        src: source,
        removed,
        at: 0,
        tokens: Vec::new(),
    }
    .run()
}

struct Scanner<'a> {
    src: &'a str,
    removed: &'a [Span],
    at: usize,
    tokens: Vec<Token>,
}

impl Scanner<'_> {
    fn run(mut self) -> Vec<Token> {
        while self.at < self.src.len() {
            if let Some(end) = self.removed_end() {
                self.at = end;
                continue;
            }
            if !self.next() {
                self.emit_rune("INVALID");
            }
        }
        let end = self.src.len();
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

    fn rest(&self) -> &str {
        &self.src[self.at..]
    }

    fn next(&mut self) -> bool {
        self.newline()
            || self.keyword()
            || self.punctuation()
            || self.arrow()
            || self.metadata()
            || self.string_literal()
            || self.identifier()
            || self.space()
            || self.comment()
            || self.icon()
            || self.title()
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let end = self.at + length;
        let text = self.src[self.at..end].to_owned();
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

    fn emit_rune(&mut self, kind: &'static str) {
        let size = self.rest().chars().next().map_or(1, char::len_utf8);
        self.emit(kind, size);
    }

    fn unterminated(&mut self, opener: usize, length: usize) {
        let end = self.src.len();
        self.tokens.push(Token {
            kind: "UNTERMINATED",
            text: self.src[opener..opener + length].to_owned(),
            span: Span { start: opener, end },
        });
        self.at = end;
    }

    fn newline(&mut self) -> bool {
        match self.src.as_bytes()[self.at] {
            b'\n' => self.emit("NEWLINE", 1),
            b'\r' => {
                let length = if self.src.as_bytes().get(self.at + 1) == Some(&b'\n') {
                    2
                } else {
                    1
                };
                self.emit("NEWLINE", length);
            }
            _ => return false,
        }
        true
    }

    fn keyword(&mut self) -> bool {
        let rest = self.rest();
        let found = KEYWORDS
            .iter()
            .copied()
            .find(|k| rest.starts_with(*k) && identifier_length(rest) <= k.len());
        match found {
            Some(k) => {
                self.emit(k, k.len());
                true
            }
            None => false,
        }
    }

    fn punctuation(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with("--") {
            self.emit("--", 2);
        } else if rest.starts_with('-') {
            self.emit("-", 1);
        } else if rest.starts_with(':') {
            self.emit(":", 1);
        } else {
            return false;
        }
        true
    }

    fn arrow(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with(['L', 'R', 'T', 'B']) {
            self.emit("ARROW_DIRECTION", 1);
        } else if rest.starts_with("{group}") {
            self.emit("ARROW_GROUP", "{group}".len());
        } else if rest.starts_with(['<', '>']) {
            self.emit("ARROW_INTO", 1);
        } else {
            return false;
        }
        true
    }

    fn metadata(&mut self) -> bool {
        let lead = horizontal_run(self.rest());
        let rest = &self.src[self.at + lead..];
        if let Some(after) = rest.strip_prefix("accDescr") {
            let after = after.to_owned();
            return self.acc_descr(lead, &after);
        }
        if let Some(after) = rest.strip_prefix("accTitle") {
            let colon = horizontal_run(after);
            if after.as_bytes().get(colon) != Some(&b':') {
                return false;
            }
            let value = after[colon + 1..].to_owned();
            return self.line("ACC_TITLE", lead + "accTitle".len() + colon + 1, &value);
        }
        if let Some(after) = rest.strip_prefix("title") {
            if after.as_bytes().first().is_some_and(|c| horizontal(*c)) {
                let value = after.to_owned();
                return self.line("TITLE", lead + "title".len(), &value);
            }
            self.emit_value("TITLE", lead + "title".len(), String::new());
            return true;
        }
        false
    }

    fn line(&mut self, kind: &'static str, prefix: usize, value: &str) -> bool {
        let line = &value[..line_length(value)];
        let value = &value[..comment_cut(line)];
        self.emit_value(kind, prefix + value.len(), collapse_line(value));
        true
    }

    fn acc_descr(&mut self, lead: usize, after: &str) -> bool {
        let colon = horizontal_run(after);
        if after.as_bytes().get(colon) == Some(&b':') {
            let value = &after[colon + 1..];
            return self.line("ACC_DESCR", lead + "accDescr".len() + colon + 1, value);
        }
        let space = after.bytes().take_while(|c| is_space(*c)).count();
        if after.as_bytes().get(space) != Some(&b'{') {
            return false;
        }
        let body = &after[space + 1..];
        let Some(closing) = body.find('}') else {
            self.unterminated(self.at + lead + "accDescr".len() + space, 1);
            return true;
        };
        let length = lead + "accDescr".len() + space + 1 + closing + 1;
        self.emit_value("ACC_DESCR", length, collapse_block(&body[..closing]));
        true
    }

    fn identifier(&mut self) -> bool {
        let n = identifier_length(self.rest());
        if n == 0 {
            return false;
        }
        self.emit("ID", n);
        true
    }

    fn space(&mut self) -> bool {
        let n = horizontal_run(self.rest());
        self.at += n;
        n > 0
    }

    fn comment(&mut self) -> bool {
        if !self.rest().starts_with("%%") {
            return false;
        }
        self.at += line_length(self.rest());
        true
    }

    fn string_literal(&mut self) -> bool {
        let quote = self.src.as_bytes()[self.at];
        if quote != b'"' && quote != b'\'' {
            return false;
        }
        match quoted(self.rest()) {
            Quoted::Closed(value, length) => self.emit_value("STRING", length, value),
            Quoted::Open => self.unterminated(self.at, 1),
            Quoted::Broken => self.emit_rune("INVALID"),
        }
        true
    }

    fn icon(&mut self) -> bool {
        let rest = self.rest();
        if !rest.starts_with('(') {
            return false;
        }
        let bytes = rest.as_bytes();
        let mut run = 1;
        while run < bytes.len() && icon_byte(bytes[run]) {
            run += 1;
        }
        if run > 1 && run < bytes.len() && bytes[run] == b')' {
            let value = rest[1..run].to_owned();
            self.emit_value("ARCH_ICON", run + 1, value);
        } else if run == bytes.len() {
            self.unterminated(self.at, 1);
        } else {
            self.emit_rune("INVALID");
        }
        true
    }

    fn title(&mut self) -> bool {
        let rest = self.rest();
        if !rest.starts_with('[') {
            return false;
        }
        let length = title_length(rest);
        if length > 0 {
            let value = title_value(&rest[1..length - 1]);
            self.emit_value("ARCH_TITLE", length, value);
        } else if !rest[1..].contains(['\n', '\r', '[', ']']) {
            self.unterminated(self.at, 1);
        } else {
            self.emit_rune("INVALID");
        }
        true
    }
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

fn comment_cut(line: &str) -> usize {
    line.find("%%").unwrap_or(line.len())
}

fn is_word(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn identifier_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    if bytes.is_empty() || !is_word(bytes[0]) {
        return 0;
    }
    let mut run = 1;
    while run < bytes.len() && (is_word(bytes[run]) || bytes[run] == b'-') {
        run += 1;
    }
    while run > 1 && !is_word(bytes[run - 1]) {
        run -= 1;
    }
    run
}

fn is_space(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c)
}

fn collapse_line(value: &str) -> String {
    collapse_runs(value.trim_matches(char::is_whitespace))
}

fn collapse_runs(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    let mut chars = value.chars().peekable();
    while let Some(c) = chars.next() {
        if c != ' ' && c != '\t' {
            out.push(c);
            continue;
        }
        let mut run = 1;
        while chars.next_if(|n| *n == ' ' || *n == '\t').is_some() {
            run += 1;
        }
        out.push(if run == 1 { c } else { ' ' });
    }
    out
}

fn collapse_block(value: &str) -> String {
    value
        .split(['\n', '\r'])
        .map(|line| line.trim_matches(char::is_whitespace))
        .filter(|line| !line.is_empty())
        .map(collapse_runs)
        .collect::<Vec<_>>()
        .join("\n")
}

fn line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

enum Quoted {
    Closed(String, usize),
    Open,
    Broken,
}

fn quoted(text: &str) -> Quoted {
    let quote = text.as_bytes()[0];
    let mut value = String::new();
    let mut i = 1;
    while i < text.len() {
        let c = text.as_bytes()[i];
        if c == quote {
            return Quoted::Closed(value, i + 1);
        }
        if c == b'\\' {
            let Some(next) = text[i + 1..].chars().next() else {
                return Quoted::Open;
            };
            if line_terminator(next) {
                return Quoted::Broken;
            }
            value.push_str(&escaped(next));
            i += 1 + next.len_utf8();
            continue;
        }
        let Some(r) = text[i..].chars().next() else {
            return Quoted::Open;
        };
        value.push(r);
        i += r.len_utf8();
    }
    Quoted::Open
}

fn escaped(c: char) -> String {
    match c {
        'b' => "\u{8}".into(),
        'f' => "\u{c}".into(),
        'n' => "\n".into(),
        'r' => "\r".into(),
        't' => "\t".into(),
        'v' => "\u{b}".into(),
        '0' => "\0".into(),
        other => other.to_string(),
    }
}

fn icon_byte(c: u8) -> bool {
    is_word(c) || c == b'-' || c == b':'
}

fn title_length(text: &str) -> usize {
    let bytes = text.as_bytes();
    if bytes.len() > 1
        && (bytes[1] == b'"' || bytes[1] == b'\'')
        && let Quoted::Closed(_, length) = quoted(&text[1..])
        && 1 + length < bytes.len()
        && bytes[1 + length] == b']'
    {
        return 1 + length + 1;
    }
    let mut run = 1;
    while run < bytes.len() && !matches!(bytes[run], b'[' | b']' | b'\r' | b'\n') {
        run += 1;
    }
    if run > 1 && run < bytes.len() && bytes[run] == b']' {
        return run + 1;
    }
    0
}

fn title_value(inner: &str) -> String {
    let trimmed = js_trim(inner);
    let bytes = trimmed.as_bytes();
    let quoted = matches!(
        (bytes.first(), bytes.last()),
        (Some(first), Some(last)) if (*first == b'"' || *first == b'\'') && first == last
    );
    if !quoted {
        return js_trim(trimmed).to_owned();
    }
    let body = if bytes.len() == 1 {
        ""
    } else {
        &trimmed[1..trimmed.len() - 1]
    };
    js_trim(&body.replace("\\\"", "\"").replace("\\'", "'")).to_owned()
}

fn js_space(c: char) -> bool {
    matches!(
        c,
        '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202f}'
                | '\u{205f}'
                | '\u{3000}'
                | '\u{feff}'
    )
}

fn js_trim(text: &str) -> &str {
    text.trim_matches(js_space)
}
