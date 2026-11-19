//! Treemap syntax, preserving visible indentation and Langium terminal precedence.
use super::langium;
use crate::diag::{Diagnostic, Severity};
use crate::source::Span;
use std::borrow::Cow;

#[derive(Debug, Clone)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: Cow<'a, str>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Name {
    pub value: String,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct MyNumber {
    pub raw: String,
    pub literal: String,
    pub valid: bool,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct ClassSelector {
    pub name: String,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Section {
    pub name: Name,
    pub selector: Option<ClassSelector>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Leaf {
    pub name: Name,
    pub value: MyNumber,
    pub selector: Option<ClassSelector>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub enum Item {
    Section(Section),
    Leaf(Leaf),
}
#[derive(Debug, Clone)]
pub struct ClassDef {
    pub name: String,
    pub style: String,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct TreemapRow {
    pub indent: Option<usize>,
    pub content: RowContent,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub enum RowContent {
    Empty,
    Item(Item),
    ClassDef(ClassDef),
}
#[derive(Debug, Clone)]
pub struct TitleAndAccessibilities {
    pub tokens: Vec<(&'static str, String)>,
}
#[derive(Debug, Clone)]
pub enum Statement {
    Row(TreemapRow),
    Metadata(TitleAndAccessibilities),
}
#[derive(Debug, Clone)]
pub struct Treemap {
    pub rows: Vec<Statement>,
    pub span: Span,
}

fn horizontal(b: u8) -> bool {
    b == b' ' || b == b'\t'
}
fn hrun(s: &str) -> usize {
    s.bytes().take_while(|b| horizontal(*b)).count()
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
    ) || ('\u{2000}'..='\u{200a}').contains(&c)
}
fn spaces(s: &str) -> usize {
    s.chars()
        .take_while(|c| js_space(*c))
        .map(char::len_utf8)
        .sum()
}
fn line_len(s: &str) -> usize {
    s.find(['\r', '\n']).unwrap_or(s.len())
}
fn name_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}
fn word_len(s: &str) -> usize {
    s.bytes()
        .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
        .count()
}
fn collapse(s: &str) -> String {
    let s = s.trim_matches(js_space);
    let mut out = String::new();
    let mut at = 0;
    while at < s.len() {
        let n = hrun(&s[at..]);
        if n > 0 {
            out.push(if n == 1 {
                char::from(s.as_bytes()[at])
            } else {
                ' '
            });
            at += n;
        } else if let Some(c) = s[at..].chars().next() {
            out.push(c);
            at += c.len_utf8();
        }
    }
    out
}
fn class_def(s: &str) -> Option<(usize, String, String)> {
    let rest = s.strip_prefix("classDef")?;
    let gap = spaces(rest);
    if gap == 0 || !rest.as_bytes().get(gap).is_some_and(|b| name_start(*b)) {
        return None;
    }
    let begin = 8 + gap;
    let n = word_len(&s[begin..]);
    if n < 2 {
        return None;
    }
    let mut end = begin + n;
    let mut style = String::new();
    let gap = spaces(&s[end..]);
    if gap > 0 {
        end += gap;
        let start = end;
        end += s[end..].find([';', '\r', '\n']).unwrap_or(s.len() - end);
        style = s[start..end].to_owned();
    }
    if s.as_bytes().get(end) == Some(&b';') {
        end += 1;
    }
    Some((end, s[begin..begin + n].to_owned(), style))
}
fn metadata(s: &str) -> Option<(&'static str, usize, String, Option<usize>)> {
    let lead = hrun(s);
    let rest = &s[lead..];
    for (word, kind) in [
        ("accDescr", "ACC_DESCR"),
        ("accTitle", "ACC_TITLE"),
        ("title", "TITLE"),
    ] {
        let Some(after) = rest.strip_prefix(word) else {
            continue;
        };
        let n = hrun(after);
        if word != "title" && after.as_bytes().get(n) == Some(&b':') {
            let prefix = lead + word.len() + n + 1;
            let value = &s[prefix..];
            let end = line_len(value);
            let end = value[..end].find("%%").unwrap_or(end);
            return Some((kind, prefix + end, collapse(&value[..end]), None));
        }
        if word == "accDescr" {
            let n = spaces(after);
            if after.as_bytes().get(n) == Some(&b'{') {
                let open = lead + word.len() + n;
                let body = &s[open + 1..];
                if let Some(end) = body.find('}') {
                    let value = body[..end]
                        .split(['\r', '\n'])
                        .map(collapse)
                        .filter(|s| !s.is_empty())
                        .collect::<Vec<_>>()
                        .join("\n");
                    return Some((kind, open + end + 2, value, None));
                }
                return Some(("UNTERMINATED", s.len(), "{".to_owned(), Some(open)));
            }
        }
        if word == "title" {
            if after.as_bytes().first().is_some_and(|b| horizontal(*b)) {
                let end = line_len(after);
                let end = after[..end].find("%%").unwrap_or(end);
                return Some((kind, lead + word.len() + end, collapse(&after[..end]), None));
            }
            return Some((kind, lead + word.len(), String::new(), None));
        }
    }
    None
}
fn borrowed<'a>(s: &'a str, kind: &'static str, n: usize) -> Token<'a> {
    Token {
        kind,
        text: Cow::Borrowed(&s[..n]),
        span: Span { start: 0, end: n },
    }
}
fn directive(s: &str) -> Option<Token<'_>> {
    for (word, kind) in [("true", "BOOLEAN"), ("false", "BOOLEAN")] {
        if s.starts_with(word) {
            return Some(borrowed(s, kind, word.len()));
        }
    }
    if let Some((kind, n, text, open)) = metadata(s) {
        return Some(Token {
            kind,
            text: Cow::Owned(text),
            span: Span {
                start: open.unwrap_or(0),
                end: n,
            },
        });
    }
    for word in ["treemap-beta", "treemap"] {
        if s.starts_with(word) {
            return Some(borrowed(s, "TREEMAP_KEYWORD", word.len()));
        }
    }
    class_def(s).map(|(n, _, _)| borrowed(s, "CLASS_DEF", n))
}
fn structure(s: &str) -> Option<Token<'_>> {
    for (word, kind) in [
        (":::", "STYLE_SEPARATOR"),
        (":", "SEPARATOR"),
        (",", "COMMA"),
    ] {
        if s.starts_with(word) {
            return Some(borrowed(s, kind, word.len()));
        }
    }
    let n = hrun(s);
    if n > 0 {
        return Some(borrowed(s, "INDENTATION", n));
    }
    None
}
fn operand(s: &str) -> Token<'_> {
    let b = s.as_bytes()[0];
    if name_start(b) {
        return borrowed(s, "ID2", word_len(s));
    }
    if b.is_ascii_digit() || b == b'.' {
        let n = s
            .bytes()
            .take_while(|b| b.is_ascii_digit() || matches!(*b, b'_' | b'.' | b','))
            .count();
        return borrowed(s, "NUMBER2", n);
    }
    if b != b'\'' && b != b'"' {
        return borrowed(s, "INVALID", s.chars().next().map_or(1, char::len_utf8));
    }
    if let Some(end) = s[1..].find(char::from(b)) {
        return borrowed(s, "STRING2", end + 2);
    }
    Token {
        kind: "UNTERMINATED",
        text: Cow::Borrowed(&s[..1]),
        span: Span {
            start: 0,
            end: s.len(),
        },
    }
}
pub fn lex<'a>(src: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    let mut out = Vec::new();
    let mut at = 0;
    while at < src.len() {
        if let Some(span) = removed.iter().find(|s| s.start <= at && at < s.end) {
            at = span.end;
            continue;
        }
        let s = &src[at..];
        let token = directive(s).or_else(|| structure(s));
        if let Some(mut token) = token {
            let n = token.span.end;
            token.span.start += at;
            token.span.end += at;
            out.push(token);
            at += n;
            continue;
        }
        if s.starts_with("%%") {
            at += line_len(s);
            continue;
        }
        if s.starts_with('\r') || s.starts_with('\n') {
            at += if s.starts_with("\r\n") { 2 } else { 1 };
            continue;
        }
        let mut token = operand(s);
        let n = token.span.end;
        token.span.start += at;
        token.span.end += at;
        out.push(token);
        at += n;
    }
    out.push(Token {
        kind: "EOF",
        text: Cow::Borrowed(""),
        span: Span {
            start: src.len(),
            end: src.len(),
        },
    });
    out
}
pub fn diagnostic(code: &'static str, message: String, span: Span) -> Diagnostic {
    langium::diagnostic(code, Severity::Error, message, span)
}
struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token<'a>>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}
impl<'a> Parser<'a> {
    fn token(&self) -> &Token<'a> {
        &self.tokens[self.at.min(self.tokens.len() - 1)]
    }
    fn kind(&self) -> &'static str {
        self.token().kind
    }
    fn take(&mut self) -> Token<'a> {
        let t = self.token().clone();
        self.at = (self.at + 1).min(self.tokens.len() - 1);
        t
    }
    fn end(&self) -> usize {
        self.at
            .checked_sub(1)
            .map_or(0, |i| self.tokens[i].span.end)
    }
    fn boundary(&self, end: usize) -> bool {
        matches!(self.kind(), "EOF" | "UNTERMINATED")
            || self.src[end..self.token().span.start].contains(['\n', '\r'])
    }
    fn recover(&mut self, mut end: usize) {
        while !self.boundary(end) {
            end = self.take().span.end;
        }
    }
    fn unterminated(&mut self) {
        let t = self.take();
        self.diagnostics.push(diagnostic(
            "treemap/unterminated",
            format!("unterminated {}", t.text),
            t.span,
        ));
    }
    fn unexpected(&mut self, expected: &[&str]) {
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
            return;
        }
        let t = self.token();
        let span = t.span;
        let mut names = expected.to_vec();
        names.sort();
        let message = format!(
            "unexpected {}, expected one of: {}",
            &self.src[span.start..span.end],
            names.join(", ")
        );
        self.diagnostics
            .push(diagnostic("treemap/unexpected-token", message, span));
        self.recover(self.end());
    }
    fn selector(&mut self) -> Result<Option<ClassSelector>, ()> {
        if self.kind() != "STYLE_SEPARATOR" {
            return Ok(None);
        }
        self.take();
        if self.kind() != "ID2" {
            self.unexpected(&["ID2"]);
            return Err(());
        }
        let t = self.take();
        Ok(Some(ClassSelector {
            name: t.text.into_owned(),
            span: t.span,
        }))
    }
    fn row(&mut self) -> Option<TreemapRow> {
        let start = self.token().span.start;
        let indent = if self.kind() == "INDENTATION" {
            Some(self.take().text.len())
        } else {
            None
        };
        let mut row = TreemapRow {
            indent,
            content: RowContent::Empty,
            span: Span { start, end: start },
        };
        match self.kind() {
            "CLASS_DEF" => {
                let t = self.take();
                if let Some((_, name, style)) = class_def(&t.text) {
                    row.content = RowContent::ClassDef(ClassDef {
                        name,
                        style,
                        span: t.span,
                    });
                }
            }
            "STRING2" => {
                let t = self.take();
                let name = Name {
                    value: t.text[1..t.text.len() - 1].to_owned(),
                    span: t.span,
                };
                let offset = usize::from(self.kind() == "INDENTATION");
                let leaf = self
                    .tokens
                    .get(self.at + offset)
                    .is_some_and(|t| matches!(t.kind, "SEPARATOR" | "COMMA"));
                let value = if leaf {
                    if self.kind() == "INDENTATION" {
                        self.take();
                    }
                    self.take();
                    let gap = self.kind() == "INDENTATION";
                    if gap {
                        self.take();
                    }
                    if self.kind() != "NUMBER2" {
                        self.unexpected(if gap {
                            &["NUMBER2"]
                        } else {
                            &["INDENTATION", "NUMBER2"]
                        });
                        return None;
                    }
                    let t = self.take();
                    let (literal, valid) = convert_number(&t.text);
                    Some(MyNumber {
                        raw: t.text.into_owned(),
                        literal,
                        valid,
                        span: t.span,
                    })
                } else {
                    None
                };
                let selector = self.selector().ok()?;
                let span = Span {
                    start: name.span.start,
                    end: self.end(),
                };
                row.content = RowContent::Item(match value {
                    Some(value) => Item::Leaf(Leaf {
                        name,
                        value,
                        selector,
                        span,
                    }),
                    None => Item::Section(Section {
                        name,
                        selector,
                        span,
                    }),
                });
            }
            _ => {
                self.unexpected(&["CLASS_DEF", "STRING2"]);
                return None;
            }
        }
        row.span.end = self.end();
        Some(row)
    }
}
pub fn convert_number(raw: &str) -> (String, bool) {
    let text = raw.replace(',', "");
    let whole = text.bytes().take_while(u8::is_ascii_digit).count();
    let mut end = whole;
    let mut frac = 0;
    if text.as_bytes().get(end) == Some(&b'.') {
        frac = text[end + 1..]
            .bytes()
            .take_while(u8::is_ascii_digit)
            .count();
        end += 1 + frac;
    }
    if whole == 0 && frac == 0 {
        (String::new(), false)
    } else {
        (text[..end].to_owned(), true)
    }
}
pub fn parse(src: &str, removed: &[Span]) -> (Treemap, Vec<Diagnostic>) {
    let mut p = Parser {
        src,
        tokens: lex(src, removed),
        at: 0,
        diagnostics: Vec::new(),
    };
    while p.kind() == "INDENTATION" {
        p.take();
    }
    let start = p.token().span.start;
    if p.kind() == "TREEMAP_KEYWORD" {
        p.take();
    } else {
        p.unexpected(&["TREEMAP_KEYWORD"]);
    }
    let mut rows = Vec::new();
    while p.kind() != "EOF" {
        match p.kind() {
            "UNTERMINATED" => p.unterminated(),
            "TITLE" | "ACC_TITLE" | "ACC_DESCR" => {
                let mut tokens = Vec::new();
                while matches!(p.kind(), "TITLE" | "ACC_TITLE" | "ACC_DESCR") {
                    let t = p.take();
                    tokens.push((t.kind, t.text.into_owned()));
                }
                rows.push(Statement::Metadata(TitleAndAccessibilities { tokens }));
            }
            "INDENTATION" | "STRING2" | "CLASS_DEF" => {
                if let Some(row) = p.row() {
                    rows.push(Statement::Row(row));
                }
            }
            _ => {
                let t = p.take();
                let mut end = t.span.end;
                while !p.boundary(end) {
                    end = p.take().span.end;
                }
                p.diagnostics.push(diagnostic(
                    "treemap/unknown-statement",
                    format!("unknown statement {}", t.text),
                    Span {
                        start: t.span.start,
                        end,
                    },
                ));
            }
        }
    }
    (
        Treemap {
            rows,
            span: Span {
                start,
                end: src.len(),
            },
        },
        p.diagnostics,
    )
}

#[cfg(test)]
#[path = "treemap_tests.rs"]
mod tests;
