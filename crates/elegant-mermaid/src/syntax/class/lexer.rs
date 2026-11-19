use std::borrow::Cow;

use crate::source::{Span, cleaned::Cleaned};

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
    let source = cleaned.text();
    let mut tokens = Vec::new();
    let mut offset = 0;
    let mut class_pending = false;
    let mut class_body = false;
    while offset < source.len() {
        let (kind, length, trim) = if class_body {
            member(&source[offset..])
        } else {
            next(&source[offset..])
        };
        match kind {
            "CLASS" => class_pending = true,
            "NEWLINE" => class_pending = false,
            "STRUCT_START" if class_pending => {
                class_body = true;
                class_pending = false;
            }
            "STRUCT_STOP" => class_body = false,
            _ => {}
        }
        let end = offset + length;
        if kind != "SPACE" {
            tokens.push(Token {
                kind,
                text: cleaned.cow(offset + trim, end - trim),
                span: cleaned.span(offset, end),
            });
        }
        offset = end;
    }
    tokens
}

fn member(source: &str) -> (&'static str, usize, usize) {
    match source.as_bytes()[0] {
        b'{' => ("STRUCT_START", 1, 0),
        b'}' => ("STRUCT_STOP", 1, 0),
        b'\r' | b'\n' => punctuation(source, source.as_bytes()[0]),
        _ => (
            "MEMBER",
            source.find(['{', '}', '\r', '\n']).unwrap_or(source.len()),
            0,
        ),
    }
}

const DIRECTIONS: [(&str, &str); 4] = [
    ("TB", "direction_tb"),
    ("BT", "direction_bt"),
    ("RL", "direction_rl"),
    ("LR", "direction_lr"),
];

fn direction(source: &str) -> Option<(&'static str, usize)> {
    DIRECTIONS
        .iter()
        .find_map(|(word, kind)| direction_end(source, word).map(|end| (*kind, end)))
}

const SPACE: [char; 5] = [' ', '\t', '\n', '\x0c', '\r'];

fn direction_end(source: &str, word: &str) -> Option<usize> {
    let line = source.find(['\r', '\n']).unwrap_or(source.len());
    source[..line]
        .rmatch_indices("direction")
        .find_map(|(at, keyword)| {
            let tail = &source[at + keyword.len()..];
            let rest = tail.trim_start_matches(SPACE);
            let word_end = source.len() - rest.len() + word.len();
            (rest.len() < tail.len() && rest.starts_with(word)).then(|| {
                source[word_end..]
                    .find(['\r', '\n'])
                    .map_or(source.len(), |n| word_end + n)
            })
        })
}

fn next(source: &str) -> (&'static str, usize, usize) {
    if let Some((kind, length)) = direction(source) {
        return (kind, length, 0);
    }
    let bytes = source.as_bytes();
    let first = bytes[0];
    for header in ["classDiagram-v2", "classDiagram"] {
        if source.strip_prefix(header).is_some_and(|tail| {
            tail.is_empty()
                || !tail.as_bytes()[0].is_ascii_alphanumeric()
                    && !matches!(tail.as_bytes()[0], b'_' | b'-')
        }) {
            return ("CLASS_DIAGRAM", header.len(), 0);
        }
    }
    if matches!(first, b'"' | b'`' | b'~') {
        return quoted(source, first);
    }
    if source.starts_with("%%") {
        return (
            "SPACE",
            source.find(['\r', '\n']).unwrap_or(source.len()),
            0,
        );
    }
    for (text, kind) in [
        ("<|", "EXTENSION"),
        ("|>", "EXTENSION"),
        ("()", "LOLLIPOP"),
        ("--", "LINE"),
        ("..", "DOTTED_LINE"),
        ("<<", "ANNOTATION_START"),
        (">>", "ANNOTATION_END"),
        (":::", "STYLE_SEPARATOR"),
    ] {
        if source.starts_with(text) {
            return (kind, text.len(), 0);
        }
    }
    punctuation(source, first)
}

fn quoted(source: &str, delimiter: u8) -> (&'static str, usize, usize) {
    let kind = match delimiter {
        b'"' => "STR",
        b'`' => "BQUOTE_STR",
        _ => "GENERICTYPE",
    };
    match source[1..].find(char::from(delimiter)) {
        Some(end) => (kind, end + 2, 1),
        None => ("UNTERMINATED", source.len(), 0),
    }
}

fn punctuation(source: &str, first: u8) -> (&'static str, usize, usize) {
    let kind = match first {
        b'\r' | b'\n' => "NEWLINE",
        b' ' | b'\t' => "SPACE",
        b'{' => "STRUCT_START",
        b'}' => "STRUCT_STOP",
        b'[' => "SQS",
        b']' => "SQE",
        b'<' | b'>' => "DEPENDENCY",
        b'*' => "COMPOSITION",
        b':' => "COLON",
        b',' => "COMMA",
        b'-' => "MINUS",
        b'.' => "DOT",
        b';' => "SEMICOLON",
        b'+' => "PLUS",
        b'#' => "BRKT",
        b'%' => "PCT",
        b'=' => "EQUALS",
        b'(' | b')' | b'$' | b'/' | b'\\' | b'!' | b'?' | b'&' => "PUNCTUATION",
        _ => return word(source),
    };
    let length = if source.starts_with("\r\n") { 2 } else { 1 };
    (kind, length, 0)
}

fn word(source: &str) -> (&'static str, usize, usize) {
    let length = source
        .char_indices()
        .take_while(|(_, c)| c.is_alphanumeric() || *c == '_')
        .last()
        .map_or(0, |(i, c)| i + c.len_utf8());
    if length == 0 {
        return (
            "INVALID",
            source.chars().next().map_or(1, char::len_utf8),
            0,
        );
    }
    let kind = match &source[..length] {
        "class" => "CLASS",
        "namespace" => "NAMESPACE",
        "note" => "NOTE",
        "classDiagram" | "classDiagram-v2" => "CLASS_DIAGRAM",
        "style" => "STYLE",
        "classDef" => "CLASSDEF",
        "cssClass" => "CSSCLASS",
        "click" | "link" | "callback" => "CLICK",
        "call" => "CALL",
        "href" => "HREF",
        "o" => "AGGREGATION",
        _ => "ALPHA",
    };
    (kind, length, 0)
}
