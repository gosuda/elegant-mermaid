use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: &'a str,
    pub span: Span,
}

pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    let mut tokens = Vec::new();
    let mut offset = 0;
    let mut class_pending = false;
    let mut class_body = false;
    while offset < source.len() {
        if let Some(span) = removed.iter().find(|s| s.start <= offset && offset < s.end) {
            offset = span.end;
            continue;
        }
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
                text: &source[offset + trim..end - trim],
                span: Span { start: offset, end },
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

fn next(source: &str) -> (&'static str, usize, usize) {
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
        b';' => "INVALID",
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
        "direction" => "DIRECTION",
        "style" => "STYLE",
        "classDef" => "CLASSDEF",
        "cssClass" => "CSSCLASS",
        "click" | "link" | "callback" => "CLICK",
        "o" => "AGGREGATION",
        _ => "ALPHA",
    };
    (kind, length, 0)
}
