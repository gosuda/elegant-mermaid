//! Borrowed styled labels (spec/math.md, math-01 through math-11).

use crate::r#gen::alphanumeric::ALPHANUMERIC;
use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label<'a> {
    pub lines: Vec<Line<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Line<'a> {
    pub segments: Vec<Segment<'a>>,
    /// Source of the forced break after this line, if any.
    pub break_span: Option<Span>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Segment<'a> {
    Text(Text<'a>),
    Math(Math<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Text<'a> {
    pub text: &'a str,
    pub bold: bool,
    pub italic: bool,
    /// Content source, excluding emphasis delimiters. For an escape this
    /// includes the backslash; `text` borrows only the escaped punctuation.
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Math<'a> {
    /// Untouched formula, including its TeX escapes, excluding the dollars.
    pub source: &'a str,
    pub span: Span,
    pub formula_span: Span,
}

#[derive(Clone, Copy)]
struct Style {
    bold: bool,
    italic: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Label,
    Emphasis,
}

/// Parses a label without interpreting TeX or decoding entities. Physical
/// CR/LF bytes remain text, as in measure::wrap; only accepted br tags force
/// lines. Even an empty label has one line.
pub fn parse(source: &str) -> Label<'_> {
    let mut label = Label {
        lines: vec![Line {
            segments: Vec::new(),
            break_span: None,
        }],
    };
    scan(
        source,
        Span {
            start: 0,
            end: source.len(),
        },
        Style {
            bold: false,
            italic: false,
        },
        Mode::Label,
        &mut label,
    );
    label
}

fn break_len(source: &str, at: usize) -> Option<usize> {
    ["<br>", "<br/>", "<br />"].iter().find_map(|tag| {
        source
            .get(at..at + tag.len())
            .filter(|text| text.eq_ignore_ascii_case(tag))
            .map(str::len)
    })
}

fn escape_len(source: &str, at: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    (bytes.get(at) == Some(&b'\\') && bytes.get(at + 1).is_some_and(u8::is_ascii_punctuation))
        .then_some(2)
}

fn alphanumeric(value: char) -> bool {
    if value.is_ascii() {
        return value.is_ascii_alphanumeric();
    }
    let cp = u32::from(value);
    let index = ALPHANUMERIC.partition_point(|row| row.hi < cp);
    ALPHANUMERIC.get(index).is_some_and(|row| row.lo <= cp)
}

fn intraword(source: &str, at: usize) -> bool {
    source[..at].chars().next_back().is_some_and(alphanumeric)
        && source[at + 1..].chars().next().is_some_and(alphanumeric)
}

fn math_end(source: &str, mut at: usize, end: usize) -> Option<usize> {
    while at < end {
        if let Some(len) = escape_len(source, at) {
            at += len;
        } else if source[at..end].starts_with("$$") {
            return Some(at);
        } else {
            at += source[at..end].chars().next()?.len_utf8();
        }
    }
    None
}

fn emphasis_end(source: &str, mut at: usize, end: usize, delimiter: &str) -> Option<usize> {
    while at < end {
        if break_len(source, at).is_some() || matches!(source.as_bytes()[at], b'\r' | b'\n') {
            return None;
        }
        if let Some(len) = escape_len(source, at) {
            at += len;
        } else if source[at..end].starts_with("$$") {
            if let Some(close) = math_end(source, at + 2, end) {
                at = close + 2;
            } else {
                at += 2;
            }
        } else if source[at..end].starts_with(delimiter)
            && (delimiter != "_" || !intraword(source, at))
        {
            return Some(at);
        } else {
            at += source[at..end].chars().next()?.len_utf8();
        }
    }
    None
}

fn text<'a>(label: &mut Label<'a>, value: &'a str, span: Span, style: Style) {
    if !value.is_empty() {
        let index = label.lines.len() - 1;
        label.lines[index].segments.push(Segment::Text(Text {
            text: value,
            bold: style.bold,
            italic: style.italic,
            span,
        }));
    }
}

fn plain_text<'a>(label: &mut Label<'a>, source: &'a str, plain: usize, at: usize, style: Style) {
    text(
        label,
        &source[plain..at],
        Span {
            start: plain,
            end: at,
        },
        style,
    );
}

fn escape<'a>(
    label: &mut Label<'a>,
    source: &'a str,
    plain: usize,
    span: Span,
    style: Style,
) -> usize {
    plain_text(label, source, plain, span.start, style);
    text(label, &source[span.start + 1..span.end], span, style);
    span.end
}

fn line_break<'a>(
    label: &mut Label<'a>,
    source: &'a str,
    plain: usize,
    span: Span,
    style: Style,
) -> usize {
    plain_text(label, source, plain, span.start, style);
    let index = label.lines.len() - 1;
    label.lines[index].break_span = Some(span);
    label.lines.push(Line {
        segments: Vec::new(),
        break_span: None,
    });
    span.end
}

fn math<'a>(
    label: &mut Label<'a>,
    source: &'a str,
    plain: usize,
    span: Span,
    style: Style,
) -> usize {
    plain_text(label, source, plain, span.start, style);
    let index = label.lines.len() - 1;
    label.lines[index].segments.push(Segment::Math(Math {
        source: &source[span.start + 2..span.end - 2],
        span,
        formula_span: Span {
            start: span.start + 2,
            end: span.end - 2,
        },
    }));
    span.end
}

fn emphasis<'a>(
    label: &mut Label<'a>,
    source: &'a str,
    plain: usize,
    delimiter: &str,
    span: Span,
    style: Style,
) -> usize {
    plain_text(label, source, plain, span.start - delimiter.len(), style);
    scan(
        source,
        span,
        Style {
            bold: delimiter == "**",
            italic: delimiter != "**",
        },
        Mode::Emphasis,
        label,
    );
    span.end + delimiter.len()
}

fn construct<'a>(
    label: &mut Label<'a>,
    source: &'a str,
    rest: Span,
    plain: usize,
    style: Style,
    mode: Mode,
) -> Option<usize> {
    let Span { start: at, end } = rest;
    if let Some(len) = escape_len(source, at) {
        return Some(escape(
            label,
            source,
            plain,
            Span {
                start: at,
                end: at + len,
            },
            style,
        ));
    }
    if let Some(len) = break_len(source, at) {
        return Some(line_break(
            label,
            source,
            plain,
            Span {
                start: at,
                end: at + len,
            },
            style,
        ));
    }
    if source[at..end].starts_with("$$")
        && let Some(close) = math_end(source, at + 2, end)
    {
        return Some(math(
            label,
            source,
            plain,
            Span {
                start: at,
                end: close + 2,
            },
            style,
        ));
    }
    if mode == Mode::Label
        && let Some(delimiter) = delimiter(source, at)
        && let Some(close) = emphasis_end(source, at + delimiter.len(), end, delimiter)
    {
        return Some(emphasis(
            label,
            source,
            plain,
            delimiter,
            Span {
                start: at + delimiter.len(),
                end: close,
            },
            style,
        ));
    }
    None
}

fn plain_step(source: &str, at: usize, end: usize, mode: Mode) -> usize {
    if mode == Mode::Label
        && let Some(delimiter) = delimiter(source, at)
    {
        return delimiter.len();
    }
    source[at..end].chars().next().map_or(0, char::len_utf8)
}

fn scan<'a>(source: &'a str, range: Span, style: Style, mode: Mode, label: &mut Label<'a>) {
    let mut at = range.start;
    let mut plain = at;
    let end = range.end;
    while at < end {
        if let Some(next) = construct(label, source, Span { start: at, end }, plain, style, mode) {
            at = next;
            plain = at;
        } else {
            at += plain_step(source, at, end, mode);
        }
    }
    plain_text(label, source, plain, end, style);
}

fn delimiter(source: &str, at: usize) -> Option<&'static str> {
    let rest = &source[at..];
    if rest.starts_with("**") {
        Some("**")
    } else if rest.starts_with('*') {
        Some("*")
    } else if rest.starts_with('_') && !intraword(source, at) {
        Some("_")
    } else {
        None
    }
}

#[cfg(test)]
mod tests;
