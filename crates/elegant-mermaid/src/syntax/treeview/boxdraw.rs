use super::prepare::decode;
use super::text::{blank, js_space, trim_end_js, trim_js, utf16_len};
use super::{C_EMPTY_BOX, C_MIXED, diagnostic, lexer::HEADER_WORD};
use crate::diag::Diagnostic;
use crate::source::Span;

const MSG_EMPTY_BOX: &str = "expected a filename or directory name after the box-drawing prefix";
const MSG_MIXED: &str = "unexpected indentation without box-drawing characters";
const INDENT_UNIT: usize = 4;
const DEFAULT_WIDTH: usize = 4;

#[derive(Clone, Copy)]
struct LineSpan {
    start: usize,
    end: usize,
}

fn is_box_rune(c: char) -> bool {
    "─━│┃└┗├┣".contains(c)
}

fn is_branch_rune(c: char) -> bool {
    "└┗├┣".contains(c)
}

fn is_dash_rune(c: char) -> bool {
    c == '─' || c == '━'
}

fn is_decoration_rune(c: char) -> bool {
    js_space(c) || c == '│' || c == '┃'
}

fn is_box_or_space(c: char) -> bool {
    js_space(c) || is_box_rune(c)
}

fn all_runes(s: &str, keep: fn(char) -> bool) -> bool {
    !s.is_empty() && s.chars().all(keep)
}

fn comment_line(line: &str) -> bool {
    line.trim_start_matches(js_space).starts_with("%%")
}

fn metadata_line(line: &str) -> bool {
    let rest = line.trim_start_matches(js_space);
    if let Some(after) = rest.strip_prefix("title") {
        return after.as_bytes().first().is_some_and(|c| blank(*c));
    }
    if let Some(after) = rest.strip_prefix("accTitle") {
        return after.trim_start_matches([' ', '\t']).starts_with(':');
    }
    if let Some(after) = rest.strip_prefix("accDescr") {
        let after = after.trim_start_matches([' ', '\t']);
        return after.starts_with(':') || after.starts_with('{');
    }
    false
}

fn split_lines(text: &str) -> Vec<LineSpan> {
    let mut lines = Vec::new();
    let mut start = 0;
    for (at, c) in text.char_indices() {
        if c == '\n' {
            lines.push(LineSpan { start, end: at });
            start = at + 1;
        }
    }
    lines.push(LineSpan {
        start,
        end: text.len(),
    });
    lines
}

struct View<'a> {
    text: &'a str,
    orig: &'a [usize],
}

impl View<'_> {
    fn line(&self, l: LineSpan) -> &str {
        self.text.get(l.start..l.end).unwrap_or("")
    }

    fn normalized(&self, l: LineSpan) -> (Vec<u8>, Vec<usize>) {
        let mut norm = Vec::with_capacity(l.end - l.start);
        let mut origin = Vec::with_capacity(l.end - l.start);
        for i in l.start..l.end {
            let byte = self.text.as_bytes().get(i).copied().unwrap_or(0);
            let at = self.orig.get(i).copied().unwrap_or(0);
            let (byte, repeat) = if byte == b'\t' {
                (b' ', INDENT_UNIT)
            } else {
                (byte, 1)
            };
            for _ in 0..repeat {
                norm.push(byte);
                origin.push(at);
            }
        }
        (norm, origin)
    }
}

fn header_line(v: &View<'_>, lines: &[LineSpan]) -> Option<usize> {
    lines
        .iter()
        .position(|l| trim_js(v.line(*l)) == HEADER_WORD)
}

fn branch_column(line: &str) -> Option<(usize, usize)> {
    let index = line.find(is_branch_rune)?;
    Some((index, utf16_len(line.get(..index).unwrap_or(""))))
}

fn content_lines(v: &View<'_>, lines: &[LineSpan]) -> Vec<String> {
    lines
        .iter()
        .map(|l| v.line(*l))
        .filter(|raw| {
            !(trim_js(raw).is_empty()
                || comment_line(raw)
                || metadata_line(raw)
                || all_runes(raw, is_decoration_rune))
        })
        .map(|raw| raw.replace('\t', "    "))
        .collect()
}

fn segment_width(content: &[String]) -> usize {
    content
        .iter()
        .filter_map(|line| branch_column(line))
        .map(|(_, column)| column)
        .find(|column| *column > 0)
        .unwrap_or(DEFAULT_WIDTH)
}

struct BoxWriter<'a> {
    v: View<'a>,
    end: usize,
    out: Vec<u8>,
    origin: Vec<usize>,
    emit: bool,
    prev_nl: usize,
    diags: Vec<Diagnostic>,
}

struct BranchAt {
    index: usize,
    column: usize,
    content: usize,
}

fn content_start(norm: &[u8], index: usize) -> usize {
    let (_, size) = decode(norm, index);
    let mut pos = index + size;
    while pos < norm.len() {
        let (r, n) = decode(norm, pos);
        if !is_dash_rune(r) {
            break;
        }
        pos += n;
    }
    while norm.get(pos) == Some(&b' ') {
        pos += 1;
    }
    pos
}

impl BoxWriter<'_> {
    fn line_break_after(&self, l: LineSpan) -> usize {
        self.v.orig.get(l.end).copied().unwrap_or(self.end)
    }

    fn separator(&mut self, l: LineSpan) {
        if self.emit {
            self.out.push(b'\n');
            self.origin.push(self.prev_nl);
        }
        self.emit = true;
        self.prev_nl = self.line_break_after(l);
    }

    fn raw(&mut self, l: LineSpan) {
        self.separator(l);
        self.out
            .extend_from_slice(self.v.text.as_bytes().get(l.start..l.end).unwrap_or(&[]));
        self.origin
            .extend_from_slice(self.v.orig.get(l.start..l.end).unwrap_or(&[]));
    }

    fn report(&mut self, code: &'static str, message: &str, span: Span) {
        self.diags.push(diagnostic(code, message.to_owned(), span));
    }

    fn finish(&self, i: usize) -> usize {
        if i == 0 || i > self.v.orig.len() {
            return self.end;
        }
        self.v.orig.get(i - 1).map_or(self.end, |o| o + 1)
    }

    fn indent(&mut self, depth: usize, first: usize, last: usize) {
        for _ in 1..depth * INDENT_UNIT {
            self.out.push(b' ');
            self.origin.push(first);
        }
        self.out.push(b' ');
        self.origin.push(last.saturating_sub(1));
    }

    fn branch(
        &mut self,
        l: LineSpan,
        norm: &[u8],
        origin: &[usize],
        at: &BranchAt,
        segment: usize,
    ) {
        let rest = String::from_utf8_lossy(norm.get(at.content..).unwrap_or(&[])).into_owned();
        let content = trim_end_js(&rest);
        let first = origin.first().copied().unwrap_or(0);
        let content_origin = origin.get(at.content).copied().unwrap_or(self.end);
        if content.is_empty() {
            let start = origin.get(at.index).copied().unwrap_or(first);
            let end = self.finish(l.end);
            self.report(C_EMPTY_BOX, MSG_EMPTY_BOX, Span { start, end });
            return;
        }
        self.separator(l);
        self.indent(
            (2 * at.column + segment) / (2 * segment) + 1,
            first,
            content_origin,
        );
        self.out.extend_from_slice(content.as_bytes());
        self.origin.extend_from_slice(
            origin
                .get(at.content..at.content + content.len())
                .unwrap_or(&[]),
        );
    }

    fn body(&mut self, l: LineSpan, segment: usize) {
        let raw = self.v.line(l).to_owned();
        if trim_js(&raw).is_empty() || comment_line(&raw) || metadata_line(&raw) {
            self.raw(l);
            return;
        }
        if all_runes(&raw, is_decoration_rune) {
            return;
        }
        let (norm, origin) = self.v.normalized(l);
        let text = String::from_utf8_lossy(&norm).into_owned();
        if let Some((index, column)) = branch_column(&text) {
            let content = content_start(&norm, index);
            let at = BranchAt {
                index,
                column,
                content,
            };
            self.branch(l, &norm, &origin, &at, segment);
            return;
        }
        self.plain(l, &text, &origin);
    }

    fn plain(&mut self, l: LineSpan, text: &str, origin: &[usize]) {
        if all_runes(text, is_box_or_space) {
            return;
        }
        if text.chars().any(is_box_rune) {
            self.raw(l);
        } else if text.chars().next().is_some_and(js_space) {
            let lead = text.len() - text.trim_start_matches(js_space).len();
            let start = origin.first().copied().unwrap_or(0);
            let end = origin.get(lead.saturating_sub(1)).map_or(start, |o| o + 1);
            self.report(C_MIXED, MSG_MIXED, Span { start, end });
        } else {
            self.raw(l);
        }
    }
}

pub(super) fn convert_box(
    text: &str,
    orig: Vec<usize>,
    end: usize,
) -> (String, Vec<usize>, Vec<Diagnostic>) {
    let v = View { text, orig: &orig };
    let lines = split_lines(text);
    let Some(keyword) = header_line(&v, &lines) else {
        return (text.to_owned(), orig, Vec::new());
    };
    let (head, body) = lines.split_at(keyword + 1);
    let content = content_lines(&v, body);
    if !content.iter().any(|line| line.chars().any(is_box_rune)) {
        return (text.to_owned(), orig, Vec::new());
    }
    let segment = segment_width(&content);
    let mut w = BoxWriter {
        v,
        end,
        out: Vec::new(),
        origin: Vec::new(),
        emit: false,
        prev_nl: 0,
        diags: Vec::new(),
    };
    for l in head {
        w.raw(*l);
    }
    for l in body {
        w.body(*l, segment);
    }
    let BoxWriter {
        out, origin, diags, ..
    } = w;
    (String::from_utf8_lossy(&out).into_owned(), origin, diags)
}
