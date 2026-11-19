use super::text::js_space;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;
use crate::syntax::{eol_len, line_content_end};

pub(super) fn prepare(src: &str, removed: &[Span]) -> (String, Vec<usize>) {
    let front = frontmatter_span(src);
    let (kept, origin) = filter_removed(src, &structural(src, removed, front));
    let (kept, origin) = normalize_breaks(&kept, &origin);
    let (kept, origin) = drop_comments(&kept, &origin);
    trim_start(&kept, &origin)
}

fn frontmatter_span(src: &str) -> Span {
    let Some(front) = preprocess(src).frontmatter else {
        return Span { start: 0, end: 0 };
    };
    let bytes = src.as_bytes();
    let content = line_content_end(bytes, front.body.end, bytes.len());
    Span {
        start: 0,
        end: content + eol_len(bytes, content),
    }
}

fn line_break(c: u8) -> bool {
    c == b'\n' || c == b'\r'
}

fn line_start_at(src: &[u8], at: usize) -> bool {
    at == 0 || src.get(at - 1).copied().is_some_and(line_break)
}

fn next_line(src: &[u8], mut at: usize) -> usize {
    while at < src.len() && !src.get(at).copied().is_some_and(line_break) {
        at += 1;
    }
    if src.get(at) == Some(&b'\r') && src.get(at + 1) == Some(&b'\n') {
        return at + 2;
    }
    (at + 1).min(src.len())
}

fn comment_line_text(line: &[u8]) -> bool {
    let skipped = line
        .iter()
        .take_while(|c| **c == b' ' || **c == b'\t')
        .count();
    let rest = line.get(skipped..).unwrap_or(&[]);
    rest.starts_with(b"%%") && !rest.starts_with(b"%%{")
}

fn structural(src: &str, removed: &[Span], front: Span) -> Vec<Span> {
    let bytes = src.as_bytes();
    let mut out: Vec<Span> = Vec::new();
    for span in removed {
        let to = span.end.min(src.len());
        let mut pos = span.start;
        while pos < to {
            let end = next_line(bytes, pos).min(to);
            let in_front = pos < front.end && pos >= front.start;
            let comment = bytes.get(pos..end).is_some_and(comment_line_text);
            if !line_start_at(bytes, pos) || in_front || !comment {
                append_span(&mut out, pos, end);
            }
            pos = end;
        }
    }
    out
}

fn append_span(spans: &mut Vec<Span>, from: usize, to: usize) {
    match spans.last_mut() {
        Some(last) if last.end == from => last.end = to,
        _ => spans.push(Span {
            start: from,
            end: to,
        }),
    }
}

fn filter_removed(src: &str, removed: &[Span]) -> (Vec<u8>, Vec<usize>) {
    let bytes = src.as_bytes();
    let mut kept = Vec::with_capacity(bytes.len());
    let mut origin = Vec::with_capacity(bytes.len());
    let mut at = 0;
    for span in removed {
        let from = span.start.max(at);
        let to = span.end.min(bytes.len());
        if from >= to {
            continue;
        }
        append_range(&mut kept, &mut origin, bytes, at, from);
        at = to;
    }
    append_range(&mut kept, &mut origin, bytes, at, bytes.len());
    (kept, origin)
}

fn append_range(kept: &mut Vec<u8>, origin: &mut Vec<usize>, src: &[u8], from: usize, to: usize) {
    for i in from..to {
        kept.push(src.get(i).copied().unwrap_or(0));
        origin.push(i);
    }
}

fn normalize_breaks(kept: &[u8], origin: &[usize]) -> (Vec<u8>, Vec<usize>) {
    let mut text = Vec::with_capacity(kept.len());
    let mut mapped = Vec::with_capacity(kept.len());
    let mut i = 0;
    while i < kept.len() {
        let mut c = kept.get(i).copied().unwrap_or(0);
        let mut at = origin.get(i).copied().unwrap_or(0);
        if c == b'\r' {
            c = b'\n';
            if kept.get(i + 1) == Some(&b'\n') {
                i += 1;
                at = origin.get(i).copied().unwrap_or(at);
            }
        }
        text.push(c);
        mapped.push(at);
        i += 1;
    }
    (text, mapped)
}

pub(super) fn decode(text: &[u8], at: usize) -> (char, usize) {
    let window = text.get(at..(at + 4).min(text.len())).unwrap_or(&[]);
    let valid = match std::str::from_utf8(window) {
        Ok(s) => s,
        Err(e) => std::str::from_utf8(window.get(..e.valid_up_to()).unwrap_or(&[])).unwrap_or(""),
    };
    valid
        .chars()
        .next()
        .map_or(('\u{fffd}', 1), |c| (c, c.len_utf8()))
}

fn skip_space(text: &[u8], mut at: usize) -> usize {
    while at < text.len() {
        let (c, n) = decode(text, at);
        if !js_space(c) {
            break;
        }
        at += n;
    }
    at
}

fn line_end_index(text: &[u8], mut at: usize) -> usize {
    while at < text.len() && text.get(at) != Some(&b'\n') {
        at += 1;
    }
    at
}

fn comment_extent(text: &[u8], q: usize) -> Option<usize> {
    let rest = text.get(q..)?;
    if !rest.starts_with(b"%%") || rest.starts_with(b"%%{") {
        return None;
    }
    Some((line_end_index(text, q + 2) + 1).min(text.len()))
}

fn drop_comments(text: &[u8], origin: &[usize]) -> (Vec<u8>, Vec<usize>) {
    let mut out = Vec::with_capacity(text.len());
    let mut mapped = Vec::with_capacity(text.len());
    let mut p = 0;
    while p < text.len() {
        let q = skip_space(text, p);
        if let Some(end) = comment_extent(text, q) {
            p = end;
            continue;
        }
        let next = (line_end_index(text, q) + 1).min(text.len());
        out.extend_from_slice(text.get(p..next).unwrap_or(&[]));
        mapped.extend_from_slice(origin.get(p..next).unwrap_or(&[]));
        p = next;
    }
    (out, mapped)
}

fn trim_start(text: &[u8], origin: &[usize]) -> (String, Vec<usize>) {
    let start = skip_space(text, 0);
    (
        String::from_utf8_lossy(text.get(start..).unwrap_or(&[])).into_owned(),
        origin.get(start..).unwrap_or(&[]).to_vec(),
    )
}
