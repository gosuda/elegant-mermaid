use std::borrow::Cow;

use crate::source::Span;

#[derive(Debug, Clone)]
pub(crate) struct Cleaned<'a> {
    src: &'a str,
    text: Cow<'a, str>,
    segments: Vec<Segment>,
}

#[derive(Debug, Clone, Copy)]
struct Segment {
    clean: usize,
    orig: usize,
    len: usize,
}

impl<'a> Cleaned<'a> {
    pub(crate) fn new(src: &'a str, removed: &[Span]) -> Self {
        let gaps = merge_gaps(removed, src.len());
        if gaps.is_empty() {
            return Self {
                src,
                text: Cow::Borrowed(src),
                segments: vec![Segment {
                    clean: 0,
                    orig: 0,
                    len: src.len(),
                }],
            };
        }
        let mut text = String::with_capacity(src.len());
        let mut segments = Vec::with_capacity(gaps.len() + 1);
        let mut at = 0;
        for gap in &gaps {
            keep(&mut text, &mut segments, src, at, gap.start);
            at = gap.end;
        }
        keep(&mut text, &mut segments, src, at, src.len());
        Self {
            src,
            text: Cow::Owned(text),
            segments,
        }
    }

    pub(crate) fn text(&self) -> &str {
        &self.text
    }

    pub(crate) fn offset(&self, clean: usize) -> usize {
        if clean >= self.text.len() {
            return self.src.len();
        }
        let i = self.segments.partition_point(|s| s.clean <= clean) - 1;
        let s = self.segments[i];
        s.orig + clean - s.clean
    }

    pub(crate) fn span(&self, start: usize, end: usize) -> Span {
        if end <= start {
            let at = self.offset(start);
            return Span { start: at, end: at };
        }
        Span {
            start: self.offset(start),
            end: self.offset(end - 1) + 1,
        }
    }

    pub(crate) fn index(&self, orig: usize) -> usize {
        let i = self.segments.partition_point(|s| s.orig <= orig);
        if i == 0 {
            return 0;
        }
        let s = self.segments[i - 1];
        s.clean + (orig - s.orig).min(s.len)
    }

    pub(crate) fn cow(&self, start: usize, end: usize) -> Cow<'a, str> {
        let span = self.span(start, end);
        if span.end - span.start == end.saturating_sub(start) {
            Cow::Borrowed(&self.src[span.start..span.end])
        } else {
            Cow::Owned(self.text[start..end].to_owned())
        }
    }

    pub(crate) fn slice(&self, span: Span) -> Cow<'a, str> {
        self.cow(self.index(span.start), self.index(span.end))
    }
}

fn keep(text: &mut String, segments: &mut Vec<Segment>, src: &str, from: usize, to: usize) {
    if to <= from {
        return;
    }
    segments.push(Segment {
        clean: text.len(),
        orig: from,
        len: to - from,
    });
    text.push_str(&src[from..to]);
}

fn merge_gaps(removed: &[Span], limit: usize) -> Vec<Span> {
    let mut gaps: Vec<Span> = removed
        .iter()
        .map(|s| {
            let start = s.start.min(limit);
            Span {
                start,
                end: s.end.min(limit).max(start),
            }
        })
        .filter(|s| s.end > s.start)
        .collect();
    gaps.sort_by_key(|s| (s.start, s.end));
    let mut out: Vec<Span> = Vec::with_capacity(gaps.len());
    for s in gaps {
        match out.last_mut() {
            Some(last) if s.start <= last.end => last.end = last.end.max(s.end),
            _ => out.push(s),
        }
    }
    out
}
