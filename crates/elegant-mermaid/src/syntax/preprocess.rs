use crate::diag::{Diagnostic, Severity};
use crate::source::Span;
use crate::syntax::config_value::{
    ConfigValue, ParsedDoc, parse_json_doc, parse_yaml_doc, token_span,
};
use crate::syntax::{eol_len, line_content_end};

/// Code for every preprocessing diagnostic (preprocessing-126 to preprocessing-129).
pub const C_MALFORMED: &str = "config/malformed";

/// One recognized `%%{...}%%` directive, in source order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Directive {
    pub name: String,
    pub body: Span,
    pub init: Option<ConfigValue>,
    pub wrap: bool,
}

/// The frontmatter block: body span, parsed value, and extracted `config` mapping.
#[derive(Debug, Clone)]
pub struct Frontmatter {
    pub body: Span,
    pub value: ConfigValue,
    pub config: Option<ConfigValue>,
}

/// The result of preprocessing one source text (spec/preprocessing.md).
#[derive(Debug, Clone)]
pub struct Preprocessed {
    pub frontmatter: Option<Frontmatter>,
    pub directives: Vec<Directive>,
    pub init_config: Option<ConfigValue>,
    pub wrap: bool,
    pub removed: Vec<Span>,
    pub diagnostics: Vec<Diagnostic>,
}

/// Splits frontmatter, directives, and `%%` comments out of src; spans never change.
pub fn preprocess(src: &str) -> Preprocessed {
    let mut p = Prep {
        src,
        b: src.as_bytes(),
        region: 0,
        wrap: false,
        init: None,
        directives: Vec::new(),
        diags: Vec::new(),
        spans: Vec::new(),
        frontmatter: None,
    };
    p.frontmatter();
    p.directive_scan();
    p.comment_scan();
    p.merge_init();
    Preprocessed {
        frontmatter: p.frontmatter.take(),
        directives: std::mem::take(&mut p.directives),
        init_config: p.init.take().map(ConfigValue::Mapping),
        wrap: p.wrap,
        removed: merge_spans(std::mem::take(&mut p.spans)),
        diagnostics: std::mem::take(&mut p.diags),
    }
}

struct Fence {
    start: usize,
    indent_end: usize,
    end: usize,
}

struct Prep<'a> {
    src: &'a str,
    b: &'a [u8],
    region: usize,
    wrap: bool,
    init: Option<Vec<Entry>>,
    directives: Vec<Directive>,
    diags: Vec<Diagnostic>,
    spans: Vec<Span>,
    frontmatter: Option<Frontmatter>,
}

use crate::syntax::config_value::Entry;

impl<'a> Prep<'a> {
    fn frontmatter(&mut self) {
        let Some(f) = fence_at(self.b, 0) else {
            return;
        };
        let Some(c) = closing_fence(self.b, f.end, &self.b[..f.indent_end]) else {
            return;
        };
        let body = Span {
            start: f.end,
            end: c.start,
        };
        let doc = parse_yaml_doc(self.src, body.start, body.end);
        let config = self.front_config(&doc, body);
        self.diags.extend(doc.diagnostics);
        self.spans.push(Span {
            start: 0,
            end: c.end,
        });
        self.frontmatter = Some(Frontmatter {
            body,
            value: doc.value,
            config,
        });
        self.region = c.end;
    }

    fn front_config(&mut self, doc: &ParsedDoc, body: Span) -> Option<ConfigValue> {
        let ConfigValue::Mapping(entries) = &doc.value else {
            return None;
        };
        let e = entries.iter().find(|e| e.key == "config")?;
        match &e.value {
            ConfigValue::Mapping(_) => Some(e.value.clone()),
            _ => {
                let at = doc
                    .starts
                    .iter()
                    .find(|(k, _)| k == "config")
                    .map(|(_, v)| *v)
                    .unwrap_or(body.end);
                let span = token_span(self.src, body.start, body.end, at);
                self.push_malformed("frontmatter config must be a mapping", span);
                None
            }
        }
    }

    fn directive_scan(&mut self) {
        let len = self.b.len();
        let mut p = self.region;
        while p < len {
            if is_dir_start(self.b, p) {
                let end = self.directive(p).max(p + 1);
                self.spans.push(Span { start: p, end });
                p = end;
            } else {
                p += 1;
            }
        }
    }

    fn directive(&mut self, p: usize) -> usize {
        let Some(cj) = self.dir_close(p) else {
            let after = self.dir_ws(p + 3, self.b.len());
            let (name, _) = self.dir_word(after, self.b.len());
            if matches!(name.as_str(), "init" | "initialize" | "wrap") {
                self.push_malformed(
                    "malformed directive",
                    Span {
                        start: p,
                        end: p + 3,
                    },
                );
            }
            return self.b.len();
        };
        let after = self.dir_ws(p + 3, cj);
        let (name, name_end) = self.dir_word(after, cj);
        let colon = self.dir_ws(name_end, cj);
        if !matches!(name.as_str(), "init" | "initialize" | "wrap") {
            return cj + 3;
        }
        if colon < cj && self.b.get(colon) == Some(&b':') {
            return self.directive_body(p, cj, colon, name);
        }
        if colon != cj {
            self.push_malformed(
                "malformed directive",
                Span {
                    start: p,
                    end: p + 3,
                },
            );
            return cj + 3;
        }
        let wrap = name == "wrap";
        self.directives.push(Directive {
            name,
            body: Span { start: cj, end: cj },
            init: None,
            wrap,
        });
        cj + 3
    }

    fn directive_body(&mut self, p: usize, cj: usize, colon: usize, name: String) -> usize {
        if name == "wrap" {
            self.push_malformed(
                "wrap takes no body",
                Span {
                    start: p,
                    end: p + 3,
                },
            );
            return cj + 3;
        }
        let mut d = Directive {
            name,
            body: Span {
                start: colon + 1,
                end: cj,
            },
            init: None,
            wrap: false,
        };
        self.init_body(&mut d);
        self.directives.push(d);
        cj + 3
    }

    fn init_body(&mut self, d: &mut Directive) {
        let (s, e) = (d.body.start, d.body.end);
        let Some(q) = self.first_non_ws(s, e) else {
            return;
        };
        if self.b.get(q) != Some(&b'{') {
            let span = token_span(self.src, s, e, q);
            self.push_malformed("directive body must be a JSON object", span);
            return;
        }
        let jd = parse_json_doc(self.src, s, e);
        self.diags.extend(jd.diagnostics);
        if !jd.stop {
            d.init = Some(jd.value);
        }
    }

    fn dir_close(&self, p: usize) -> Option<usize> {
        let len = self.b.len();
        let mut j = p + 3;
        while j + 2 < len {
            if matches!(
                (self.b.get(j), self.b.get(j + 1), self.b.get(j + 2)),
                (Some(b'}'), Some(b'%'), Some(b'%'))
            ) {
                return Some(j);
            }
            j += 1;
        }
        None
    }

    fn dir_ws(&self, from: usize, to: usize) -> usize {
        let mut i = from;
        while i < to
            && matches!(
                self.b.get(i),
                Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
            )
        {
            i += 1;
        }
        i
    }

    fn dir_word(&self, from: usize, to: usize) -> (String, usize) {
        let mut i = from;
        while i < to && matches!(self.b.get(i), Some(c) if c.is_ascii_alphanumeric() || *c == b'_')
        {
            i += 1;
        }
        (self.src.get(from..i).unwrap_or_default().to_string(), i)
    }

    fn first_non_ws(&self, from: usize, to: usize) -> Option<usize> {
        let mut i = from;
        while i < to
            && matches!(
                self.b.get(i),
                Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
            )
        {
            i += 1;
        }
        (i < to).then_some(i)
    }

    fn comment_scan(&mut self) {
        let len = self.b.len();
        let mut blanked = SpanCursor::new(merge_spans(self.spans.clone()));
        let mut blank_from: Option<usize> = None;
        let mut p = self.region;
        while p < len {
            let e = line_content_end(self.b, p, len);
            let nl = e + eol_len(self.b, e);
            if self.comment_line(p, e) {
                self.spans.push(Span {
                    start: blank_from.take().unwrap_or(p),
                    end: nl,
                });
            } else if self.blank_line(p, e, &mut blanked) {
                blank_from.get_or_insert(p);
            } else {
                blank_from = None;
            }
            if nl <= p {
                break;
            }
            p = nl;
        }
    }

    fn blank_line(&self, start: usize, end: usize, removed: &mut SpanCursor) -> bool {
        (start..end).all(|i| matches!(self.b.get(i), Some(b' ') | Some(b'\t')) || removed.covers(i))
    }

    fn comment_line(&self, ls: usize, e: usize) -> bool {
        let mut i = ls;
        while i < e && matches!(self.b.get(i), Some(b' ') | Some(b'\t')) {
            i += 1;
        }
        if !matches!((self.b.get(i), self.b.get(i + 1)), (Some(b'%'), Some(b'%'))) {
            return false;
        }
        self.b.get(i + 2) != Some(&b'{')
    }

    fn merge_init(&mut self) {
        let dirs = std::mem::take(&mut self.directives);
        let mut acc: Option<Vec<Entry>> = None;
        for d in &dirs {
            if d.wrap {
                self.wrap = true;
            }
            let Some(ConfigValue::Mapping(add)) = &d.init else {
                continue;
            };
            acc = Some(match acc.take() {
                None => add.clone(),
                Some(base) => merge_top(&base, add),
            });
        }
        self.directives = dirs;
        self.init = acc;
    }

    fn push_malformed(&mut self, msg: &str, span: Span) {
        self.diags.push(Diagnostic {
            code: C_MALFORMED,
            severity: Severity::Error,
            message: msg.to_string(),
            span,
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        });
    }
}

fn fence_at(b: &[u8], from: usize) -> Option<Fence> {
    let mut i = from;
    while matches!(b.get(i), Some(b' ') | Some(b'\t')) {
        i += 1;
    }
    if !matches!(
        (b.get(i), b.get(i + 1), b.get(i + 2)),
        (Some(b'-'), Some(b'-'), Some(b'-'))
    ) {
        return None;
    }
    let mut j = i + 3;
    while matches!(b.get(j), Some(b' ') | Some(b'\t')) {
        j += 1;
    }
    let e = line_content_end(b, j, b.len());
    if e != j {
        return None;
    }
    let el = eol_len(b, e);
    if el == 0 {
        return None;
    }
    Some(Fence {
        start: from,
        indent_end: i,
        end: e + el,
    })
}

fn closing_fence(b: &[u8], mut from: usize, indent: &[u8]) -> Option<Fence> {
    while from < b.len() {
        if let Some(f) = fence_at(b, from)
            && &b[from..f.indent_end] == indent
        {
            return Some(f);
        }
        let e = line_content_end(b, from, b.len());
        if e >= b.len() {
            return None;
        }
        from = e + eol_len(b, e);
    }
    None
}

fn is_dir_start(b: &[u8], p: usize) -> bool {
    matches!(
        (b.get(p), b.get(p + 1), b.get(p + 2)),
        (Some(b'%'), Some(b'%'), Some(b'{'))
    )
}

fn merge_spans(mut spans: Vec<Span>) -> Vec<Span> {
    spans.sort_by_key(|s| s.start);
    let mut out: Vec<Span> = Vec::new();
    for s in spans {
        match out.last_mut() {
            Some(l) if s.start <= l.end => {
                if s.end > l.end {
                    l.end = s.end;
                }
            }
            _ => out.push(s),
        }
    }
    out
}

struct SpanCursor {
    spans: Vec<Span>,
    next: usize,
}

impl SpanCursor {
    fn new(spans: Vec<Span>) -> Self {
        Self { spans, next: 0 }
    }

    fn covers(&mut self, offset: usize) -> bool {
        while self.spans.get(self.next).is_some_and(|s| s.end <= offset) {
            self.next += 1;
        }
        self.spans.get(self.next).is_some_and(|s| s.start <= offset)
    }
}

fn merge_top(base: &[Entry], add: &[Entry]) -> Vec<Entry> {
    let mut out = base.to_vec();
    for e in add {
        match out.iter_mut().find(|x| x.key == e.key) {
            Some(slot) => slot.value = merged_value(&slot.value, &e.value),
            None => out.push(e.clone()),
        }
    }
    out
}

fn merged_value(a: &ConfigValue, b: &ConfigValue) -> ConfigValue {
    let (ConfigValue::Mapping(ma), ConfigValue::Mapping(mb)) = (a, b) else {
        return b.clone();
    };
    ConfigValue::Mapping(merge_one(ma, mb))
}

fn merge_one(base: &[Entry], add: &[Entry]) -> Vec<Entry> {
    let mut out = base.to_vec();
    for e in add {
        match out.iter_mut().find(|x| x.key == e.key) {
            Some(slot) => slot.value = e.value.clone(),
            None => out.push(e.clone()),
        }
    }
    out
}

#[cfg(test)]
#[path = "preprocess_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "preprocess/comment_tests.rs"]
mod comment_tests;
