use crate::diag::{Diagnostic, Severity};
use crate::source::Span;
use crate::syntax::{eol_len, is_ws_byte, line_content_end};

/// Diagnostic codes and messages follow spec/preprocessing.md, table preprocessing-128.
pub const C_MALFORMED: &str = "config/malformed";
const C_ANCHOR: &str = "config/unsupported-anchor";
const C_TAG: &str = "config/unsupported-tag";
const C_DEPTH: &str = "limit/nesting-depth";

/// One parsed config value; integers and decimals keep their source text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfigValue {
    Null,
    Bool(bool),
    Integer(String),
    Decimal(String),
    String(String),
    Sequence(Vec<ConfigValue>),
    Mapping(Vec<Entry>),
}

/// One mapping entry in source order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    pub key: String,
    pub key_span: Span,
    pub value: ConfigValue,
}

pub(crate) struct ParsedDoc {
    pub value: ConfigValue,
    pub stop: bool,
    pub diagnostics: Vec<Diagnostic>,
    pub starts: Vec<(String, usize)>,
}

/// Parses the YAML subset of spec/preprocessing.md over src[start..end].
pub fn parse_config_yaml(src: &str, start: usize, end: usize) -> (ConfigValue, Vec<Diagnostic>) {
    let d = parse_yaml_doc(src, start, end);
    (d.value, d.diagnostics)
}

/// Parses the JSON grammar of spec/preprocessing.md; every `'` byte is read as `"`.
pub fn parse_config_json(src: &str, start: usize, end: usize) -> (ConfigValue, Vec<Diagnostic>) {
    let d = parse_json_doc(src, start, end);
    (d.value, d.diagnostics)
}

pub(crate) fn parse_yaml_doc(src: &str, start: usize, end: usize) -> ParsedDoc {
    run_doc(src, start, end, false)
}

pub(crate) fn parse_json_doc(src: &str, start: usize, end: usize) -> ParsedDoc {
    run_doc(src, start, end, true)
}

pub(crate) fn token_span(src: &str, start: usize, end: usize, at: usize) -> Span {
    let s = start.min(src.len());
    let e = end.min(src.len()).max(s);
    Cfg::new(src, s, e, false).token_span(at)
}

fn run_doc(src: &str, start: usize, end: usize, json: bool) -> ParsedDoc {
    let s = start.min(src.len());
    let e = end.min(src.len()).max(s);
    let mut p = Cfg::new(src, s, e, json);
    let v = if json {
        p.json_run()
    } else {
        p.yaml_document()
    };
    let stop = p.stop;
    let starts = std::mem::take(&mut p.starts);
    ParsedDoc {
        value: if stop { ConfigValue::Null } else { v },
        stop,
        diagnostics: p.diags,
        starts,
    }
}

/// Converts an integer or decimal config value to thousandths (preprocessing-137).
pub fn thousandths(v: &ConfigValue) -> Option<i32> {
    match v {
        ConfigValue::Integer(t) | ConfigValue::Decimal(t) => thousandths_text(t.as_str()),
        _ => None,
    }
}

#[derive(Clone, Copy, PartialEq)]
enum LineKind {
    Entry,
    Scalar,
}

#[derive(Clone, Copy, PartialEq)]
enum Step {
    Next,
    Done,
    Stopped,
}

struct Line {
    from: usize,
    content: usize,
    col: usize,
    eol_pos: usize,
    next: usize,
    tab_at: Option<usize>,
}

struct Cfg<'a> {
    src: &'a str,
    b: &'a [u8],
    start: usize,
    end: usize,
    pos: usize,
    depth: usize,
    json: bool,
    yaml_continuation_col: Option<usize>,
    stop: bool,
    diags: Vec<Diagnostic>,
    starts: Vec<(String, usize)>,
}

mod block_mapping;
mod block_scalars;
mod cursor;
mod flow_collections;
mod json;
mod numbers;
mod quoted_scalars;
mod yaml_document;
use numbers::*;

fn simple_escape(c: Option<u8>) -> Option<(u8, usize)> {
    match c {
        Some(b'"') => Some((b'"', 2)),
        Some(b'\\') => Some((b'\\', 2)),
        Some(b'/') => Some((b'/', 2)),
        Some(b'b') => Some((8, 2)),
        Some(b'f') => Some((12, 2)),
        Some(b'n') => Some((b'\n', 2)),
        Some(b'r') => Some((b'\r', 2)),
        Some(b't') => Some((b'\t', 2)),
        _ => None,
    }
}

struct EntryOut {
    key: String,
    key_span: Span,
    value_start: usize,
    value: ConfigValue,
    inline: bool,
}

fn hex_digit(c: u8) -> Option<u32> {
    match c {
        b'0'..=b'9' => Some(u32::from(c - b'0')),
        b'a'..=b'f' => Some(u32::from(c - b'a' + 10)),
        b'A'..=b'F' => Some(u32::from(c - b'A' + 10)),
        _ => None,
    }
}

fn push_char(out: &mut Vec<u8>, cp: u32) {
    if let Some(ch) = char::from_u32(cp) {
        let mut buf = [0u8; 4];
        out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
    }
}

fn trim_end(b: &[u8], from: usize, to: usize) -> usize {
    let mut e = to;
    while e > from {
        match b.get(e - 1) {
            Some(b' ') | Some(b'\t') => e -= 1,
            _ => break,
        }
    }
    e
}

fn block_sep(out: &mut String, folded: bool, e: usize, a_more: bool, b_more: bool) {
    let lfs = if !folded || a_more || b_more {
        e + 1
    } else if e == 0 {
        0
    } else {
        e
    };
    for _ in 0..lfs {
        out.push('\n');
    }
    if folded && !a_more && !b_more && e == 0 {
        out.push(' ');
    }
}

fn assemble_block(folded: bool, chomp: u8, leading: usize, parts: &[Option<Vec<u8>>]) -> String {
    let mut trailing = 0usize;
    let mut body = parts;
    while matches!(body.last(), Some(None)) {
        body = &body[..body.len() - 1];
        trailing += 1;
    }
    let mut out = String::new();
    let mut pending = 0usize;
    let mut prev_more = false;
    let mut first = true;
    for p in body {
        match p {
            None => pending += 1,
            Some(line) => {
                if first {
                    for _ in 0..leading {
                        out.push('\n');
                    }
                } else {
                    let more = matches!(line.first(), Some(b' ') | Some(b'\t'));
                    block_sep(&mut out, folded, pending, prev_more, more);
                    prev_more = more;
                }
                out.push_str(&String::from_utf8_lossy(line));
                pending = 0;
                first = false;
            }
        }
    }
    if first {
        return match chomp {
            b'+' => "\n".repeat(leading),
            _ => String::new(),
        };
    }
    match chomp {
        b'-' => {}
        b'+' => {
            out.push('\n');
            for _ in 0..trailing {
                out.push('\n');
            }
        }
        _ => out.push('\n'),
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    pub(super) fn check(ds: &[Diagnostic], code: &str, msg: &str, span: Span) {
        assert!(!ds.is_empty(), "no diagnostic; want {code} {msg} {span:?}");
        let d = &ds[0];
        assert_eq!(d.code, code);
        assert_eq!(d.message, msg);
        assert_eq!(d.span, span);
        assert_eq!(d.severity, Severity::Error);
        assert!(
            d.help.is_empty(),
            "expected d.help.is_empty(); observed d.help={:?}",
            d.help
        );
        assert!(
            d.fixes.is_empty(),
            "expected d.fixes.is_empty(); observed d.fixes={:?}",
            d.fixes
        );
        assert!(
            d.related.is_empty(),
            "expected d.related.is_empty(); observed d.related={:?}",
            d.related
        );
    }

    pub(super) fn mapping(v: ConfigValue) -> Vec<Entry> {
        let ConfigValue::Mapping(m) = v else {
            unreachable!("expected ConfigValue::Mapping(m); observed {:?}", v)
        };
        m
    }

    pub(super) fn sequence(v: ConfigValue) -> Vec<ConfigValue> {
        let ConfigValue::Sequence(s) = v else {
            unreachable!("expected ConfigValue::Sequence(s); observed {:?}", v)
        };
        s
    }

    pub(super) fn text(v: ConfigValue) -> String {
        let ConfigValue::String(s) = v else {
            unreachable!("expected ConfigValue::String(s); observed {:?}", v)
        };
        s
    }

    pub(super) fn int_text(v: &ConfigValue) -> &str {
        let ConfigValue::Integer(t) = v else {
            unreachable!("expected ConfigValue::Integer(t); observed {:?}", v)
        };
        t
    }

    pub(super) fn dec_text(v: &ConfigValue) -> &str {
        let ConfigValue::Decimal(t) = v else {
            unreachable!("expected ConfigValue::Decimal(t); observed {:?}", v)
        };
        t
    }

    pub(super) fn parse_top(src: &str) -> ConfigValue {
        let (v, ds) = parse_config_yaml(src, 0, src.len());
        assert!(ds.is_empty(), "diags {ds:?} src {src:?}");
        v
    }

    pub(super) fn entry_of<'a>(m: &'a [Entry], key: &str) -> &'a Entry {
        let Some(e) = m.iter().find(|e| e.key == key) else {
            unreachable!(
                "expected Some(e); observed {:?}",
                m.iter().find(|e| e.key == key)
            )
        };
        e
    }

    pub(super) fn entry_value(src: &str, key: &str) -> ConfigValue {
        let v = parse_top(src);
        entry_of(&mapping(v), key).value.clone()
    }

    const ALPHABET: [char; 25] = [
        ' ', '\t', '\n', ':', '-', '#', '[', ']', '{', '}', ',', '\'', '"', '|', '>', '&', '*',
        '!', 'a', 'b', 'c', '0', '1', '2', '\\',
    ];

    struct Xs(u32);

    impl Xs {
        fn next(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            self.0 = x;
            x
        }

        fn below(&mut self, n: u32) -> u32 {
            self.next() % n
        }
    }

    pub(super) fn random_case(i: u32) -> String {
        let mut g = Xs(i.wrapping_add(1));
        let len = 1 + g.below(40);
        let mut s = String::new();
        for _ in 0..len {
            let idx = g.below(25) as usize;
            let Some(c) = ALPHABET.get(idx) else {
                unreachable!("expected Some(c); observed {:?}", ALPHABET.get(idx))
            };
            s.push(*c);
        }
        s
    }

    pub(super) fn in_bounds(s: &str, sp: Span) -> bool {
        sp.start <= sp.end
            && sp.end <= s.len()
            && s.is_char_boundary(sp.start)
            && s.is_char_boundary(sp.end)
    }

    pub(super) fn block_value(src: &str) -> String {
        text(entry_value(src, "a"))
    }

    mod extensions {
        include!("config_value/extensions_tests.rs");
    }
    mod diagnostic_spans {
        include!("config_value/diagnostic_spans_tests.rs");
    }
    mod collections {
        include!("config_value/collections_tests.rs");
    }
    mod settled_grammar {
        include!("config_value/settled_grammar_tests.rs");
    }
    mod reader_rules {
        include!("config_value/reader_rules_tests.rs");
    }
}
