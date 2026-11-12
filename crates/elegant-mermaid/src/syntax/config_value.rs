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
    stop: bool,
    diags: Vec<Diagnostic>,
    starts: Vec<(String, usize)>,
}

impl<'a> Cfg<'a> {
    fn new(src: &'a str, start: usize, end: usize, json: bool) -> Cfg<'a> {
        Cfg {
            src,
            b: src.as_bytes(),
            start,
            end,
            pos: start,
            depth: 0,
            json,
            stop: false,
            diags: Vec::new(),
            starts: Vec::new(),
        }
    }

    fn raw(&self, i: usize) -> Option<u8> {
        self.b.get(i).copied()
    }

    fn at(&self, i: usize) -> Option<u8> {
        self.b
            .get(i)
            .map(|c| if self.json && *c == b'\'' { b'"' } else { *c })
    }

    fn cur(&self) -> Option<u8> {
        self.at(self.pos)
    }

    fn at_end(&self) -> bool {
        self.pos >= self.end
    }

    fn text(&self, a: usize, b: usize) -> String {
        self.src.get(a..b).unwrap_or_default().to_string()
    }

    fn eol(&self, i: usize) -> usize {
        eol_len(self.b, i)
    }

    fn content_end(&self, from: usize) -> usize {
        line_content_end(self.b, from, self.end)
    }

    fn token_span(&self, at: usize) -> Span {
        let p = at.min(self.end).max(self.start);
        if p >= self.end {
            return Span { start: p, end: p };
        }
        let e = match self.raw(p).unwrap_or(0) {
            b'\n' => p + 1,
            b'\r' => p + self.eol(p),
            b' ' | b'\t' => p + 1,
            _ => self.token_run(p),
        };
        Span { start: p, end: e }
    }

    fn token_run(&self, p: usize) -> usize {
        let mut j = p;
        while j < self.end && matches!(self.raw(j), Some(c) if !is_ws_byte(c)) {
            j += 1;
        }
        j
    }

    fn err(&mut self, code: &'static str, msg: &str, span: Span) {
        self.diags.push(Diagnostic {
            code,
            severity: Severity::Error,
            message: msg.to_string(),
            span,
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        });
    }

    fn fail(&mut self, at: usize) {
        let span = self.token_span(at);
        self.err(C_MALFORMED, "malformed config value", span);
        self.stop = true;
    }

    fn enter(&mut self, open: usize) -> bool {
        if self.depth >= 64 {
            self.err(
                C_DEPTH,
                "nesting depth exceeds 64",
                Span {
                    start: open,
                    end: open + 1,
                },
            );
            self.stop = true;
            return false;
        }
        self.depth += 1;
        true
    }

    fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    fn skip_inline_ws(&mut self) {
        while matches!(self.cur(), Some(b' ') | Some(b'\t')) {
            self.pos += 1;
        }
    }

    fn boundary(&self, i: usize) -> bool {
        matches!(
            self.raw(i),
            Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
        )
    }

    fn line_scan(&self, from: usize) -> Line {
        let mut i = from;
        let mut col = 0usize;
        while self.raw(i) == Some(b' ') {
            i += 1;
            col += 1;
        }
        let tab_at = (self.raw(i) == Some(b'\t')).then_some(i);
        let eol = line_content_end(self.b, i, self.end);
        Line {
            from,
            content: i,
            col,
            eol_pos: eol,
            next: eol + self.eol(eol),
            tab_at,
        }
    }

    fn take_line(&mut self, from: usize) -> Line {
        let l = self.line_scan(from);
        if let Some(t) = l.tab_at {
            self.err(
                C_MALFORMED,
                "tab in indentation",
                Span {
                    start: t,
                    end: t + 1,
                },
            );
            self.stop = true;
        }
        l
    }

    fn line_blank(&self, l: &Line) -> bool {
        matches!(self.raw(l.content), None | Some(b'\r') | Some(b'\n'))
    }

    fn skip_lines(&mut self) {
        while !self.stop && self.pos < self.end {
            let l = self.take_line(self.pos);
            if self.stop {
                return;
            }
            match self.raw(l.content) {
                None | Some(b'\r') | Some(b'\n') | Some(b'#') => self.pos = l.next,
                Some(_) => return,
            }
        }
    }

    fn marker_check(&mut self) -> bool {
        let tri = (
            self.raw(self.pos),
            self.raw(self.pos + 1),
            self.raw(self.pos + 2),
        );
        let marker = matches!(
            tri,
            (Some(b'.'), Some(b'.'), Some(b'.')) | (Some(b'-'), Some(b'-'), Some(b'-'))
        );
        if !marker {
            return false;
        }
        let bounded = match self.raw(self.pos + 3) {
            None => true,
            Some(c) => is_ws_byte(c),
        };
        if bounded {
            self.err(
                C_MALFORMED,
                "multi-document streams are not supported",
                Span {
                    start: self.pos,
                    end: self.pos + 3,
                },
            );
            self.stop = true;
        }
        bounded
    }

    fn node_guard(&mut self) -> bool {
        let p = self.pos;
        let Some(c) = self.raw(p) else {
            return false;
        };
        if matches!(c, b'-' | b'?') && self.boundary(p + 1) {
            self.node_block_error(c);
            return true;
        }
        if c == b'&' || c == b'*' {
            let mut j = p + 1;
            while j < self.end && self.anchor_byte(j) {
                j += 1;
            }
            self.err(
                C_ANCHOR,
                "anchors and aliases are not supported",
                Span { start: p, end: j },
            );
            self.stop = true;
            return true;
        }
        if c == b'!' {
            let mut j = p + 1;
            while j < self.end && self.tag_byte(j) {
                j += 1;
            }
            self.err(C_TAG, "tags are not supported", Span { start: p, end: j });
            self.stop = true;
            return true;
        }
        false
    }

    fn node_block_error(&mut self, c: u8) {
        let msg = if c == b'-' {
            "block sequences are not supported"
        } else {
            "complex keys are not supported"
        };
        self.err(
            C_MALFORMED,
            msg,
            Span {
                start: self.pos,
                end: self.pos + 1,
            },
        );
        self.stop = true;
    }

    fn anchor_byte(&self, j: usize) -> bool {
        match self.raw(j) {
            Some(c) => c.is_ascii_alphanumeric() || c == b'_' || c == b'-',
            None => false,
        }
    }

    fn tag_byte(&self, j: usize) -> bool {
        match self.raw(j) {
            Some(c) => !is_ws_byte(c) && !matches!(c, b',' | b'[' | b']' | b'{' | b'}'),
            None => false,
        }
    }

    fn plain_first_rejected(&self) -> bool {
        matches!(
            self.raw(self.pos),
            Some(b'%') | Some(b'@') | Some(b'`') | Some(b',') | Some(b']') | Some(b'}')
        )
    }

    fn plain_line_kind(&self) -> LineKind {
        let from = self.pos;
        let to = self.content_end(from);
        let mut j = from;
        while j < to {
            let c = self.raw(j);
            if c == Some(b':') && self.boundary(j + 1) {
                return LineKind::Entry;
            }
            if matches!(c, Some(b' ') | Some(b'\t')) && self.raw(j + 1) == Some(b'#') {
                return LineKind::Scalar;
            }
            j += 1;
        }
        LineKind::Scalar
    }

    fn yaml_document(&mut self) -> ConfigValue {
        self.skip_lines();
        if self.stop || self.at_end() || self.marker_check() {
            return ConfigValue::Null;
        }
        let l = self.take_line(self.pos);
        if self.stop {
            return ConfigValue::Null;
        }
        let v = self.root_value(l.col);
        if !self.stop {
            self.tail();
        }
        v
    }

    fn root_value(&mut self, col: usize) -> ConfigValue {
        match self.raw(self.pos) {
            Some(b'[') => self.flow_seq_value(col),
            Some(b'{') => self.flow_map_value(col),
            Some(b'"') => self.root_quoted_double(),
            Some(b'\'') => self.root_quoted_single(),
            Some(b'|') | Some(b'>') => {
                self.fail(self.pos);
                ConfigValue::Null
            }
            _ => self.plain_or_map(col),
        }
    }

    fn root_quoted_double(&mut self) -> ConfigValue {
        let q = self.quoted_double();
        self.root_quoted_done(q)
    }

    fn root_quoted_single(&mut self) -> ConfigValue {
        let q = self.quoted_single();
        self.root_quoted_done(q)
    }

    fn root_quoted_done(&mut self, q: Option<(String, Span)>) -> ConfigValue {
        let Some((t, _)) = q else {
            return ConfigValue::Null;
        };
        self.finish_line();
        ConfigValue::String(t)
    }

    fn plain_or_map(&mut self, col: usize) -> ConfigValue {
        if self.node_guard() {
            return ConfigValue::Null;
        }
        if self.plain_line_kind() == LineKind::Entry {
            return self.block_map(col, self.pos);
        }
        if self.raw(self.pos) == Some(b':') && self.boundary(self.pos + 1) {
            self.fail(self.pos);
            return ConfigValue::Null;
        }
        if self.plain_first_rejected() {
            self.fail(self.pos);
            return ConfigValue::Null;
        }
        let text = self.plain_value_text();
        let v = resolve_plain(&text);
        self.finish_line();
        v
    }

    fn tail(&mut self) {
        self.skip_lines();
        if self.stop || self.at_end() {
            return;
        }
        if self.marker_check() {
            return;
        }
        let l = self.take_line(self.pos);
        if self.stop {
            return;
        }
        self.fail(l.content);
    }

    fn block_map(&mut self, n: usize, open: usize) -> ConfigValue {
        if !self.enter(open) {
            return ConfigValue::Null;
        }
        let root = self.depth == 1;
        let mut entries: Vec<Entry> = Vec::new();
        let mut first = true;
        while !self.stop {
            if first {
                let l = self.take_line(self.pos);
                if self.stop {
                    break;
                }
                self.pos = l.content;
                first = false;
            } else if !self.map_advance(n) {
                break;
            }
            let Some(mut out) = self.entry(n) else {
                break;
            };
            if !out.inline {
                out.value = self.nested_or_null(n);
            }
            if self.stop {
                break;
            }
            self.map_commit(root, &mut entries, out);
        }
        let v = if self.stop {
            ConfigValue::Null
        } else {
            ConfigValue::Mapping(entries)
        };
        self.leave();
        v
    }

    fn map_advance(&mut self, n: usize) -> bool {
        self.skip_lines();
        if self.stop || self.at_end() {
            return false;
        }
        if n == 0 && self.marker_check() {
            return false;
        }
        let l = self.take_line(self.pos);
        if self.stop {
            return false;
        }
        if l.col > n {
            self.fail(l.content);
            return false;
        }
        if l.col < n {
            return false;
        }
        self.pos = l.content;
        true
    }

    fn map_commit(&mut self, root: bool, entries: &mut Vec<Entry>, out: EntryOut) {
        match entries.iter().position(|e| e.key == out.key) {
            Some(i) => {
                self.err(C_MALFORMED, "duplicate key", out.key_span);
                entries[i].value = out.value;
            }
            None => entries.push(Entry {
                key: out.key.clone(),
                key_span: out.key_span,
                value: out.value,
            }),
        }
        if root {
            match self.starts.iter().position(|(k, _)| *k == out.key) {
                Some(i) => self.starts[i].1 = out.value_start,
                None => self.starts.push((out.key, out.value_start)),
            }
        }
    }

    fn nested_or_null(&mut self, n: usize) -> ConfigValue {
        self.skip_lines();
        if self.stop || self.at_end() {
            return ConfigValue::Null;
        }
        let l = self.take_line(self.pos);
        if self.stop {
            return ConfigValue::Null;
        }
        if l.col > n {
            return self.block_map(l.col, l.content);
        }
        ConfigValue::Null
    }

    fn entry(&mut self, n: usize) -> Option<EntryOut> {
        if self.node_guard() {
            return None;
        }
        let (key, key_span, colon) = self.entry_key()?;
        self.pos = colon + 1;
        self.skip_inline_ws();
        let value_start = self.pos;
        let (value, inline, consumed) = self.entry_value(n)?;
        if self.stop {
            return None;
        }
        if !consumed {
            self.finish_line()?;
        }
        Some(EntryOut {
            key,
            key_span,
            value_start,
            value,
            inline,
        })
    }

    fn entry_value(&mut self, n: usize) -> Option<(ConfigValue, bool, bool)> {
        match self.raw(self.pos) {
            None | Some(b'\r') | Some(b'\n') | Some(b'#') => {
                self.finish_line()?;
                Some((ConfigValue::Null, false, true))
            }
            Some(b'[') => Some((self.flow_seq_value(n), true, false)),
            Some(b'{') => Some((self.flow_map_value(n), true, false)),
            Some(b'"') => {
                let (t, _) = self.quoted_double()?;
                Some((ConfigValue::String(t), true, false))
            }
            Some(b'\'') => {
                let (t, _) = self.quoted_single()?;
                Some((ConfigValue::String(t), true, false))
            }
            Some(b'|') | Some(b'>') => {
                let s = self.block_scalar(n)?;
                Some((ConfigValue::String(s), true, true))
            }
            Some(_) => {
                let v = self.entry_plain_value()?;
                Some((v, true, false))
            }
        }
    }

    fn entry_plain_value(&mut self) -> Option<ConfigValue> {
        if self.node_guard() || self.plain_first_rejected() {
            if !self.stop {
                self.fail(self.pos);
            }
            return None;
        }
        if self.raw(self.pos) == Some(b':') && self.boundary(self.pos + 1) {
            self.fail(self.pos);
            return None;
        }
        let text = self.plain_value_text();
        Some(resolve_plain(&text))
    }

    fn entry_key(&mut self) -> Option<(String, Span, usize)> {
        match self.raw(self.pos) {
            Some(b'"') => {
                let (t, sp) = self.quoted_double()?;
                self.entry_colon(t, sp)
            }
            Some(b'\'') => {
                let (t, sp) = self.quoted_single()?;
                self.entry_colon(t, sp)
            }
            _ => self.plain_key(),
        }
    }

    fn entry_colon(&mut self, t: String, sp: Span) -> Option<(String, Span, usize)> {
        self.skip_inline_ws();
        let cp = self.pos;
        if self.raw(cp) != Some(b':') {
            self.fail(cp);
            return None;
        }
        Some((t, sp, cp))
    }

    fn plain_key(&mut self) -> Option<(String, Span, usize)> {
        let colon = self.plain_key_colon();
        match colon {
            Some(cp) => {
                let from = self.pos;
                let te = trim_end(self.b, from, cp);
                let sp = Span {
                    start: from,
                    end: te,
                };
                let t = self.text(from, te);
                self.pos = cp;
                Some((t, sp, cp))
            }
            None => {
                self.skip_inline_ws();
                self.fail(self.pos);
                None
            }
        }
    }

    fn plain_key_colon(&mut self) -> Option<usize> {
        let from = self.pos;
        let to = self.content_end(from);
        let mut j = from;
        while j < to {
            let c = self.raw(j);
            if c == Some(b':') && self.boundary(j + 1) {
                return Some(j);
            }
            if matches!(c, Some(b' ') | Some(b'\t')) && self.raw(j + 1) == Some(b'#') {
                break;
            }
            j += 1;
        }
        self.pos = j;
        None
    }

    fn plain_value_text(&mut self) -> String {
        let from = self.pos;
        let to = self.content_end(from);
        let mut j = from;
        while j < to {
            let c = self.raw(j);
            if matches!(c, Some(b' ') | Some(b'\t')) && self.raw(j + 1) == Some(b'#') {
                break;
            }
            j += 1;
        }
        self.pos = j;
        let te = trim_end(self.b, from, j);
        self.text(from, te)
    }

    fn finish_line(&mut self) -> Option<()> {
        self.skip_inline_ws();
        let e = self.content_end(self.pos);
        if self.pos < e {
            if self.raw(self.pos) == Some(b'#') {
                self.pos = e;
            } else {
                self.fail(self.pos);
                return None;
            }
        }
        self.pos = e + self.eol(e);
        Some(())
    }

    fn block_scalar(&mut self, n: usize) -> Option<String> {
        let (folded, chomp) = self.block_header()?;
        self.finish_line()?;
        let (leading, parts) = self.block_content(n);
        if self.stop {
            return None;
        }
        Some(assemble_block(folded, chomp, leading, &parts))
    }

    fn block_header(&mut self) -> Option<(bool, u8)> {
        let folded = self.raw(self.pos)? == b'>';
        self.pos += 1;
        let mut chomp = b'c';
        match self.raw(self.pos) {
            Some(c @ (b'-' | b'+')) => {
                chomp = c;
                self.pos += 1;
            }
            Some(c) if c.is_ascii_digit() => {
                self.err(
                    C_MALFORMED,
                    "block scalar indentation indicator is not supported",
                    Span {
                        start: self.pos,
                        end: self.pos + 1,
                    },
                );
                self.stop = true;
                return None;
            }
            _ => {}
        }
        Some((folded, chomp))
    }

    fn block_content(&mut self, n: usize) -> (usize, Vec<Option<Vec<u8>>>) {
        let mut leading = 0usize;
        let mut parts: Vec<Option<Vec<u8>>> = Vec::new();
        let mut m = 0usize;
        let mut m_set = false;
        while !self.stop && self.pos < self.end {
            let l = self.take_line(self.pos);
            if self.stop {
                break;
            }
            if self.line_blank(&l) {
                if m_set {
                    parts.push(None);
                } else {
                    leading += 1;
                }
                self.pos = l.next;
                continue;
            }
            if !m_set {
                if l.col <= n {
                    break;
                }
                m = l.col;
                m_set = true;
            } else if l.col < m {
                break;
            }
            let cs = (l.from + m).min(l.eol_pos);
            parts.push(Some(self.b.get(cs..l.eol_pos).unwrap_or_default().to_vec()));
            self.pos = l.next;
        }
        (leading, parts)
    }

    fn flow_seq_value(&mut self, n: usize) -> ConfigValue {
        let open = self.pos;
        if !self.enter(open) {
            return ConfigValue::Null;
        }
        self.pos = open + 1;
        let v = self.flow_seq(n);
        self.leave();
        v
    }

    fn flow_map_value(&mut self, n: usize) -> ConfigValue {
        let open = self.pos;
        if !self.enter(open) {
            return ConfigValue::Null;
        }
        self.pos = open + 1;
        let v = self.flow_map(n);
        self.leave();
        v
    }

    fn flow_skip_ws(&mut self, n: usize) {
        loop {
            self.skip_inline_ws();
            if !matches!(self.raw(self.pos), Some(b'\r') | Some(b'\n')) {
                return;
            }
            let e = self.content_end(self.pos);
            self.pos = e + self.eol(e);
            if self.stop || self.at_end() {
                return;
            }
            let l = self.take_line(self.pos);
            if self.stop {
                return;
            }
            if l.col <= n {
                self.fail(l.content);
                return;
            }
        }
    }

    fn flow_seq(&mut self, n: usize) -> ConfigValue {
        let mut items = Vec::new();
        self.flow_skip_ws(n);
        if self.stop {
            return ConfigValue::Null;
        }
        if self.cur() == Some(b']') {
            self.pos += 1;
            return ConfigValue::Sequence(items);
        }
        while !self.stop {
            let v = self.flow_item(n);
            if self.stop {
                break;
            }
            items.push(v);
            if self.flow_tail(n, b']') != Step::Next {
                break;
            }
        }
        if self.stop {
            ConfigValue::Null
        } else {
            ConfigValue::Sequence(items)
        }
    }

    fn flow_map(&mut self, n: usize) -> ConfigValue {
        let mut entries: Vec<Entry> = Vec::new();
        self.flow_skip_ws(n);
        if self.stop {
            return ConfigValue::Null;
        }
        if self.cur() == Some(b'}') {
            self.pos += 1;
            return ConfigValue::Mapping(entries);
        }
        while !self.stop && self.flow_pair(n, &mut entries) {}
        if self.stop {
            ConfigValue::Null
        } else {
            ConfigValue::Mapping(entries)
        }
    }

    fn flow_pair(&mut self, n: usize, entries: &mut Vec<Entry>) -> bool {
        if self.node_guard() {
            return false;
        }
        let Some((key, key_span)) = self.flow_key() else {
            return false;
        };
        if self.stop {
            return false;
        }
        self.flow_skip_ws(n);
        if self.stop {
            return false;
        }
        if self.cur() != Some(b':') {
            self.fail(self.pos);
            return false;
        }
        self.pos += 1;
        self.flow_skip_ws(n);
        if self.stop {
            return false;
        }
        let v = self.flow_item(n);
        if self.stop {
            return false;
        }
        match entries.iter().position(|e| e.key == key) {
            Some(i) => {
                self.err(C_MALFORMED, "duplicate key", key_span);
                entries[i].value = v;
            }
            None => entries.push(Entry {
                key,
                key_span,
                value: v,
            }),
        }
        self.flow_tail(n, b'}') == Step::Next
    }

    fn flow_tail(&mut self, n: usize, closer: u8) -> Step {
        if self.stop {
            return Step::Stopped;
        }
        self.flow_skip_ws(n);
        if self.stop {
            return Step::Stopped;
        }
        match self.cur() {
            Some(b',') => self.flow_comma(n, closer),
            Some(c) if c == closer => {
                self.pos += 1;
                Step::Done
            }
            _ => {
                self.fail(self.pos);
                Step::Stopped
            }
        }
    }

    fn flow_comma(&mut self, n: usize, closer: u8) -> Step {
        self.pos += 1;
        self.flow_skip_ws(n);
        if self.stop {
            return Step::Stopped;
        }
        if self.cur() == Some(closer) {
            self.fail(self.pos);
            return Step::Stopped;
        }
        Step::Next
    }

    fn flow_key(&mut self) -> Option<(String, Span)> {
        match self.raw(self.pos) {
            Some(b'"') => self.quoted_double(),
            Some(b'\'') => self.quoted_single(),
            _ => self.plain_flow_text(),
        }
    }

    fn flow_item(&mut self, n: usize) -> ConfigValue {
        if self.node_guard() {
            return ConfigValue::Null;
        }
        match self.raw(self.pos) {
            Some(b'[') => self.flow_seq_value(n),
            Some(b'{') => self.flow_map_value(n),
            Some(b'"') => {
                let q = self.quoted_double();
                self.quoted_string(q)
            }
            Some(b'\'') => {
                let q = self.quoted_single();
                self.quoted_string(q)
            }
            Some(b'#' | b'%' | b'@' | b'`' | b'|' | b'>' | b',' | b']' | b'}') => {
                self.fail(self.pos);
                ConfigValue::Null
            }
            _ => self.plain_flow(),
        }
    }

    fn quoted_string(&mut self, q: Option<(String, Span)>) -> ConfigValue {
        match q {
            Some((t, _)) => ConfigValue::String(t),
            None => ConfigValue::Null,
        }
    }

    fn plain_flow(&mut self) -> ConfigValue {
        match self.plain_flow_text() {
            Some((t, _)) => resolve_plain(&t),
            None => ConfigValue::Null,
        }
    }

    fn plain_flow_text(&mut self) -> Option<(String, Span)> {
        let from = self.pos;
        if self.raw(from) == Some(b':') && self.boundary(from + 1) {
            self.fail(from);
            return None;
        }
        let mut j = from;
        while j < self.end {
            match self.raw(j) {
                Some(b',') | Some(b'[') | Some(b']') | Some(b'{') | Some(b'}') | Some(b':')
                | Some(b'\r') | Some(b'\n') => break,
                Some(b' ') | Some(b'\t') => {
                    if self.raw(j + 1) == Some(b'#') {
                        break;
                    }
                    j += 1;
                }
                _ => j += 1,
            }
        }
        let te = trim_end(self.b, from, j);
        self.pos = j;
        Some((
            self.text(from, te),
            Span {
                start: from,
                end: te,
            },
        ))
    }

    fn quoted_single(&mut self) -> Option<(String, Span)> {
        self.quoted_core(true, false)
    }

    fn quoted_double(&mut self) -> Option<(String, Span)> {
        self.quoted_core(false, false)
    }

    fn json_string(&mut self) -> Option<(String, Span)> {
        self.quoted_core(false, true)
    }

    fn quoted_core(&mut self, single: bool, json: bool) -> Option<(String, Span)> {
        let open = self.pos;
        let qc = if json { b'"' } else { self.raw(open)? };
        self.pos = open + 1;
        let mut out: Vec<u8> = Vec::new();
        loop {
            if self.at_end() {
                self.fail(self.end);
                return None;
            }
            let c = self.raw(self.pos).unwrap_or(0);
            if c == b'\r' || c == b'\n' || c <= 0x1F {
                self.fail(self.pos);
                return None;
            }
            let step = if single {
                self.single_step(&mut out, c)
            } else {
                self.double_step(&mut out, c, qc, json)
            };
            match step {
                Step::Next => {}
                Step::Done => break,
                Step::Stopped => return None,
            }
        }
        let s = match String::from_utf8(out) {
            Ok(s) => s,
            Err(e) => String::from_utf8_lossy(e.as_bytes()).into_owned(),
        };
        Some((
            s,
            Span {
                start: open,
                end: self.pos,
            },
        ))
    }

    fn single_step(&mut self, out: &mut Vec<u8>, c: u8) -> Step {
        if c != b'\'' {
            out.push(c);
            self.pos += 1;
            return Step::Next;
        }
        if self.raw(self.pos + 1) == Some(b'\'') {
            out.push(b'\'');
            self.pos += 2;
            return Step::Next;
        }
        self.pos += 1;
        Step::Done
    }

    fn double_step(&mut self, out: &mut Vec<u8>, c: u8, qc: u8, json: bool) -> Step {
        if c == b'\\' {
            return if self.escape(out, json) {
                Step::Next
            } else {
                Step::Stopped
            };
        }
        let eff = if self.json && c == b'\'' { b'"' } else { c };
        if eff == qc {
            self.pos += 1;
            return Step::Done;
        }
        out.push(c);
        self.pos += 1;
        Step::Next
    }

    fn escape(&mut self, out: &mut Vec<u8>, json: bool) -> bool {
        let bs = self.pos;
        let nx = self.at(bs + 1);
        if let Some((byte, len)) = simple_escape(nx) {
            out.push(byte);
            self.pos += len;
            return true;
        }
        if nx == Some(b'u') {
            return self.unicode_escape(out, json);
        }
        self.err(
            C_MALFORMED,
            "invalid escape",
            Span {
                start: bs,
                end: (bs + 2).min(self.end),
            },
        );
        self.stop = true;
        false
    }

    fn unicode_escape(&mut self, out: &mut Vec<u8>, json: bool) -> bool {
        let bs = self.pos;
        let h0 = bs + 2;
        let Some(val) = self.hex_value(h0) else {
            self.err(
                C_MALFORMED,
                "invalid escape",
                Span {
                    start: bs,
                    end: (bs + 2).min(self.end),
                },
            );
            self.stop = true;
            return false;
        };
        let six = Span {
            start: bs,
            end: (bs + 6).min(self.end),
        };
        if json && (0xD800..=0xDBFF).contains(&val) {
            return self.surrogate_pair(out, val, h0, six);
        }
        if (0xD800..=0xDFFF).contains(&val) {
            self.err(C_MALFORMED, "invalid unicode escape", six);
            self.stop = true;
            return false;
        }
        push_char(out, val);
        self.pos = h0 + 4;
        true
    }

    fn surrogate_pair(&mut self, out: &mut Vec<u8>, hi: u32, h0: usize, six: Span) -> bool {
        match self.surrogate_low(h0 + 4) {
            Some(lv) => {
                push_char(out, 0x10000 + ((hi - 0xD800) << 10) + (lv - 0xDC00));
                self.pos = h0 + 10;
                true
            }
            None => {
                self.err(C_MALFORMED, "invalid unicode escape", six);
                self.stop = true;
                false
            }
        }
    }

    fn hex_value(&self, at: usize) -> Option<u32> {
        let mut v = 0u32;
        for k in 0..4 {
            v = v
                .wrapping_mul(16)
                .wrapping_add(self.raw(at + k).and_then(hex_digit)?);
        }
        Some(v)
    }

    fn surrogate_low(&self, p: usize) -> Option<u32> {
        if self.raw(p) != Some(b'\\') || self.at(p + 1) != Some(b'u') {
            return None;
        }
        let v = self.hex_value(p + 2)?;
        (0xDC00..=0xDFFF).contains(&v).then_some(v)
    }

    fn json_run(&mut self) -> ConfigValue {
        self.json_ws();
        if self.at_end() {
            self.fail(self.pos);
            return ConfigValue::Null;
        }
        let v = if self.cur() == Some(b'{') {
            self.json_object()
        } else {
            self.fail(self.pos);
            ConfigValue::Null
        };
        if !self.stop {
            self.json_ws();
            if !self.at_end() {
                self.fail(self.pos);
            }
        }
        if self.stop { ConfigValue::Null } else { v }
    }

    fn json_ws(&mut self) {
        while matches!(
            self.cur(),
            Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
        ) {
            self.pos += 1;
        }
    }

    fn json_object(&mut self) -> ConfigValue {
        let open = self.pos;
        if !self.enter(open) {
            return ConfigValue::Null;
        }
        self.pos += 1;
        let mut entries: Vec<Entry> = Vec::new();
        while !self.stop {
            self.json_ws();
            if self.stop {
                break;
            }
            if self.cur() == Some(b'}') {
                self.pos += 1;
                break;
            }
            if !self.json_pair(&mut entries) {
                break;
            }
        }
        let v = if self.stop {
            ConfigValue::Null
        } else {
            ConfigValue::Mapping(entries)
        };
        self.leave();
        v
    }

    fn json_pair(&mut self, entries: &mut Vec<Entry>) -> bool {
        let Some((key, key_span)) = self.json_key() else {
            return false;
        };
        if self.stop {
            return false;
        }
        self.json_ws();
        if self.stop {
            return false;
        }
        if self.cur() != Some(b':') {
            self.fail(self.pos);
            return false;
        }
        self.pos += 1;
        self.json_ws();
        if self.stop {
            return false;
        }
        let v = self.json_value();
        if self.stop {
            return false;
        }
        match entries.iter().position(|e| e.key == key) {
            Some(i) => {
                self.err(C_MALFORMED, "duplicate key", key_span);
                entries[i].value = v;
            }
            None => entries.push(Entry {
                key,
                key_span,
                value: v,
            }),
        }
        self.json_tail(b'}') == Step::Next
    }

    fn json_tail(&mut self, closer: u8) -> Step {
        if self.stop {
            return Step::Stopped;
        }
        self.json_ws();
        if self.stop {
            return Step::Stopped;
        }
        match self.cur() {
            Some(b',') => {
                self.pos += 1;
                self.json_ws();
                if self.stop {
                    return Step::Stopped;
                }
                if self.cur() == Some(closer) {
                    self.fail(self.pos);
                    return Step::Stopped;
                }
                Step::Next
            }
            Some(c) if c == closer => {
                self.pos += 1;
                Step::Done
            }
            _ => {
                self.fail(self.pos);
                Step::Stopped
            }
        }
    }

    fn json_key(&mut self) -> Option<(String, Span)> {
        if self.cur() != Some(b'"') {
            self.fail(self.pos);
            return None;
        }
        self.json_string()
    }

    fn json_array(&mut self) -> ConfigValue {
        let open = self.pos;
        if !self.enter(open) {
            return ConfigValue::Null;
        }
        self.pos += 1;
        let mut items = Vec::new();
        while !self.stop {
            self.json_ws();
            if self.stop {
                break;
            }
            if self.cur() == Some(b']') {
                self.pos += 1;
                break;
            }
            let v = self.json_value();
            if self.stop {
                break;
            }
            items.push(v);
            if self.json_tail(b']') != Step::Next {
                break;
            }
        }
        let v = if self.stop {
            ConfigValue::Null
        } else {
            ConfigValue::Sequence(items)
        };
        self.leave();
        v
    }

    fn json_value(&mut self) -> ConfigValue {
        match self.cur() {
            Some(b'{') => self.json_object(),
            Some(b'[') => self.json_array(),
            Some(b'"') => {
                let q = self.json_string();
                self.quoted_string(q)
            }
            Some(b't') => self.json_literal("true", ConfigValue::Bool(true)),
            Some(b'f') => self.json_literal("false", ConfigValue::Bool(false)),
            Some(b'n') => self.json_literal("null", ConfigValue::Null),
            Some(b'-') => self.json_number(),
            Some(c) if c.is_ascii_digit() => self.json_number(),
            _ => {
                self.fail(self.pos);
                ConfigValue::Null
            }
        }
    }

    fn json_literal(&mut self, word: &str, v: ConfigValue) -> ConfigValue {
        for (k, wc) in word.as_bytes().iter().enumerate() {
            match self.at(self.pos + k) {
                Some(c) if c == *wc => {}
                _ => {
                    self.fail(self.pos + k);
                    return ConfigValue::Null;
                }
            }
        }
        self.pos += word.len();
        v
    }

    fn json_number(&mut self) -> ConfigValue {
        let from = self.pos;
        if self.cur() == Some(b'-') {
            self.pos += 1;
        }
        if !self.digit_cur() {
            self.fail(self.pos);
            return ConfigValue::Null;
        }
        let mut integer = true;
        self.json_digits();
        if self.cur() == Some(b'.') {
            self.pos += 1;
            if !self.digit_cur() {
                self.fail(self.pos);
                return ConfigValue::Null;
            }
            self.json_digits();
            integer = false;
        }
        if matches!(self.cur(), Some(b'e') | Some(b'E')) {
            self.pos += 1;
            if matches!(self.cur(), Some(b'+') | Some(b'-')) {
                self.pos += 1;
            }
            if !self.digit_cur() {
                self.fail(self.pos);
                return ConfigValue::Null;
            }
            self.json_digits();
            integer = false;
        }
        let t = self.text(from, self.pos);
        if integer {
            ConfigValue::Integer(t)
        } else {
            ConfigValue::Decimal(t)
        }
    }

    fn json_digits(&mut self) {
        while self.digit_cur() {
            self.pos += 1;
        }
    }

    fn digit_cur(&self) -> bool {
        matches!(self.cur(), Some(c) if c.is_ascii_digit())
    }
}

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

fn resolve_plain(text: &str) -> ConfigValue {
    match text {
        "" | "null" | "Null" | "NULL" | "~" => ConfigValue::Null,
        "true" | "True" | "TRUE" => ConfigValue::Bool(true),
        "false" | "False" | "FALSE" => ConfigValue::Bool(false),
        _ => {
            let b = text.as_bytes();
            let ds = match b.first() {
                Some(b'+') | Some(b'-') => 1,
                _ => 0,
            };
            if all_digits(&b[ds..]) {
                return ConfigValue::Integer(text.to_string());
            }
            if decimal_shape(b) {
                return ConfigValue::Decimal(text.to_string());
            }
            ConfigValue::String(text.to_string())
        }
    }
}

fn all_digits(b: &[u8]) -> bool {
    !b.is_empty() && b.iter().all(|c| c.is_ascii_digit())
}

fn decimal_shape(b: &[u8]) -> bool {
    let Some(dot) = b.iter().position(|c| *c == b'.') else {
        return false;
    };
    let mut head = &b[..dot];
    if matches!(head.first(), Some(b'+') | Some(b'-')) {
        head = &head[1..];
    }
    all_digits(head) && all_digits(&b[dot + 1..])
}

fn add_one(s: &str) -> String {
    let mut out = s.as_bytes().to_vec();
    let mut i = out.len();
    while i > 0 {
        i -= 1;
        if out[i] == b'9' {
            out[i] = b'0';
        } else {
            out[i] += 1;
            return String::from_utf8(out).unwrap_or_else(|_| s.to_string());
        }
    }
    let mut r = String::from("1");
    r.push_str(&String::from_utf8(out).unwrap_or_default());
    r
}

fn parse_exp_clamped(digits: &str, neg: bool) -> i64 {
    let mut v = 0i64;
    for c in digits.bytes() {
        v = v.saturating_mul(10).saturating_add(i64::from(c - b'0'));
    }
    let lim = 999999999i64;
    if v > lim {
        v = lim;
    }
    if neg { -v } else { v }
}

fn scan_sign(b: &[u8], i: &mut usize) -> bool {
    match b.first() {
        Some(b'-') => {
            *i = 1;
            true
        }
        Some(b'+') => {
            *i = 1;
            false
        }
        _ => false,
    }
}

fn scan_digits<'a>(b: &'a [u8], i: &mut usize) -> &'a [u8] {
    let s = *i;
    while matches!(b.get(*i), Some(c) if c.is_ascii_digit()) {
        *i += 1;
    }
    &b[s..*i]
}

fn scan_frac<'a>(b: &'a [u8], i: &mut usize) -> Option<&'a [u8]> {
    if b.get(*i) != Some(&b'.') {
        return Some(&[]);
    }
    *i += 1;
    let f = scan_digits(b, i);
    if f.is_empty() { None } else { Some(f) }
}

fn scan_exp(b: &[u8], i: &mut usize) -> Option<i64> {
    if !matches!(b.get(*i), Some(b'e') | Some(b'E')) {
        return Some(0);
    }
    *i += 1;
    let neg = match b.get(*i) {
        Some(b'-') => {
            *i += 1;
            true
        }
        Some(b'+') => {
            *i += 1;
            false
        }
        _ => false,
    };
    let d = scan_digits(b, i);
    if d.is_empty() {
        return None;
    }
    let Ok(s) = std::str::from_utf8(d) else {
        return None;
    };
    Some(parse_exp_clamped(s, neg))
}

fn thousandths_text(text: &str) -> Option<i32> {
    let b = text.as_bytes();
    let mut i = 0usize;
    let neg = scan_sign(b, &mut i);
    let int = scan_digits(b, &mut i);
    let frac = scan_frac(b, &mut i)?;
    let exp = scan_exp(b, &mut i)?;
    if i != b.len() {
        return None;
    }
    finish_thousandths(int, frac, exp, neg)
}

fn finish_thousandths(int_digits: &[u8], frac_digits: &[u8], exp: i64, neg: bool) -> Option<i32> {
    let mut raw = Vec::with_capacity(int_digits.len() + frac_digits.len());
    raw.extend_from_slice(int_digits);
    raw.extend_from_slice(frac_digits);
    let Ok(dtext) = String::from_utf8(raw) else {
        return None;
    };
    let trimmed = dtext.trim_start_matches('0');
    let d = if trimmed.is_empty() { "0" } else { trimmed };
    let t = mantissa_thousandths(d, exp, i64::try_from(frac_digits.len()).unwrap_or(i64::MAX))?;
    let Ok(tv) = t.parse::<u64>() else {
        return None;
    };
    if tv > 2147483647 {
        return None;
    }
    let Ok(mag) = i64::try_from(tv) else {
        return None;
    };
    let signed = if neg { -mag } else { mag };
    i32::try_from(signed).ok()
}

fn mantissa_thousandths(d: &str, exp: i64, k: i64) -> Option<String> {
    if d == "0" {
        return Some(String::from("0"));
    }
    let p = exp - k + 3;
    if p > 10 {
        return None;
    }
    if p >= 0 {
        let mut t = String::from(d);
        for _ in 0..p {
            t.push('0');
        }
        return Some(t);
    }
    let r = usize::try_from(-p).unwrap_or(usize::MAX);
    let len = d.len();
    if len < r {
        return Some(String::from("0"));
    }
    let keep = &d[..len - r];
    let mut t = if keep.is_empty() {
        String::from("0")
    } else {
        String::from(keep)
    };
    if d.as_bytes()[len - r] >= b'5' {
        t = add_one(&t);
    }
    Some(t)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(ds: &[Diagnostic], code: &str, msg: &str, span: Span) {
        let [d] = ds else { unreachable!() };
        assert_eq!(d.code, code);
        assert_eq!(d.message, msg);
        assert_eq!(d.span, span);
        assert_eq!(d.severity, Severity::Error);
        assert!(d.help.is_empty());
        assert!(d.fixes.is_empty());
        assert!(d.related.is_empty());
    }

    fn mapping(v: ConfigValue) -> Vec<Entry> {
        let ConfigValue::Mapping(m) = v else {
            unreachable!()
        };
        m
    }

    fn sequence(v: ConfigValue) -> Vec<ConfigValue> {
        let ConfigValue::Sequence(s) = v else {
            unreachable!()
        };
        s
    }

    fn text(v: ConfigValue) -> String {
        let ConfigValue::String(s) = v else {
            unreachable!()
        };
        s
    }

    fn int_text(v: &ConfigValue) -> &str {
        let ConfigValue::Integer(t) = v else {
            unreachable!()
        };
        t
    }

    fn dec_text(v: &ConfigValue) -> &str {
        let ConfigValue::Decimal(t) = v else {
            unreachable!()
        };
        t
    }

    fn parse_top(src: &str) -> ConfigValue {
        let (v, ds) = parse_config_yaml(src, 0, src.len());
        assert!(ds.is_empty(), "diags {ds:?} src {src:?}");
        v
    }

    fn entry_of<'a>(m: &'a [Entry], key: &str) -> &'a Entry {
        let Some(e) = m.iter().find(|e| e.key == key) else {
            unreachable!()
        };
        e
    }

    fn entry_value(src: &str, key: &str) -> ConfigValue {
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

    fn random_case(i: u32) -> String {
        let mut g = Xs(i.wrapping_add(1));
        let len = 1 + g.below(40);
        let mut s = String::new();
        for _ in 0..len {
            let idx = g.below(25) as usize;
            let Some(c) = ALPHABET.get(idx) else {
                unreachable!()
            };
            s.push(*c);
        }
        s
    }

    fn in_bounds(s: &str, sp: Span) -> bool {
        sp.start <= sp.end
            && sp.end <= s.len()
            && s.is_char_boundary(sp.start)
            && s.is_char_boundary(sp.end)
    }

    #[test]
    fn tab_in_indentation_span() {
        let src = "a: 1\n\tb: 2\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "tab in indentation",
            Span { start: 5, end: 6 },
        );
    }

    #[test]
    fn block_sequence_span() {
        let (_, ds) = parse_config_yaml("- x\n", 0, 4);
        check(
            &ds,
            C_MALFORMED,
            "block sequences are not supported",
            Span { start: 0, end: 1 },
        );
    }

    #[test]
    fn complex_key_span() {
        let (_, ds) = parse_config_yaml("? x\n", 0, 4);
        check(
            &ds,
            C_MALFORMED,
            "complex keys are not supported",
            Span { start: 0, end: 1 },
        );
    }

    #[test]
    fn multi_document_marker_span() {
        let src = "---\na: 1\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "multi-document streams are not supported",
            Span { start: 0, end: 3 },
        );
        let src = "...\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "multi-document streams are not supported",
            Span { start: 0, end: 3 },
        );
    }

    #[test]
    fn block_header_digit_span() {
        let src = "a: |2\n  x\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "block scalar indentation indicator is not supported",
            Span { start: 4, end: 5 },
        );
    }

    #[test]
    fn invalid_escape_span() {
        let src = "a: \"x\\q\"\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "invalid escape",
            Span { start: 5, end: 7 },
        );
    }

    #[test]
    fn yaml_surrogate_escape_span() {
        let src = "a: \"\\uD800\"\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "invalid unicode escape",
            Span { start: 4, end: 10 },
        );
    }

    #[test]
    fn json_surrogate_pair_forms_one_char() {
        let src = "{\"a\": \"\\uD83D\\uDE00\"}";
        let (v, ds) = parse_config_json(src, 0, src.len());
        assert!(ds.is_empty());
        let m = mapping(v);
        let [e] = m.as_slice() else { unreachable!() };
        assert_eq!(e.key, "a");
        assert_eq!(text(e.value.clone()), "\u{1F600}");
    }

    #[test]
    fn json_surrogate_failures() {
        let src = "{\"a\": \"\\uDC00\"}";
        let (_, ds) = parse_config_json(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "invalid unicode escape",
            Span { start: 7, end: 13 },
        );
        let src = "{\"a\": \"\\uD800x\"}";
        let (_, ds) = parse_config_json(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "invalid unicode escape",
            Span { start: 7, end: 13 },
        );
    }

    #[test]
    fn duplicate_key_later_wins_at_first_position() {
        let src = "a: 1\nb: 2\na: 3\n";
        let (v, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "duplicate key",
            Span { start: 10, end: 11 },
        );
        let m = mapping(v);
        let [a, b] = m.as_slice() else { unreachable!() };
        assert_eq!(a.key, "a");
        assert_eq!(a.key_span, Span { start: 0, end: 1 });
        assert_eq!(int_text(&a.value), "3");
        assert_eq!(b.key, "b");
        assert_eq!(int_text(&b.value), "2");
    }

    #[test]
    fn json_duplicate_key_follows_same_rule() {
        let src = "{\"a\": 1, \"a\": 2}";
        let (v, ds) = parse_config_json(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "duplicate key",
            Span { start: 9, end: 12 },
        );
        let m = mapping(v);
        let [a] = m.as_slice() else { unreachable!() };
        assert_eq!(int_text(&a.value), "2");
    }

    #[test]
    fn malformed_config_value_token_spans() {
        let cases = [
            ("a: @x\n", 3, 5),
            ("a: [1,]\n", 6, 7),
            ("a: {b 1}\n", 7, 8),
            ("a: \"xy\n", 6, 7),
            ("a: [1 #x]\n", 6, 9),
            ("a: 1\n    b: 2\n", 9, 11),
            ("a: [\n1]\n", 5, 7),
        ];
        for (src, start, end) in cases {
            let (_, ds) = parse_config_yaml(src, 0, src.len());
            check(
                &ds,
                C_MALFORMED,
                "malformed config value",
                Span { start, end },
            );
        }
    }

    #[test]
    fn anchor_and_tag_spans() {
        let src = "a: &x 1\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            "config/unsupported-anchor",
            "anchors and aliases are not supported",
            Span { start: 3, end: 5 },
        );
        let src = "a: !x 1\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            "config/unsupported-tag",
            "tags are not supported",
            Span { start: 3, end: 5 },
        );
        let src = "a: *y\n";
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            "config/unsupported-anchor",
            "anchors and aliases are not supported",
            Span { start: 3, end: 5 },
        );
    }

    #[test]
    fn nesting_depth_at_level_65() {
        let src = format!("k: {}", "[".repeat(65));
        let (_, ds) = parse_config_yaml(&src, 0, src.len());
        check(
            &ds,
            "limit/nesting-depth",
            "nesting depth exceeds 64",
            Span { start: 66, end: 67 },
        );
    }

    #[test]
    fn json_grammar_failures() {
        let src = "{a: 1}";
        let (_, ds) = parse_config_json(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "malformed config value",
            Span { start: 1, end: 3 },
        );

        let src = "{} x";
        let (_, ds) = parse_config_json(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "malformed config value",
            Span { start: 3, end: 4 },
        );

        let src = "{\"a\": \"x'y\"}";
        let (_, ds) = parse_config_json(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "malformed config value",
            Span { start: 9, end: 12 },
        );
    }

    #[test]
    fn plain_scalar_resolution_order() {
        assert_eq!(entry_value("k: null\n", "k"), ConfigValue::Null);
        assert_eq!(entry_value("k: ~\n", "k"), ConfigValue::Null);
        assert_eq!(entry_value("k: True\n", "k"), ConfigValue::Bool(true));
        assert_eq!(entry_value("k: FALSE\n", "k"), ConfigValue::Bool(false));
        assert_eq!(int_text(&entry_value("k: 007\n", "k")), "007");
        assert_eq!(int_text(&entry_value("k: +3\n", "k")), "+3");
        assert_eq!(dec_text(&entry_value("k: 1.25\n", "k")), "1.25");
        assert_eq!(
            entry_value("k: .inf\n", "k"),
            ConfigValue::String(String::from(".inf"))
        );
        assert_eq!(
            entry_value("k: 0x1F\n", "k"),
            ConfigValue::String(String::from("0x1F"))
        );
        assert_eq!(
            entry_value("k: hello world\n", "k"),
            ConfigValue::String(String::from("hello world"))
        );
    }

    #[test]
    fn quoted_scalars_decode() {
        assert_eq!(text(entry_value("a: 'it''s'\n", "a")), "it's");
        assert_eq!(text(entry_value("a: \"n\\tt\\u0041\"\n", "a")), "n\ttA");
        assert_eq!(text(entry_value("a: \"\"\n", "a")), "");
        let (_, ds) = parse_config_yaml("a: 'x\\y'\n", 0, 9);
        assert!(ds.is_empty());
    }

    #[test]
    fn flow_collections() {
        let s = sequence(entry_value("a: [1, \"x y\", {b: 2}]\n", "a"));
        assert_eq!(s.len(), 3);
        assert_eq!(int_text(&s[0]), "1");
        assert_eq!(text(s[1].clone()), "x y");
        let m = mapping(s[2].clone());
        let [b] = m.as_slice() else { unreachable!() };
        assert_eq!(b.key, "b");
        assert_eq!(int_text(&b.value), "2");

        assert!(sequence(entry_value("a: []\n", "a")).is_empty());
        assert!(mapping(entry_value("a: {}\n", "a")).is_empty());

        let s = sequence(entry_value("a: [\n  1,\n  2]\n", "a"));
        assert_eq!(s.len(), 2);
        assert_eq!(int_text(&s[1]), "2");

        let (_, ds) = parse_config_yaml("k: # note\nz: 1\n", 0, 15);
        assert!(ds.is_empty());
    }

    #[test]
    fn nested_maps() {
        let m = mapping(entry_value("a:\n  b: 1\n  c: 2\nd: x\n", "a"));
        let [b, c] = m.as_slice() else { unreachable!() };
        assert_eq!(b.key, "b");
        assert_eq!(int_text(&b.value), "1");
        assert_eq!(c.key, "c");
        assert_eq!(int_text(&c.value), "2");

        assert_eq!(mapping(parse_top("  a: 1\n  b: 2\n")).len(), 2);
        assert_eq!(text(entry_value("a:\n  b: 1\nd: x\n", "d")), "x");
    }

    #[test]
    fn roots_allow_scalar_flow_and_map() {
        let (v, ds) = parse_config_yaml("hello world\n", 0, 12);
        assert!(ds.is_empty());
        assert_eq!(v, ConfigValue::String(String::from("hello world")));
        let (v, ds) = parse_config_yaml("[1, 2]\n", 0, 7);
        assert!(ds.is_empty());
        assert_eq!(sequence(v).len(), 2);
        let (v, ds) = parse_config_yaml("\"abc\"\n", 0, 6);
        assert!(ds.is_empty());
        assert_eq!(v, ConfigValue::String(String::from("abc")));
        let (v, ds) = parse_config_yaml("true\n", 0, 5);
        assert!(ds.is_empty());
        assert_eq!(v, ConfigValue::Bool(true));
        let (v, ds) = parse_config_yaml("abc", 2, 2);
        assert!(ds.is_empty());
        assert_eq!(v, ConfigValue::Null);
        let (_, ds) = parse_config_yaml("hello # c\n", 0, 10);
        assert!(ds.is_empty());
    }

    fn block_value(src: &str) -> String {
        text(entry_value(src, "a"))
    }

    #[test]
    fn literal_block_chomping() {
        assert_eq!(block_value("a: |\n  x\n  y\nz: 1\n"), "x\ny\n");
        assert_eq!(block_value("a: |-\n  x\n  y\n"), "x\ny");
        assert_eq!(block_value("a: |+\n  x\n\n\nz: 1\n"), "x\n\n\n");
        assert_eq!(block_value("a: |\n\n  x\n"), "\nx\n");
        assert_eq!(block_value("a: |+\n\n\nz: 1\n"), "\n\n");
        assert_eq!(block_value("a: |-\n\n\nz: 1\n"), "");
        assert_eq!(block_value("a: |\n  x\n\n  y\n"), "x\n\ny\n");
    }

    #[test]
    fn folded_block_chomping() {
        assert_eq!(block_value("a: >\n  x\n  y\n"), "x y\n");
        assert_eq!(block_value("a: >\n  x\n\n  y\n"), "x\ny\n");
        assert_eq!(block_value("a: >\n  x\n   z\n  y\n"), "x\n z\ny\n");
        assert_eq!(block_value("a: >-\n  x\n  y\n"), "x y");
    }

    #[test]
    fn thousandths_examples() {
        let cases = [
            ("0.75", Some(750)),
            ("0.0005", Some(1)),
            ("1", Some(1000)),
            ("2.5", Some(2500)),
            ("-1.5", Some(-1500)),
            ("0", Some(0)),
            ("-0", Some(0)),
            ("0.0004", Some(0)),
            ("-0.0005", Some(-1)),
            ("9999999999999", None),
            ("2147483", Some(2147483000)),
            ("2147484", None),
            ("0.0075", Some(8)),
            ("1e3", Some(1000000)),
        ];
        for (t, want) in cases {
            let v = if t.contains('.') {
                ConfigValue::Decimal(String::from(t))
            } else {
                ConfigValue::Integer(String::from(t))
            };
            assert_eq!(thousandths(&v), want, "value {t}");
        }
        assert_eq!(thousandths(&ConfigValue::Null), None);
        assert_eq!(thousandths(&ConfigValue::Bool(true)), None);
        assert_eq!(thousandths(&ConfigValue::String(String::from("1"))), None);
    }

    #[test]
    fn json_numbers_and_rewrite() {
        let src = "{\"a\": 1, \"b\": 2.5, \"c\": -3, \"d\": 1e2}";
        let (v, ds) = parse_config_json(src, 0, src.len());
        assert!(ds.is_empty());
        let m = mapping(v);
        let [a, b, c, d] = m.as_slice() else {
            unreachable!()
        };
        assert_eq!(int_text(&a.value), "1");
        assert_eq!(dec_text(&b.value), "2.5");
        assert_eq!(int_text(&c.value), "-3");
        assert_eq!(dec_text(&d.value), "1e2");

        let src = "{'theme': 'dark'}";
        let (v, ds) = parse_config_json(src, 0, src.len());
        assert!(ds.is_empty());
        let m = mapping(v);
        let [t] = m.as_slice() else { unreachable!() };
        assert_eq!(t.key, "theme");
        assert_eq!(text(t.value.clone()), "dark");
    }

    #[test]
    fn range_clamps_and_empty_range() {
        let (v, ds) = parse_config_yaml("a: 1", 0, 100);
        assert!(ds.is_empty());
        assert_eq!(int_text(&entry_of(&mapping(v), "a").value), "1");
        let (v, ds) = parse_config_yaml("abc", 2, 2);
        assert!(ds.is_empty());
        assert_eq!(v, ConfigValue::Null);
        let (v, ds) = parse_config_json("", 0, 0);
        assert!(!ds.is_empty());
        assert_eq!(v, ConfigValue::Null);
    }

    #[test]
    fn random_spans_stay_in_range() {
        for i in 0u32..2000 {
            let s = random_case(i);
            let (v, ds) = parse_config_yaml(&s, 0, s.len());
            let _ = v;
            for d in &ds {
                assert!(
                    in_bounds(&s, d.span),
                    "yaml case {i} span {:?} src {s:?}",
                    d.span
                );
            }
            let (jv, jd) = parse_config_json(&s, 0, s.len());
            let _ = jv;
            for d in &jd {
                assert!(
                    in_bounds(&s, d.span),
                    "json case {i} span {:?} src {s:?}",
                    d.span
                );
            }
        }
    }
}
