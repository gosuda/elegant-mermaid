use super::*;

impl<'a> Cfg<'a> {
    pub(super) fn block_map(&mut self, n: usize, open: usize) -> ConfigValue {
        if !self.enter(open) {
            return ConfigValue::Null;
        }
        let root = self.depth == 1;
        let mut entries: Vec<Entry> = Vec::new();
        let mut first = true;
        while !self.stop {
            if first {
                if self.pos == self.line_start(self.pos) {
                    let l = self.take_line(self.pos);
                    if self.stop {
                        break;
                    }
                    self.pos = l.content;
                }
                first = false;
            } else if !self.map_advance(n) {
                break;
            }
            let Some(mut out) = self.entry(n) else {
                break;
            };
            if !out.inline {
                let (value, start) = self.nested_or_null(n);
                out.value = value;
                if let Some(start) = start {
                    out.value_start = start;
                }
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

    pub(super) fn map_advance(&mut self, n: usize) -> bool {
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

    pub(super) fn map_commit(&mut self, root: bool, entries: &mut Vec<Entry>, out: EntryOut) {
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

    pub(super) fn nested_or_null(&mut self, n: usize) -> (ConfigValue, Option<usize>) {
        self.skip_lines();
        if self.stop || self.at_end() {
            return (ConfigValue::Null, None);
        }
        let l = self.take_line(self.pos);
        if self.stop {
            return (ConfigValue::Null, None);
        }
        if l.col > n {
            self.pos = l.content;
            let start = l.content;
            if self.block_scalar_start() {
                let value = match self.block_scalar(n) {
                    Some(text) => ConfigValue::String(text),
                    None => ConfigValue::Null,
                };
                return (value, Some(start));
            }
            return (self.node_value(l.col, n, n + 1), Some(start));
        }
        (ConfigValue::Null, None)
    }

    pub(super) fn entry(&mut self, n: usize) -> Option<EntryOut> {
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

    pub(super) fn entry_value(&mut self, n: usize) -> Option<(ConfigValue, bool, bool)> {
        self.yaml_continuation_col = Some(n + 1);
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

    pub(super) fn entry_plain_value(&mut self) -> Option<ConfigValue> {
        if self.node_guard() || self.plain_first_rejected() {
            if !self.stop {
                self.fail(self.pos);
            }
            return None;
        }
        if self.raw(self.pos) == Some(b':') && self.map_boundary(self.pos + 1) {
            self.fail(self.pos);
            return None;
        }
        let text = self.plain_value_text();
        Some(resolve_plain(&text))
    }

    pub(super) fn entry_key(&mut self) -> Option<(String, Span, usize)> {
        if self.raw(self.pos) == Some(b':') && self.map_boundary(self.pos + 1) {
            self.fail(self.pos);
            return None;
        }
        match self.raw(self.pos) {
            Some(b'"') => {
                self.yaml_continuation_col = None;
                let (t, sp) = self.quoted_double()?;
                self.entry_colon(t, sp)
            }
            Some(b'\'') => {
                self.yaml_continuation_col = None;
                let (t, sp) = self.quoted_single()?;
                self.entry_colon(t, sp)
            }
            _ => {
                if self.plain_first_rejected() {
                    self.fail(self.pos);
                    return None;
                }
                self.plain_key()
            }
        }
    }

    pub(super) fn entry_colon(&mut self, t: String, sp: Span) -> Option<(String, Span, usize)> {
        self.skip_inline_ws();
        let cp = self.pos;
        if self.raw(cp) != Some(b':') || !self.map_boundary(cp + 1) {
            self.fail(cp);
            return None;
        }
        Some((t, sp, cp))
    }

    pub(super) fn plain_key(&mut self) -> Option<(String, Span, usize)> {
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
                self.fail(self.content_end(self.pos));
                None
            }
        }
    }

    pub(super) fn plain_key_colon(&self) -> Option<usize> {
        let from = self.pos;
        let to = self.content_end(from);
        let mut j = from;
        while j < to {
            let c = self.raw(j);
            if c == Some(b':') && self.map_boundary(j + 1) {
                return Some(j);
            }
            if matches!(c, Some(b' ') | Some(b'\t')) && self.raw(j + 1) == Some(b'#') {
                break;
            }
            j += 1;
        }
        None
    }
}
