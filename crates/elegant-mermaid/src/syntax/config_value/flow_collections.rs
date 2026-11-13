use super::*;

impl<'a> Cfg<'a> {
    pub(super) fn flow_seq_value(&mut self, n: usize) -> ConfigValue {
        let open = self.pos;
        if !self.enter(open) {
            return ConfigValue::Null;
        }
        self.pos = open + 1;
        let v = self.flow_seq(n);
        self.leave();
        v
    }

    pub(super) fn flow_map_value(&mut self, n: usize) -> ConfigValue {
        let open = self.pos;
        if !self.enter(open) {
            return ConfigValue::Null;
        }
        self.pos = open + 1;
        let v = self.flow_map(n);
        self.leave();
        v
    }

    pub(super) fn flow_skip_ws(&mut self, n: usize) {
        self.skip_inline_ws();
        if !matches!(self.raw(self.pos), Some(b'\r') | Some(b'\n')) {
            return;
        }
        let e = self.content_end(self.pos);
        self.pos = e + self.eol(e);
        while !self.stop && !self.at_end() {
            let l = self.take_line(self.pos);
            if self.stop {
                return;
            }
            if !self.line_blank(&l) {
                if l.col <= n {
                    self.fail(l.content);
                } else {
                    self.pos = l.content;
                }
                return;
            }
            self.pos = l.next;
        }
    }

    pub(super) fn flow_seq(&mut self, n: usize) -> ConfigValue {
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

    pub(super) fn flow_map(&mut self, n: usize) -> ConfigValue {
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

    pub(super) fn flow_pair(&mut self, n: usize, entries: &mut Vec<Entry>) -> bool {
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
        let v = if self.flow_value_absent() {
            ConfigValue::Null
        } else {
            self.flow_item(n)
        };
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

    pub(super) fn flow_value_absent(&self) -> bool {
        matches!(self.cur(), None | Some(b',') | Some(b'}'))
    }

    pub(super) fn flow_tail(&mut self, n: usize, closer: u8) -> Step {
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

    pub(super) fn flow_comma(&mut self, n: usize, closer: u8) -> Step {
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

    pub(super) fn flow_key(&mut self) -> Option<(String, Span)> {
        self.yaml_value_indent = None;
        match self.raw(self.pos) {
            Some(b'"') => self.quoted_double(),
            Some(b'\'') => self.quoted_single(),
            _ => self.plain_flow_text(),
        }
    }

    pub(super) fn flow_item(&mut self, n: usize) -> ConfigValue {
        self.yaml_value_indent = Some(n);
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
            _ => self.plain_flow(n),
        }
    }

    pub(super) fn quoted_string(&mut self, q: Option<(String, Span)>) -> ConfigValue {
        match q {
            Some((t, _)) => ConfigValue::String(t),
            None => ConfigValue::Null,
        }
    }

    pub(super) fn plain_flow(&mut self, n: usize) -> ConfigValue {
        let Some((mut text, _)) = self.plain_flow_text() else {
            return ConfigValue::Null;
        };
        while self.eol(self.pos) > 0 {
            let saved = self.pos;
            let mut next = saved + self.eol(saved);
            let mut blanks = 0;
            while next < self.end {
                let line = self.line_scan(next);
                if !self.line_blank(&line) {
                    break;
                }
                blanks += 1;
                next = line.next;
            }
            let line = self.line_scan(next);
            if line.col <= n
                || matches!(
                    self.raw(line.content),
                    None | Some(b',' | b'[' | b']' | b'{' | b'}' | b':' | b'#')
                )
            {
                break;
            }
            let line = self.take_line(next);
            if self.stop {
                return ConfigValue::Null;
            }
            self.pos = line.content;
            let Some((part, _)) = self.plain_flow_text() else {
                return ConfigValue::Null;
            };
            if blanks == 0 {
                text.push(' ');
            } else {
                text.extend(std::iter::repeat_n('\n', blanks));
            }
            text.push_str(&part);
        }
        resolve_plain(&text)
    }
    pub(super) fn plain_flow_text(&mut self) -> Option<(String, Span)> {
        let from = self.pos;
        if self.plain_start_fails() {
            self.fail(from);
            return None;
        }
        let mut j = from;
        while j < self.end {
            match self.raw(j) {
                Some(b',') | Some(b'[') | Some(b']') | Some(b'{') | Some(b'}') | Some(b':')
                | Some(b'\r') | Some(b'\n') => break,
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
}
