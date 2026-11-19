use super::*;

impl<'a> Cfg<'a> {
    pub(super) fn line_scan(&self, from: usize) -> Line {
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

    pub(super) fn take_line(&mut self, from: usize) -> Line {
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

    pub(super) fn line_blank(&self, l: &Line) -> bool {
        matches!(self.raw(l.content), None | Some(b'\r') | Some(b'\n'))
    }

    pub(super) fn skip_lines(&mut self) {
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

    pub(super) fn marker_check(&mut self) -> bool {
        if self.end - self.pos < 3 || self.pos != self.line_start(self.pos) {
            return false;
        }
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

    pub(super) fn line_start(&self, at: usize) -> usize {
        let mut i = at.min(self.end);
        while i > self.start && !matches!(self.raw(i - 1), Some(b'\r') | Some(b'\n')) {
            i -= 1;
        }
        i
    }

    pub(super) fn node_guard(&mut self) -> bool {
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

    pub(super) fn node_block_error(&mut self, c: u8) {
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

    pub(super) fn anchor_byte(&self, j: usize) -> bool {
        match self.raw(j) {
            Some(c) => c.is_ascii_alphanumeric() || c == b'_' || c == b'-',
            None => false,
        }
    }

    pub(super) fn tag_byte(&self, j: usize) -> bool {
        match self.raw(j) {
            Some(c) => !is_ws_byte(c) && !matches!(c, b',' | b'[' | b']' | b'{' | b'}'),
            None => false,
        }
    }
    pub(super) fn plain_first_rejected(&self) -> bool {
        matches!(
            self.raw(self.pos),
            Some(b'[')
                | Some(b']')
                | Some(b'{')
                | Some(b'}')
                | Some(b'#')
                | Some(b'|')
                | Some(b'>')
                | Some(b'\'')
                | Some(b'"')
                | Some(b',')
                | Some(b'%')
                | Some(b'@')
                | Some(b'`')
        )
    }

    pub(super) fn plain_start_fails(&self) -> bool {
        let Some(c) = self.raw(self.pos) else {
            return true;
        };
        if self.plain_first_rejected() {
            return true;
        }
        matches!(c, b'-' | b'?' | b':') && self.boundary(self.pos + 1)
    }

    pub(super) fn line_kind(&self) -> LineKind {
        let from = self.pos;
        let to = self.content_end(from);
        if matches!(self.raw(from), Some(b'"' | b'\'')) {
            return self.quoted_line_kind(from, to);
        }
        let mut j = from;
        while j < to {
            let c = self.raw(j);
            if c == Some(b':') && self.map_boundary(j + 1) {
                return LineKind::Entry;
            }
            if matches!(c, Some(b' ') | Some(b'\t')) && self.raw(j + 1) == Some(b'#') {
                return LineKind::Scalar;
            }
            j += 1;
        }
        LineKind::Scalar
    }

    fn quoted_line_kind(&self, from: usize, to: usize) -> LineKind {
        let Some(after) = self.quote_token_end(from, to) else {
            return LineKind::Scalar;
        };
        let mut j = after;
        while j < to && matches!(self.raw(j), Some(b' ' | b'\t')) {
            j += 1;
        }
        if j < to && self.raw(j) == Some(b':') {
            LineKind::Entry
        } else {
            LineKind::Scalar
        }
    }

    fn quote_token_end(&self, from: usize, to: usize) -> Option<usize> {
        let quote = self.raw(from)?;
        let mut i = from + 1;
        while i < to {
            let c = self.raw(i)?;
            if quote == b'"' && c == b'\\' {
                i += 2;
            } else if c != quote {
                i += 1;
            } else if quote == b'\'' && i + 1 < to && self.raw(i + 1) == Some(b'\'') {
                i += 2;
            } else {
                return Some(i + 1);
            }
        }
        None
    }

    pub(super) fn yaml_document(&mut self) -> ConfigValue {
        self.skip_lines();
        if self.stop || self.marker_check() {
            return ConfigValue::Null;
        }
        if self.at_end() {
            return ConfigValue::Mapping(Vec::new());
        }

        let l = self.take_line(self.pos);
        if self.stop {
            return ConfigValue::Null;
        }
        self.pos = l.content;
        let v = self.root_value(l.col);
        if !self.stop {
            self.tail();
        }
        v
    }

    pub(super) fn sequence_start(&self) -> bool {
        self.raw(self.pos) == Some(b'-') && self.map_boundary(self.pos + 1)
    }

    pub(super) fn flow_start(&self) -> bool {
        matches!(self.raw(self.pos), Some(b'[' | b'{'))
    }

    pub(super) fn block_scalar_start(&self) -> bool {
        matches!(self.raw(self.pos), Some(b'|' | b'>')) && self.line_kind() != LineKind::Entry
    }

    pub(super) fn block_sequence(&mut self, n: usize) -> ConfigValue {
        if !self.enter(self.pos) {
            return ConfigValue::Null;
        }
        let mut items = Vec::new();
        while !self.stop && self.sequence_start() {
            self.pos += 1;
            self.skip_inline_ws();
            let value = self.sequence_item(n);
            if self.stop {
                break;
            }
            items.push(value);
            self.skip_lines();
            if self.at_end() || self.stop {
                break;
            }
            let line = self.take_line(self.pos);
            if line.col < n {
                break;
            }
            self.pos = line.content;
            if line.col != n || !self.sequence_start() {
                self.fail(self.pos);
            }
        }
        self.leave();
        if self.stop {
            ConfigValue::Null
        } else {
            ConfigValue::Sequence(items)
        }
    }

    pub(super) fn sequence_item(&mut self, n: usize) -> ConfigValue {
        if matches!(self.raw(self.pos), None | Some(b'\r' | b'\n' | b'#')) {
            self.finish_line();
            return self.nested_or_null(n).0;
        }
        let col = self.pos - self.line_start(self.pos);
        if self.sequence_start() {
            return self.block_sequence(col);
        }
        if !self.flow_start() && self.line_kind() == LineKind::Entry {
            return self.block_map(col, self.pos);
        }
        let Some((value, _, consumed)) = self.entry_value(n) else {
            return ConfigValue::Null;
        };
        if !consumed {
            self.finish_line();
        }
        value
    }

    pub(super) fn quoted_break(&mut self) -> Option<usize> {
        let mut breaks = 0;
        loop {
            self.pos += self.eol(self.pos);
            breaks += 1;
            while matches!(self.raw(self.pos), Some(b' ' | b'\t')) {
                self.pos += 1;
            }
            if self.pos == self.line_start(self.pos)
                && (self.b[self.pos..self.end].starts_with(b"---")
                    || self.b[self.pos..self.end].starts_with(b"..."))
                && matches!(
                    self.raw(self.pos + 3),
                    None | Some(b' ' | b'\t' | b'\r' | b'\n')
                )
            {
                self.fail(self.pos);
                return None;
            }
            if self.eol(self.pos) == 0 {
                if self.at_end() {
                    self.fail(self.pos);
                    return None;
                }
                return Some(breaks);
            }
        }
    }
    pub(super) fn root_value(&mut self, col: usize) -> ConfigValue {
        self.node_value(col, col, col)
    }

    pub(super) fn node_value(
        &mut self,
        col: usize,
        flow_bound: usize,
        plain_min: usize,
    ) -> ConfigValue {
        self.yaml_continuation_col = Some(plain_min);
        if self.sequence_start() {
            return self.block_sequence(col);
        }
        match self.raw(self.pos) {
            Some(b'[') => {
                let value = self.flow_seq_value(flow_bound);
                self.finish_line();
                value
            }
            Some(b'{') => {
                let value = self.flow_map_value(flow_bound);
                self.finish_line();
                value
            }
            Some(b'|') | Some(b'>') => {
                self.fail(self.pos);
                ConfigValue::Null
            }
            _ => self.plain_or_map(col),
        }
    }

    pub(super) fn root_quoted_double(&mut self) -> ConfigValue {
        let q = self.quoted_double();
        self.root_quoted_done(q)
    }

    pub(super) fn root_quoted_single(&mut self) -> ConfigValue {
        let q = self.quoted_single();
        self.root_quoted_done(q)
    }

    pub(super) fn root_quoted_done(&mut self, q: Option<(String, Span)>) -> ConfigValue {
        let Some((t, _)) = q else {
            return ConfigValue::Null;
        };
        self.finish_line();
        ConfigValue::String(t)
    }

    pub(super) fn plain_or_map(&mut self, col: usize) -> ConfigValue {
        if self.node_guard() {
            return ConfigValue::Null;
        }
        if self.raw(self.pos) == Some(b':') && self.map_boundary(self.pos + 1) {
            self.fail(self.pos);
            return ConfigValue::Null;
        }
        if self.line_kind() == LineKind::Entry {
            return self.block_map(col, self.pos);
        }
        match self.raw(self.pos) {
            Some(b'"') => self.root_quoted_double(),
            Some(b'\'') => self.root_quoted_single(),
            _ => {
                if self.plain_first_rejected() {
                    self.fail(self.pos);
                    return ConfigValue::Null;
                }
                let text = self.plain_value_text();
                let v = resolve_plain(&text);
                self.finish_line();
                v
            }
        }
    }

    pub(super) fn tail(&mut self) {
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
}
