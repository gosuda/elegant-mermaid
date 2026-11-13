use super::*;

impl<'a> Cfg<'a> {
    pub(super) fn quoted_single(&mut self) -> Option<(String, Span)> {
        self.quoted_core(true, false)
    }

    pub(super) fn quoted_double(&mut self) -> Option<(String, Span)> {
        self.quoted_core(false, false)
    }

    pub(super) fn json_string(&mut self) -> Option<(String, Span)> {
        self.quoted_core(false, true)
    }

    pub(super) fn fold_quoted_break(&mut self, out: &mut Vec<u8>, escaped: bool) -> Option<()> {
        if escaped {
            self.pos += 1;
        } else {
            while matches!(out.last(), Some(b' ' | b'\t')) {
                out.pop();
            }
        }
        let breaks = self.quoted_break()?;
        if !escaped && breaks == 1 {
            out.push(b' ');
        } else {
            out.extend(std::iter::repeat_n(b'\n', breaks - 1));
        }
        Some(())
    }

    pub(super) fn quoted_core(&mut self, single: bool, json: bool) -> Option<(String, Span)> {
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
            let escaped = !single && c == b'\\' && self.eol(self.pos + 1) > 0;
            if !json && self.yaml_value_indent.is_some() && (self.eol(self.pos) > 0 || escaped) {
                self.fold_quoted_break(&mut out, escaped)?;
                continue;
            }
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

    pub(super) fn single_step(&mut self, out: &mut Vec<u8>, c: u8) -> Step {
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

    pub(super) fn double_step(&mut self, out: &mut Vec<u8>, c: u8, qc: u8, json: bool) -> Step {
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

    pub(super) fn escape(&mut self, out: &mut Vec<u8>, json: bool) -> bool {
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

    pub(super) fn unicode_escape(&mut self, out: &mut Vec<u8>, json: bool) -> bool {
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

    pub(super) fn surrogate_pair(
        &mut self,
        out: &mut Vec<u8>,
        hi: u32,
        h0: usize,
        six: Span,
    ) -> bool {
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

    pub(super) fn hex_value(&self, at: usize) -> Option<u32> {
        let mut v = 0u32;
        for k in 0..4 {
            v = v
                .wrapping_mul(16)
                .wrapping_add(self.raw(at + k).and_then(hex_digit)?);
        }
        Some(v)
    }

    pub(super) fn surrogate_low(&self, p: usize) -> Option<u32> {
        if self.raw(p) != Some(b'\\') || self.at(p + 1) != Some(b'u') {
            return None;
        }
        let v = self.hex_value(p + 2)?;
        (0xDC00..=0xDFFF).contains(&v).then_some(v)
    }
}
