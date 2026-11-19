use super::*;

impl<'a> Cfg<'a> {
    pub(super) fn json_run(&mut self) -> ConfigValue {
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

    pub(super) fn json_ws(&mut self) {
        while matches!(
            self.cur(),
            Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
        ) {
            self.pos += 1;
        }
    }

    pub(super) fn json_object(&mut self) -> ConfigValue {
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

    pub(super) fn json_pair(&mut self, entries: &mut Vec<Entry>) -> bool {
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

    pub(super) fn json_tail(&mut self, closer: u8) -> Step {
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

    pub(super) fn json_key(&mut self) -> Option<(String, Span)> {
        if self.cur() != Some(b'"') {
            self.fail(self.pos);
            return None;
        }
        self.json_string()
    }

    pub(super) fn json_array(&mut self) -> ConfigValue {
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

    pub(super) fn json_value(&mut self) -> ConfigValue {
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

    pub(super) fn json_literal(&mut self, word: &str, v: ConfigValue) -> ConfigValue {
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

    pub(super) fn json_number(&mut self) -> ConfigValue {
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

    pub(super) fn json_digits(&mut self) {
        while self.digit_cur() {
            self.pos += 1;
        }
    }

    pub(super) fn digit_cur(&self) -> bool {
        matches!(self.cur(), Some(c) if c.is_ascii_digit())
    }
}
