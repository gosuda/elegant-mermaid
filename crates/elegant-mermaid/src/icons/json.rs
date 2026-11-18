const MAX_DEPTH: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("invalid JSON at byte {at}: {reason}")]
pub(super) struct JsonError {
    at: usize,
    reason: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Json {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

impl Json {
    pub(super) fn member(&self, key: &str) -> Option<&Json> {
        let Json::Object(members) = self else {
            return None;
        };
        members.iter().rev().find(|(k, _)| k == key).map(|(_, v)| v)
    }
}

pub(super) fn parse(text: &str) -> Result<Json, JsonError> {
    let mut reader = Reader {
        bytes: text.as_bytes(),
        at: 0,
    };
    reader.skip_space();
    let value = reader.value(0)?;
    reader.skip_space();
    if reader.at != reader.bytes.len() {
        return Err(reader.fail("trailing content"));
    }
    Ok(value)
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn fail(&self, reason: &'static str) -> JsonError {
        JsonError {
            at: self.at,
            reason,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.at).copied()
    }

    fn skip_space(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\r' | b'\n')) {
            self.at += 1;
        }
    }

    fn eat(&mut self, byte: u8) -> bool {
        if self.peek() == Some(byte) {
            self.at += 1;
            true
        } else {
            false
        }
    }

    fn enter(&self, depth: usize) -> Result<(), JsonError> {
        if depth >= MAX_DEPTH {
            return Err(self.fail("nesting is too deep"));
        }
        Ok(())
    }

    fn value(&mut self, depth: usize) -> Result<Json, JsonError> {
        match self.peek() {
            Some(b'{') => self.object(depth),
            Some(b'[') => self.array(depth),
            Some(b'"') => self.string().map(Json::String),
            Some(b't') => self.literal("true", Json::Bool(true)),
            Some(b'f') => self.literal("false", Json::Bool(false)),
            Some(b'n') => self.literal("null", Json::Null),
            Some(b'-' | b'0'..=b'9') => self.number(),
            _ => Err(self.fail("expected a value")),
        }
    }

    fn literal(&mut self, word: &str, value: Json) -> Result<Json, JsonError> {
        if self.bytes[self.at..].starts_with(word.as_bytes()) {
            self.at += word.len();
            Ok(value)
        } else {
            Err(self.fail("unknown literal"))
        }
    }

    fn object(&mut self, depth: usize) -> Result<Json, JsonError> {
        self.enter(depth)?;
        self.at += 1;
        let mut members = Vec::new();
        self.skip_space();
        if self.eat(b'}') {
            return Ok(Json::Object(members));
        }
        loop {
            self.skip_space();
            if self.peek() != Some(b'"') {
                return Err(self.fail("expected a member name"));
            }
            let key = self.string()?;
            self.skip_space();
            if !self.eat(b':') {
                return Err(self.fail("expected ':'"));
            }
            self.skip_space();
            members.push((key, self.value(depth + 1)?));
            self.skip_space();
            if self.eat(b',') {
                continue;
            }
            if self.eat(b'}') {
                return Ok(Json::Object(members));
            }
            return Err(self.fail("expected ',' or '}'"));
        }
    }

    fn array(&mut self, depth: usize) -> Result<Json, JsonError> {
        self.enter(depth)?;
        self.at += 1;
        let mut items = Vec::new();
        self.skip_space();
        if self.eat(b']') {
            return Ok(Json::Array(items));
        }
        loop {
            self.skip_space();
            items.push(self.value(depth + 1)?);
            self.skip_space();
            if self.eat(b',') {
                continue;
            }
            if self.eat(b']') {
                return Ok(Json::Array(items));
            }
            return Err(self.fail("expected ',' or ']'"));
        }
    }

    fn number(&mut self) -> Result<Json, JsonError> {
        let start = self.at;
        self.eat(b'-');
        match self.peek() {
            Some(b'0') => self.at += 1,
            Some(b'1'..=b'9') => self.digits(),
            _ => return Err(self.fail("expected a digit")),
        }
        if self.eat(b'.') {
            if !matches!(self.peek(), Some(b'0'..=b'9')) {
                return Err(self.fail("expected a fraction digit"));
            }
            self.digits();
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.at += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.at += 1;
            }
            if !matches!(self.peek(), Some(b'0'..=b'9')) {
                return Err(self.fail("expected an exponent digit"));
            }
            self.digits();
        }
        let text = std::str::from_utf8(&self.bytes[start..self.at])
            .map_err(|_| self.fail("invalid number"))?;
        Ok(Json::Number(text.to_owned()))
    }

    fn digits(&mut self) {
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.at += 1;
        }
    }

    fn string(&mut self) -> Result<String, JsonError> {
        self.at += 1;
        let mut out = Vec::new();
        loop {
            let Some(byte) = self.peek() else {
                return Err(self.fail("unterminated string"));
            };
            self.at += 1;
            match byte {
                b'"' => break,
                b'\\' => self.escape(&mut out)?,
                0..=0x1f => return Err(self.fail("control character in string")),
                other => out.push(other),
            }
        }
        String::from_utf8(out).map_err(|_| self.fail("invalid UTF-8"))
    }

    fn escape(&mut self, out: &mut Vec<u8>) -> Result<(), JsonError> {
        let Some(byte) = self.peek() else {
            return Err(self.fail("unterminated escape"));
        };
        self.at += 1;
        let simple = match byte {
            b'"' => Some('"'),
            b'\\' => Some('\\'),
            b'/' => Some('/'),
            b'b' => Some('\u{8}'),
            b'f' => Some('\u{c}'),
            b'n' => Some('\n'),
            b'r' => Some('\r'),
            b't' => Some('\t'),
            _ => None,
        };
        if let Some(c) = simple {
            push(out, c);
            return Ok(());
        }
        if byte != b'u' {
            return Err(self.fail("invalid escape"));
        }
        let first = self.hex4()?;
        let code = if (0xd800..0xdc00).contains(&first) {
            if !(self.eat(b'\\') && self.eat(b'u')) {
                return Err(self.fail("unpaired surrogate"));
            }
            let second = self.hex4()?;
            if !(0xdc00..0xe000).contains(&second) {
                return Err(self.fail("unpaired surrogate"));
            }
            0x10000 + ((first - 0xd800) << 10) + (second - 0xdc00)
        } else {
            first
        };
        let c = char::from_u32(code).ok_or_else(|| self.fail("invalid code point"))?;
        push(out, c);
        Ok(())
    }

    fn hex4(&mut self) -> Result<u32, JsonError> {
        let mut value = 0u32;
        for _ in 0..4 {
            let digit = self
                .peek()
                .and_then(|b| char::from(b).to_digit(16))
                .ok_or_else(|| self.fail("expected a hex digit"))?;
            self.at += 1;
            value = value * 16 + digit;
        }
        Ok(value)
    }
}

fn push(out: &mut Vec<u8>, c: char) {
    let mut buffer = [0u8; 4];
    out.extend_from_slice(c.encode_utf8(&mut buffer).as_bytes());
}

#[cfg(test)]
mod tests {
    use super::{Json, parse};

    #[test]
    fn reads_nested_values_and_escapes() -> Result<(), super::JsonError> {
        let value = parse(r#" {"a":[1,2.5e1,true,null],"s":"x\u00e9\"\ud83d\ude00","a":0} "#)?;
        assert_eq!(value.member("a"), Some(&Json::Number("0".into())));
        assert_eq!(
            value.member("s"),
            Some(&Json::String("x\u{e9}\"\u{1f600}".into()))
        );
        Ok(())
    }

    #[test]
    fn rejects_malformed_text() {
        for text in [
            "",
            "{",
            "[1,]",
            "{\"a\" 1}",
            "01",
            "1.",
            "\"\\x\"",
            "\"\\ud800\"",
            "nul",
            "{} {}",
            "\"a\nb\"",
        ] {
            assert!(parse(text).is_err(), "{text:?}");
        }
        assert!(parse(&"[".repeat(70)).is_err());
    }
}
