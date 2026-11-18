use super::{
    ast::{JsonObject, JsonProperty, JsonValue, JsonValueKind},
    lexer::Token,
};
use crate::source::{Span, cleaned::Cleaned};
pub(crate) struct JsonFailure {
    pub span: Span,
    pub reason: &'static str,
    pub limit: bool,
}
pub(crate) fn json_object<'a>(
    token: &Token<'a>,
    cleaned: &Cleaned<'a>,
) -> Result<JsonObject<'a>, JsonFailure> {
    let mut reader = JsonReader {
        text: &token.text,
        cleaned,
        base: cleaned.index(token.span.start),
        at: 0,
    };
    reader.object(1)
}
struct JsonReader<'a, 't> {
    text: &'t str,
    cleaned: &'t Cleaned<'a>,
    base: usize,
    at: usize,
}
impl<'a> JsonReader<'a, '_> {
    fn byte(&self) -> Option<u8> {
        self.text.as_bytes().get(self.at).copied()
    }
    fn ws(&mut self) {
        while self
            .byte()
            .is_some_and(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
        {
            self.at += 1;
        }
    }
    fn fail(&self, reason: &'static str) -> JsonFailure {
        let n = self
            .text
            .get(self.at..)
            .and_then(|s| s.chars().next())
            .map_or(0, char::len_utf8);
        JsonFailure {
            span: self
                .cleaned
                .span(self.base + self.at, self.base + self.at + n),
            reason,
            limit: false,
        }
    }
    fn span(&self, start: usize) -> Span {
        self.cleaned.span(self.base + start, self.base + self.at)
    }
    fn require(&mut self, b: u8) -> Result<(), JsonFailure> {
        self.ws();
        if self.byte() != Some(b) {
            return Err(self.fail("unexpected token"));
        }
        self.at += 1;
        Ok(())
    }
    fn depth(&self, depth: usize) -> Result<(), JsonFailure> {
        if depth <= 64 {
            return Ok(());
        }
        let mut failure = self.fail("nesting depth exceeds 64");
        failure.limit = true;
        Err(failure)
    }
    fn object(&mut self, depth: usize) -> Result<JsonObject<'a>, JsonFailure> {
        self.ws();
        self.depth(depth)?;
        let start = self.at;
        self.require(b'{')?;
        self.ws();
        let properties = self.properties(depth)?;
        self.require(b'}')?;
        Ok(JsonObject {
            span: self.span(start),
            properties,
        })
    }
    fn properties(&mut self, depth: usize) -> Result<Vec<JsonProperty<'a>>, JsonFailure> {
        let mut properties = Vec::new();
        if self.byte() == Some(b'}') {
            return Ok(properties);
        }
        loop {
            let key = self.string()?;
            self.require(b':')?;
            let value = self.value(depth)?;
            let span = Span {
                start: key.span.start,
                end: value.span.end,
            };
            properties.push(JsonProperty { span, key, value });
            self.ws();
            if self.byte() != Some(b',') {
                break;
            }
            self.at += 1;
        }
        Ok(properties)
    }
    fn array(&mut self, depth: usize) -> Result<Vec<JsonValue<'a>>, JsonFailure> {
        self.depth(depth)?;
        self.require(b'[')?;
        self.ws();
        let mut values = Vec::new();
        if self.byte() != Some(b']') {
            loop {
                values.push(self.value(depth)?);
                self.ws();
                if self.byte() != Some(b',') {
                    break;
                }
                self.at += 1;
            }
        }
        self.require(b']')?;
        Ok(values)
    }
    fn value(&mut self, depth: usize) -> Result<JsonValue<'a>, JsonFailure> {
        self.ws();
        let start = self.at;
        let kind = match self.byte() {
            Some(b'{') => JsonValueKind::Object(self.object(depth + 1)?),
            Some(b'[') => JsonValueKind::Array(self.array(depth + 1)?),
            Some(b'"') => JsonValueKind::Scalar(self.string()?),
            _ => JsonValueKind::Scalar(self.scalar()?),
        };
        Ok(JsonValue {
            span: self.span(start),
            kind,
        })
    }
    fn string(&mut self) -> Result<Token<'a>, JsonFailure> {
        self.ws();
        let start = self.at;
        self.require(b'"')?;
        loop {
            match self.byte() {
                Some(b'"') => {
                    self.at += 1;
                    break;
                }
                Some(b'\\') => {
                    self.at += 1;
                    self.escape()?;
                }
                Some(0..=31) | None => return Err(self.fail("invalid string")),
                Some(_) => self.at += 1,
            }
        }
        Ok(Token {
            kind: "JSON_STRING",
            text: self.cleaned.cow(self.base + start, self.base + self.at),
            span: self.span(start),
        })
    }
    fn escape(&mut self) -> Result<(), JsonFailure> {
        match self.byte() {
            Some(b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't') => self.at += 1,
            Some(b'u') => {
                self.at += 1;
                for _ in 0..4 {
                    if !self.byte().is_some_and(|b| b.is_ascii_hexdigit()) {
                        return Err(self.fail("invalid unicode escape"));
                    }
                    self.at += 1;
                }
            }
            _ => return Err(self.fail("invalid escape")),
        }
        Ok(())
    }
    fn scalar(&mut self) -> Result<Token<'a>, JsonFailure> {
        let start = self.at;
        for (text, kind) in [
            ("true", "JSON_TRUE"),
            ("false", "JSON_FALSE"),
            ("null", "JSON_NULL"),
        ] {
            if self
                .text
                .get(self.at..)
                .is_some_and(|s| s.starts_with(text))
            {
                self.at += text.len();
                return Ok(Token {
                    kind,
                    text: self.cleaned.cow(self.base + start, self.base + self.at),
                    span: self.span(start),
                });
            }
        }
        self.number()?;
        Ok(Token {
            kind: "JSON_NUMBER",
            text: self.cleaned.cow(self.base + start, self.base + self.at),
            span: self.span(start),
        })
    }
    fn number(&mut self) -> Result<(), JsonFailure> {
        if self.byte() == Some(b'-') {
            self.at += 1;
        }
        match self.byte() {
            Some(b'0') => self.at += 1,
            Some(b'1'..=b'9') => self.digits(),
            _ => return Err(self.fail("expected value")),
        }
        if self.byte() == Some(b'.') {
            self.at += 1;
            self.require_digits()?;
        }
        if matches!(self.byte(), Some(b'e' | b'E')) {
            self.at += 1;
            if matches!(self.byte(), Some(b'+' | b'-')) {
                self.at += 1;
            }
            self.require_digits()?;
        }
        Ok(())
    }
    fn digits(&mut self) {
        while self.byte().is_some_and(|b| b.is_ascii_digit()) {
            self.at += 1;
        }
    }
    fn require_digits(&mut self) -> Result<(), JsonFailure> {
        if !self.byte().is_some_and(|b| b.is_ascii_digit()) {
            return Err(self.fail("expected digit"));
        }
        self.digits();
        Ok(())
    }
}
