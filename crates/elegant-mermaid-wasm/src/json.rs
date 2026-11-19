const MAX_DEPTH: usize = 10_000;

pub struct Scanner<'a> {
    text: &'a str,
    at: usize,
}

impl<'a> Scanner<'a> {
    pub fn new(text: &'a str) -> Scanner<'a> {
        Scanner { text, at: 0 }
    }

    pub fn eat(&mut self, expected: u8) -> bool {
        self.skip_space();
        if self.byte() == Some(expected) {
            self.at += 1;
            true
        } else {
            false
        }
    }

    pub fn at_end(&mut self) -> bool {
        self.skip_space();
        self.at == self.text.len()
    }

    pub fn key(&mut self) -> Option<String> {
        self.skip_space();
        let raw = self.string_raw()?;
        self.eat(b':').then(|| decode(raw))
    }

    pub fn value(&mut self) -> Option<&'a str> {
        self.skip_space();
        let start = self.at;
        let mut stack: Vec<bool> = Vec::new();
        let mut complete = self.begin(&mut stack)?;
        loop {
            if !complete {
                complete = self.begin(&mut stack)?;
                continue;
            }
            let Some(&object) = stack.last() else {
                return self.text.get(start..self.at);
            };
            if self.eat(b',') {
                if object {
                    self.member_key()?;
                }
                complete = false;
            } else if self.eat(if object { b'}' } else { b']' }) {
                stack.pop();
            } else {
                return None;
            }
        }
    }

    fn byte(&self) -> Option<u8> {
        self.text.as_bytes().get(self.at).copied()
    }

    fn skip_space(&mut self) {
        while matches!(self.byte(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.at += 1;
        }
    }

    fn begin(&mut self, stack: &mut Vec<bool>) -> Option<bool> {
        self.skip_space();
        match self.byte()? {
            b'{' => self.open(stack, b'}'),
            b'[' => self.open(stack, b']'),
            b'"' => self.string_raw().map(|_| true),
            b'-' | b'0'..=b'9' => self.number().map(|()| true),
            b't' => self.literal("true"),
            b'f' => self.literal("false"),
            b'n' => self.literal("null"),
            _ => None,
        }
    }

    fn open(&mut self, stack: &mut Vec<bool>, close: u8) -> Option<bool> {
        let object = close == b'}';
        self.at += 1;
        if self.eat(close) {
            return Some(true);
        }
        if stack.len() >= MAX_DEPTH {
            return None;
        }
        stack.push(object);
        if object {
            self.member_key()?;
        }
        Some(false)
    }

    fn member_key(&mut self) -> Option<()> {
        self.skip_space();
        self.string_raw()?;
        self.eat(b':').then_some(())
    }

    fn literal(&mut self, word: &str) -> Option<bool> {
        let rest = self.text.as_bytes().get(self.at..)?;
        if rest.starts_with(word.as_bytes()) {
            self.at += word.len();
            Some(true)
        } else {
            None
        }
    }

    fn string_raw(&mut self) -> Option<&'a str> {
        let start = self.at;
        if self.byte() != Some(b'"') {
            return None;
        }
        self.at += 1;
        loop {
            match self.byte()? {
                b'"' => {
                    self.at += 1;
                    return self.text.get(start..self.at);
                }
                b'\\' => self.escape()?,
                0..=0x1f => return None,
                _ => self.at += 1,
            }
        }
    }

    fn escape(&mut self) -> Option<()> {
        self.at += 1;
        match self.byte()? {
            b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => self.at += 1,
            b'u' => {
                self.at += 1;
                for _ in 0..4 {
                    if !self.byte()?.is_ascii_hexdigit() {
                        return None;
                    }
                    self.at += 1;
                }
            }
            _ => return None,
        }
        Some(())
    }

    fn number(&mut self) -> Option<()> {
        if self.byte() == Some(b'-') {
            self.at += 1;
        }
        match self.byte()? {
            b'0' => self.at += 1,
            b'1'..=b'9' => self.digits()?,
            _ => return None,
        }
        if self.byte() == Some(b'.') {
            self.at += 1;
            self.digits()?;
        }
        if matches!(self.byte(), Some(b'e' | b'E')) {
            self.at += 1;
            if matches!(self.byte(), Some(b'+' | b'-')) {
                self.at += 1;
            }
            self.digits()?;
        }
        Some(())
    }

    fn digits(&mut self) -> Option<()> {
        if !self.byte()?.is_ascii_digit() {
            return None;
        }
        while matches!(self.byte(), Some(b'0'..=b'9')) {
            self.at += 1;
        }
        Some(())
    }
}

pub fn string(raw: &str) -> Option<String> {
    raw.starts_with('"').then(|| decode(raw))
}

fn decode(raw: &str) -> String {
    let inner = raw
        .strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .unwrap_or(raw);
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            Some('b') => out.push('\u{8}'),
            Some('f') => out.push('\u{c}'),
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('u') => push_unicode(&mut chars, &mut out),
            Some(other) => out.push(other),
            None => {}
        }
    }
    out
}

fn push_unicode(chars: &mut std::str::Chars<'_>, out: &mut String) {
    let first = hex4(chars);
    if (0xD800..0xDC00).contains(&first) {
        let mut ahead = chars.clone();
        if ahead.next() == Some('\\') && ahead.next() == Some('u') {
            let second = hex4(&mut ahead);
            if (0xDC00..0xE000).contains(&second) {
                *chars = ahead;
                let code = 0x1_0000 + ((first - 0xD800) << 10) + (second - 0xDC00);
                out.push(char::from_u32(code).unwrap_or('\u{fffd}'));
                return;
            }
        }
    }
    out.push(char::from_u32(first).unwrap_or('\u{fffd}'));
}

fn hex4(chars: &mut std::str::Chars<'_>) -> u32 {
    (0..4).fold(0, |code, _| {
        code * 16 + chars.next().and_then(|ch| ch.to_digit(16)).unwrap_or(0)
    })
}
