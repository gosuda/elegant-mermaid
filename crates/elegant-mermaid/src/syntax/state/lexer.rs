use crate::source::Span;

pub const MODES: &[&str] = &[
    "INITIAL",
    "ID",
    "STATE",
    "FORK_STATE",
    "STATE_STRING",
    "STATE_ID",
    "ALIAS",
    "SCALE",
    "acc_title",
    "acc_descr",
    "acc_descr_multiline",
    "CLASSDEF",
    "CLASSDEFID",
    "CLASS",
    "CLASS_STYLE",
    "STYLE",
    "STYLE_IDS",
    "STYLEDEF_STYLES",
    "STYLEDEF_STYLEOPTS",
    "NOTE",
    "NOTE_ID",
    "NOTE_TEXT",
    "FLOATING_NOTE",
    "FLOATING_NOTE_ID",
    "struct",
    "LINE",
];
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: &'a str,
    pub span: Span,
}

pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    Scanner {
        source,
        removed,
        at: 0,
        modes: vec!["INITIAL"],
        tokens: Vec::new(),
        pending: None,
        opening: None,
    }
    .run()
}
struct Scanner<'a, 'r> {
    source: &'a str,
    removed: &'r [Span],
    at: usize,
    modes: Vec<&'static str>,
    tokens: Vec<Token<'a>>,
    pending: Option<usize>,
    opening: Option<usize>,
}
impl<'a> Scanner<'a, '_> {
    fn mode(&self) -> &'static str {
        self.modes.last().copied().unwrap_or("INITIAL")
    }
    fn pop(&mut self) {
        self.modes.pop();
        if self.modes.is_empty() {
            self.modes.push("INITIAL");
        }
    }
    fn replace(&mut self, mode: &'static str) {
        self.pop();
        self.modes.push(mode);
    }
    fn emit(&mut self, kind: &'static str, length: usize, value: &'a str) {
        let pending = self.pending.take();
        let start = if kind == "UNTERMINATED" {
            self.opening.or(pending).unwrap_or(self.at)
        } else {
            pending.unwrap_or(self.at)
        };
        let value = if kind == "UNTERMINATED" {
            &self.source[start..self.at + length]
        } else {
            value
        };
        self.tokens.push(Token {
            kind,
            text: value,
            span: Span {
                start,
                end: self.at + length,
            },
        });
        self.at += length;
    }
    fn raw(&mut self, kind: &'static str, length: usize) {
        let value = &self.source[self.at..self.at + length];
        self.emit(kind, length, value);
    }
    fn run(mut self) -> Vec<Token<'a>> {
        while self.at < self.source.len() {
            if let Some(span) = self
                .removed
                .iter()
                .find(|s| s.start <= self.at && self.at < s.end)
            {
                self.at = span.end;
                continue;
            }
            let before = self.at;
            let mode = self.mode();
            let count = self.tokens.len();
            self.next();
            if self.at == before && self.mode() == mode && self.tokens.len() == count {
                self.raw(
                    "INVALID",
                    self.source[self.at..]
                        .chars()
                        .next()
                        .map_or(1, char::len_utf8),
                );
            }
        }
        if matches!(
            self.mode(),
            "STATE_STRING" | "NOTE_TEXT" | "FLOATING_NOTE" | "acc_descr_multiline"
        ) {
            let start = self.opening.or(self.pending).unwrap_or(self.at);
            self.tokens.push(Token {
                kind: "UNTERMINATED",
                text: &self.source[start..],
                span: Span {
                    start,
                    end: self.at,
                },
            });
        }
        if matches!(
            self.mode(),
            "acc_title" | "acc_descr" | "CLASSDEFID" | "CLASS_STYLE" | "STYLEDEF_STYLES"
        ) {
            self.mode_value("", self.mode(), 0);
        }
        self.tokens
    }
    fn next(&mut self) {
        let s = &self.source[self.at..];
        let mode = self.mode();
        let line = line_len(s);
        if self.mode_value(s, mode, line) {
            return;
        }
        if mode == "struct" && s.starts_with('}') {
            self.pop();
            self.raw("STRUCT_STOP", 1);
            return;
        }
        if matches!(mode, "INITIAL" | "struct") && self.initial(s, line) {
            return;
        }
        if mode == "STATE" && (s.starts_with('#') || s.starts_with("%%") && !s.starts_with("%%{")) {
            self.at += line;
            return;
        }
        if mode == "STATE" && self.state(s, line) {
            return;
        }
        if self.note(s, mode) {
            return;
        }
        if s.starts_with(['\r', '\n']) {
            let n = if s.starts_with("\r\n") { 2 } else { 1 };
            while !matches!(self.mode(), "INITIAL" | "struct") {
                self.pop();
            }
            self.pending = None;
            self.raw("NL", n);
            return;
        }
        let ws = s.len()
            - s.trim_start_matches(|c: char| c.is_whitespace() && !matches!(c, '\r' | '\n'))
                .len();
        if ws > 0 {
            self.at += ws;
            return;
        }
        if matches!(mode, "INITIAL" | "struct" | "STATE" | "ID" | "LINE")
            && (s.starts_with('#') || s.starts_with("%%") && !s.starts_with("%%{"))
        {
            self.at += line;
            return;
        }
        if matches!(mode, "INITIAL" | "STATE") && s.starts_with('{') {
            self.pop();
            self.modes.push("struct");
            self.raw("STRUCT_START", 1);
        }
    }
    fn mode_value(&mut self, s: &'a str, mode: &str, line: usize) -> bool {
        let kind = match mode {
            "acc_title" => "acc_title_value",
            "acc_descr" => "acc_descr_value",
            "CLASSDEFID" => "CLASSDEF_STYLEOPTS",
            "CLASS_STYLE" => "STYLECLASS",
            "STYLEDEF_STYLES" => "STYLEDEF_STYLEOPTS",
            "STATE_ID" | "FLOATING_NOTE_ID" => "ID",
            _ => "",
        };
        if !kind.is_empty() {
            return self.line_value(s, kind, line);
        }
        match mode {
            "STATE_STRING" => self.state_description(s),
            "acc_descr_multiline" => self.accessibility_block(s),
            "SCALE" => self.scale_width(s),
            "CLASSDEF" | "CLASS" | "STYLE" => self.style_value(s, mode),
            _ => false,
        }
    }
    fn line_value(&mut self, s: &'a str, kind: &'static str, line: usize) -> bool {
        let mut n = if self.mode() == "STATE_ID" {
            s[..line].find('{').unwrap_or(line)
        } else {
            line
        };
        if kind == "ID" {
            n = s[..n].find("%%").unwrap_or(n);
        }
        self.pop();
        if n == 0 && kind == "ID" {
            self.pending = None;
            return false;
        }
        self.raw(kind, n);
        true
    }
    fn state_description(&mut self, s: &'a str) -> bool {
        if let Some(n) = s.find('"') {
            self.emit("STATE_DESCR", n + 1, &s[..n]);
            self.pop();
            return true;
        }
        self.pending = Some(self.at.saturating_sub(1));
        self.raw("UNTERMINATED", s.len());
        self.pop();
        true
    }
    fn accessibility_block(&mut self, s: &'a str) -> bool {
        if let Some(n) = s.find('}') {
            self.emit("acc_descr_multiline_value", n + 1, &s[..n]);
            self.pop();
            return true;
        }
        self.pending = Some(self.at.saturating_sub(1));
        self.raw("UNTERMINATED", s.len());
        self.pop();
        true
    }
    fn scale_width(&mut self, s: &'a str) -> bool {
        let n = s.bytes().take_while(u8::is_ascii_digit).count();
        if n > 0 {
            self.raw("WIDTH", n);
            return true;
        }
        let t = s.trim_start_matches(char::is_whitespace);
        if !word(t, "width") {
            return false;
        }
        self.at += s.len() - t.len() + 5;
        self.pop();
        true
    }
    fn style_value(&mut self, s: &'a str, mode: &str) -> bool {
        let n = if mode == "CLASS" {
            class_ids_len(s)
        } else {
            s.bytes()
                .take_while(|b| {
                    b.is_ascii_alphanumeric() || *b == b'_' || mode == "STYLE" && *b == b','
                })
                .count()
        };
        if n == 0 {
            return false;
        }
        let ws = s[n..].len() - s[n..].trim_start_matches(char::is_whitespace).len();
        if mode != "CLASS" && ws == 0 {
            return false;
        }
        let (kind, next) = match mode {
            "CLASS" => ("CLASSENTITY_IDS", "CLASS_STYLE"),
            "STYLE" => ("STYLE_IDS", "STYLEDEF_STYLES"),
            _ if s[..n].eq_ignore_ascii_case("default") => ("DEFAULT_CLASSDEF_ID", "CLASSDEFID"),
            _ => ("CLASSDEF_ID", "CLASSDEFID"),
        };
        self.replace(next);
        self.raw(kind, n + if mode == "CLASS" { 0 } else { ws });
        true
    }
    fn initial(&mut self, s: &'a str, line: usize) -> bool {
        if self.mode() == "INITIAL" && self.root_literal(s) {
            return true;
        }
        if let Some(kind) = direction(&s[..line]) {
            self.raw(kind, line);
            return true;
        }
        if s.starts_with('#') || s.starts_with("%%") && !s.starts_with("%%{") {
            self.at += line;
            return true;
        }
        self.declaration(s)
            || self.mode() == "INITIAL" && self.accessibility(s)
            || self.atom(s, line)
    }
    fn root_literal(&mut self, s: &'a str) -> bool {
        for (literal, kind) in [("click", "CLICK"), ("href", "HREF"), ("default", "DEFAULT")] {
            if word(s, literal) {
                self.raw(kind, literal.len());
                return true;
            }
        }
        if !s.starts_with('"') {
            return false;
        }
        self.opening = Some(self.at);
        if let Some(n) = s[1..].find('"') {
            self.emit("STRING", n + 2, &s[1..n + 1]);
        } else {
            self.raw("UNTERMINATED", s.len());
        }
        true
    }
    fn declaration(&mut self, s: &'a str) -> bool {
        for (literal, kind, mode) in [
            ("scale", "scale", "SCALE"),
            ("classDef", "classDef", "CLASSDEF"),
            ("class", "class", "CLASS"),
            ("style", "style", "STYLE"),
            ("state", "", "STATE"),
            ("note", "note", "NOTE"),
        ] {
            if mode == "SCALE" && self.mode() != "INITIAL" {
                continue;
            }
            if !word(s, literal) {
                continue;
            }
            let ws = s[literal.len()..].len()
                - s[literal.len()..]
                    .trim_start_matches(char::is_whitespace)
                    .len();
            if ws == 0 {
                continue;
            }
            self.modes.push(mode);
            if mode == "NOTE" {
                self.opening = Some(self.at);
            }
            if kind.is_empty() {
                self.pending = Some(self.at);
                self.at += literal.len() + ws;
            } else {
                self.raw(kind, literal.len() + ws);
            }
            return true;
        }
        false
    }
    fn accessibility(&mut self, s: &'a str) -> bool {
        for (name, mode, kind) in [
            ("accTitle", "acc_title", "acc_title"),
            ("accDescr", "acc_descr", "acc_descr"),
        ] {
            if !word(s, name) {
                continue;
            }
            let tail = s[name.len()..].trim_start_matches(char::is_whitespace);
            let prefix = s.len() - tail.len();
            if let Some(value) = tail.strip_prefix(':') {
                let n =
                    prefix + 1 + value.len() - value.trim_start_matches(char::is_whitespace).len();
                self.modes.push(mode);
                self.raw(kind, n);
                return true;
            }
            if name == "accDescr" && tail.starts_with('{') {
                self.opening = Some(self.at + prefix);
                self.pending = Some(self.at);
                self.at += prefix + 1;
                self.modes.push("acc_descr_multiline");
                return true;
            }
        }
        false
    }
    fn atom(&mut self, s: &'a str, line: usize) -> bool {
        if self.mode() == "INITIAL" && self.header(s) {
            return true;
        }
        if self.mode() == "INITIAL" && word(s, "hide empty description") {
            self.raw("HIDE_EMPTY", 22);
            return true;
        }
        if s.starts_with("[*]") {
            self.raw("EDGE_STATE", 3);
            return true;
        }
        let n = s
            .char_indices()
            .take_while(|(_, c)| !c.is_whitespace() && !matches!(c, ':' | '-' | '{'))
            .last()
            .map_or(0, |(i, c)| i + c.len_utf8());
        if n > 0 {
            let n = s[..n].find("%%").unwrap_or(n);
            if n > 0 {
                self.raw("ID", n);
                return true;
            }
        }
        if self.description(s, line) {
            return true;
        }
        for (text, kind) in [
            ("-->", "-->"),
            ("--", "CONCURRENT"),
            (":::", "STYLE_SEPARATOR"),
        ] {
            if s.starts_with(text) && (kind != "CONCURRENT" || self.mode() == "struct") {
                self.raw(kind, text.len());
                return true;
            }
        }
        false
    }
    fn header(&mut self, s: &'a str) -> bool {
        for h in ["stateDiagram", "stateDiagram-v2"] {
            if !s.starts_with(h) {
                continue;
            }
            let tail = &s[h.len()..];
            if !tail.is_empty() && !tail.starts_with(char::is_whitespace) {
                continue;
            }
            let n = h.len() + tail.len() - tail.trim_start_matches(char::is_whitespace).len();
            self.raw("SD", n);
            return true;
        }
        false
    }
    fn description(&mut self, s: &'a str, line: usize) -> bool {
        if !s.starts_with(':') {
            return false;
        }
        let mut n = 1;
        let b = s.as_bytes();
        while n < line && b[n] != b';' {
            if b[n] != b':' {
                n += s[n..].chars().next().map_or(1, char::len_utf8);
                continue;
            }
            if n + 1 >= line || matches!(b[n + 1], b':' | b';') {
                break;
            }
            n += 1 + s[n + 1..].chars().next().map_or(1, char::len_utf8);
        }
        if n == 1 {
            return false;
        }
        self.emit("DESCR", n, s[..n].trim());
        true
    }
    fn state(&mut self, s: &'a str, line: usize) -> bool {
        for (suffix, kind) in [
            ("<<fork>>", "FORK"),
            ("<<join>>", "JOIN"),
            ("<<choice>>", "CHOICE"),
            ("[[fork]]", "FORK"),
            ("[[join]]", "JOIN"),
            ("[[choice]]", "CHOICE"),
        ] {
            if let Some(p) = find_ascii(&s[..line], suffix) {
                self.pop();
                self.emit(kind, p + suffix.len(), s[..p].trim());
                return true;
            }
        }
        if s.starts_with('"') {
            self.opening = Some(self.at);
            self.pending.get_or_insert(self.at);
            self.at += 1;
            self.modes.push("STATE_STRING");
            return true;
        }
        let t = s.trim_start_matches(char::is_whitespace);
        if word(t, "as") {
            let tail = &t[2..];
            let ws = tail.len() - tail.trim_start_matches(char::is_whitespace).len();
            if ws > 0 {
                self.modes.push("STATE_ID");
                self.raw("AS", s.len() - t.len() + 2 + ws);
                return true;
            }
        }
        if let Some(p) = s[..line].find('{')
            && multiword_name(&s[..p])
        {
            self.emit("MULTIWORD", p + 1, s[..p + 1].trim());
            return true;
        }
        let n = s
            .char_indices()
            .take_while(|(_, c)| !c.is_whitespace() && *c != '{')
            .last()
            .map_or(0, |(i, c)| i + c.len_utf8());
        if n > 0 {
            self.raw("COMPOSIT_STATE", n);
            return true;
        }
        false
    }
    fn note(&mut self, s: &'a str, mode: &str) -> bool {
        match mode {
            "NOTE" => self.note_position(s),
            "NOTE_ID" => self.note_target(s),
            "NOTE_TEXT" => self.note_text(s),
            "FLOATING_NOTE" => self.floating_note(s),
            _ => false,
        }
    }
    fn note_position(&mut self, s: &'a str) -> bool {
        for (text, kind) in [("left of", "left_of"), ("right of", "right_of")] {
            if word(s, text) {
                self.replace("NOTE_ID");
                self.raw(kind, text.len());
                return true;
            }
        }
        if s.starts_with('"') {
            self.pending = Some(self.at);
            self.opening = Some(self.at);
            self.at += 1;
            self.replace("FLOATING_NOTE");
            return true;
        }
        false
    }
    fn note_target(&mut self, s: &'a str) -> bool {
        let text = s.trim_start_matches(char::is_whitespace);
        let prefix = s.len() - text.len();
        let n = text
            .char_indices()
            .take_while(|(_, c)| !c.is_whitespace() && !matches!(c, ':' | '-'))
            .last()
            .map_or(0, |(i, c)| i + c.len_utf8());
        let n = text[..n].find("%%").unwrap_or(n);
        if n == 0 {
            return false;
        }
        self.replace("NOTE_TEXT");
        self.emit("ID", prefix + n, &text[..n]);
        true
    }
    fn note_text(&mut self, s: &'a str) -> bool {
        let t = s.trim_start_matches(char::is_whitespace);
        let p = s.len() - t.len();
        if let Some(value) = t.strip_prefix(':') {
            let n = value
                .find([':', '\r', '\n', ';'])
                .map_or(t.len(), |i| i + 1);
            if n > 1 {
                self.pop();
                self.emit("NOTE_TEXT", p + n, value[..n - 1].trim());
                return true;
            }
        }
        if let Some((end, value_end)) = note_end(s) {
            self.pop();
            self.emit("NOTE_TEXT", end, s[..value_end].trim());
            return true;
        }
        self.raw("UNTERMINATED", s.len());
        self.pop();
        true
    }
    fn floating_note(&mut self, s: &'a str) -> bool {
        let t = s.trim_start_matches(char::is_whitespace);
        if word(t, "as") {
            self.replace("FLOATING_NOTE_ID");
            self.raw("AS", s.len() - t.len() + 2);
            return true;
        }
        if s.starts_with('"') {
            self.at += 1;
            return true;
        }
        if let Some(n) = s.find('"') {
            self.raw("NOTE_TEXT", n);
            return true;
        }
        self.raw("UNTERMINATED", s.len());
        self.pop();
        true
    }
}
fn line_len(s: &str) -> usize {
    s.find(['\r', '\n']).unwrap_or(s.len())
}
fn word(s: &str, word: &str) -> bool {
    s.get(..word.len())
        .is_some_and(|p| p.eq_ignore_ascii_case(word))
        && s[word.len()..]
            .chars()
            .next()
            .is_none_or(|c| !c.is_ascii_alphanumeric() && c != '_')
}
fn find_ascii(s: &str, needle: &str) -> Option<usize> {
    s.as_bytes()
        .windows(needle.len())
        .rposition(|w| w.eq_ignore_ascii_case(needle.as_bytes()))
}
fn direction(s: &str) -> Option<&'static str> {
    for (axis, kind) in [
        ("TB", "direction_tb"),
        ("BT", "direction_bt"),
        ("RL", "direction_rl"),
        ("LR", "direction_lr"),
    ] {
        for (p, _) in s.char_indices() {
            if !word(&s[p..], "direction") {
                continue;
            }
            let tail = &s[p + 9..];
            let t = tail.trim_start_matches(char::is_whitespace);
            if t.len() < tail.len() && word(t, axis) {
                return Some(kind);
            }
        }
    }
    None
}
fn class_ids_len(s: &str) -> usize {
    let mut n = 0;
    loop {
        let k = s[n..]
            .bytes()
            .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
            .count();
        if k == 0 {
            return n;
        }
        n += k;
        if !s[n..].starts_with(',') {
            return n;
        }
        let tail = s[n + 1..].trim_start_matches(char::is_whitespace);
        if tail
            .bytes()
            .next()
            .is_none_or(|b| !b.is_ascii_alphanumeric() && b != b'_')
        {
            return n;
        }
        n = s.len() - tail.len();
    }
}
fn note_end(s: &str) -> Option<(usize, usize)> {
    for (p, c) in s.char_indices() {
        if !matches!(c, '\r' | '\n') {
            continue;
        }
        let tail = s[p..].trim_start_matches(char::is_whitespace);
        if word(tail, "end note") {
            return Some((s.len() - tail.len() + 8, p));
        }
    }
    None
}
fn multiword_name(s: &str) -> bool {
    let first = s
        .bytes()
        .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
        .count();
    if first == 0 {
        return false;
    }
    let tail = &s[first..];
    let second = tail.trim_start_matches(char::is_whitespace);
    second.len() < tail.len()
        && second
            .bytes()
            .next()
            .is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_')
}
