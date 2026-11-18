//! Lexer for the block grammar of `spec/grammar/block.md`.
//!
//! One pass in source order; inside one mode the first rule that matches at the cursor
//! wins. Keyword rules end at a word boundary, and padded tokens drop their surrounding
//! white space from the span. Removed spans (comments, directives) are skipped.

use crate::source::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: &'a str,
    pub span: Span,
}

pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    Scanner {
        src: source,
        removed,
        at: 0,
        frames: vec![Frame {
            mode: Mode::Initial,
            opener: 0,
            text: "",
        }],
        tokens: Vec::new(),
    }
    .run()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Initial,
    String,
    MdString,
    Node,
    BlockArrow,
    ArrowDir,
    LinkLabel,
    Class,
    ClassStyle,
    ClassDef,
    ClassDefId,
    StyleStatement,
    StyleDefinition,
    AccTitle,
    AccDescr,
    AccDescrMultiline,
}

#[derive(Debug, Clone, Copy)]
struct Frame<'a> {
    mode: Mode,
    opener: usize,
    text: &'a str,
}

const ROOT: Frame<'static> = Frame {
    mode: Mode::Initial,
    opener: 0,
    text: "",
};

const OPENERS: [&str; 19] = [
    "-)", "(-", "))", ")", "(((", "((", "{{", "{", ">", "([", "(", "[[", "[|", "[(", ")))", "[\\",
    "[/", "[\\", "[",
];

const CLOSERS: [&str; 17] = [
    "(((", ")))", "))", "}}", "}", "(-", "-)", "((", "]]", "(", "])", "\\]", "/]", ")]", ")", "]>",
    "]",
];

const DIRECTIONS: [&str; 6] = ["right", "left", "x", "y", "up", "down"];

const PADDED: [&str; 12] = [
    "end",
    "classDef",
    "class",
    "style",
    "LINK",
    "START_LINK",
    "DIR",
    "BLOCK_ARROW_END",
    "acc_title",
    "acc_descr",
    "CLASSDEF_ID",
    "DEFAULT_CLASSDEF_ID",
];

fn remainder_kind(mode: Mode) -> Option<&'static str> {
    match mode {
        Mode::ClassStyle => Some("STYLECLASS"),
        Mode::ClassDefId => Some("CLASSDEF_STYLEOPTS"),
        Mode::StyleDefinition => Some("STYLE_DEFINITION_DATA"),
        Mode::AccTitle => Some("acc_title_value"),
        Mode::AccDescr => Some("acc_descr_value"),
        _ => None,
    }
}

fn opens_construct(mode: Mode) -> bool {
    matches!(
        mode,
        Mode::String
            | Mode::MdString
            | Mode::Node
            | Mode::BlockArrow
            | Mode::ArrowDir
            | Mode::LinkLabel
    )
}

fn is_space(c: char) -> bool {
    matches!(
        c,
        '\u{09}'..='\u{0d}'
            | ' '
            | '\u{a0}'
            | '\u{1680}'
            | '\u{2000}'..='\u{200a}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
            | '\u{feff}'
    )
}

fn space_len(text: &str) -> usize {
    text.len() - text.trim_start_matches(is_space).len()
}

fn is_word(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn run_len(text: &str, c: u8) -> usize {
    text.bytes().take_while(|&b| b == c).count()
}

fn digit_len(text: &str) -> usize {
    text.bytes().take_while(u8::is_ascii_digit).count()
}

fn word_len(text: &str) -> usize {
    text.bytes().take_while(|&b| is_word(b)).count()
}

fn boundary(text: &str, n: usize) -> bool {
    text.as_bytes().get(n).is_none_or(|&b| !is_word(b))
}

fn keyword(text: &str, word: &str) -> bool {
    text.starts_with(word) && boundary(text, word.len())
}

fn line_len(text: &str) -> usize {
    text.find('\n').unwrap_or(text.len())
}

fn byte_at(text: &str, i: usize) -> Option<u8> {
    text.as_bytes().get(i).copied()
}

fn marker(text: &str, i: usize) -> usize {
    match byte_at(text, i) {
        Some(b'x' | b'o' | b'<') => i + 1,
        _ => i,
    }
}

fn repeated_link(rest: &str, c: u8) -> usize {
    let mut i = marker(rest, space_len(rest));
    let run = run_len(&rest[i..], c);
    if run < 2 {
        return 0;
    }
    i += run;
    if matches!(byte_at(rest, i), Some(b'x' | b'o' | b'>')) {
        i += 1;
    } else if run < 3 {
        return 0;
    }
    i + space_len(&rest[i..])
}

fn dotted_link(rest: &str) -> usize {
    let mut i = marker(rest, space_len(rest));
    if byte_at(rest, i) == Some(b'-') {
        i += 1;
    }
    let dots = run_len(&rest[i..], b'.');
    if dots == 0 {
        return 0;
    }
    i += dots;
    if byte_at(rest, i) != Some(b'-') {
        return 0;
    }
    i += 1;
    if matches!(byte_at(rest, i), Some(b'x' | b'o' | b'>')) {
        i += 1;
    }
    i + space_len(&rest[i..])
}

fn link_len(rest: &str) -> usize {
    [
        repeated_link(rest, b'-'),
        repeated_link(rest, b'='),
        dotted_link(rest),
    ]
    .into_iter()
    .find(|&n| n > 0)
    .unwrap_or(0)
}

fn start_link_len(rest: &str) -> usize {
    let i = marker(rest, space_len(rest));
    ["--", "==", "-."]
        .iter()
        .find(|pattern| rest[i..].starts_with(**pattern))
        .map_or(0, |_| i + 2 + space_len(&rest[i + 2..]))
}

fn node_excluded(c: char) -> bool {
    matches!(c, '(' | '[' | '-' | ')' | '{' | '}' | '<' | '>' | ':' | '=') || is_space(c)
}

fn id_list_len(text: &str) -> usize {
    let mut n = word_len(text);
    if n == 0 {
        return 0;
    }
    while byte_at(text, n) == Some(b',') {
        let next = n + 1 + space_len(&text[n + 1..]);
        let word = word_len(&text[next..]);
        if word == 0 {
            break;
        }
        n = next + word;
    }
    n
}

fn class_def_id(rest: &str) -> (&'static str, usize) {
    if let Some(tail) = rest.strip_prefix("DEFAULT") {
        let gap = space_len(tail);
        if gap > 0 {
            return ("DEFAULT_CLASSDEF_ID", "DEFAULT".len() + gap);
        }
    }
    let word = word_len(rest);
    let gap = space_len(&rest[word..]);
    if word == 0 || gap == 0 {
        return ("", 0);
    }
    ("CLASSDEF_ID", word + gap)
}

struct Scanner<'a, 'r> {
    src: &'a str,
    removed: &'r [Span],
    at: usize,
    frames: Vec<Frame<'a>>,
    tokens: Vec<Token<'a>>,
}

type Scan<'a, 'r> = fn(&mut Scanner<'a, 'r>, &'a str) -> bool;

impl<'a, 'r> Scanner<'a, 'r> {
    fn run(mut self) -> Vec<Token<'a>> {
        while self.at < self.src.len() {
            if let Some(end) = self.removed_end() {
                self.at = end;
                continue;
            }
            if !self.step() {
                self.invalid();
            }
        }
        self.finish();
        self.tokens
    }

    fn finish(&mut self) {
        let end = self.src.len();
        while let Some(kind) = remainder_kind(self.top().mode) {
            self.tokens.push(Token {
                kind,
                text: "",
                span: Span { start: end, end },
            });
            self.pop();
        }
        let top = self.top();
        if opens_construct(top.mode) {
            self.tokens.push(Token {
                kind: "UNTERMINATED",
                text: top.text,
                span: Span {
                    start: top.opener,
                    end,
                },
            });
        }
        self.tokens.push(Token {
            kind: "EOF",
            text: "",
            span: Span { start: end, end },
        });
    }

    fn removed_end(&self) -> Option<usize> {
        self.removed
            .iter()
            .find(|span| span.start <= self.at && self.at < span.end)
            .map(|span| span.end)
    }

    fn top(&self) -> Frame<'a> {
        self.frames.last().copied().unwrap_or(ROOT)
    }

    fn push(&mut self, mode: Mode, opener: usize, text: &'a str) {
        self.frames.push(Frame { mode, opener, text });
    }

    fn pop(&mut self) {
        if self.frames.len() > 1 {
            self.frames.pop();
        }
    }

    fn rest(&self) -> &'a str {
        &self.src[self.at..]
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let text = &self.src[self.at..self.at + length];
        self.value(kind, length, text);
    }

    fn value(&mut self, kind: &'static str, length: usize, text: &'a str) {
        let mut start = self.at;
        let mut end = self.at + length;
        if PADDED.contains(&kind) {
            let raw = &self.src[start..end];
            let lead = space_len(raw);
            start += lead;
            end = start + raw[lead..].trim_end_matches(is_space).len();
        }
        self.tokens.push(Token {
            kind,
            text,
            span: Span { start, end },
        });
        self.at += length;
    }

    fn invalid(&mut self) {
        let size = self.rest().chars().next().map_or(1, char::len_utf8);
        self.emit("INVALID", size);
        self.frames.truncate(1);
    }

    fn step(&mut self) -> bool {
        let mode = self.top().mode;
        if let Some(kind) = remainder_kind(mode) {
            return self.remainder(kind);
        }
        match mode {
            Mode::String => self.string_mode(),
            Mode::MdString => self.md_string_mode(),
            Mode::Node => self.node_mode(),
            Mode::BlockArrow => self.block_arrow_mode(),
            Mode::ArrowDir => self.arrow_dir_mode(),
            Mode::LinkLabel => self.link_label_mode(),
            Mode::Class | Mode::StyleStatement => self.id_list_mode(),
            Mode::ClassDef => self.class_def_mode(),
            Mode::AccDescrMultiline => self.acc_descr_multiline(),
            _ => self.initial(),
        }
    }

    fn initial(&mut self) -> bool {
        let rest = self.rest();
        if keyword(rest, "block-beta") {
            self.emit("BLOCK_DIAGRAM_KEY", "block-beta".len());
        } else if rest.starts_with("block:") {
            self.emit("id-block", "block:".len());
        } else if keyword(rest, "block") {
            self.emit("BLOCK_DIAGRAM_KEY", "block".len());
        } else {
            return self.space_or_statement(rest);
        }
        true
    }

    fn space_or_statement(&mut self, rest: &'a str) -> bool {
        let n = space_len(rest);
        if n > 0 {
            self.at += n;
            return true;
        }
        let scanners: [Scan<'a, 'r>; 11] = [
            Self::columns,
            Self::open_quote,
            Self::space_block,
            Self::plain_keyword,
            Self::statement_keyword,
            Self::accessibility,
            Self::end_keyword,
            Self::shape_opener,
            Self::node_identifier,
            Self::link,
            Self::size,
        ];
        scanners.iter().any(|scan| scan(self, rest))
    }

    fn columns(&mut self, rest: &'a str) -> bool {
        if !rest.starts_with("columns") {
            return false;
        }
        let mut i = "columns".len();
        let gap = space_len(&rest[i..]);
        if gap == 0 {
            return false;
        }
        i += gap;
        if keyword(&rest[i..], "auto") {
            self.value("COLUMNS", i + "auto".len(), "-1");
            return true;
        }
        let digits = digit_len(&rest[i..]);
        if digits == 0 {
            return false;
        }
        self.value("COLUMNS", i + digits, &rest[i..i + digits]);
        true
    }

    fn open_quote(&mut self, rest: &'a str) -> bool {
        if rest.starts_with("\"`") {
            self.push(Mode::MdString, self.at, "\"`");
            self.at += 2;
        } else if rest.starts_with('"') {
            self.push(Mode::String, self.at, "\"");
            self.at += 1;
        } else {
            return false;
        }
        true
    }

    fn space_block(&mut self, rest: &'a str) -> bool {
        if !rest.starts_with("space") {
            return false;
        }
        let i = "space".len();
        if byte_at(rest, i) == Some(b':') {
            let digits = digit_len(&rest[i + 1..]);
            if digits > 0 {
                self.value("SPACE_BLOCK", i + 1 + digits, &rest[i + 1..i + 1 + digits]);
                return true;
            }
        }
        if boundary(rest, i) {
            self.value("SPACE_BLOCK", i, "1");
            return true;
        }
        false
    }

    fn plain_keyword(&mut self, rest: &'a str) -> bool {
        const WORDS: [(&str, &str); 3] = [
            ("default", "DEFAULT"),
            ("linkStyle", "LINKSTYLE"),
            ("interpolate", "INTERPOLATE"),
        ];
        let Some((word, kind)) = WORDS.iter().find(|(word, _)| keyword(rest, word)) else {
            return false;
        };
        self.emit(kind, word.len());
        true
    }

    fn statement_keyword(&mut self, rest: &'a str) -> bool {
        const WORDS: [(&str, Mode); 3] = [
            ("classDef", Mode::ClassDef),
            ("class", Mode::Class),
            ("style", Mode::StyleStatement),
        ];
        for (word, mode) in WORDS {
            if !rest.starts_with(word) {
                continue;
            }
            let gap = space_len(&rest[word.len()..]);
            if gap > 0 {
                self.push(mode, self.at, word);
                self.emit(word, word.len() + gap);
                return true;
            }
        }
        false
    }

    fn accessibility(&mut self, rest: &'a str) -> bool {
        const WORDS: [(&str, Mode, &str); 2] = [
            ("accTitle", Mode::AccTitle, "acc_title"),
            ("accDescr", Mode::AccDescr, "acc_descr"),
        ];
        for (word, mode, kind) in WORDS {
            if !rest.starts_with(word) {
                continue;
            }
            let mut i = word.len() + space_len(&rest[word.len()..]);
            if byte_at(rest, i) == Some(b':') {
                i += 1 + space_len(&rest[i + 1..]);
                self.push(mode, self.at, word);
                self.emit(kind, i);
                return true;
            }
            if mode == Mode::AccDescr && byte_at(rest, i) == Some(b'{') {
                i += 1 + space_len(&rest[i + 1..]);
                self.push(Mode::AccDescrMultiline, self.at, word);
                self.at += i;
                return true;
            }
        }
        false
    }

    fn end_keyword(&mut self, rest: &'a str) -> bool {
        if !keyword(rest, "end") {
            return false;
        }
        self.emit("end", "end".len() + space_len(&rest["end".len()..]));
        true
    }

    fn shape_opener(&mut self, rest: &'a str) -> bool {
        if let Some(opener) = OPENERS.iter().find(|opener| rest.starts_with(**opener)) {
            self.push(Mode::Node, self.at, opener);
            self.emit("NODE_DSTART", opener.len());
            return true;
        }
        if rest.starts_with("<[") {
            self.push(Mode::BlockArrow, self.at, "<[");
            self.emit("BLOCK_ARROW_START", 2);
            return true;
        }
        false
    }

    fn node_identifier(&mut self, rest: &'a str) -> bool {
        let n = rest
            .char_indices()
            .find(|&(_, c)| node_excluded(c))
            .map_or(rest.len(), |(i, _)| i);
        if n == 0 {
            return false;
        }
        self.emit("NODE_ID", n);
        true
    }

    fn size(&mut self, rest: &'a str) -> bool {
        if rest.len() < 2 || !rest.starts_with(':') {
            return false;
        }
        let digits = digit_len(&rest[1..]);
        if digits == 0 {
            return false;
        }
        self.value("SIZE", 1 + digits, &rest[1..1 + digits]);
        true
    }

    fn link(&mut self, rest: &'a str) -> bool {
        let n = link_len(rest);
        if n > 0 {
            self.emit("LINK", n);
            return true;
        }
        let n = start_link_len(rest);
        if n > 0 {
            self.push(Mode::LinkLabel, self.at, rest[..n].trim());
            self.emit("START_LINK", n);
            return true;
        }
        false
    }

    fn string_mode(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with('"') {
            self.at += 1;
            self.pop();
            return true;
        }
        let n = rest.find('"').unwrap_or(rest.len());
        self.emit("STR", n);
        true
    }

    fn md_string_mode(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with("`\"") {
            self.at += 2;
            self.pop();
            return true;
        }
        let n = rest.bytes().take_while(|&b| b != b'`' && b != b'"').count();
        if n == 0 {
            return false;
        }
        self.emit("MD_STR", n);
        true
    }

    fn node_mode(&mut self) -> bool {
        let rest = self.rest();
        if let Some(closer) = CLOSERS.iter().find(|closer| rest.starts_with(**closer)) {
            self.emit("NODE_DEND", closer.len());
            self.pop();
            return true;
        }
        self.open_quote(rest)
    }

    fn block_arrow_mode(&mut self) -> bool {
        let rest = self.rest();
        if self.open_quote(rest) {
            return true;
        }
        if !rest.starts_with("]>") {
            return false;
        }
        let i = 2 + space_len(&rest[2..]);
        if byte_at(rest, i) != Some(b'(') {
            return false;
        }
        self.push(Mode::ArrowDir, self.top().opener, "<[");
        self.at += i + 1;
        true
    }

    fn arrow_dir_mode(&mut self) -> bool {
        let rest = self.rest();
        let mut i = usize::from(rest.starts_with(','));
        i += space_len(&rest[i..]);
        if let Some(name) = DIRECTIONS.iter().find(|name| rest[i..].starts_with(**name)) {
            let length = name.len() + space_len(&rest[i + name.len()..]);
            self.at += i;
            self.value("DIR", length, name);
            return true;
        }
        if !rest.starts_with(')') {
            return false;
        }
        self.value("BLOCK_ARROW_END", 1 + space_len(&rest[1..]), "]>");
        self.pop();
        self.pop();
        true
    }

    fn link_label_mode(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with("\"`") {
            self.push(Mode::MdString, self.at, "\"`");
            self.at += 2;
            return true;
        }
        if rest.starts_with('"') {
            self.push(Mode::String, self.at, "\"");
            self.emit("LINK_LABEL", 1);
            return true;
        }
        let n = link_len(rest);
        if n == 0 {
            return false;
        }
        self.emit("LINK", n);
        self.pop();
        true
    }

    fn id_list_mode(&mut self) -> bool {
        let n = id_list_len(self.rest());
        if n == 0 {
            return false;
        }
        let opener = self.top().opener;
        let (kind, next) = if self.top().mode == Mode::StyleStatement {
            ("STYLE_ENTITY_IDS", Mode::StyleDefinition)
        } else {
            ("CLASSENTITY_IDS", Mode::ClassStyle)
        };
        self.pop();
        self.push(next, opener, "");
        self.emit(kind, n);
        true
    }

    fn class_def_mode(&mut self) -> bool {
        let (kind, n) = class_def_id(self.rest());
        if n == 0 {
            return false;
        }
        let opener = self.top().opener;
        self.pop();
        self.push(Mode::ClassDefId, opener, "");
        self.emit(kind, n);
        true
    }

    fn remainder(&mut self, kind: &'static str) -> bool {
        self.emit(kind, line_len(self.rest()));
        self.pop();
        true
    }

    fn acc_descr_multiline(&mut self) -> bool {
        let rest = self.rest();
        if rest.starts_with('}') {
            self.at += 1;
            self.pop();
            return true;
        }
        let n = rest.find('}').unwrap_or(rest.len());
        self.emit("acc_descr_multiline_value", n);
        true
    }
}
