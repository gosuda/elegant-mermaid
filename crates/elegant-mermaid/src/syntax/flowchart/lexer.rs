mod edge_shape_rules;
mod matchers;
mod statement_rules;
mod text_rules;
mod unicode;

use std::borrow::Cow;

use super::diagnostic;
use super::tokens::{BRPoint, Mode, TextVal, Token, TokenKind};
use crate::diag::{Diagnostic, Severity};
use crate::source::Span;

pub(crate) const C_UNEXPECTED_TOKEN: &str = "flowchart/unexpected-token";
pub(crate) struct Lexed {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
    pub eof_quote: Option<usize>,
    pub eof_label: Option<Span>,
    pub eof_shape: Option<Span>,
    pub eof_acc: Option<Span>,
}
#[derive(Clone, Copy)]
struct Frame {
    mode: Mode,
    open: Span,
}
#[derive(Clone, Copy)]
enum Act {
    None,
    OpenString,
    OpenMDString,
    CloseString,
    CloseMDString,
    ShapeOpen,
    ShapeRun,
    Graph,
    AccBlockOpen,
    AccBlockClose,
    LeaveOnly,
    BeginCallbackArgs,
}
struct Rule {
    matcher: fn(&mut Lexer<'_>, usize) -> Option<usize>,
    kind: Option<TokenKind>,
    act: Act,
    push: Option<Mode>,
    pop: bool,
    empty: bool,
    modes: u32,
}
pub(crate) struct Lexer<'a> {
    src: &'a str,
    removed: &'a [Span],
    pos: usize,
    rm: usize,
    frames: Vec<Frame>,
    tokens: Vec<Token>,
    diagnostics: Vec<Diagnostic>,
    graph_seen: bool,
    silent: bool,
    open_quote: Option<usize>,
    first_cont: Option<usize>,
    last_cont: Option<usize>,
    reach: usize,
}
pub(crate) fn lex_all(src: &str, removed: &[Span]) -> Lexed {
    Lexer::new(src, removed).collect()
}
impl<'a> Lexer<'a> {
    pub(crate) fn new(src: &'a str, removed: &'a [Span]) -> Self {
        Self {
            src,
            removed,
            pos: 0,
            rm: 0,
            frames: vec![Frame {
                mode: Mode::Initial,
                open: Span { start: 0, end: 0 },
            }],
            tokens: Vec::new(),
            diagnostics: Vec::new(),
            graph_seen: false,
            silent: false,
            open_quote: None,
            first_cont: None,
            last_cont: None,
            reach: 0,
        }
    }
    fn mode(&self) -> Mode {
        self.frames.last().map_or(Mode::Initial, |f| f.mode)
    }
    fn push(&mut self, mode: Mode, open: Span) {
        self.frames.push(Frame { mode, open });
    }
    fn pop(&mut self) {
        if self.frames.len() > 1 {
            self.frames.pop();
        }
    }
    fn skip_removed(&mut self) {
        loop {
            while self.rm < self.removed.len() && self.removed[self.rm].end <= self.pos {
                self.rm += 1;
            }
            let Some(s) = self.removed.get(self.rm) else {
                return;
            };
            if self.pos < s.start {
                return;
            }
            self.pos = s.end;
        }
    }
    fn limit(&self) -> usize {
        self.limit_at(self.pos)
    }
    fn removed_from(&self, p: usize) -> usize {
        let mut j = self.rm;
        while j < self.removed.len() && self.removed[j].end <= p {
            j += 1;
        }
        j
    }
    fn limit_at(&self, p: usize) -> usize {
        let j = self.removed_from(p);
        if j < self.removed.len() && p < self.removed[j].start {
            return self.removed[j].start;
        }
        self.src.len()
    }
    fn skip_removed_at(&self, p: usize) -> usize {
        let j = self.removed_from(p);
        if j < self.removed.len() && p >= self.removed[j].start {
            return self.removed[j].end;
        }
        p
    }
    /// Advances `pos` over bytes that satisfy `pred`, hopping whole removed spans
    /// when the run reaches one; a removed `%%` comment line is invisible to the
    /// run, so a token that spans lines continues across it.
    fn run_while(
        &mut self,
        mut pos: usize,
        mut limit: usize,
        mut pred: impl FnMut(u8) -> bool,
    ) -> (usize, usize) {
        loop {
            while pos < limit && pred(self.src.as_bytes()[pos]) {
                pos += 1;
            }
            if pos < limit || limit >= self.src.len() {
                return (pos, limit);
            }
            let next = self.skip_removed_at(pos);
            if next == pos {
                return (pos, limit);
            }
            pos = next;
            limit = self.limit_at(pos);
            self.reach = self.reach.max(limit);
        }
    }
    fn run_nonempty(&mut self, limit: usize, pred: impl FnMut(u8) -> bool) -> Option<usize> {
        let (end, _) = self.run_while(self.pos, limit, pred);
        (end > self.pos).then_some(end)
    }
    /// Skips `js_space` bytes, hopping whole removed spans; a jison `\s` run treats
    /// a removed `%%` comment line exactly like the blank line it blanks out.
    fn skip_space(&mut self, pos: usize, limit: usize) -> (usize, usize) {
        self.run_while(pos, limit, js_space)
    }
    fn space_end(&mut self, pos: usize, limit: usize) -> usize {
        self.skip_space(pos, limit).0
    }
    fn space_follows(&self, mut pos: usize, limit: usize) -> bool {
        if pos >= limit {
            pos = self.skip_removed_at(pos);
        }
        pos < self.src.len() && js_space(self.src.as_bytes()[pos])
    }
    fn collect(mut self) -> Lexed {
        loop {
            self.skip_removed();
            if self.pos >= self.src.len() {
                break;
            }
            if self.step().is_none() {
                self.unexpected();
            }
        }
        let mut out = Lexed {
            tokens: Vec::new(),
            diagnostics: Vec::new(),
            eof_quote: self.open_quote,
            eof_label: None,
            eof_shape: None,
            eof_acc: None,
        };
        for f in &self.frames {
            match f.mode {
                Mode::Text | Mode::EllipseText | Mode::TrapText => {
                    if out.eof_label.is_none() {
                        out.eof_label = Some(f.open);
                    }
                }
                Mode::ShapeData => out.eof_shape = Some(f.open),
                Mode::AccDescrMultiline => out.eof_acc = Some(f.open),
                _ => {}
            }
        }
        self.keep(Token::new(
            TokenKind::Eof,
            Span {
                start: self.pos,
                end: self.pos,
            },
            TextVal::None,
        ));
        out.tokens = self.tokens;
        out.diagnostics = self.diagnostics;
        out
    }
    fn step(&mut self) -> Option<Option<TokenKind>> {
        let n = self.limit();
        for r in rules() {
            if r.modes & (1 << self.mode() as u32) == 0 {
                continue;
            }
            self.reach = n;
            let Some(end) = (r.matcher)(self, n) else {
                continue;
            };
            if end > self.reach || end == self.pos && !r.empty {
                continue;
            }
            self.emit(r, end);
            return Some(r.kind);
        }
        None
    }
    fn keep(&mut self, t: Token) {
        if !self.silent {
            self.tokens.push(t);
        }
    }
    fn report(&mut self, span: Span, raw: &str, names: &[&str]) {
        if self.silent {
            return;
        }
        self.diagnostics.push(diagnostic(
            C_UNEXPECTED_TOKEN,
            Severity::Error,
            format!("unexpected {raw}, expected one of: {}", names.join(", ")),
            span,
        ));
    }
    fn emit(&mut self, r: &Rule, end: usize) {
        let start = self.pos;
        self.pos = end;
        let span = Span { start, end };
        match r.act {
            Act::OpenString | Act::OpenMDString => {
                if self.mode() == Mode::CallbackName && matches!(r.act, Act::OpenString) {
                    self.report(
                        span,
                        self.src.get(start..end).unwrap_or(""),
                        &["CALLBACKNAME"],
                    );
                }
                self.open_quote = Some(start);
                self.push(
                    if matches!(r.act, Act::OpenString) {
                        Mode::Stringlit
                    } else {
                        Mode::MdString
                    },
                    span,
                );
                return;
            }
            Act::CloseString | Act::CloseMDString => {
                self.end_string(end);
                return;
            }
            Act::AccBlockOpen => {
                self.push(Mode::AccDescrMultiline, span);
                return;
            }
            Act::AccBlockClose | Act::LeaveOnly => {
                self.pop();
                return;
            }
            Act::BeginCallbackArgs => {
                self.pop();
                self.push(Mode::CallbackArgs, span);
                return;
            }
            _ => {}
        }
        if matches!(r.act, Act::ShapeOpen) {
            self.push(Mode::ShapeData, span);
        }
        if matches!(r.act, Act::Graph) && !self.graph_seen {
            self.graph_seen = true;
            self.push(Mode::Dir, span);
        }
        if let Some(mode) = r.push {
            self.push(mode, span);
        }
        if r.pop {
            self.pop();
        }
        self.finish_emit(r, span);
    }

    fn finish_emit(&mut self, r: &Rule, span: Span) {
        let Span { start, end } = span;
        let Some(kind) = r.kind else { return };
        let text = if matches!(r.act, Act::ShapeOpen) {
            TextVal::None
        } else {
            self.text_value(span)
        };
        let mut token = Token::new(kind, span, text);
        if matches!(r.act, Act::ShapeRun) {
            let (text, brs) = replace_line_ends(self.clean_text(start, end).as_bytes());
            token.text = TextVal::Owned(text);
            token.brs = brs;
            self.keep(token);
            return;
        }
        token.string_open = self.open_quote;
        if matches!(kind, TokenKind::Str | TokenKind::MdStr) {
            if self.first_cont.is_none() {
                self.first_cont = Some(self.tokens.len());
            }
            self.last_cont = Some(self.tokens.len());
        }
        self.keep(token);
    }
    /// The source text of `start..end` without the removed spans inside it.
    fn clean_text(&self, start: usize, end: usize) -> Cow<'a, str> {
        let src: &'a str = self.src;
        let mut j = self.removed_from(start);
        if j >= self.removed.len() || self.removed[j].start >= end {
            return Cow::Borrowed(src.get(start..end).unwrap_or(""));
        }
        let mut out = String::new();
        let mut at = start;
        while j < self.removed.len() && self.removed[j].start < end {
            out.push_str(&src[at..self.removed[j].start]);
            at = self.removed[j].end;
            j += 1;
        }
        if at < end {
            out.push_str(&src[at..end]);
        }
        Cow::Owned(out)
    }
    fn text_value(&self, span: Span) -> TextVal {
        if span.start >= span.end {
            return TextVal::None;
        }
        match self.clean_text(span.start, span.end) {
            Cow::Borrowed(_) => TextVal::Slice(span),
            Cow::Owned(out) => TextVal::Owned(out),
        }
    }
    fn end_string(&mut self, end: usize) {
        let open = self.open_quote;
        self.pop();
        self.open_quote = None;
        if let (Some(first), Some(last)) = (self.first_cont, self.last_cont)
            && !self.silent
        {
            self.tokens[first].span.start = open.unwrap_or(0);
            self.tokens[last].span.end = end;
            self.first_cont = None;
            self.last_cont = None;
            return;
        }
        self.first_cont = None;
        self.last_cont = None;
        self.keep(Token::new(
            TokenKind::Str,
            Span {
                start: open.unwrap_or(0),
                end,
            },
            TextVal::None,
        ));
    }
    fn unexpected(&mut self) {
        let start = self.pos;
        let n = self.limit();
        let size = self
            .src
            .get(start..n)
            .and_then(|s| s.chars().next())
            .map_or(1, char::len_utf8);
        let mut names: Vec<&str> = rules()
            .filter(|r| r.modes & (1 << self.mode() as u32) != 0)
            .filter_map(|r| r.kind.map(TokenKind::as_str))
            .collect();
        names.sort_unstable();
        names.dedup();
        self.report(
            Span {
                start,
                end: start + size,
            },
            self.src.get(start..start + size).unwrap_or("�"),
            &names,
        );
        self.frames.truncate(1);
        self.open_quote = None;
        self.first_cont = None;
        self.last_cont = None;
        self.pos = self.skip_to_boundary(start);
        self.skip_removed();
    }
    fn skip_to_boundary(&mut self, from: usize) -> usize {
        let frames = std::mem::replace(
            &mut self.frames,
            vec![Frame {
                mode: Mode::Initial,
                open: Span { start: 0, end: 0 },
            }],
        );
        self.pos = from;
        self.silent = true;
        let end = loop {
            self.skip_removed();
            if self.pos >= self.src.len() {
                break self.src.len();
            }
            let start = self.pos;
            match self.step() {
                None => self.pos = start + 1,
                Some(kind)
                    if self.frames.len() == 1
                        && matches!(kind, Some(TokenKind::Newline | TokenKind::Semi)) =>
                {
                    break start;
                }
                _ => {}
            }
        };
        self.silent = false;
        self.frames = frames;
        end
    }
}

fn js_space(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\r' | b'\x0c' | b'\x0b')
}
fn horizontal_space(b: u8) -> bool {
    matches!(b, b' ' | b'\t')
}
fn marker_start(b: u8) -> bool {
    matches!(b, b'x' | b'o' | b'<')
}
fn marker_end(b: u8) -> bool {
    matches!(b, b'x' | b'o' | b'>')
}
fn line_end(src: &[u8], p: usize) -> Option<usize> {
    match src.get(p) {
        Some(b'\n') => Some(p + 1),
        Some(b'\r') => Some(p + 1 + usize::from(src.get(p + 1) == Some(&b'\n'))),
        _ => None,
    }
}
fn replace_line_ends(src: &[u8]) -> (String, Vec<BRPoint>) {
    let mut bytes = Vec::with_capacity(src.len());
    let mut brs = Vec::new();
    let mut p = 0;
    while p < src.len() {
        if let Some(end) = line_end(src, p) {
            brs.push(BRPoint {
                text: bytes.len(),
                src: p,
            });
            bytes.extend_from_slice(b"<br/>");
            p = end;
            while p < src.len() && horizontal_space(src[p]) {
                p += 1;
            }
        } else {
            bytes.push(src[p]);
            p += 1;
        }
    }
    (String::from_utf8_lossy(&bytes).into_owned(), brs)
}

fn rules() -> impl Iterator<Item = &'static Rule> {
    text_rules::RULES
        .iter()
        .chain(statement_rules::RULES)
        .chain(edge_shape_rules::RULES)
}
