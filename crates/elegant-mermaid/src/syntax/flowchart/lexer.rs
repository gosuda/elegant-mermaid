mod edge_shape_rules;
mod matchers;
mod statement_rules;
mod text_rules;
mod unicode;

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
    matcher: fn(&Lexer<'_>, usize) -> Option<usize>,
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
        self.removed
            .get(self.rm)
            .filter(|s| self.pos < s.start)
            .map_or(self.src.len(), |s| s.start)
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
            let Some(end) = (r.matcher)(self, n) else {
                continue;
            };
            if end > n || end == self.pos && !r.empty {
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
            let (text, brs) = replace_line_ends(&self.src.as_bytes()[start..end]);
            token.text = TextVal::Owned(text);
            token.brs = brs;
            self.keep(token);
            return;
        }
        token.string_open = self.open_quote;
        if matches!(kind, TokenKind::Str | TokenKind::MdStr) {
            if self.first_cont.is_some() {
                token.split_continuation = true;
            } else {
                self.first_cont = Some(self.tokens.len());
            }
            self.last_cont = Some(self.tokens.len());
        }
        self.keep(token);
    }
    fn text_value(&self, span: Span) -> TextVal {
        if self.src.get(span.start..span.end).is_some() {
            TextVal::Slice(span)
        } else {
            TextVal::Owned(
                String::from_utf8_lossy(&self.src.as_bytes()[span.start..span.end]).into_owned(),
            )
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
