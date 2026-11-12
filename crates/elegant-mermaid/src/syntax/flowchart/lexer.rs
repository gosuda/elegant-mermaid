//! The mode-driven lexer of the flowchart grammar, `flowchart-015` to `flowchart-029`.
//!
//! Rules run in the order of the tables of `spec/grammar/flowchart.md`, and the first
//! rule that matches at the current byte wins (`flowchart-017`, `flowchart-105`). A
//! rule that produces no token consumes its bytes and returns `None`.

use crate::diag::{Diagnostic, Edit, Fix, FixSafety, Severity};
use crate::source::Span;
use crate::syntax::flowchart::diagnostic;
use crate::syntax::flowchart::tokens::{Mode, TextVal, Token, TokenKind};

pub(crate) const C_UNEXPECTED_TOKEN: &str = "flowchart/unexpected-token";
const C_DIR_INVALID: &str = "flowchart/dir-invalid";
const C_DIR_KW_INVALID: &str = "flowchart/dir-kw-invalid";
const C_LABEL_ESCAPED_QUOTE: &str = "flowchart/label-escaped-quote";
const C_LABEL_DOUBLE_IN_SINGLE: &str = "flowchart/label-double-in-single";
const C_UNCLOSED_BRACKET: &str = "flowchart/unclosed-node-bracket";
const C_QUOTE_UNCLOSED: &str = "flowchart/quote-unclosed";
const C_UNTERMINATED: &str = "flowchart/unterminated";

/// One frame of the mode stack; `opener` is the span of the token that pushed it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct OpenMode {
    pub mode: Mode,
    pub opener: Span,
    pub label: bool,
}

/// The lexer with its mode stack, skipped-span table and diagnostics.
pub(crate) struct Lexer<'a> {
    src: &'a str,
    removed: &'a [Span],
    pos: usize,
    stack: Vec<OpenMode>,
    stmt_start: bool,
    first_graph: bool,
    diags: Vec<Diagnostic>,
    blocks: Vec<Span>,
}

impl<'a> Lexer<'a> {
    pub(crate) fn new(src: &'a str, removed: &'a [Span]) -> Lexer<'a> {
        Lexer {
            src,
            removed,
            pos: 0,
            stack: Vec::new(),
            stmt_start: true,
            first_graph: true,
            diags: Vec::new(),
            blocks: Vec::new(),
        }
    }

    pub(crate) fn into_diags(self) -> Vec<Diagnostic> {
        self.diags
    }

    pub(crate) fn raw(&self, span: Span) -> &'a str {
        self.src.get(span.start..span.end).unwrap_or("")
    }

    /// The single diagnostic for anything still open when the input ends.
    pub(crate) fn end_state(&self) -> Option<Diagnostic> {
        let eof = self.src.len();
        if let Some(frame) = self
            .stack
            .iter()
            .find(|frame| matches!(frame.mode, Mode::Text | Mode::EllipseText | Mode::TrapText))
        {
            let opener = self.raw(frame.opener);
            let mut diagnostic = diagnostic(
                C_UNCLOSED_BRACKET,
                Severity::Error,
                format!("node bracket {opener} is never closed"),
                Span {
                    start: frame.opener.start,
                    end: eof,
                },
            );
            diagnostic.fixes.push(Fix {
                title: String::from("Add the closing bracket"),
                safety: FixSafety::Unsafe,
                edits: vec![Edit {
                    span: Span {
                        start: eof,
                        end: eof,
                    },
                    new_text: String::from(closer_for(opener)),
                }],
            });
            return Some(diagnostic);
        }
        if let Some(frame) = self
            .stack
            .iter()
            .find(|frame| matches!(frame.mode, Mode::Stringlit | Mode::MdString))
        {
            return Some(diagnostic(
                C_QUOTE_UNCLOSED,
                Severity::Error,
                String::from("A node label opens a quote but never closes it"),
                Span {
                    start: frame.opener.start,
                    end: eof,
                },
            ));
        }
        if let Some(frame) = self
            .stack
            .iter()
            .find(|frame| frame.mode == Mode::ShapeData)
        {
            return Some(diagnostic(
                C_UNTERMINATED,
                Severity::Error,
                String::from("unterminated @{"),
                Span {
                    start: frame.opener.start,
                    end: eof,
                },
            ));
        }
        let block = *self.blocks.last()?;
        Some(diagnostic(
            C_UNTERMINATED,
            Severity::Error,
            String::from("unterminated accDescr {"),
            Span {
                start: block.start,
                end: eof,
            },
        ))
    }

    fn skip_gaps(&self, mut pos: usize) -> usize {
        loop {
            let i = self.removed.partition_point(|s| s.end <= pos);
            match self.removed.get(i) {
                Some(span) if span.start <= pos && pos < span.end => pos = span.end,
                _ => return pos.min(self.src.len()),
            }
        }
    }

    fn at(&self, pos: usize) -> Option<u8> {
        self.src.as_bytes().get(pos).copied()
    }

    fn char_at(&self, pos: usize) -> Option<char> {
        self.src.get(pos..).and_then(|s| s.chars().next())
    }

    fn next_visible(&self, pos: usize) -> usize {
        let len = self.char_at(pos).map_or(1, char::len_utf8);
        self.skip_gaps(pos + len)
    }

    fn next_char(&self, pos: usize) -> Option<char> {
        self.char_at(self.next_visible(pos))
    }

    fn match_lit(&self, mut pos: usize, literal: &str) -> Option<usize> {
        for byte in literal.bytes() {
            if self.at(pos) != Some(byte) {
                return None;
            }
            pos = self.next_visible(pos);
        }
        Some(pos)
    }

    fn ws_star(&self, mut pos: usize) -> usize {
        while let Some(c) = self.char_at(pos) {
            if !is_ws(c) {
                break;
            }
            pos = self.next_visible(pos);
        }
        pos
    }

    fn ws_plus(&self, pos: usize) -> Option<usize> {
        let end = self.ws_star(pos);
        (end > pos).then_some(end)
    }

    fn line_end(&self, pos: usize) -> Option<usize> {
        match self.at(pos) {
            Some(b'\r') => {
                let after = self.next_visible(pos);
                if self.at(after) == Some(b'\n') {
                    Some(self.next_visible(after))
                } else {
                    Some(after)
                }
            }
            Some(b'\n') => Some(self.next_visible(pos)),
            _ => None,
        }
    }

    fn push(&mut self, mode: Mode, opener: Span, label: bool) {
        self.stack.push(OpenMode {
            mode,
            opener,
            label,
        });
    }

    fn pop(&mut self) {
        self.stack.pop();
    }

    fn mode(&self) -> Mode {
        self.stack.last().map_or(Mode::Initial, |frame| frame.mode)
    }

    fn top_label(&self) -> bool {
        self.stack.last().is_some_and(|frame| frame.label)
    }

    fn opener_start(&self, fallback: usize) -> usize {
        self.stack
            .last()
            .map_or(fallback, |frame| frame.opener.start)
    }

    fn run_while<F>(&self, from: usize, pred: F) -> (String, bool, usize)
    where
        F: Fn(char) -> bool,
    {
        let mut out = String::new();
        let mut pos = from;
        let mut end = from;
        let mut bridged = false;
        while let Some(c) = self.char_at(pos) {
            if !pred(c) {
                break;
            }
            if self.next_visible(pos) > pos + c.len_utf8() {
                bridged = true;
            }
            out.push(c);
            end = pos + c.len_utf8();
            pos = self.next_visible(pos);
        }
        (out, bridged, end)
    }

    fn value(start: usize, end: usize, text: String, bridged: bool) -> TextVal {
        if bridged {
            TextVal::Owned(text)
        } else {
            TextVal::Slice(Span { start, end })
        }
    }

    fn finish(&mut self, kind: TokenKind, start: usize, end: usize, text: TextVal) -> Token {
        self.pos = self.skip_gaps(end);
        match kind {
            TokenKind::Newline | TokenKind::Semi | TokenKind::Nodir | TokenKind::End => {
                self.stmt_start = true;
            }
            TokenKind::Space => {}
            _ => self.stmt_start = false,
        }
        Token::new(kind, Span { start, end }, text)
    }

    /// Consumes `end` for a rule that produces no token, as `flowchart-023` states.
    fn consumed(&mut self, end: usize) {
        self.pos = self.skip_gaps(end);
        self.stmt_start = false;
    }

    fn record(&mut self, code: &'static str, span: Span, message: String) {
        self.diags
            .push(diagnostic(code, Severity::Error, message, span));
    }

    /// Drops every open mode, jumps to the statement boundary after `from`, and returns it.
    pub(crate) fn abort_to_boundary(&mut self, from: usize) -> usize {
        let end = self.statement_boundary(from);
        self.stack.clear();
        self.stmt_start = true;
        self.pos = if end < self.src.len() {
            self.next_visible(end)
        } else {
            end
        };
        end
    }

    /// The first `;` or line end outside a string, a bracket pair, a label and shape data.
    pub(crate) fn statement_boundary(&self, from: usize) -> usize {
        let mut pos = from;
        let mut in_string = false;
        let mut in_shape = false;
        let mut shape_string = false;
        let mut pipe = false;
        let mut brackets: Vec<&'static str> = Vec::new();
        while let Some(c) = self.char_at(pos) {
            let after = self.next_visible(pos);
            if in_shape {
                match c {
                    '"' => shape_string = !shape_string,
                    '}' if !shape_string => in_shape = false,
                    _ => {}
                }
                pos = after;
                continue;
            }
            if in_string {
                if c == '"' {
                    in_string = false;
                }
                pos = after;
                continue;
            }
            match c {
                '"' => in_string = true,
                '@' if self.at(after) == Some(b'{') => {
                    in_shape = true;
                    shape_string = false;
                    pos = self.next_visible(after);
                    continue;
                }
                '|' => pipe = !pipe,
                '[' | '(' | '{' => {
                    let (closer, end) = self.opener_closer(pos, c);
                    brackets.push(closer);
                    pos = end;
                    continue;
                }
                ']' | ')' | '}' => {
                    if let Some(closer) = brackets.last().copied()
                        && closer.starts_with(c)
                        && self.closer_at(pos, closer)
                    {
                        brackets.pop();
                        if closer.len() == 2 {
                            pos = self.next_visible(after);
                            continue;
                        }
                    }
                }
                ';' | '\n' | '\r' if !pipe && brackets.is_empty() => return pos,
                _ => {}
            }
            pos = after;
        }
        self.src.len()
    }

    fn opener_closer(&self, pos: usize, first: char) -> (&'static str, usize) {
        let after = self.next_visible(pos);
        let second = self.char_at(after);
        match (first, second) {
            ('[', Some('[')) => ("]]", self.next_visible(after)),
            ('[', Some('(')) => (")]", self.next_visible(after)),
            ('[', Some('|')) => ("]", after),
            ('(', Some('(')) => ("))", self.next_visible(after)),
            ('{', Some('{')) => ("}}", self.next_visible(after)),
            ('[', _) => ("]", after),
            ('(', _) => (")", after),
            _ => ("}", after),
        }
    }

    fn closer_at(&self, pos: usize, closer: &str) -> bool {
        let mut q = pos;
        for byte in closer.bytes() {
            if self.at(q) != Some(byte) {
                return false;
            }
            q = self.next_visible(q);
        }
        true
    }

    fn eof(&self) -> Token {
        let pos = self.src.len();
        Token::new(
            TokenKind::Eof,
            Span {
                start: pos,
                end: pos,
            },
            TextVal::None,
        )
    }

    pub(crate) fn next_token(&mut self) -> Token {
        loop {
            self.pos = self.skip_gaps(self.pos);
            if self.pos >= self.src.len() {
                return self.eof();
            }
            let before = self.pos;
            let produced = match self.mode() {
                Mode::Initial => self.lex_initial(before),
                Mode::Dir => self.lex_dir(before),
                Mode::AccTitle | Mode::AccDescr => self.lex_acc_value(before),
                Mode::AccDescrMultiline => self.lex_acc_multiline(before),
                Mode::Stringlit => self.lex_string(before),
                Mode::MdString => self.lex_md_string(before),
                Mode::Click => self.lex_click(before),
                Mode::CallbackName => self.lex_callback_name(before),
                Mode::CallbackArgs => self.lex_callback_args(before),
                Mode::Text => self.lex_text(before),
                Mode::EllipseText => self.lex_ellipse_text(before),
                Mode::TrapText => self.lex_trap_text(before),
                Mode::EdgeText | Mode::ThickEdgeText | Mode::DottedEdgeText => {
                    self.lex_edge_text(before)
                }
                Mode::ShapeData => self.lex_shape_data(before),
                Mode::ShapeDataStr => self.lex_shape_data_str(before),
            };
            if let Some(token) = produced {
                return token;
            }
            if self.pos == before {
                self.pos = self.next_visible(before);
            }
        }
    }

    fn unmatched(&mut self, mode: Mode, start: usize) -> Option<Token> {
        let end = self.next_visible(start);
        let raw = self.raw(Span { start, end });
        let mut names: Vec<&'static str> = mode_kinds(mode).iter().map(|k| k.as_str()).collect();
        names.sort_unstable();
        names.dedup();
        self.record(
            C_UNEXPECTED_TOKEN,
            Span { start, end },
            format!("unexpected {raw}, expected one of: {}", names.join(", ")),
        );
        let boundary = self.abort_to_boundary(start);
        Some(Token::new(
            TokenKind::Newline,
            Span {
                start: boundary,
                end: boundary,
            },
            TextVal::None,
        ))
    }

    fn lex_initial(&mut self, p: usize) -> Option<Token> {
        self.try_acc(p)
            .or_else(|| self.try_shape_data_open(p))
            .or_else(|| self.try_call(p))
            .or_else(|| self.try_quote(p))
            .or_else(|| self.try_keyword(p))
            .or_else(|| self.try_href(p))
            .or_else(|| self.try_click(p))
            .or_else(|| self.try_header(p))
            .or_else(|| self.try_block_keyword(p))
            .or_else(|| self.try_direction_stmt(p))
            .or_else(|| self.try_link_id(p))
            .or_else(|| self.try_punct(p))
            .or_else(|| self.try_link(p))
            .or_else(|| self.try_opener(p))
            .or_else(|| self.try_angle(p))
            .or_else(|| self.try_node_string(p))
            .or_else(|| self.try_minus(p))
            .or_else(|| self.try_unicode_text(p))
            .or_else(|| self.try_loose_opener(p))
            .or_else(|| self.whitespace(p))
            .or_else(|| self.unmatched(Mode::Initial, p))
    }

    fn simple_token(&mut self, kind: TokenKind, p: usize) -> Option<Token> {
        let end = self.next_visible(p);
        Some(self.finish(kind, p, end, TextVal::Slice(Span { start: p, end })))
    }

    fn try_acc(&mut self, p: usize) -> Option<Token> {
        if self.title_rule(p).is_some() {
            return self.simple_token(TokenKind::AccTitle, p);
        }
        let kw_end = self.match_lit(p, "accDescr")?;
        let colon = self.ws_star(kw_end);
        if self.at(colon) == Some(b':') {
            let end = self.ws_star(self.next_visible(colon));
            let span = Span { start: p, end };
            let token = self.finish(TokenKind::AccDescr, p, end, TextVal::Slice(span));
            self.push(Mode::AccDescr, span, false);
            return Some(token);
        }
        let brace = self.ws_star(kw_end);
        if self.at(brace) != Some(b'{') {
            return None;
        }
        let end = self.ws_star(self.next_visible(brace));
        let span = Span { start: p, end };
        self.push(Mode::AccDescrMultiline, span, false);
        self.blocks.push(span);
        self.consumed(end);
        None
    }

    fn title_rule(&self, p: usize) -> Option<usize> {
        let kw_end = self.match_lit(p, "accTitle")?;
        let colon = self.ws_star(kw_end);
        if self.at(colon) != Some(b':') {
            return None;
        }
        Some(self.ws_star(self.next_visible(colon)))
    }

    fn try_shape_data_open(&mut self, p: usize) -> Option<Token> {
        let end = self.match_lit(p, "@{")?;
        let token = self.finish(TokenKind::ShapeData, p, end, TextVal::None);
        self.push(Mode::ShapeData, Span { start: p, end }, false);
        Some(token)
    }

    fn try_call(&mut self, p: usize) -> Option<Token> {
        let kw = self.match_lit(p, "call")?;
        let end = self.ws_plus(kw)?;
        self.push(Mode::CallbackName, Span { start: p, end }, false);
        self.consumed(end);
        None
    }

    fn try_quote(&mut self, p: usize) -> Option<Token> {
        if self.at(p) != Some(b'"') {
            return None;
        }
        let after = self.next_visible(p);
        let (mode, end) = if self.at(after) == Some(b'`') {
            (Mode::MdString, self.next_visible(after))
        } else {
            (Mode::Stringlit, after)
        };
        let label = self.top_label();
        self.push(mode, Span { start: p, end }, label);
        self.consumed(end);
        None
    }

    fn try_keyword(&mut self, p: usize) -> Option<Token> {
        for (lit, kind) in [
            ("style", TokenKind::Style),
            ("default", TokenKind::Default),
            ("linkStyle", TokenKind::LinkStyle),
            ("interpolate", TokenKind::Interpolate),
            ("classDef", TokenKind::ClassDef),
            ("class", TokenKind::Class),
        ] {
            if let Some(end) = self.match_lit(p, lit) {
                let span = Span { start: p, end };
                return Some(self.finish(kind, p, end, TextVal::Slice(span)));
            }
        }
        None
    }

    fn try_href(&mut self, p: usize) -> Option<Token> {
        let kw = self.match_lit(p, "href")?;
        let end = self.ws_plus(kw)?;
        let span = Span { start: p, end };
        Some(self.finish(TokenKind::Href, p, end, TextVal::Slice(span)))
    }

    fn try_click(&mut self, p: usize) -> Option<Token> {
        let kw = self.match_lit(p, "click")?;
        let end = self.ws_plus(kw)?;
        self.push(Mode::Click, Span { start: p, end }, false);
        self.consumed(end);
        None
    }

    fn try_header(&mut self, p: usize) -> Option<Token> {
        for lit in ["flowchart-elk", "graph", "flowchart"] {
            if let Some(end) = self.match_lit(p, lit) {
                let span = Span { start: p, end };
                let token = self.finish(TokenKind::Graph, p, end, TextVal::Slice(span));
                if self.first_graph {
                    self.first_graph = false;
                    self.push(Mode::Dir, span, false);
                }
                return Some(token);
            }
        }
        None
    }

    fn try_block_keyword(&mut self, p: usize) -> Option<Token> {
        if let Some(end) = self.match_lit(p, "subgraph") {
            let span = Span { start: p, end };
            return Some(self.finish(TokenKind::Subgraph, p, end, TextVal::Slice(span)));
        }
        if let Some(tok) = self.try_end(p) {
            return Some(tok);
        }
        for lit in ["_self", "_blank", "_parent", "_top"] {
            if let Some(end) = self.match_lit(p, lit) {
                let span = Span { start: p, end };
                return Some(self.finish(TokenKind::LinkTarget, p, end, TextVal::Slice(span)));
            }
        }
        None
    }

    fn try_end(&mut self, p: usize) -> Option<Token> {
        let kw = self.match_lit(p, "end")?;
        if let Some(c) = self.char_at(kw)
            && (c.is_ascii_alphanumeric() || c == '_')
        {
            return None;
        }
        let mut end = kw;
        while matches!(self.at(end), Some(b' ' | b'\t')) {
            end += 1;
        }
        let span = Span { start: p, end };
        Some(self.finish(TokenKind::End, p, end, TextVal::Slice(span)))
    }

    fn try_direction_stmt(&mut self, p: usize) -> Option<Token> {
        let (kind, end) = self.direction_stmt(p)?;
        let span = Span { start: p, end };
        Some(self.finish(kind, p, end, TextVal::Slice(span)))
    }

    fn direction_stmt(&self, p: usize) -> Option<(TokenKind, usize)> {
        if !self.stmt_start {
            return None;
        }
        let mut found = None;
        let mut q = p;
        while let Some(c) = self.char_at(q) {
            if matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}') {
                break;
            }
            if let Some(end) = self.direction_at(q) {
                found = Some(end);
            }
            q = self.next_visible(q);
        }
        found
    }

    fn direction_at(&self, p: usize) -> Option<(TokenKind, usize)> {
        let kw = self.match_lit(p, "direction")?;
        let after = self.ws_plus(kw)?;
        for (code, kind) in [
            ("TB", TokenKind::DirectionTb),
            ("BT", TokenKind::DirectionBt),
            ("RL", TokenKind::DirectionRl),
            ("LR", TokenKind::DirectionLr),
            ("TD", TokenKind::DirectionTd),
        ] {
            if let Some(end) = self.match_lit(after, code) {
                return Some((kind, self.to_line_feed(end)));
            }
        }
        None
    }

    fn to_line_feed(&self, from: usize) -> usize {
        let mut q = from;
        while let Some(c) = self.char_at(q) {
            if c == '\n' {
                break;
            }
            q = self.next_visible(q);
        }
        q
    }

    fn try_link_id(&mut self, p: usize) -> Option<Token> {
        let end = self.link_id(p)?;
        let span = Span { start: p, end };
        Some(self.finish(TokenKind::LinkId, p, end, TextVal::Slice(span)))
    }

    fn link_id(&self, p: usize) -> Option<usize> {
        let mut ats = Vec::new();
        let mut q = p;
        while let Some(c) = self.char_at(q) {
            if !link_id_char(c) {
                break;
            }
            if c == '@' {
                ats.push(q);
            }
            q = self.next_visible(q);
        }
        for at in ats.into_iter().rev() {
            let after = self.next_visible(at);
            if !matches!(self.at(after), Some(b'{') | Some(b'"')) {
                return Some(after);
            }
        }
        None
    }

    fn try_punct(&mut self, p: usize) -> Option<Token> {
        if let Some(end) = self.digits(p) {
            let span = Span { start: p, end };
            return Some(self.finish(TokenKind::Num, p, end, TextVal::Slice(span)));
        }
        if let Some(end) = self.match_lit(p, ":::") {
            let span = Span { start: p, end };
            return Some(self.finish(TokenKind::StyleSeparator, p, end, TextVal::Slice(span)));
        }
        let kind = match self.at(p)? {
            b'#' => TokenKind::Brkt,
            b':' => TokenKind::Colon,
            b'&' => TokenKind::Amp,
            b';' => TokenKind::Semi,
            b',' => TokenKind::Comma,
            b'*' => TokenKind::Mult,
            _ => return None,
        };
        self.simple_token(kind, p)
    }

    fn digits(&self, p: usize) -> Option<usize> {
        let (_, _, end) = self.run_while(p, |c| c.is_ascii_digit());
        (end > p).then_some(end)
    }

    fn try_link(&mut self, p: usize) -> Option<Token> {
        if let Some(end) = [self.normal_link(p), self.thick_link(p), self.dotted_link(p)]
            .into_iter()
            .flatten()
            .next()
        {
            let span = Span { start: p, end };
            return Some(self.finish(TokenKind::Link, p, end, TextVal::Slice(span)));
        }
        if let Some(end) = self.tilde_link(p) {
            let span = Span { start: p, end };
            return Some(self.finish(TokenKind::Link, p, end, TextVal::Slice(span)));
        }
        for mode in [Mode::EdgeText, Mode::ThickEdgeText, Mode::DottedEdgeText] {
            if let Some(end) = self.start_link(p, mode) {
                let span = Span { start: p, end };
                let token = self.finish(TokenKind::StartLink, p, end, TextVal::Slice(span));
                self.push(mode, span, false);
                return Some(token);
            }
        }
        None
    }

    fn edge_prefix(&self, pos: usize) -> usize {
        let p = self.ws_star(pos);
        match self.at(p) {
            Some(b'x') | Some(b'o') | Some(b'<') => self.next_visible(p),
            _ => p,
        }
    }

    fn normal_link(&self, pos: usize) -> Option<usize> {
        let body = self.edge_prefix(pos);
        let dashes = self.count_run(body, '-');
        if dashes < 2 {
            return None;
        }
        let p = self.advance(body, dashes);
        match self.at(p) {
            Some(b'-') | Some(b'x') | Some(b'o') | Some(b'>') => {
                Some(self.ws_star(self.next_visible(p)))
            }
            _ => None,
        }
    }

    fn thick_link(&self, pos: usize) -> Option<usize> {
        let body = self.edge_prefix(pos);
        let run = self.count_run(body, '=');
        if run < 2 {
            return None;
        }
        let p = self.advance(body, run);
        match self.at(p) {
            Some(b'=') | Some(b'x') | Some(b'o') | Some(b'>') => {
                Some(self.ws_star(self.next_visible(p)))
            }
            _ => None,
        }
    }

    fn dotted_link(&self, pos: usize) -> Option<usize> {
        let body = self.edge_prefix(pos);
        let mut p = body;
        if self.at(p) == Some(b'-') {
            p = self.next_visible(p);
        }
        let dots = self.count_run(p, '.');
        if dots < 1 {
            return None;
        }
        p = self.advance(p, dots);
        if self.at(p) != Some(b'-') {
            return None;
        }
        p = self.next_visible(p);
        if matches!(self.at(p), Some(b'x') | Some(b'o') | Some(b'>')) {
            p = self.next_visible(p);
        }
        Some(self.ws_star(p))
    }

    fn tilde_link(&self, pos: usize) -> Option<usize> {
        let body = self.ws_star(pos);
        let run = self.count_run(body, '~');
        if run < 3 {
            return None;
        }
        Some(self.ws_star(self.advance(body, run)))
    }

    fn start_link(&self, pos: usize, mode: Mode) -> Option<usize> {
        let body = self.edge_prefix(self.ws_star(pos));
        match mode {
            Mode::ThickEdgeText => {
                (self.count_run(body, '=') == 2).then(|| self.ws_star(self.advance(body, 2)))
            }
            Mode::DottedEdgeText => {
                if self.at(body) == Some(b'-') {
                    let dot = self.next_visible(body);
                    if self.at(dot) == Some(b'.') {
                        return Some(self.ws_star(dot));
                    }
                }
                None
            }
            _ => (self.count_run(body, '-') == 2).then(|| self.ws_star(self.advance(body, 2))),
        }
    }

    fn advance(&self, from: usize, count: usize) -> usize {
        let mut q = from;
        for _ in 0..count {
            q = self.next_visible(q);
        }
        q
    }

    fn count_run(&self, from: usize, byte: char) -> usize {
        let mut count = 0;
        let mut p = from;
        while self.char_at(p) == Some(byte) {
            count += 1;
            p = self.next_visible(p);
        }
        count
    }

    fn try_opener(&mut self, p: usize) -> Option<Token> {
        const OPENERS: [(&str, TokenKind, Mode); 8] = [
            ("(-", TokenKind::EllipseStart, Mode::EllipseText),
            ("([", TokenKind::StadiumStart, Mode::Text),
            ("[[", TokenKind::SubroutineStart, Mode::Text),
            ("[(", TokenKind::CylinderStart, Mode::Text),
            ("(((", TokenKind::DoubleCircleStart, Mode::Text),
            ("[/", TokenKind::TrapStart, Mode::TrapText),
            ("[\\", TokenKind::InvTrapStart, Mode::TrapText),
            ("[|", TokenKind::VertexWithPropsStart, Mode::Text),
        ];
        for (lit, kind, mode) in OPENERS {
            if let Some(end) = self.match_lit(p, lit) {
                let span = Span { start: p, end };
                let token = self.finish(kind, p, end, TextVal::Slice(span));
                self.push(mode, span, true);
                return Some(token);
            }
        }
        if let Some(end) = self.match_lit(p, ">") {
            let span = Span { start: p, end };
            let token = self.finish(TokenKind::TagEnd, p, end, TextVal::Slice(span));
            self.push(Mode::Text, span, true);
            return Some(token);
        }
        None
    }

    fn try_angle(&mut self, p: usize) -> Option<Token> {
        let kind = match self.at(p)? {
            b'<' => TokenKind::TagStart,
            b'^' => TokenKind::Up,
            b'v' => TokenKind::Down,
            _ => return None,
        };
        self.simple_token(kind, p)
    }

    fn try_node_string(&mut self, p: usize) -> Option<Token> {
        let mut q = p;
        let mut end = p;
        while let Some(c) = self.char_at(q) {
            if !word_char(self, q, c) {
                break;
            }
            end = q + c.len_utf8();
            q = self.next_visible(q);
        }
        if end == p {
            return None;
        }
        let span = Span { start: p, end };
        Some(self.finish(TokenKind::NodeString, p, end, TextVal::Slice(span)))
    }

    fn try_minus(&mut self, p: usize) -> Option<Token> {
        if self.at(p) != Some(b'-') {
            return None;
        }
        self.simple_token(TokenKind::Minus, p)
    }

    fn try_unicode_text(&mut self, p: usize) -> Option<Token> {
        let c = self.char_at(p)?;
        if !unicode_text(c) {
            return None;
        }
        self.simple_token(TokenKind::UnicodeText, p)
    }

    fn try_loose_opener(&mut self, p: usize) -> Option<Token> {
        let kind = match self.at(p)? {
            b'|' => TokenKind::Pipe,
            b'(' => TokenKind::Ps,
            b'[' => TokenKind::Sqs,
            b'{' => TokenKind::DiamondStart,
            _ => return None,
        };
        let end = self.next_visible(p);
        let span = Span { start: p, end };
        let token = self.finish(kind, p, end, TextVal::Slice(span));
        self.push(Mode::Text, span, false);
        Some(token)
    }

    fn whitespace(&mut self, p: usize) -> Option<Token> {
        if self.line_end(p).is_some() {
            let mut q = p;
            while let Some(end) = self.line_end(q) {
                q = end;
            }
            let span = Span { start: p, end: q };
            return Some(self.finish(TokenKind::Newline, p, q, TextVal::Slice(span)));
        }
        let (_, _, end) = self.run_while(p, |c| is_ws(c) && c != '\n' && c != '\r');
        (end > p).then(|| {
            let span = Span { start: p, end };
            self.finish(TokenKind::Space, p, end, TextVal::Slice(span))
        })
    }

    fn lex_dir(&mut self, p: usize) -> Option<Token> {
        if let Some(end) = self.nodir_end(p) {
            let span = Span { start: p, end };
            return Some(self.finish(TokenKind::Nodir, p, end, TextVal::Slice(span)));
        }
        if let Some((_, end)) = self.direction_keyword(p) {
            let span = Span { start: p, end };
            let token = self.finish(TokenKind::Dir, p, end, TextVal::Slice(span));
            self.pop();
            return Some(token);
        }
        self.dir_failure(p)
    }

    fn nodir_end(&self, p: usize) -> Option<usize> {
        if p >= self.src.len() {
            return Some(p);
        }
        let mut q = p;
        let mut last = None;
        loop {
            if let Some(end) = self.line_end(q) {
                last = Some(end);
                q = end;
                continue;
            }
            match self.char_at(q) {
                Some(c) if is_ws(c) && c != '\n' && c != '\r' => q = self.next_visible(q),
                _ => break,
            }
        }
        last
    }

    fn direction_keyword(&self, p: usize) -> Option<(char, usize)> {
        let body = self.ws_star(p);
        for (code, lit) in [
            ('L', "LR"),
            ('R', "RL"),
            ('T', "TB"),
            ('B', "BT"),
            ('D', "TD"),
            ('B', "BR"),
            ('<', "<"),
            ('>', ">"),
            ('^', "^"),
            ('v', "v"),
        ] {
            if let Some(end) = self.match_lit(body, lit) {
                return Some((code, end));
            }
        }
        None
    }

    fn dir_failure(&mut self, p: usize) -> Option<Token> {
        let start = self.ws_star(p);
        let (_, _, end) = self.run_while(start, |c| !is_ws(c) && c != ';');
        let span = if end > start {
            Span { start, end }
        } else {
            Span {
                start,
                end: self.next_visible(start),
            }
        };
        let kw_later = self.later_direction_word(span.end);
        let (code, message) = if kw_later {
            (
                C_DIR_KW_INVALID,
                "An unknown keyword appears before the direction token",
            )
        } else {
            (
                C_DIR_INVALID,
                "The direction token after the header is not one of TD, TB, BT, RL, LR",
            )
        };
        let mut diagnostic = diagnostic(code, Severity::Error, message.to_owned(), span);
        if kw_later {
            let cut = self.trailing_space(span.end);
            diagnostic.fixes.push(Fix {
                title: String::from("Remove the unknown keyword"),
                safety: FixSafety::Safe,
                edits: vec![Edit {
                    span: Span {
                        start: span.start,
                        end: cut,
                    },
                    new_text: String::new(),
                }],
            });
        }
        self.diags.push(diagnostic);
        let boundary = self.abort_to_boundary(p);
        Some(Token::new(
            TokenKind::Newline,
            Span {
                start: boundary,
                end: boundary,
            },
            TextVal::None,
        ))
    }

    fn trailing_space(&self, from: usize) -> usize {
        match self.char_at(from) {
            Some(c) if is_ws(c) && c != '\n' && c != '\r' => self.next_visible(from),
            _ => from,
        }
    }

    fn later_direction_word(&self, from: usize) -> bool {
        let mut q = from;
        while let Some(c) = self.char_at(q) {
            if matches!(c, '\n' | '\r' | ';') {
                return false;
            }
            if is_ws(c) {
                q = self.next_visible(q);
                continue;
            }
            let (_, _, end) = self.run_while(q, |c| !is_ws(c) && c != ';');
            if is_direction_word(self.raw(Span { start: q, end })) {
                return true;
            }
            q = end;
        }
        false
    }

    fn lex_acc_value(&mut self, p: usize) -> Option<Token> {
        let (_, _, end) = self.run_while(p, |c| !matches!(c, '\n' | '\r' | ';' | '#'));
        let span = Span { start: p, end };
        let kind = match self.mode() {
            Mode::AccTitle => TokenKind::AccTitleValue,
            _ => TokenKind::AccDescrValue,
        };
        let token = self.finish(kind, p, end, TextVal::Slice(span));
        self.pop();
        Some(token)
    }

    fn lex_acc_multiline(&mut self, p: usize) -> Option<Token> {
        if self.at(p) == Some(b'}') {
            let end = self.next_visible(p);
            self.pop();
            self.consumed(end);
            return None;
        }
        let (_, _, end) = self.run_while(p, |c| c != '}');
        let span = Span { start: p, end };
        Some(self.finish(
            TokenKind::AccDescrMultilineValue,
            p,
            end,
            TextVal::Slice(span),
        ))
    }

    fn lex_string(&mut self, p: usize) -> Option<Token> {
        if self.at(p) == Some(b'"') {
            let after = self.next_visible(p);
            self.pop();
            self.consumed(after);
            return None;
        }
        let (text, bridged, end) = self.run_while(p, |c| c != '"');
        let open = self.opener_start(p);
        if text.ends_with('\\') && self.top_label() {
            let close = if self.at(end) == Some(b'"') {
                self.next_visible(end)
            } else {
                end
            };
            self.record(
                C_LABEL_ESCAPED_QUOTE,
                Span {
                    start: end.saturating_sub(1),
                    end: close,
                },
                String::from(
                    "A node label contains a backslash-escaped quote, which Mermaid does not support",
                ),
            );
            let token = self.finish(TokenKind::Str, open, close, TextVal::Owned(text));
            self.pop();
            return Some(token);
        }
        let value = Lexer::value(p, end, text, bridged);
        Some(self.finish(TokenKind::Str, open, end, value))
    }

    fn lex_md_string(&mut self, p: usize) -> Option<Token> {
        if self.at(p) == Some(b'`') && self.at(self.next_visible(p)) == Some(b'"') {
            let end = self.next_visible(self.next_visible(p));
            self.pop();
            self.consumed(end);
            return None;
        }
        if self.at(p) == Some(b'"') {
            let after = self.next_visible(p);
            self.record(
                C_LABEL_DOUBLE_IN_SINGLE,
                Span {
                    start: p,
                    end: after,
                },
                String::from("A single-quoted label contains an unescaped double quote"),
            );
            let owned = self
                .raw(Span {
                    start: p,
                    end: after,
                })
                .to_owned();
            return Some(self.finish(TokenKind::MdStr, p, after, TextVal::Owned(owned)));
        }
        let (text, bridged, end) = self.run_while(p, |c| c != '"' && c != '`');
        if end == p {
            return self.unmatched(Mode::MdString, p);
        }
        let open = self.opener_start(p);
        let value = Lexer::value(p, end, text, bridged);
        Some(self.finish(TokenKind::MdStr, open, end, value))
    }

    fn lex_click(&mut self, p: usize) -> Option<Token> {
        if self.char_at(p).is_some_and(is_ws) {
            let end = self.next_visible(p);
            self.pop();
            self.consumed(end);
            return None;
        }
        let (text, bridged, end) = self.run_while(p, |c| !is_ws(c));
        if end == p {
            return self.unmatched(Mode::Click, p);
        }
        let value = Lexer::value(p, end, text, bridged);
        Some(self.finish(TokenKind::Click, p, end, value))
    }

    fn lex_callback_name(&mut self, p: usize) -> Option<Token> {
        if self.at(p) == Some(b'(') {
            let after = self.next_visible(p);
            let close = self.ws_star(after);
            if self.at(close) == Some(b')') {
                let end = self.next_visible(close);
                self.pop();
                self.consumed(end);
                return None;
            }
            self.pop();
            self.push(
                Mode::CallbackArgs,
                Span {
                    start: p,
                    end: after,
                },
                false,
            );
            self.consumed(after);
            return None;
        }
        let (text, bridged, end) = self.run_while(p, |c| c != '(');
        if end == p {
            return self.unmatched(Mode::CallbackName, p);
        }
        let value = Lexer::value(p, end, text, bridged);
        Some(self.finish(TokenKind::CallbackName, p, end, value))
    }

    fn lex_callback_args(&mut self, p: usize) -> Option<Token> {
        if self.at(p) == Some(b')') {
            let end = self.next_visible(p);
            self.pop();
            self.consumed(end);
            return None;
        }
        let (text, bridged, end) = self.run_while(p, |c| c != ')');
        if end == p {
            return self.unmatched(Mode::CallbackArgs, p);
        }
        let value = Lexer::value(p, end, text, bridged);
        Some(self.finish(TokenKind::CallbackArgs, p, end, value))
    }

    fn lex_text(&mut self, p: usize) -> Option<Token> {
        if let Some(tok) = self.text_closer(p) {
            return Some(tok);
        }
        if let Some(tok) = self.shared_opener(p) {
            return Some(tok);
        }
        let (text, bridged, end) = self.run_while(p, |c| !"[\\](){}|\"".contains(c));
        if end == p {
            return self.unmatched(Mode::Text, p);
        }
        let value = Lexer::value(p, end, text, bridged);
        Some(self.finish(TokenKind::Text, p, end, value))
    }

    fn text_closer(&mut self, p: usize) -> Option<Token> {
        for (lit, kind) in [
            ("])", TokenKind::StadiumEnd),
            ("]]", TokenKind::SubroutineEnd),
            (")]", TokenKind::CylinderEnd),
            (")))", TokenKind::DoubleCircleEnd),
        ] {
            if let Some(end) = self.match_lit(p, lit) {
                let span = Span { start: p, end };
                let token = self.finish(kind, p, end, TextVal::Slice(span));
                self.pop();
                return Some(token);
            }
        }
        let kind = match self.at(p)? {
            b'|' => TokenKind::Pipe,
            b')' => TokenKind::Pe,
            b']' => TokenKind::Sqe,
            b'}' => TokenKind::DiamondStop,
            _ => return None,
        };
        let end = self.next_visible(p);
        let span = Span { start: p, end };
        let token = self.finish(kind, p, end, TextVal::Slice(span));
        self.pop();
        Some(token)
    }

    fn shared_opener(&mut self, p: usize) -> Option<Token> {
        if self.at(p) == Some(b'"') {
            let after = self.next_visible(p);
            let (mode, end) = if self.at(after) == Some(b'`') {
                (Mode::MdString, self.next_visible(after))
            } else {
                (Mode::Stringlit, after)
            };
            let label = self.top_label();
            self.push(mode, Span { start: p, end }, label);
            self.consumed(end);
            return None;
        }
        for (lit, kind, label) in [
            ("(-", TokenKind::EllipseStart, true),
            ("([", TokenKind::StadiumStart, true),
            ("[[", TokenKind::SubroutineStart, true),
            ("[(", TokenKind::CylinderStart, true),
            ("(((", TokenKind::DoubleCircleStart, true),
            ("[/", TokenKind::TrapStart, true),
            ("[\\", TokenKind::InvTrapStart, true),
            ("(", TokenKind::Ps, true),
            ("[|", TokenKind::VertexWithPropsStart, true),
            ("|", TokenKind::Pipe, false),
            ("[", TokenKind::Sqs, true),
            ("{", TokenKind::DiamondStart, true),
            (">", TokenKind::TagEnd, true),
        ] {
            if let Some(end) = self.match_lit(p, lit) {
                let span = Span { start: p, end };
                let token = self.finish(kind, p, end, TextVal::Slice(span));
                self.push(opener_mode(kind), span, label);
                return Some(token);
            }
        }
        None
    }

    fn lex_ellipse_text(&mut self, p: usize) -> Option<Token> {
        if let Some(end) = self.ellipse_end(p) {
            self.pop();
            let span = Span { start: p, end };
            return Some(self.finish(TokenKind::EllipseEnd, p, end, TextVal::Slice(span)));
        }
        if let Some(tok) = self.shared_opener(p) {
            return Some(tok);
        }
        let (text, bridged, end) = self.run_while(p, |c| !"()[]{}".contains(c));
        if end == p {
            return self.unmatched(Mode::EllipseText, p);
        }
        let value = Lexer::value(p, end, text, bridged);
        Some(self.finish(TokenKind::Text, p, end, value))
    }

    fn ellipse_end(&self, p: usize) -> Option<usize> {
        match self.at(p) {
            Some(b'-') | Some(b'/') => {
                let after = self.next_visible(p);
                (self.at(after) == Some(b')')).then_some(self.next_visible(after))
            }
            _ => None,
        }
    }

    fn lex_trap_text(&mut self, p: usize) -> Option<Token> {
        if let Some(tok) = self.trap_end(p) {
            return Some(tok);
        }
        if let Some(tok) = self.shared_opener(p) {
            return Some(tok);
        }
        let (text, bridged, end) = self.run_while(p, |c| !"\\[](){}".contains(c) && c != '/');
        if end > p {
            let value = Lexer::value(p, end, text, bridged);
            return Some(self.finish(TokenKind::Text, p, end, value));
        }
        match self.char_at(p) {
            Some('\\') | Some('/') => {
                let next = self.next_visible(p);
                let span = Span {
                    start: p,
                    end: next,
                };
                Some(self.finish(TokenKind::Text, p, next, TextVal::Slice(span)))
            }
            _ => self.unmatched(Mode::TrapText, p),
        }
    }

    fn trap_end(&mut self, p: usize) -> Option<Token> {
        for (first, kind) in [('/', TokenKind::InvTrapEnd), ('\\', TokenKind::TrapEnd)] {
            if self.char_at(p) == Some(first) {
                let after = self.next_visible(p);
                if self.at(after) != Some(b']') {
                    return None;
                }
                let end = self.next_visible(after);
                let span = Span { start: p, end };
                let token = self.finish(kind, p, end, TextVal::Slice(span));
                self.pop();
                return Some(token);
            }
        }
        if self.at(p) == Some(b']') {
            let end = self.next_visible(p);
            let span = Span { start: p, end };
            let token = self.finish(TokenKind::TrapEnd, p, end, TextVal::Slice(span));
            self.pop();
            return Some(token);
        }
        None
    }

    fn lex_edge_text(&mut self, p: usize) -> Option<Token> {
        let mode = self.mode();
        if let Some(end) = self.edge_link(p, mode) {
            let span = Span { start: p, end };
            let token = self.finish(TokenKind::Link, p, end, TextVal::Slice(span));
            self.pop();
            return Some(token);
        }
        if self.at(p) == Some(b'"') {
            let after = self.next_visible(p);
            let (next_mode, end) = if self.at(after) == Some(b'`') {
                (Mode::MdString, self.next_visible(after))
            } else {
                (Mode::Stringlit, after)
            };
            self.push(next_mode, Span { start: p, end }, false);
            self.consumed(end);
            return None;
        }
        let blocked = match mode {
            Mode::ThickEdgeText => '=',
            Mode::DottedEdgeText => '.',
            _ => '-',
        };
        let (text, bridged, end) = self.run_while(p, |c| c != blocked && !is_ws(c));
        if end > p {
            let value = Lexer::value(p, end, text, bridged);
            return Some(self.finish(TokenKind::EdgeText, p, end, value));
        }
        let c = self.char_at(p)?;
        if c == blocked && !self.escapable(p, mode) {
            return self.unmatched(mode, p);
        }
        let next = self.next_visible(p);
        let span = Span {
            start: p,
            end: next,
        };
        Some(self.finish(TokenKind::EdgeText, p, next, TextVal::Slice(span)))
    }

    fn edge_link(&self, p: usize, mode: Mode) -> Option<usize> {
        match mode {
            Mode::ThickEdgeText => self.thick_link(p),
            Mode::DottedEdgeText => self.dotted_link(p),
            _ => self.normal_link(p),
        }
    }

    fn escapable(&self, p: usize, mode: Mode) -> bool {
        match mode {
            Mode::ThickEdgeText => self.next_char(p) != Some('='),
            Mode::DottedEdgeText => self.next_char(p) != Some('-'),
            _ => self.next_char(p) != Some('-'),
        }
    }

    fn lex_shape_data(&mut self, p: usize) -> Option<Token> {
        if self.at(p) == Some(b'"') {
            let end = self.next_visible(p);
            let span = Span { start: p, end };
            let token = self.finish(TokenKind::ShapeData, p, end, TextVal::Slice(span));
            self.push(Mode::ShapeDataStr, span, false);
            return Some(token);
        }
        if self.at(p) == Some(b'}') {
            let end = self.next_visible(p);
            let token = self.finish(TokenKind::ShapeData, p, end, TextVal::None);
            self.pop();
            return Some(token);
        }
        let (text, bridged, end) = self.run_while(p, |c| !matches!(c, '}' | '"' | '^'));
        if end == p {
            return self.unmatched(Mode::ShapeData, p);
        }
        let value = Lexer::value(p, end, text, bridged);
        Some(self.finish(TokenKind::ShapeData, p, end, value))
    }

    fn lex_shape_data_str(&mut self, p: usize) -> Option<Token> {
        if self.at(p) == Some(b'"') {
            let end = self.next_visible(p);
            let span = Span { start: p, end };
            let token = self.finish(TokenKind::ShapeData, p, end, TextVal::Slice(span));
            self.pop();
            return Some(token);
        }
        let (text, bridged, end) = self.run_while(p, |c| c != '"');
        if end == p {
            return self.unmatched(Mode::ShapeDataStr, p);
        }
        let replaced = replace_line_breaks(&text);
        let value = if bridged || replaced != text {
            TextVal::Owned(replaced)
        } else {
            TextVal::Slice(Span { start: p, end })
        };
        Some(self.finish(TokenKind::ShapeData, p, end, value))
    }
}

fn closer_for(opener: &str) -> &'static str {
    match opener {
        "(" => ")",
        "(-" => "-)",
        "([" => "])",
        "[[" => "]]",
        "[(" => ")]",
        "(((" => ")))",
        "[/" => "\\]",
        "[\\" => "/]",
        "{" => "}",
        _ => "]",
    }
}

fn word_char(lexer: &Lexer<'_>, q: usize, c: char) -> bool {
    match c {
        'A'..='Z' | 'a'..='z' | '0'..='9' => true,
        '!' | '"' | '#' | '$' | '%' | '&' | '\'' | '*' | '+' | '.' | '`' | '?' | '\\' | '_'
        | '/' => true,
        '-' => matches!(lexer.next_char(q), Some(next)
            if next != '>' && next != '-' && next != '.'),
        '=' => lexer.next_char(q) != Some('='),
        _ => false,
    }
}

fn replace_line_breaks(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\n' {
            out.push_str("<br/>");
            while chars.peek().is_some_and(|next| is_ws(*next)) {
                chars.next();
            }
        } else {
            out.push(c);
        }
    }
    out
}

fn is_direction_word(word: &str) -> bool {
    matches!(
        word,
        "LR" | "RL" | "TB" | "BT" | "TD" | "BR" | "<" | ">" | "^" | "v"
    )
}

fn is_ws(c: char) -> bool {
    c.is_whitespace()
}

fn link_id_char(c: char) -> bool {
    !(is_ws(c) || matches!(c, '"' | '[' | ']' | '(' | ')' | '{' | '}' | '|'))
}

fn opener_mode(kind: TokenKind) -> Mode {
    match kind {
        TokenKind::EllipseStart => Mode::EllipseText,
        TokenKind::TrapStart | TokenKind::InvTrapStart => Mode::TrapText,
        _ => Mode::Text,
    }
}

fn unicode_text(c: char) -> bool {
    !c.is_ascii() && (c.is_alphabetic() || c.is_numeric())
}

fn mode_kinds(mode: Mode) -> &'static [TokenKind] {
    use TokenKind::*;
    match mode {
        Mode::Initial => &[
            AccTitle,
            AccTitleValue,
            AccDescr,
            AccDescrValue,
            AccDescrMultilineValue,
            Amp,
            Brkt,
            Class,
            ClassDef,
            Click,
            Colon,
            Comma,
            CylinderStart,
            Default,
            DiamondStart,
            Dir,
            DoubleCircleStart,
            Down,
            EllipseStart,
            End,
            Eof,
            Graph,
            Href,
            InvTrapStart,
            Interpolate,
            Link,
            LinkId,
            LinkStyle,
            LinkTarget,
            Minus,
            Mult,
            Newline,
            NodeString,
            Nodir,
            Num,
            Pipe,
            Ps,
            Semi,
            ShapeData,
            Space,
            Sqs,
            StartLink,
            Style,
            StyleSeparator,
            Subgraph,
            TagEnd,
            TagStart,
            TrapStart,
            UnicodeText,
            Up,
        ],
        Mode::Dir => &[Dir, Eof, Newline, Nodir, Space],
        Mode::AccTitle => &[AccTitleValue],
        Mode::AccDescr => &[AccDescrValue],
        Mode::AccDescrMultiline => &[AccDescrMultilineValue],
        Mode::Stringlit => &[Str],
        Mode::MdString => &[MdStr],
        Mode::Click => &[Click],
        Mode::CallbackName => &[CallbackName],
        Mode::CallbackArgs => &[CallbackArgs],
        Mode::Text => &[
            CylinderEnd,
            CylinderStart,
            DiamondStart,
            DiamondStop,
            DoubleCircleEnd,
            DoubleCircleStart,
            EllipseStart,
            InvTrapStart,
            MdStr,
            Pe,
            Pipe,
            Ps,
            Sqe,
            Sqs,
            StadiumEnd,
            StadiumStart,
            Str,
            SubroutineEnd,
            SubroutineStart,
            TagEnd,
            Text,
            TrapStart,
        ],
        Mode::EllipseText => &[
            CylinderStart,
            DiamondStart,
            DoubleCircleStart,
            EllipseEnd,
            EllipseStart,
            InvTrapStart,
            MdStr,
            Ps,
            Sqs,
            StadiumStart,
            Str,
            SubroutineStart,
            TagEnd,
            Text,
            TrapStart,
        ],
        Mode::TrapText => &[
            CylinderStart,
            DiamondStart,
            DoubleCircleStart,
            EllipseStart,
            InvTrapEnd,
            InvTrapStart,
            MdStr,
            Ps,
            Sqs,
            StadiumStart,
            Str,
            SubroutineStart,
            TagEnd,
            Text,
            TrapEnd,
            TrapStart,
        ],
        Mode::EdgeText | Mode::ThickEdgeText | Mode::DottedEdgeText => {
            &[EdgeText, Link, MdStr, Str]
        }
        Mode::ShapeData => &[ShapeData],
        Mode::ShapeDataStr => &[ShapeData],
    }
}
