use super::ast::*;
use super::lexer::lex_all;
use super::tokens::{TextVal, Token, TokenKind as K, is_alpha_num_token};
use crate::diag::{Diagnostic, Edit, Fix, FixSafety, Severity};
use crate::source::Span;

pub struct Parsed {
    pub document: Document,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EndState {
    Clean,
    Bracket,
    Unterminated,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StatementEnd {
    Clean,
    Broken,
}

struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    end: EndState,
    depth: usize,
}

pub fn parse(src: &str, removed: &[Span]) -> Parsed {
    let lexed = lex_all(src, removed);
    let mut p = Parser {
        src,
        tokens: lexed.tokens,
        i: 0,
        diags: lexed.diagnostics,
        end: EndState::Clean,
        depth: 0,
    };
    let config = p.header();
    let lines = p.statements();
    let document = Document {
        span: Span {
            start: 0,
            end: src.len(),
        },
        config,
        lines,
    };
    match p.end {
        EndState::Unterminated => {
            if let Some(span) = lexed.eof_shape {
                p.token_diag(
                    "flowchart/unterminated",
                    Span {
                        start: span.start,
                        end: src.len(),
                    },
                    "@{",
                );
            }
            if let Some(span) = lexed.eof_acc {
                p.token_diag(
                    "flowchart/unterminated",
                    Span {
                        start: span.start,
                        end: src.len(),
                    },
                    "{",
                );
            }
        }
        EndState::Bracket => {
            if let Some(span) = lexed.eof_label {
                p.token_diag(
                    "flowchart/unclosed-node-bracket",
                    Span {
                        start: span.start,
                        end: src.len(),
                    },
                    src.get(span.start..span.end).unwrap_or(""),
                );
            }
        }
        EndState::Clean => {
            if let Some(start) = lexed.eof_quote {
                p.plain(
                    "flowchart/quote-unclosed",
                    Span {
                        start,
                        end: src.len(),
                    },
                );
            }
        }
    }
    attach_fixes(src, &mut p.diags);
    crate::diag::sort(&mut p.diags);
    Parsed {
        document,
        diagnostics: p.diags,
    }
}

impl Parser<'_> {
    fn peek(&self) -> Token {
        self.tokens.get(self.i).cloned().unwrap_or_else(|| {
            Token::new(
                K::Eof,
                Span {
                    start: self.src.len(),
                    end: self.src.len(),
                },
                TextVal::None,
            )
        })
    }
    fn at(&self, kind: K) -> bool {
        self.peek().kind == kind
    }
    fn any(&self, kinds: &[K]) -> bool {
        kinds.contains(&self.peek().kind)
    }
    fn next(&mut self) -> Token {
        let token = self.peek();
        if self.i < self.tokens.len() {
            self.i += 1;
        }
        token
    }
    fn accept(&mut self, kind: K) -> Option<Token> {
        if self.at(kind) {
            Some(self.next())
        } else {
            None
        }
    }
    fn text(&self, token: &Token) -> String {
        token.text(self.src).to_owned()
    }
    fn skip_spaces(&mut self) {
        while self.at(K::Space) {
            self.next();
        }
    }
    fn trivia(&mut self) {
        while self.any(&[K::Space, K::Newline, K::Semi]) {
            self.next();
        }
    }
    fn boundary(&self) -> bool {
        self.any(&[K::Eof, K::Newline, K::Semi])
    }
    fn recover(&mut self) {
        while !self.boundary() {
            self.next();
        }
    }
    fn last_end(&self) -> usize {
        self.i
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or(self.peek().span.start, |t| t.span.end)
    }
    fn plain(&mut self, code: &'static str, span: Span) {
        self.token_diag(code, span, "TOKEN");
    }
    fn token_diag(&mut self, code: &'static str, span: Span, token: &str) {
        let (message, help) = diagnostic_row(code);
        let mut d = super::diagnostic(code, Severity::Error, message.replace("TOKEN", token), span);
        d.help = help.to_owned();
        self.diags.push(d);
    }
    fn unexpected(&mut self, names: &[&str]) {
        let token = self.peek();
        let message = format!(
            "unexpected {}, expected one of: {}",
            token.text(self.src),
            names.join(", ")
        );
        let mut d = super::diagnostic(
            "flowchart/unexpected-token",
            Severity::Error,
            message,
            token.span,
        );
        d.help = diagnostic_row("flowchart/unexpected-token").1.to_owned();
        self.diags.push(d);
    }
    fn header(&mut self) -> GraphConfig {
        self.trivia();
        let Some(keyword) = self.accept(K::Graph) else {
            return GraphConfig {
                span: zero(),
                keyword: zero(),
                direction: None,
            };
        };
        let mut cfg = GraphConfig {
            span: keyword.span,
            keyword: keyword.span,
            direction: None,
        };
        self.accept(K::Space);
        let token = self.peek();
        if token.kind == K::Dir || direction(token.kind) {
            cfg.direction = Some(token.span);
            cfg.span.end = token.span.end;
            self.next();
        } else if token.kind == K::Nodir {
            self.next();
        } else if token.kind == K::NodeString {
            self.recover_direction();
        }
        if self.any(&[K::Newline, K::Semi]) {
            self.next();
        }
        cfg
    }
    fn recover_direction(&mut self) {
        let word = self.next();
        while !self.boundary() {
            if self.at(K::Dir) {
                self.plain("flowchart/dir-kw-invalid", word.span);
                self.recover();
                return;
            }
            self.next();
        }
        self.plain("flowchart/dir-invalid", word.span);
        self.recover();
    }
    fn statements(&mut self) -> Vec<Line> {
        let mut lines = Vec::new();
        loop {
            self.trivia();
            if self.at(K::Eof) {
                return lines;
            }
            if let Some(line) = self.statement() {
                lines.push(line);
            }
        }
    }
    fn statement(&mut self) -> Option<Line> {
        let token = self.peek();
        let kind = match token.kind {
            K::Subgraph => self.subgraph(),
            K::Style => self.style(),
            K::ClassDef => self.class_def(),
            K::Class => self.class(),
            K::LinkStyle => self.link_style(),
            K::Click => self.click(),
            K::AccTitle => self.acc_title(),
            K::AccDescr => self.acc_descr(),
            K::AccDescrMultilineValue => {
                let t = self.next();
                Statement::AccDescrBlock(AccDescrBlock {
                    span: t.span,
                    value: t.span,
                })
            }
            k if direction(k) => {
                let t = self.next();
                Statement::Direction(Direction { span: t.span })
            }
            K::End => {
                self.next();
                self.plain("flowchart/end-without-subgraph", token.span);
                return None;
            }
            _ if self.vertex_start() => return self.vertex_statement(),
            _ => return self.reject(),
        };
        Some(Line {
            span: statement_span(&kind),
            kind,
        })
    }
    fn reject(&mut self) -> Option<Line> {
        let token = self.next();
        self.recover();
        self.token_diag(
            "flowchart/unknown-statement",
            Span {
                start: token.span.start,
                end: self.last_end(),
            },
            &self.text(&token),
        );
        None
    }
    fn acc_title(&mut self) -> Statement {
        let kw = self.next();
        let value = self.accept(K::AccTitleValue).map_or(zero(), |t| t.span);
        Statement::AccTitle(AccTitle {
            span: Span {
                start: kw.span.start,
                end: kw.span.end.max(value.end),
            },
            value,
        })
    }
    fn acc_descr(&mut self) -> Statement {
        let kw = self.next();
        let value = self.accept(K::AccDescrValue).map_or(zero(), |t| t.span);
        Statement::AccDescr(AccDescr {
            span: Span {
                start: kw.span.start,
                end: kw.span.end.max(value.end),
            },
            value,
        })
    }
    fn subgraph(&mut self) -> Statement {
        let kw = self.next();
        let mut sg = Subgraph {
            span: kw.span,
            keyword: kw.span,
            id: None,
            title: None,
            body: Vec::new(),
            end_span: None,
        };
        let save = self.i;
        self.skip_spaces();
        let mut tokens = self.take_while(text_no_tags);
        if tokens.is_empty() {
            self.i = save;
        } else {
            let span = token_span(&tokens);
            while tokens.last().is_some_and(|t| t.kind == K::Space) {
                tokens.pop();
            }
            sg.id = Some(TextNoTags {
                span,
                text: self.concat(&tokens),
            });
            sg.span.end = span.end;
            if let Some(open) = self.accept(K::Sqs) {
                let (text, _) = self.label_text(&[K::Sqe]);
                sg.span.end = self
                    .accept(K::Sqe)
                    .map_or(text.span.end.max(open.span.end), |t| t.span.end);
                if self
                    .tokens
                    .get(self.i.wrapping_sub(1))
                    .is_none_or(|t| t.kind != K::Sqe)
                {
                    self.plain(
                        "flowchart/unclosed-node-bracket",
                        Span {
                            start: open.span.start,
                            end: sg.span.end,
                        },
                    );
                }
                sg.title = Some(text);
            }
        }
        if sg.id.is_none() {
            self.unexpected(&["NODE_STRING", "STR"]);
        }
        if self.any(&[K::Newline, K::Semi]) {
            self.next();
        }
        if self.depth >= 64 {
            self.recover();
        } else {
            self.depth += 1;
            loop {
                self.trivia();
                if self.any(&[K::Eof, K::End]) {
                    break;
                }
                if let Some(line) = self.statement() {
                    sg.body.push(line);
                }
            }
            self.depth -= 1;
        }
        if let Some(end) = self.accept(K::End) {
            sg.end_span = Some(end.span);
            sg.span.end = end.span.end;
        } else {
            self.token_diag("flowchart/unterminated", sg.span, "subgraph");
        }
        Statement::Subgraph(sg)
    }
    fn concat(&self, tokens: &[Token]) -> String {
        let mut result = String::new();
        let mut i = 0;
        while i < tokens.len() {
            if tokens[i].kind != K::EdgeText {
                result.push_str(tokens[i].text(self.src));
                i += 1;
                continue;
            }
            let start = i;
            i += 1;
            while i < tokens.len()
                && tokens[i].kind == K::EdgeText
                && tokens[i - 1].span.end == tokens[i].span.start
            {
                i += 1;
            }
            let span = Span {
                start: tokens[start].span.start,
                end: tokens[i - 1].span.end,
            };
            if let Some(text) = self.src.get(span.start..span.end) {
                result.push_str(text);
            } else {
                for token in &tokens[start..i] {
                    result.push_str(token.text(self.src));
                }
            }
        }
        result
    }
    fn take_while(&mut self, predicate: fn(K) -> bool) -> Vec<Token> {
        let mut tokens = Vec::new();
        while predicate(self.peek().kind) {
            tokens.push(self.next());
        }
        tokens
    }
    fn id(&mut self) -> Option<IdString> {
        let tokens = self.take_while(id_token);
        if tokens.is_empty() {
            return None;
        }
        Some(IdString {
            span: token_span(&tokens),
            text: self.concat(&tokens),
        })
    }
    fn vertex_start(&self) -> bool {
        matches!(
            self.peek().kind,
            K::NodeString
                | K::Str
                | K::MdStr
                | K::LinkId
                | K::Num
                | K::UnicodeText
                | K::Down
                | K::Default
                | K::Comma
                | K::Colon
                | K::Amp
                | K::Brkt
                | K::Mult
                | K::Minus
        )
    }
    fn vertex_statement(&mut self) -> Option<Line> {
        let Some(first) = self.node_group() else {
            return self.reject();
        };
        let mut stmt = VertexStatement {
            span: first.span,
            first,
            rest: Vec::new(),
        };
        loop {
            let (link, broken) = self.try_link();
            let Some(link) = link else {
                let end = if broken {
                    StatementEnd::Broken
                } else {
                    StatementEnd::Clean
                };
                return Some(self.finish_vertex(stmt, end));
            };
            self.skip_spaces();
            if !self.vertex_start() {
                self.plain("flowchart/link-missing", link.span);
                return Some(self.finish_vertex(stmt, StatementEnd::Broken));
            }
            let Some(group) = self.node_group() else {
                return Some(self.finish_vertex(stmt, StatementEnd::Broken));
            };
            stmt.span = join(join(stmt.span, link.span), group.span);
            stmt.rest.push((link, group));
        }
    }
    fn finish_vertex(&mut self, mut stmt: VertexStatement, end: StatementEnd) -> Line {
        self.accept(K::Space);
        if !self.boundary() {
            if end == StatementEnd::Clean && self.vertex_start() {
                self.plain("flowchart/link-missing", self.peek().span);
            } else if end == StatementEnd::Clean {
                self.unexpected(&[
                    "AMP",
                    "EOF",
                    "LINK",
                    "NEWLINE",
                    "SEMI",
                    "SHAPE_DATA",
                    "START_LINK",
                    "STYLE_SEPARATOR",
                ]);
            }
            self.recover();
        }
        if self.i > 0 {
            stmt.span.end = self.last_end();
        }
        Line {
            span: stmt.span,
            kind: Statement::Vertex(stmt),
        }
    }
    fn node_group(&mut self) -> Option<NodeGroup> {
        let first = self.styled_vertex()?;
        let mut group = NodeGroup {
            span: first.span,
            nodes: vec![first],
        };
        loop {
            let save = self.i;
            self.skip_spaces();
            let Some(amp) = self.accept(K::Amp) else {
                self.i = save;
                return Some(group);
            };
            self.skip_spaces();
            let Some(next) = self.styled_vertex() else {
                self.plain("flowchart/link-missing", amp.span);
                return Some(group);
            };
            group.span = join(group.span, next.span);
            group.nodes.push(next);
        }
    }
    fn styled_vertex(&mut self) -> Option<StyledVertex> {
        let vertex = self.vertex()?;
        let mut sv = StyledVertex {
            span: vertex.span,
            vertex,
            class: None,
            shape_data: None,
        };
        if self.accept(K::StyleSeparator).is_some()
            && let Some(class) = self.id()
        {
            sv.span = join(sv.span, class.span);
            sv.class = Some(class);
        }
        if self.at(K::ShapeData) {
            let data = self.shape_data();
            sv.span = join(sv.span, data.span);
            sv.shape_data = Some(data);
        }
        Some(sv)
    }
    fn vertex(&mut self) -> Option<Vertex> {
        let id = self.id()?;
        let mut vertex = Vertex {
            span: id.span,
            id,
            label: None,
        };
        let open = self.peek();
        let Some(mut form) = label_form(open.kind) else {
            return Some(vertex);
        };
        self.next();
        if open.kind == K::VertexWithPropsStart {
            form = self.rect_props();
        }
        let paired = matches!(open.kind, K::Ps | K::DiamondStart) && self.at(open.kind);
        if paired {
            self.next();
            form = if open.kind == K::Ps {
                LabelForm::Round2
            } else {
                LabelForm::Diamond2
            };
        }
        let closers = closers(open.kind);
        let (text, tokens) = self.label_text(closers);
        self.label_rules(&tokens, &text, &open);
        let mut end = text.span.end.max(open.span.end);
        if paired {
            for _ in 0..2 {
                if let Some(close) = self.accept(closers[0]) {
                    vertex.span.end = close.span.end;
                    end = close.span.end;
                } else {
                    self.end = EndState::Bracket;
                    break;
                }
            }
        } else {
            end = self.close_label(&open, &text, closers);
            vertex.span.end = end;
        }
        vertex.label = Some(Label {
            span: Span {
                start: open.span.start,
                end,
            },
            form,
            text,
        });
        Some(vertex)
    }
    fn rect_props(&mut self) -> LabelForm {
        let mut field = String::new();
        let mut value = String::new();
        for (i, kind) in [K::NodeString, K::Colon, K::NodeString, K::Pipe]
            .into_iter()
            .enumerate()
        {
            if let Some(t) = self.accept(kind) {
                if i == 0 {
                    field = self.text(&t);
                }
                if i == 2 {
                    value = self.text(&t);
                }
            } else {
                self.unexpected(&[kind.as_str()]);
            }
        }
        LabelForm::RectProps { field, value }
    }
    fn close_label(&mut self, open: &Token, text: &Text, accepted: &[K]) -> usize {
        if accepted.contains(&self.peek().kind) {
            return self.next().span.end;
        }
        self.end = EndState::Bracket;
        if closer(self.peek().kind) {
            let token = self.next();
            self.plain("flowchart/node-mixed-brackets", token.span);
            return token.span.end;
        }
        if !self.at(K::Eof) {
            self.plain("flowchart/node-mixed-brackets", self.peek().span);
        }
        text.span.end.max(open.span.end)
    }
    fn label_text(&mut self, accepted: &[K]) -> (Text, Vec<Token>) {
        let mut tokens = Vec::new();
        loop {
            let k = self.peek().kind;
            if accepted.contains(&k) || !label_token(k) {
                break;
            }
            if !tokens.is_empty() && quoted(k) {
                let token = self.peek();
                let first: &Token = &tokens[0];
                let code = match first.kind {
                    K::Str => "flowchart/label-double-in-double",
                    K::MdStr => "flowchart/label-double-in-single",
                    _ => "flowchart/label-quote-in-unquoted",
                };
                let start = token.string_open.unwrap_or(token.span.start);
                self.plain(
                    code,
                    Span {
                        start,
                        end: start + 1,
                    },
                );
                break;
            }
            tokens.push(self.next());
        }
        (
            Text {
                span: token_span(&tokens),
                kind: tokens
                    .first()
                    .map_or(TextKind::Plain, |t| text_kind(t.kind)),
                text: self.concat(&tokens),
            },
            tokens,
        )
    }
    fn label_rules(&mut self, tokens: &[Token], text: &Text, open: &Token) {
        let Some(first) = tokens.first() else {
            self.plain("flowchart/node-empty", open.span);
            return;
        };
        for token in tokens.iter().filter(|t| quoted(t.kind)) {
            let bytes = self.src.as_bytes();
            for i in token.span.start..token.span.end.min(bytes.len()).saturating_sub(1) {
                if bytes[i] == b'\\' && bytes[i + 1] == b'"' {
                    self.plain(
                        "flowchart/label-escaped-quote",
                        Span {
                            start: i,
                            end: i + 2,
                        },
                    );
                }
            }
        }
        let code = match first.kind {
            K::Str => "flowchart/label-double-in-double",
            K::MdStr => "flowchart/label-double-in-single",
            _ => "flowchart/label-quote-in-unquoted",
        };
        for token in tokens.iter().skip(1).filter(|t| quoted(t.kind)) {
            let start = token.string_open.unwrap_or(token.span.start);
            self.plain(
                code,
                Span {
                    start,
                    end: start.saturating_add(1),
                },
            );
        }
        if text.kind != TextKind::Plain {
            return;
        }
        for token in tokens {
            if let Some(off) = token
                .text(self.src)
                .bytes()
                .position(|b| b == b'(' || b == b')')
            {
                self.plain(
                    "flowchart/label-parens-unquoted",
                    Span {
                        start: token.span.start + off,
                        end: token.span.start + off + 1,
                    },
                );
            }
        }
    }
    fn shape_data(&mut self) -> ShapeData {
        let open = self.next();
        let mut data = ShapeData {
            span: open.span,
            text: String::new(),
        };
        loop {
            if !self.at(K::ShapeData) {
                if self.at(K::Eof) {
                    self.end = EndState::Unterminated;
                }
                return data;
            }
            let token = self.next();
            data.span.end = token.span.end;
            if token.text(self.src).is_empty() {
                return data;
            }
            data.text.push_str(token.text(self.src));
        }
    }
    fn try_link(&mut self) -> (Option<Link>, bool) {
        let save = self.i;
        self.skip_spaces();
        let mut id = None;
        let mut span = zero();
        if self.at(K::LinkId) {
            let token = self.next();
            let text = token
                .text(self.src)
                .strip_suffix('@')
                .unwrap_or(token.text(self.src));
            let s = Span {
                start: token.span.start,
                end: token.span.start + text.len(),
            };
            id = Some(s);
            span = s;
        }
        if let Some(open) = self.accept(K::Link) {
            span = join(span, open.span);
            if open.text(self.src).trim() == "->" {
                self.plain("flowchart/arrow-invalid", open.span);
            }
            if self.at(K::Link) {
                let next = self.next();
                self.plain(
                    "flowchart/link-unsupported-marker",
                    Span {
                        start: open.span.start,
                        end: next.span.end,
                    },
                );
            }
            let mut link = Link {
                span,
                statement: LinkStatement {
                    span,
                    link_id: id,
                    start: None,
                    end: open.span,
                },
                arrow_text: None,
                edge_text: None,
            };
            self.arrow_text(&mut link);
            return (Some(link), false);
        }
        let Some(start) = self.accept(K::StartLink) else {
            self.i = save;
            return (None, false);
        };
        span = join(span, start.span);
        let edge = self.edge_text();
        let Some(end) = self.accept(K::Link) else {
            self.unexpected(&["LINK"]);
            self.i = save;
            return (None, true);
        };
        span = join(span, end.span);
        let mut link = Link {
            span: join(span, edge.span),
            statement: LinkStatement {
                span,
                link_id: id,
                start: Some(start.span),
                end: end.span,
            },
            arrow_text: None,
            edge_text: Some(edge),
        };
        self.arrow_text(&mut link);
        (Some(link), false)
    }
    fn edge_text(&mut self) -> EdgeText {
        let mut tokens = Vec::new();
        while self.at(K::EdgeText) || (tokens.is_empty() && quoted(self.peek().kind)) {
            tokens.push(self.next());
        }
        EdgeText {
            span: token_span(&tokens),
            kind: tokens
                .first()
                .map_or(TextKind::Plain, |t| text_kind(t.kind)),
            text: self.concat(&tokens),
        }
    }
    fn arrow_text(&mut self, link: &mut Link) {
        let Some(open) = self.accept(K::Pipe) else {
            return;
        };
        let (text, _) = self.label_text(&[K::Pipe]);
        let mut span = Span {
            start: open.span.start,
            end: text.span.end.max(open.span.end),
        };
        if let Some(close) = self.accept(K::Pipe) {
            span.end = close.span.end;
        } else {
            self.plain("flowchart/unclosed-node-bracket", span);
        }
        link.span = join(link.span, span);
        link.arrow_text = Some(ArrowText { span, text });
    }
    fn styles(&mut self) -> Option<StylesOpt> {
        let mut result = StylesOpt {
            span: zero(),
            styles: Vec::new(),
        };
        loop {
            let tokens = self.take_while(style_token);
            let start = tokens
                .iter()
                .position(|t| t.kind != K::Space)
                .unwrap_or(tokens.len());
            let end = tokens
                .iter()
                .rposition(|t| t.kind != K::Space)
                .map_or(start, |i| i + 1);
            let tokens = &tokens[start..end];
            if tokens.is_empty() {
                break;
            }
            result.span = join(result.span, token_span(tokens));
            result.styles.push(self.concat(tokens));
            if self.accept(K::Comma).is_none() {
                return Some(result);
            }
            self.skip_spaces();
        }
        if result.styles.is_empty() {
            None
        } else {
            Some(result)
        }
    }
    fn style(&mut self) -> Statement {
        let kw = self.next();
        self.skip_spaces();
        let Some(target) = self.id() else {
            self.plain("flowchart/link-missing", kw.span);
            return Statement::Style(StyleStatement {
                span: kw.span,
                target: empty_id(),
                styles: empty_styles(),
            });
        };
        let mut span = join(kw.span, target.span);
        self.skip_spaces();
        let styles = self.styles().unwrap_or_else(empty_styles);
        if styles.span != zero() {
            span.end = styles.span.end;
        }
        Statement::Style(StyleStatement {
            span,
            target,
            styles,
        })
    }
    fn class_def(&mut self) -> Statement {
        let kw = self.next();
        self.skip_spaces();
        let Some(names) = self.id() else {
            self.plain("flowchart/class-malformed", kw.span);
            return Statement::ClassDef(ClassDefStatement {
                span: kw.span,
                names: empty_id(),
                styles: empty_styles(),
            });
        };
        let mut span = join(kw.span, names.span);
        self.skip_spaces();
        let styles = self.styles().unwrap_or_else(empty_styles);
        if styles.span != zero() {
            span.end = styles.span.end;
        }
        Statement::ClassDef(ClassDefStatement {
            span,
            names,
            styles,
        })
    }
    fn class(&mut self) -> Statement {
        let kw = self.next();
        let mut stmt = ClassStatement {
            span: kw.span,
            targets: empty_id(),
            class_name: empty_id(),
        };
        if self.accept(K::Space).is_none() {
            self.plain("flowchart/class-malformed", kw.span);
            return Statement::Class(stmt);
        }
        let Some(targets) = self.id() else {
            self.plain("flowchart/class-malformed", kw.span);
            return Statement::Class(stmt);
        };
        stmt.span.end = targets.span.end;
        stmt.targets = targets;
        if self.accept(K::Space).is_none() {
            self.plain("flowchart/class-malformed", kw.span);
            return Statement::Class(stmt);
        }
        if let Some(class) = self.id() {
            stmt.span.end = class.span.end;
            stmt.class_name = class;
        } else {
            self.plain("flowchart/class-malformed", kw.span);
        }
        Statement::Class(stmt)
    }
    fn num_list(&mut self) -> Option<NumList> {
        let mut numbers = Vec::new();
        loop {
            if self.at(K::Colon) {
                let t = self.next();
                self.plain("flowchart/linkstyle-range-not-supported", t.span);
                continue;
            }
            let Some(num) = self.accept(K::Num) else {
                break;
            };
            numbers.push(num.span);
            if self.at(K::Colon) {
                self.plain("flowchart/linkstyle-range-not-supported", self.peek().span);
            }
            if self.accept(K::Comma).is_none() {
                break;
            }
            self.skip_spaces();
        }
        let first = numbers.first()?;
        Some(NumList {
            span: Span {
                start: first.start,
                end: numbers.last().map_or(first.end, |s| s.end),
            },
            numbers,
        })
    }
    fn alpha(&mut self) -> Option<AlphaNum> {
        let tokens = self.take_while(is_alpha_num_token);
        if tokens.is_empty() {
            return None;
        }
        Some(AlphaNum {
            span: token_span(&tokens),
            text: self.concat(&tokens),
        })
    }
    fn link_style(&mut self) -> Statement {
        let kw = self.next();
        let mut stmt = LinkStyleStatement {
            span: kw.span,
            selector: LinkSelector::NumList(NumList {
                span: zero(),
                numbers: Vec::new(),
            }),
            interpolate: None,
            styles: None,
        };
        self.skip_spaces();
        if let Some(def) = self.accept(K::Default) {
            stmt.selector = LinkSelector::Default(def.span);
            stmt.span.end = def.span.end;
        } else if let Some(list) = self.num_list() {
            stmt.span.end = list.span.end;
            stmt.selector = LinkSelector::NumList(list);
        } else {
            self.plain("flowchart/linkstyle-range-not-supported", kw.span);
            return Statement::LinkStyle(stmt);
        }
        self.skip_spaces();
        if self.accept(K::Interpolate).is_some() {
            self.skip_spaces();
            let Some(alpha) = self.alpha() else {
                self.plain("flowchart/linkstyle-range-not-supported", kw.span);
                return Statement::LinkStyle(stmt);
            };
            stmt.span.end = alpha.span.end;
            stmt.interpolate = Some(alpha);
            self.skip_spaces();
        }
        if let Some(styles) = self.styles() {
            stmt.span.end = styles.span.end;
            stmt.styles = Some(styles);
        }
        Statement::LinkStyle(stmt)
    }
    fn click_string(&mut self) -> Option<Text> {
        if !quoted(self.peek().kind) {
            return None;
        }
        let token = self.next();
        Some(Text {
            span: token.span,
            kind: text_kind(token.kind),
            text: self.text(&token),
        })
    }
    fn click(&mut self) -> Statement {
        let kw = self.next();
        self.skip_spaces();
        let mut span = kw.span;
        let action = match self.peek().kind {
            K::CallbackName => self.callback(&mut span),
            K::Href | K::Str | K::MdStr => self.click_link(&mut span),
            _ => {
                let alpha = self.alpha();
                let mut href = String::new();
                let mut tooltip = None;
                if let Some(alpha) = alpha {
                    span.end = alpha.span.end;
                    href = alpha.text;
                    self.skip_spaces();
                    if let Some(tip) = self.click_string() {
                        span.end = tip.span.end;
                        tooltip = Some(tip.text);
                    }
                }
                ClickAction::Link {
                    href,
                    tooltip,
                    target: None,
                }
            }
        };
        Statement::Click(ClickStatement {
            span,
            target: kw.span,
            action,
        })
    }
    fn callback(&mut self, span: &mut Span) -> ClickAction {
        let name = self.next();
        span.end = name.span.end;
        let args = self.accept(K::CallbackArgs).map(|t| {
            span.end = t.span.end;
            self.text(&t)
        });
        self.skip_spaces();
        let tooltip = self.click_string().map(|t| {
            span.end = t.span.end;
            t.text
        });
        self.skip_spaces();
        if let Some(extra) = self.accept(K::LinkTarget) {
            span.end = extra.span.end;
            self.plain("flowchart/click-call-extra-text", extra.span);
            self.recover();
        }
        ClickAction::Call {
            name: self.text(&name),
            args,
            tooltip,
        }
    }
    fn click_link(&mut self, span: &mut Span) -> ClickAction {
        let href_token = self.accept(K::Href);
        let mut action_span = href_token.as_ref().map_or(zero(), |t| t.span);
        if href_token.is_some() {
            self.skip_spaces();
        }
        let Some(url) = self.click_string() else {
            span.end = action_span.end;
            return ClickAction::Link {
                href: String::new(),
                tooltip: None,
                target: None,
            };
        };
        action_span = join(action_span, url.span);
        self.skip_spaces();
        let tooltip = self.click_string().map(|t| {
            action_span.end = t.span.end;
            self.skip_spaces();
            t.text
        });
        let target = self.accept(K::LinkTarget).map(|t| {
            action_span.end = t.span.end;
            self.text(&t)
        });
        span.end = action_span.end;
        ClickAction::Link {
            href: url.text,
            tooltip,
            target,
        }
    }
}

fn zero() -> Span {
    Span { start: 0, end: 0 }
}
fn join(a: Span, b: Span) -> Span {
    if a == zero() {
        return b;
    }
    Span {
        start: a.start.min(b.start),
        end: a.end.max(b.end),
    }
}
fn token_span(tokens: &[Token]) -> Span {
    tokens.first().map_or(zero(), |first| Span {
        start: first.span.start,
        end: tokens.last().map_or(first.span.end, |last| last.span.end),
    })
}
fn empty_id() -> IdString {
    IdString {
        span: zero(),
        text: String::new(),
    }
}
fn empty_styles() -> StylesOpt {
    StylesOpt {
        span: zero(),
        styles: Vec::new(),
    }
}
fn direction(k: K) -> bool {
    matches!(
        k,
        K::DirectionTb | K::DirectionBt | K::DirectionRl | K::DirectionLr | K::DirectionTd
    )
}
fn quoted(k: K) -> bool {
    matches!(k, K::Str | K::MdStr)
}
fn text_kind(k: K) -> TextKind {
    match k {
        K::Str => TextKind::String,
        K::MdStr => TextKind::Markdown,
        _ => TextKind::Plain,
    }
}
fn id_token(k: K) -> bool {
    matches!(
        k,
        K::Num
            | K::NodeString
            | K::Down
            | K::Minus
            | K::Default
            | K::Comma
            | K::Colon
            | K::Amp
            | K::Brkt
            | K::Mult
            | K::UnicodeText
    )
}
fn label_token(k: K) -> bool {
    matches!(
        k,
        K::Text | K::TagStart | K::TagEnd | K::UnicodeText | K::Str | K::MdStr
    )
}
fn text_no_tags(k: K) -> bool {
    id_token(k)
        || label_token(k)
        || matches!(
            k,
            K::Space
                | K::Style
                | K::LinkStyle
                | K::ClassDef
                | K::Class
                | K::Click
                | K::Up
                | K::Subgraph
                | K::End
                | K::Graph
                | K::Dir
                | K::DirectionTb
                | K::DirectionBt
                | K::DirectionRl
                | K::DirectionLr
                | K::DirectionTd
                | K::StartLink
        )
}
fn style_token(k: K) -> bool {
    matches!(
        k,
        K::Num | K::NodeString | K::Colon | K::Space | K::Brkt | K::Style
    )
}
fn label_form(k: K) -> Option<LabelForm> {
    Some(match k {
        K::Sqs => LabelForm::Square,
        K::Ps => LabelForm::Round,
        K::DoubleCircleStart => LabelForm::Circle,
        K::EllipseStart => LabelForm::Ellipse,
        K::StadiumStart => LabelForm::Stadium,
        K::SubroutineStart => LabelForm::Subroutine,
        K::CylinderStart => LabelForm::Cylinder,
        K::DiamondStart => LabelForm::Diamond,
        K::TagEnd => LabelForm::Odd,
        K::TrapStart => LabelForm::Trap {
            closer: TrapCloser::Trap,
        },
        K::InvTrapStart => LabelForm::InvTrap {
            closer: TrapCloser::InvTrap,
        },
        K::VertexWithPropsStart => LabelForm::RectProps {
            field: String::new(),
            value: String::new(),
        },
        _ => return None,
    })
}
fn closers(k: K) -> &'static [K] {
    match k {
        K::Sqs | K::TagEnd | K::VertexWithPropsStart => &[K::Sqe],
        K::Ps => &[K::Pe],
        K::DoubleCircleStart => &[K::DoubleCircleEnd],
        K::EllipseStart => &[K::EllipseEnd],
        K::StadiumStart => &[K::StadiumEnd],
        K::SubroutineStart => &[K::SubroutineEnd],
        K::CylinderStart => &[K::CylinderEnd],
        K::DiamondStart => &[K::DiamondStop],
        K::TrapStart => &[K::TrapEnd, K::InvTrapEnd],
        K::InvTrapStart => &[K::InvTrapEnd, K::TrapEnd],
        _ => &[],
    }
}
fn closer(k: K) -> bool {
    matches!(
        k,
        K::Sqe
            | K::Pe
            | K::DiamondStop
            | K::StadiumEnd
            | K::SubroutineEnd
            | K::CylinderEnd
            | K::DoubleCircleEnd
            | K::EllipseEnd
            | K::TrapEnd
            | K::InvTrapEnd
    )
}
fn statement_span(s: &Statement) -> Span {
    match s {
        Statement::Vertex(s) => s.span,
        Statement::Style(s) => s.span,
        Statement::ClassDef(s) => s.span,
        Statement::Class(s) => s.span,
        Statement::LinkStyle(s) => s.span,
        Statement::Click(s) => s.span,
        Statement::Subgraph(s) => s.span,
        Statement::Direction(s) => s.span,
        Statement::AccTitle(s) => s.span,
        Statement::AccDescr(s) => s.span,
        Statement::AccDescrBlock(s) => s.span,
    }
}
fn diagnostic_row(code: &str) -> (&'static str, &'static str) {
    match code {
        "flowchart/unexpected-token" => (
            "unexpected TOKEN, expected one of: LIST",
            "Remove the token, or replace it with one of the listed tokens.",
        ),
        "flowchart/unknown-statement" => (
            "unknown statement TOKEN",
            "Start the line with a node, an edge, or a flowchart statement such as style or subgraph.",
        ),
        "flowchart/unterminated" => (
            "unterminated TOKEN",
            "Close the opening delimiter before the end of the input.",
        ),
        "flowchart/unclosed-node-bracket" => (
            "node bracket TOKEN is never closed",
            "Add the closing bracket that matches the opening bracket.",
        ),
        "flowchart/arrow-invalid" => (
            "A single arrow -> is used in a flowchart",
            "Replace -> with -->, or use -- text --> for an inline label.",
        ),
        "flowchart/link-unsupported-marker" => (
            "An inline link uses a one-sided end marker, such as --x--> or --o-->",
            "Use a symmetric marker pair such as x--x, or a plain arrow with a label.",
        ),
        "flowchart/label-double-in-double" => (
            "A double-quoted label contains another double quote",
            "Use &quot; for the inner quotes.",
        ),
        "flowchart/label-double-in-single" => (
            "A single-quoted label contains an unescaped double quote",
            "Replace the inner double quote with &quot;, or use a double-quoted label with &quot; inside.",
        ),
        "flowchart/label-escaped-quote" => (
            "A node label contains a backslash-escaped quote, which Mermaid does not support",
            "Use &quot; for the inner quotes instead of a backslash escape.",
        ),
        "flowchart/label-quote-in-unquoted" => (
            "A double quote appears inside an unquoted label",
            "Wrap the whole label in double quotes and write inner quotes as &quot;.",
        ),
        "flowchart/label-parens-unquoted" => (
            "An unquoted label contains an opening or closing parenthesis",
            "Wrap the label in double quotes, or replace ( and ) with &#40; and &#41;.",
        ),
        "flowchart/dir-invalid" => (
            "The direction token after the header is not one of TD, TB, BT, RL, LR",
            "Use one of TD, TB, BT, RL, or LR.",
        ),
        "flowchart/dir-kw-invalid" => (
            "An unknown keyword appears before the direction token",
            "Replace the unknown keyword with direction.",
        ),
        "flowchart/link-missing" => (
            "Two nodes appear on one line without a connecting arrow",
            "Insert --> between the two nodes.",
        ),
        "flowchart/end-without-subgraph" => (
            "end appears without a matching subgraph",
            "Remove this end line, or add a subgraph above it.",
        ),
        "flowchart/node-mixed-brackets" => (
            "The opening and closing brackets of a node shape do not match",
            "Close with the bracket that matches the opener, for example ) for (.",
        ),
        "flowchart/node-empty" => (
            "A node shape has empty content, such as A[]",
            "Write text inside the brackets, or drop the brackets and use the bare node id.",
        ),
        "flowchart/quote-unclosed" => (
            "A node label opens a quote but never closes it",
            "Close the quote, for example A[\"Label\"].",
        ),
        "flowchart/class-malformed" => (
            "A class statement is missing node ids or the class name",
            "Write class A,B classname.",
        ),
        "flowchart/linkstyle-range-not-supported" => (
            "A range such as 0:3 is used in the linkStyle index list",
            "Use comma-separated indices instead, for example linkStyle 0,1,2.",
        ),
        "flowchart/click-call-extra-text" => (
            "A click call statement carries tooltip or target text after call fn()",
            "Write click A call doThing() with no trailing text.",
        ),
        _ => ("", ""),
    }
}

fn attach_fixes(src: &str, diagnostics: &mut [Diagnostic]) {
    for d in diagnostics {
        d.fixes.clear();
        if let Some(fix) = diagnostic_fix(src, d) {
            d.fixes.push(fix);
        }
    }
}

fn single_fix(title: &str, safety: FixSafety, span: Span, text: impl Into<String>) -> Fix {
    Fix {
        title: title.to_owned(),
        safety,
        edits: vec![Edit {
            span,
            new_text: text.into(),
        }],
    }
}

fn diagnostic_fix(src: &str, d: &Diagnostic) -> Option<Fix> {
    let safe = FixSafety::Safe;
    let unsafe_fix = FixSafety::Unsafe;
    let point = Span {
        start: d.span.start,
        end: d.span.start,
    };
    Some(match d.code {
        "flowchart/arrow-invalid" => single_fix("Replace -> with -->", safe, d.span, "-->"),
        "flowchart/link-missing" => single_fix(
            "Insert --> between the two nodes",
            unsafe_fix,
            point,
            "--> ",
        ),
        "flowchart/end-without-subgraph" | "flowchart/meta-unsupported" => {
            let (start, mut end) = line_bounds(src, d.span.start);
            let bytes = src.as_bytes();
            if end < bytes.len() {
                if bytes[end] == b'\r' && bytes.get(end + 1) == Some(&b'\n') {
                    end += 1;
                }
                end += 1;
            }
            let title = if d.code == "flowchart/end-without-subgraph" {
                "Remove the stray end line"
            } else {
                "Remove the unsupported meta line"
            };
            single_fix(title, unsafe_fix, Span { start, end }, "")
        }
        "flowchart/unclosed-node-bracket"
        | "flowchart/node-mixed-brackets"
        | "flowchart/node-empty" => return bracket_fix(src, d),
        "flowchart/label-escaped-quote" | "flowchart/label-double-in-single" => {
            single_fix("Replace the quote with &quot;", safe, d.span, "&quot;")
        }
        "flowchart/label-backtick" => single_fix("Remove the backtick", safe, d.span, ""),
        "flowchart/dir-kw-invalid" => single_fix(
            "Replace the keyword with direction",
            safe,
            d.span,
            "direction",
        ),
        "flowchart/dir-missing" => single_fix(
            "Insert the default direction TD",
            safe,
            Span {
                start: d.span.end,
                end: d.span.end,
            },
            " TD",
        ),
        "flowchart/link-unsupported-marker" => {
            let text: String = src
                .get(d.span.start..d.span.end)
                .unwrap_or("")
                .chars()
                .filter(|c| *c != 'x' && *c != 'o')
                .collect();
            single_fix(
                "Remove the unsupported one-sided marker",
                unsafe_fix,
                d.span,
                text,
            )
        }
        "flowchart/quote-unclosed" => {
            let (_, mut end) = line_bounds(src, d.span.start);
            for i in d.span.start.saturating_add(1)..end {
                if matches!(src.as_bytes()[i], b']' | b')' | b'}') {
                    end = i;
                    break;
                }
            }
            single_fix(
                "Insert the closing quote",
                unsafe_fix,
                Span { start: end, end },
                "\"",
            )
        }
        "flowchart/label-quote-in-unquoted" => return quote_wrapping_fix(src, d),
        _ => return None,
    })
}

fn line_bounds(src: &str, at: usize) -> (usize, usize) {
    let bytes = src.as_bytes();
    let mut start = at.min(bytes.len());
    let mut end = start;
    while start > 0 && !matches!(bytes[start - 1], b'\n' | b'\r') {
        start -= 1;
    }
    while end < bytes.len() && !matches!(bytes[end], b'\n' | b'\r') {
        end += 1;
    }
    (start, end)
}

fn bracket_opening(src: &str, at: usize) -> Option<(usize, &'static str, &'static str)> {
    let (start, end) = line_bounds(src, at);
    let pairs = [
        ("(((", ")))"),
        ("((", "))"),
        ("([", "])"),
        ("[[", "]]"),
        ("[(", ")]"),
        ("{{", "}}"),
        ("[/", "/]"),
        ("[\\", "\\]"),
        ("(-", "-)"),
        ("[", "]"),
        ("(", ")"),
        ("{", "}"),
        (">", "]"),
        ("|", "|"),
    ];
    let mut i = start;
    while i <= at && i < end {
        if src.as_bytes()[i] == b'>' && i > 0 && b"-=.".contains(&src.as_bytes()[i - 1]) {
            i += 1;
            continue;
        }
        let Some(text) = src.get(i..) else {
            i += 1;
            continue;
        };
        let Some((open, close)) = pairs.iter().find(|(open, _)| text.starts_with(open)) else {
            i += 1;
            continue;
        };
        let offset = src.get(i + open.len()..end)?.find(close);
        if let Some(offset) = offset {
            let finish = i + open.len() + offset + close.len();
            if finish <= at {
                i = finish;
                continue;
            }
        }
        return Some((i, open, close));
    }
    None
}

fn bracket_fix(src: &str, d: &Diagnostic) -> Option<Fix> {
    let (at, open, close) = bracket_opening(src, d.span.start)?;
    match d.code {
        "flowchart/unclosed-node-bracket" => Some(single_fix(
            "Add the closing bracket",
            FixSafety::Unsafe,
            Span {
                start: d.span.end,
                end: d.span.end,
            },
            close,
        )),
        "flowchart/node-mixed-brackets" => Some(single_fix(
            "Close with the matching bracket",
            FixSafety::Safe,
            d.span,
            close,
        )),
        "flowchart/node-empty" => {
            let (_, end) = line_bounds(src, at);
            let offset = src.get(at + open.len()..end)?.find(close)?;
            Some(single_fix(
                "Remove the empty bracket pair",
                FixSafety::Safe,
                Span {
                    start: at,
                    end: at + open.len() + offset + close.len(),
                },
                "",
            ))
        }
        _ => None,
    }
}

fn quote_wrapping_fix(src: &str, d: &Diagnostic) -> Option<Fix> {
    let (at, open, close) = bracket_opening(src, d.span.start)?;
    let start = at + open.len();
    let (_, end) = line_bounds(src, start);
    let body = src.get(start..end)?;
    let offset = body.find(close)?;
    let text = format!("\"{}\"", body[..offset].replace('"', "&quot;"));
    Some(single_fix(
        "Wrap the label in quotes",
        FixSafety::Safe,
        Span {
            start,
            end: start + offset,
        },
        text,
    ))
}

#[cfg(test)]
mod fix_contract_tests {
    use super::*;

    #[test]
    fn flowchart_diagnostic_fix_contracts() {
        let safe = FixSafety::Safe;
        let unsafe_fix = FixSafety::Unsafe;
        for (code, src, start, end, title, safety, edit_start, edit_end, text) in [
            (
                "flowchart/arrow-invalid",
                "A -> B",
                2,
                4,
                "Replace -> with -->",
                safe,
                2,
                4,
                "-->",
            ),
            (
                "flowchart/link-missing",
                "A B",
                2,
                3,
                "Insert --> between the two nodes",
                unsafe_fix,
                2,
                2,
                "--> ",
            ),
            (
                "flowchart/end-without-subgraph",
                " end\n",
                1,
                4,
                "Remove the stray end line",
                unsafe_fix,
                0,
                5,
                "",
            ),
            (
                "flowchart/meta-unsupported",
                " title foo\n",
                1,
                10,
                "Remove the unsupported meta line",
                unsafe_fix,
                0,
                11,
                "",
            ),
            (
                "flowchart/unclosed-node-bracket",
                "A[foo",
                1,
                5,
                "Add the closing bracket",
                unsafe_fix,
                5,
                5,
                "]",
            ),
            (
                "flowchart/node-mixed-brackets",
                "A(foo]",
                5,
                6,
                "Close with the matching bracket",
                safe,
                5,
                6,
                ")",
            ),
            (
                "flowchart/node-empty",
                "A[]",
                1,
                2,
                "Remove the empty bracket pair",
                safe,
                1,
                3,
                "",
            ),
            (
                "flowchart/label-escaped-quote",
                "A[\"x\\\"y\"]",
                4,
                6,
                "Replace the quote with &quot;",
                safe,
                4,
                6,
                "&quot;",
            ),
            (
                "flowchart/label-double-in-single",
                "A[x\"y]",
                3,
                4,
                "Replace the quote with &quot;",
                safe,
                3,
                4,
                "&quot;",
            ),
            (
                "flowchart/label-backtick",
                "A[x`y]",
                3,
                4,
                "Remove the backtick",
                safe,
                3,
                4,
                "",
            ),
            (
                "flowchart/dir-kw-invalid",
                "graph directionx LR",
                6,
                16,
                "Replace the keyword with direction",
                safe,
                6,
                16,
                "direction",
            ),
            (
                "flowchart/dir-missing",
                "graph",
                0,
                5,
                "Insert the default direction TD",
                safe,
                5,
                5,
                " TD",
            ),
            (
                "flowchart/link-unsupported-marker",
                "A --x--> B",
                2,
                8,
                "Remove the unsupported one-sided marker",
                unsafe_fix,
                2,
                8,
                "---->",
            ),
            (
                "flowchart/quote-unclosed",
                "A[\"foo]",
                2,
                7,
                "Insert the closing quote",
                unsafe_fix,
                6,
                6,
                "\"",
            ),
            (
                "flowchart/label-quote-in-unquoted",
                "A[foo\"bar\"]",
                5,
                6,
                "Wrap the label in quotes",
                safe,
                2,
                10,
                "\"foo&quot;bar&quot;\"",
            ),
        ] {
            let mut diagnostic =
                super::super::diagnostic(code, Severity::Error, String::new(), Span { start, end });
            attach_fixes(src, std::slice::from_mut(&mut diagnostic));
            assert_eq!(diagnostic.fixes.len(), 1, "{code}");
            let fix = &diagnostic.fixes[0];
            assert_eq!((fix.title.as_str(), fix.safety), (title, safety), "{code}");
            assert_eq!(fix.edits.len(), 1, "{code}");
            assert_eq!(
                fix.edits[0].span,
                Span {
                    start: edit_start,
                    end: edit_end
                },
                "{code}"
            );
            assert_eq!(fix.edits[0].new_text, text, "{code}");
        }
    }
}
