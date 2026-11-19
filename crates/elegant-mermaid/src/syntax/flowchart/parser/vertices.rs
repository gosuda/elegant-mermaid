use super::*;

impl Parser<'_> {
    pub(super) fn concat(&self, tokens: &[Token]) -> String {
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
    pub(super) fn take_while(&mut self, predicate: fn(K) -> bool) -> Vec<Token> {
        let mut tokens = Vec::new();
        while predicate(self.peek().kind) {
            tokens.push(self.next());
        }
        tokens
    }
    pub(super) fn id(&mut self) -> Option<IdString> {
        let tokens = self.take_while(id_token);
        if tokens.is_empty() {
            return None;
        }
        Some(IdString {
            span: token_span(&tokens),
            text: self.concat(&tokens),
        })
    }
    pub(super) fn vertex_start(&self) -> bool {
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
    pub(super) fn vertex_statement(&mut self) -> Option<Line> {
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
    pub(super) fn finish_vertex(&mut self, mut stmt: VertexStatement, end: StatementEnd) -> Line {
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
    pub(super) fn node_group(&mut self) -> Option<NodeGroup> {
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
    pub(super) fn styled_vertex(&mut self) -> Option<StyledVertex> {
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
    pub(super) fn vertex(&mut self) -> Option<Vertex> {
        let id = self.id()?;
        let open = self.peek();
        let Some(mut form) = label_form(open.kind) else {
            return Some(Vertex {
                span: id.span,
                id,
                label: None,
            });
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
        let mut span = id.span;
        if paired {
            for _ in 0..2 {
                if let Some(close) = self.accept(closers[0]) {
                    span.end = close.span.end;
                    end = close.span.end;
                } else {
                    self.end = EndState::Bracket;
                    break;
                }
            }
        } else {
            end = self.close_label(&open, &text, closers);
            span.end = end;
        }
        Some(Vertex {
            span,
            id,
            label: Some(Label {
                span: Span {
                    start: open.span.start,
                    end,
                },
                form,
                text,
            }),
        })
    }
    pub(super) fn rect_props(&mut self) -> LabelForm {
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
    pub(super) fn close_label(&mut self, open: &Token, text: &Text, accepted: &[K]) -> usize {
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
    pub(super) fn label_text(&mut self, accepted: &[K]) -> (Text, Vec<Token>) {
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
                tokens: tokens.clone(),
            },
            tokens,
        )
    }
    pub(super) fn label_rules(&mut self, tokens: &[Token], text: &Text, open: &Token) {
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
    pub(super) fn shape_data(&mut self) -> ShapeData {
        let open = self.next();
        let mut data = ShapeData {
            span: open.span,
            text: String::new(),
            src_at: Vec::new(),
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
            let text = token.text(self.src);
            if text.is_empty() {
                return data;
            }
            data.src_at
                .extend((0..text.len()).map(|i| token.span.start + i));
            data.text.push_str(text);
        }
    }
}
