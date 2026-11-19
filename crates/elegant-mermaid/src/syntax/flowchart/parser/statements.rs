use super::*;

impl Parser<'_> {
    pub(super) fn header(&mut self) -> GraphConfig {
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
    pub(super) fn recover_direction(&mut self) {
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
    pub(super) fn statements(&mut self) -> Vec<Line> {
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
    pub(super) fn statement(&mut self) -> Option<Line> {
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
                    text: self.text(&t),
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
    pub(super) fn reject(&mut self) -> Option<Line> {
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
    pub(super) fn acc_title(&mut self) -> Statement {
        let kw = self.next();
        let token = self.accept(K::AccTitleValue);
        let value = token.as_ref().map_or(zero(), |t| t.span);
        let text = token.as_ref().map_or_else(String::new, |t| self.text(t));
        Statement::AccTitle(AccTitle {
            span: Span {
                start: kw.span.start,
                end: kw.span.end.max(value.end),
            },
            value,
            text,
        })
    }
    pub(super) fn acc_descr(&mut self) -> Statement {
        let kw = self.next();
        let token = self.accept(K::AccDescrValue);
        let value = token.as_ref().map_or(zero(), |t| t.span);
        let text = token.as_ref().map_or_else(String::new, |t| self.text(t));
        Statement::AccDescr(AccDescr {
            span: Span {
                start: kw.span.start,
                end: kw.span.end.max(value.end),
            },
            value,
            text,
        })
    }
    pub(super) fn subgraph(&mut self) -> Statement {
        let kw = self.next();
        let mut sg = Subgraph {
            span: kw.span,
            keyword: kw.span,
            id: None,
            title: None,
            body: Vec::new(),
            end_span: None,
        };
        self.subgraph_heading(&mut sg);
        self.subgraph_body(&mut sg);
        Statement::Subgraph(sg)
    }

    pub(super) fn subgraph_heading(&mut self, sg: &mut Subgraph) {
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
    }

    pub(super) fn subgraph_body(&mut self, sg: &mut Subgraph) {
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
    }
}
