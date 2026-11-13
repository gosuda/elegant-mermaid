use super::*;

impl Parser<'_> {
    pub(super) fn try_link(&mut self) -> (Option<Link>, bool) {
        let save = self.i;
        self.skip_spaces();
        let id = self.link_id();
        let span = id.unwrap_or_else(zero);
        if let Some(open) = self.accept(K::Link) {
            let span = join(span, open.span);
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
        let span = join(span, start.span);
        let edge = self.edge_text();
        let Some(end) = self.accept(K::Link) else {
            self.unexpected(&["LINK"]);
            self.i = save;
            return (None, true);
        };
        let span = join(span, end.span);
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
    pub(super) fn link_id(&mut self) -> Option<Span> {
        if !self.at(K::LinkId) {
            return None;
        }
        let token = self.next();
        let text = token
            .text(self.src)
            .strip_suffix('@')
            .unwrap_or(token.text(self.src));
        Some(Span {
            start: token.span.start,
            end: token.span.start + text.len(),
        })
    }
    pub(super) fn edge_text(&mut self) -> EdgeText {
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
    pub(super) fn arrow_text(&mut self, link: &mut Link) {
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
}
