use super::*;

impl Parser<'_> {
    pub(super) fn click_string(&mut self) -> Option<Text> {
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
    pub(super) fn click(&mut self) -> Statement {
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
    pub(super) fn callback(&mut self, span: &mut Span) -> ClickAction {
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
    pub(super) fn click_link(&mut self, span: &mut Span) -> ClickAction {
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
