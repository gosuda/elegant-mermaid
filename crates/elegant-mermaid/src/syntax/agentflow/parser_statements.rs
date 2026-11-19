use super::{
    ast::*,
    parser::{Parser, alpha_kind, boundary},
};

impl<'a> Parser<'a, '_> {
    pub(super) fn link(&mut self) -> Option<Link<'a>> {
        let start = self.position();
        let id = if self.kind() == "LINK_ID" {
            self.take()
        } else {
            None
        };
        let opening = if self.kind() == "START_LINK" {
            self.take()
        } else {
            None
        };
        let split_label = if opening.is_some() {
            Some(self.text(&["EDGE_TEXT", "UNICODE_TEXT"])?)
        } else {
            None
        };
        let operator = self.require("LINK")?;
        let statement = LinkStatement {
            span: self.span(start),
            id,
            operator,
        };
        let arrow_text = if self.kind() == "PIPE" {
            Some(self.arrow_text()?)
        } else {
            None
        };
        let edge_text = split_label.map(|text| EdgeText {
            span: text.span,
            text,
        });
        Some(Link {
            span: self.span(start),
            statement,
            opening,
            arrow_text,
            edge_text,
        })
    }
    fn arrow_text(&mut self) -> Option<ArrowText<'a>> {
        let open = self.take()?;
        let text = self.label_text(&open)?;
        self.close(&open, "PIPE")?;
        Some(ArrowText {
            span: self.span(open.span.start),
            text,
        })
    }
    pub(super) fn style_statement(&mut self) -> Option<StatementKind<'a>> {
        let keyword = self.take()?;
        self.require_space()?;
        let targets = self.id()?;
        self.require_space()?;
        let span_start = keyword.span.start;
        if keyword.kind == "CLASS" {
            let class = self.id()?;
            return Some(StatementKind::Class(ClassStatement {
                span: self.span(span_start),
                targets,
                class,
            }));
        }
        let styles = self.styles()?;
        let span = self.span(span_start);
        if keyword.kind == "CLASSDEF" {
            return Some(StatementKind::ClassDef(ClassDefStatement {
                span,
                id: targets,
                styles,
            }));
        }
        Some(StatementKind::Style(StyleStatement {
            span,
            targets,
            styles,
        }))
    }
    fn require_space(&mut self) -> Option<()> {
        if self.spaces() > 0 {
            return Some(());
        }
        self.unexpected("SPACE");
        None
    }
    fn styles(&mut self) -> Option<StylesOpt<'a>> {
        let start = self.position();
        let mut styles = vec![self.style()?];
        while self.kind() == "COMMA" {
            self.at += 1;
            styles.push(self.style()?);
        }
        Some(StylesOpt {
            span: self.span(start),
            styles,
        })
    }
    fn style(&mut self) -> Option<Style<'a>> {
        let start = self.position();
        let mut components = Vec::new();
        while matches!(
            self.kind(),
            "NUM" | "NODE_STRING" | "COLON" | "SPACE" | "BRKT" | "STYLE"
        ) {
            let token = self.take()?;
            components.push(StyleComponent {
                span: token.span,
                token,
            });
        }
        if components.is_empty() {
            self.unexpected("BRKT, COLON, NODE_STRING, NUM, SPACE, STYLE");
            return None;
        }
        Some(Style {
            span: self.span(start),
            components,
        })
    }
    pub(super) fn link_style(&mut self) -> Option<LinkStyleStatement<'a>> {
        let start = self.take()?.span.start;
        self.require_space()?;
        let default = if self.kind() == "DEFAULT" {
            self.take()
        } else {
            None
        };
        let indices = if default.is_none() {
            Some(self.num_list()?)
        } else {
            None
        };
        self.require_space()?;
        let interpolation = if self.kind() == "INTERPOLATE" {
            self.at += 1;
            self.require_space()?;
            Some(self.alpha_num()?)
        } else {
            None
        };
        self.spaces();
        let styles = if boundary(self.kind()) {
            None
        } else {
            Some(self.styles()?)
        };
        if interpolation.is_none() && styles.is_none() {
            self.unexpected("NODE_STRING");
            return None;
        }
        Some(LinkStyleStatement {
            span: self.span(start),
            default,
            indices,
            interpolation,
            styles,
        })
    }
    fn num_list(&mut self) -> Option<NumList<'a>> {
        let start = self.position();
        let mut indices = vec![self.require("NUM")?];
        while self.kind() == "COMMA" {
            self.at += 1;
            indices.push(self.require("NUM")?);
        }
        Some(NumList {
            span: self.span(start),
            indices,
        })
    }
    fn alpha_num(&mut self) -> Option<AlphaNum<'a>> {
        let start = self.position();
        let mut tokens = Vec::new();
        while alpha_kind(self.kind()) {
            tokens.push(self.take()?);
        }
        if tokens.is_empty() {
            self.unexpected(
                "AMP, BRKT, COLON, COMMA, DIR, DOWN, MINUS, MULT, NODE_STRING, NUM, UNICODE_TEXT",
            );
            return None;
        }
        Some(AlphaNum {
            span: self.span(start),
            tokens,
        })
    }
    pub(super) fn click(&mut self) -> Option<ClickStatement<'a>> {
        let id = self.take()?;
        let start = id.span.start;
        let mut result = ClickStatement {
            span: id.span,
            id,
            callback: None,
            arguments: None,
            url: None,
            tooltip: None,
            target: None,
        };
        self.click_action(&mut result)?;
        self.spaces();
        if self.kind() == "STR" {
            result.tooltip = self.take();
            self.spaces();
        }
        if self.kind() == "LINK_TARGET" {
            result.target = self.take();
        }
        if result.callback.is_some() && result.target.is_some() {
            self.unexpected("COMMENT, EOF, NEWLINE, SEMI");
            return None;
        }
        result.span = self.span(start);
        Some(result)
    }
    fn click_action(&mut self, result: &mut ClickStatement<'a>) -> Option<()> {
        if self.kind() == "HREF" {
            self.at += 1;
            result.url = Some(self.require("STR")?);
        } else if self.kind() == "STR" {
            result.url = self.take();
        } else if self.kind() == "CALLBACKNAME" {
            let t = self.take()?;
            result.callback = Some(AlphaNum {
                span: t.span,
                tokens: vec![t],
            });
            if self.kind() == "CALLBACKARGS" {
                result.arguments = self.take();
            }
        } else {
            result.callback = Some(self.alpha_num()?);
        }
        Some(())
    }
}
