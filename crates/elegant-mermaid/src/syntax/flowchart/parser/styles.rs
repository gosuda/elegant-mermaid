use super::*;

impl Parser<'_> {
    pub(super) fn styles(&mut self) -> Option<StylesOpt> {
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
    pub(super) fn style(&mut self) -> Statement {
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
    pub(super) fn class_def(&mut self) -> Statement {
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
    pub(super) fn class(&mut self) -> Statement {
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
    pub(super) fn num_list(&mut self) -> Option<NumList> {
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
    pub(super) fn alpha(&mut self) -> Option<AlphaNum> {
        let tokens = self.take_while(is_alpha_num_token);
        if tokens.is_empty() {
            return None;
        }
        Some(AlphaNum {
            span: token_span(&tokens),
            text: self.concat(&tokens),
        })
    }
    pub(super) fn link_style(&mut self) -> Statement {
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
}
