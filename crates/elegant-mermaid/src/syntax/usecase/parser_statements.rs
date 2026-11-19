use super::{
    ast::*,
    diagnostic,
    lexer::{Token, is_label, is_word},
    parser::{Parser, content_span},
};
use crate::source::Span;

impl<'a> Parser<'a> {
    pub(super) fn statement(&mut self) -> Option<StatementKind<'a>> {
        match self.kind() {
            "ACC_TITLE_LINE" | "ACC_DESCR_LINE" | "ACC_DESCR_BLOCK" => self.accessibility(),
            "DIRECTION" => self.direction(),
            "ACTOR" => self.actors().map(|a| StatementKind::Actor(Box::new(a))),
            "SYSTEM_BOUNDARY" => self
                .boundary()
                .map(|b| StatementKind::SystemBoundary(Box::new(b))),
            "NOTE" => self.note().map(StatementKind::Note),
            "JSON_DECLARATION_START" => self.json().map(StatementKind::Json),
            "CLASS_DEF" | "CLASS" | "STYLE" => self.style_statement(),
            "IDENTIFIER" | "PLAIN_STRING" | "MARKDOWN_STRING" => self.named_statement(),
            k if k.starts_with("UNCLOSED_") => {
                self.unexpected(&["STATEMENT"]);
                None
            }
            _ => {
                self.unknown();
                None
            }
        }
    }
    fn unknown(&mut self) {
        let Some(token) = self.take() else { return };
        self.recover();
        self.diagnostics.push(diagnostic(
            "usecase/unknown-statement",
            format!("unknown statement {}", token.text),
            self.span(token.span.start),
        ));
    }
    fn named_statement(&mut self) -> Option<StatementKind<'a>> {
        if self.peek(1).is_some_and(|t| t.kind == "METADATA_START") {
            return self
                .metadata_assignment()
                .map(StatementKind::MetadataAssignment);
        }
        let text = self.peek(0)?.text.clone();
        if [
            "allowmixing",
            "newpage",
            "package",
            "rectangle",
            "skinparam",
        ]
        .iter()
        .any(|s| text.eq_ignore_ascii_case(s))
        {
            self.unknown();
            return None;
        }
        let name = self.entity()?;
        let relation = self.optional_relation()?;
        Some(StatementKind::Entity(Box::new(EntityStatement {
            span: self.span(name.span.start),
            name,
            relation,
        })))
    }
    fn metadata_assignment(&mut self) -> Option<MetadataAssignmentStatement<'a>> {
        let token = self.take()?;
        let target = MetadataAssignmentTarget {
            span: token.span,
            content_span: content_span(&token),
            token,
        };
        let metadata = self.metadata()?;
        Some(MetadataAssignmentStatement {
            span: self.span(target.span.start),
            target,
            metadata,
        })
    }
    fn accessibility(&mut self) -> Option<StatementKind<'a>> {
        let token = self.take()?;
        let delimiter = if token.kind == "ACC_DESCR_BLOCK" {
            '{'
        } else {
            ':'
        };
        let offset = token.text.find(delimiter)? + 1;
        let closing = usize::from(delimiter == '{');
        let raw = token
            .text
            .get(offset..token.text.len().saturating_sub(closing))
            .unwrap_or("");
        let trimmed = raw.trim();
        let begin =
            self.cleaned.index(token.span.start) + offset + raw.len() - raw.trim_start().len();
        let value = self.cleaned.cow(begin, begin + trimmed.len());
        let content_span = self.cleaned.span(begin, begin + trimmed.len());
        let span = token.span;
        if token.kind == "ACC_TITLE_LINE" {
            return Some(StatementKind::AccTitle(AccTitleStatement {
                span,
                token,
                value,
                content_span,
            }));
        }
        Some(StatementKind::AccDescr(AccDescrStatement {
            span,
            token,
            value,
            content_span,
        }))
    }
    fn direction(&mut self) -> Option<StatementKind<'a>> {
        let keyword = self.take()?;
        let direction = self.one_of(&["TD", "TB", "BT", "LR", "RL"])?;
        Some(StatementKind::Direction(DirectionStatement {
            span: self.span(keyword.span.start),
            keyword,
            direction,
        }))
    }
    fn actors(&mut self) -> Option<ActorStatement<'a>> {
        let keyword = self.expect("ACTOR")?;
        let mut items = vec![self.actor_item()?];
        let relation = if self.kind() == "COMMA" {
            while self.kind() == "COMMA" {
                self.at += 1;
                items.push(self.actor_item()?);
            }
            None
        } else {
            self.optional_relation()?
        };
        Some(ActorStatement {
            span: self.span(keyword.span.start),
            keyword,
            items,
            relation,
        })
    }
    fn boundary(&mut self) -> Option<SystemBoundaryStatement<'a>> {
        let keyword = self.expect("SYSTEM_BOUNDARY")?;
        self.openings.push(keyword.clone());
        let name = self.boundary_name()?;
        let metadata = if self.kind() == "METADATA_START" {
            Some(self.metadata()?)
        } else {
            None
        };
        let classes = self.optional_classes()?;
        let line_end = self.line_end()?;
        let content = self.boundary_content();
        let close = self.expect("END")?;
        self.openings.pop();
        Some(SystemBoundaryStatement {
            span: self.span(keyword.span.start),
            keyword,
            name,
            metadata,
            classes,
            line_end,
            content,
            close,
        })
    }
    fn boundary_name(&mut self) -> Option<SystemBoundaryName<'a>> {
        let base = self.base_name(&["LPAREN", "LBRACKET"])?;
        Some(SystemBoundaryName {
            span: base.span,
            id_content_span: base.id_content_span,
            id: base.id,
            label: base.label,
            delimiters: base.delimiters,
        })
    }
    fn boundary_content(&mut self) -> SystemBoundaryContent<'a> {
        let start = self.here().start;
        let mut elements = Vec::new();
        while !matches!(self.kind(), "END" | "EOF") {
            let before = self.at;
            if let Some(element) = self.boundary_element() {
                elements.push(element);
            } else {
                self.recover();
                if self.kind() == "NEWLINE" {
                    self.at += 1;
                }
            }
            self.openings.truncate(1);
            if self.at == before {
                self.at += 1;
            }
        }
        SystemBoundaryContent {
            span: Span {
                start,
                end: self.here().start,
            },
            elements,
        }
    }
    fn boundary_element(&mut self) -> Option<BoundaryElement<'a>> {
        let kind = match self.spacing() {
            Some(LineKind::Blank(b)) => BoundaryElementKind::Blank(b),
            Some(LineKind::Comment(c)) => BoundaryElementKind::Comment(c),
            _ => self.boundary_declaration()?,
        };
        let span = match &kind {
            BoundaryElementKind::Blank(b) => b.span,
            BoundaryElementKind::Comment(c) => c.span,
            BoundaryElementKind::Actor(a) => a.span,
            BoundaryElementKind::Entity(n, _) => n.span,
        };
        Some(BoundaryElement { span, kind })
    }
    fn boundary_declaration(&mut self) -> Option<BoundaryElementKind<'a>> {
        if self.kind() == "ACTOR" {
            let keyword = self.take()?;
            let mut items = vec![self.actor_item()?];
            while self.kind() == "COMMA" {
                self.at += 1;
                items.push(self.actor_item()?);
            }
            let span = self.span(keyword.span.start);
            let line_end = self.line_end()?;
            let actor = ActorDeclarationOnly {
                span,
                keyword,
                items,
                line_end,
            };
            return Some(BoundaryElementKind::Actor(actor));
        }
        let name = self.entity()?;
        let line_end = self.line_end()?;
        Some(BoundaryElementKind::Entity(Box::new(name), line_end))
    }
    fn note(&mut self) -> Option<NoteStatement<'a>> {
        let keyword = self.expect("NOTE")?;
        let for_token = self.expect("FOR")?;
        let target = self.expect("IDENTIFIER")?;
        let label = self.label()?;
        Some(NoteStatement {
            span: self.span(keyword.span.start),
            keyword,
            for_token,
            target,
            label,
        })
    }
    fn style_statement(&mut self) -> Option<StatementKind<'a>> {
        let keyword = self.take()?;
        match keyword.kind {
            "CLASS" => self.class_assignment(keyword).map(StatementKind::Class),
            "CLASS_DEF" => self.class_definition(keyword).map(StatementKind::ClassDef),
            _ => {
                let target = self.expect("IDENTIFIER")?;
                let styles = self.styles()?;
                Some(StatementKind::Style(StyleStatement {
                    span: self.span(keyword.span.start),
                    keyword,
                    target,
                    styles,
                }))
            }
        }
    }
    fn class_assignment(&mut self, keyword: Token<'a>) -> Option<ClassStatement<'a>> {
        let targets = self.identifiers()?;
        let classes = self.identifiers()?;
        Some(ClassStatement {
            span: self.span(keyword.span.start),
            keyword,
            targets,
            classes,
        })
    }
    fn class_definition(&mut self, keyword: Token<'a>) -> Option<ClassDefStatement<'a>> {
        let classes = self.identifiers()?;
        let styles = self.styles()?;
        Some(ClassDefStatement {
            span: self.span(keyword.span.start),
            keyword,
            classes,
            styles,
        })
    }
    fn styles(&mut self) -> Option<Styles<'a>> {
        let start = self.here().start;
        let mut values = vec![self.style_value()?];
        while self.kind() == "COMMA" {
            self.at += 1;
            values.push(self.style_value()?);
        }
        Some(Styles {
            span: self.span(start),
            values,
        })
    }
    fn style_value(&mut self) -> Option<StyleValue<'a>> {
        let start = self.here().start;
        let mut key = Vec::new();
        if self.kind() == "MARKERLESS_SOLID" {
            key.push(self.take()?);
        }
        if !is_word(self.kind()) && self.kind() != "CSS_IDENTIFIER" {
            self.unexpected(&["CSS_IDENTIFIER", "MARKERLESS_SOLID", "WORD"]);
            return None;
        }
        key.push(self.take()?);
        self.expect("COLON")?;
        let mut components = Vec::new();
        while is_style_component(self.kind()) {
            let token = self.take()?;
            components.push(StyleComponent {
                span: token.span,
                token,
            });
        }
        if components.is_empty() {
            self.unexpected(&["STYLE_COMPONENT"]);
            return None;
        }
        Some(StyleValue {
            span: self.span(start),
            key,
            components,
        })
    }
    pub(super) fn optional_relation(&mut self) -> Option<Option<RelationTail<'a>>> {
        if matches!(self.kind(), "NEWLINE" | "EOF") {
            return Some(None);
        }
        let start = self.here().start;
        let (id, at) =
            if self.kind() == "IDENTIFIER" && self.peek(1).is_some_and(|t| t.kind == "AT") {
                (self.take(), self.take())
            } else {
                (None, None)
            };
        let arrow = self.arrow()?;
        let endpoint = self.entity()?;
        Some(Some(RelationTail {
            span: self.span(start),
            id,
            at,
            arrow,
            endpoint,
        }))
    }
    fn arrow(&mut self) -> Option<Arrow<'a>> {
        let token = self.one_of(ARROW_KINDS)?;
        let start = token.span.start;
        let kind = if matches!(token.kind, "DEPENDENCY_ARROW" | "GENERALIZATION") {
            ArrowKind::Semantic(self.semantic_relation(token)?)
        } else {
            self.association(token)?
        };
        Some(Arrow {
            span: self.span(start),
            kind,
        })
    }
    fn semantic_relation(&mut self, token: Token<'a>) -> Option<SemanticRelation<'a>> {
        let colon = if token.kind == "DEPENDENCY_ARROW" {
            Some(self.expect("COLON")?)
        } else {
            None
        };
        let relation = if colon.is_some() {
            Some(self.one_of(&["INCLUDE", "EXTEND"])?)
        } else {
            None
        };
        Some(SemanticRelation {
            span: self.span(token.span.start),
            operator: token,
            colon,
            relation,
        })
    }
    fn association(&mut self, token: Token<'a>) -> Option<ArrowKind<'a>> {
        let allowed: &[&str] = match (token.kind, &*token.text) {
            ("MARKERLESS_SOLID", "--") => &[
                "FORWARD_SOLID",
                "MARKERLESS_SOLID",
                "FORWARD_CIRCLE",
                "FORWARD_CROSS",
            ],
            ("BACKWARD_SOLID", "<--") | ("BACKWARD_CIRCLE", _) | ("BACKWARD_CROSS", _) => {
                &["MARKERLESS_SOLID"]
            }
            _ => &[],
        };
        let (label, right) = if self.labeled_right(allowed).is_some() {
            let label = self.label()?;
            let span = label.span;
            let right = self.one_of(allowed)?;
            (Some(EdgeLabel { span, label }), Some(right))
        } else {
            (None, None)
        };
        let span = self.span(token.span.start);
        Some(association_kind(token, span, label, right))
    }
    fn labeled_right(&self, allowed: &[&str]) -> Option<usize> {
        let mut n = 0;
        while let Some(token) = self.peek(n) {
            if n > 0 && allowed.contains(&token.kind) {
                return Some(n);
            }
            if !is_label(token.kind) && !matches!(token.kind, "PLAIN_STRING" | "MARKDOWN_STRING") {
                return None;
            }
            n += 1;
        }
        None
    }
}
fn association_kind<'a>(
    token: Token<'a>,
    span: Span,
    label: Option<EdgeLabel<'a>>,
    right: Option<Token<'a>>,
) -> ArrowKind<'a> {
    match token.kind {
        "FORWARD_SOLID" => ArrowKind::ForwardSolid(ForwardSolidOperator { span, token }),
        "FORWARD_CIRCLE" => ArrowKind::ForwardCircle(ForwardCircleOperator { span, token }),
        "FORWARD_CROSS" => ArrowKind::ForwardCross(ForwardCrossOperator { span, token }),
        _ => backward_association(token, span, label, right),
    }
}
fn backward_association<'a>(
    token: Token<'a>,
    span: Span,
    label: Option<EdgeLabel<'a>>,
    right: Option<Token<'a>>,
) -> ArrowKind<'a> {
    match token.kind {
        "BACKWARD_SOLID" => ArrowKind::BackwardSolid(BackwardSolidOperator {
            span,
            token,
            label,
            right,
        }),
        "BACKWARD_CIRCLE" => ArrowKind::BackwardCircle(BackwardCircleOperator {
            span,
            token,
            label,
            right,
        }),
        "BACKWARD_CROSS" => ArrowKind::BackwardCross(BackwardCrossOperator {
            span,
            token,
            label,
            right,
        }),
        _ => ArrowKind::MarkerlessSolid(MarkerlessSolidOperator {
            span,
            token,
            label,
            right,
        }),
    }
}
fn is_style_component(kind: &str) -> bool {
    is_word(kind)
        || matches!(
            kind,
            "PLAIN_STRING"
                | "NUMBER"
                | "HASH_COLOR"
                | "CSS_IDENTIFIER"
                | "CSS_ESCAPED_COMMA"
                | "DASH"
                | "DOT"
                | "PERCENT"
                | "CSS_PUNCTUATION"
                | "COLON"
                | "LPAREN"
                | "RPAREN"
                | "LBRACKET"
                | "RBRACKET"
                | "LBRACE"
                | "RBRACE"
                | "AT"
                | "MARKERLESS_SOLID"
        )
}

const ARROW_KINDS: &[&str] = &[
    "DEPENDENCY_ARROW",
    "GENERALIZATION",
    "FORWARD_SOLID",
    "BACKWARD_SOLID",
    "MARKERLESS_SOLID",
    "FORWARD_CIRCLE",
    "BACKWARD_CIRCLE",
    "FORWARD_CROSS",
    "BACKWARD_CROSS",
];
