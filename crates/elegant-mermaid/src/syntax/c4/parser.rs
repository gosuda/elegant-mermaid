use super::{
    ast::*,
    diagnostic,
    lexer::{MACROS, Token, lex_cleaned},
};
use crate::{
    diag::Diagnostic,
    source::{Span, cleaned::Cleaned},
};

pub struct Parsed<'a> {
    pub document: Start<'a>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse<'a>(source: &'a str, removed: &[Span]) -> Parsed<'a> {
    let cleaned = Cleaned::new(source, removed);
    let mut parser = Parser {
        source,
        tokens: lex_cleaned(&cleaned),
        cleaned,
        at: 0,
        diagnostics: Vec::new(),
    };
    parser.newlines();
    let document = if parser.kind().starts_with("direction_") {
        parser.direction()
    } else {
        parser.mermaid_doc()
    };
    Parsed {
        document,
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    cleaned: Cleaned<'a>,
    tokens: Vec<Token<'a>>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Parser<'a> {
    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |token| token.kind)
    }
    fn take(&mut self) -> Option<Token<'a>> {
        let token = self.tokens.get(self.at)?.clone();
        self.at += 1;
        Some(token)
    }
    fn end(&self) -> usize {
        self.tokens
            .get(self.at.saturating_sub(1))
            .map_or(0, |token| token.span.end)
    }
    fn span(&self) -> Span {
        self.tokens.get(self.at).map_or(
            Span {
                start: self.source.len(),
                end: self.source.len(),
            },
            |token| token.span,
        )
    }
    fn newlines(&mut self) {
        while self.kind() == "NEWLINE" {
            self.at += 1;
        }
    }
    fn unexpected(&mut self, expected: &str) {
        if self.enclosing_unterminated() {
            return;
        }
        let span = self.span();
        let text = self.cleaned.slice(span);
        self.diagnostics.push(diagnostic(
            "c4/unexpected-token",
            format!("unexpected {text}, expected one of: {expected}"),
            span,
        ));
    }
    fn enclosing_unterminated(&mut self) -> bool {
        let span = self.span();
        let position = self
            .tokens
            .iter()
            .enumerate()
            .skip(self.at)
            .find(|(_, token)| {
                token.kind == "UNTERMINATED"
                    && token.span.start <= span.start
                    && span.end <= token.span.end
            })
            .map(|(index, _)| index);
        let Some(position) = position else {
            return false;
        };
        self.at = position;
        self.unterminated();
        true
    }
    fn expect(&mut self, expected: &'static str) -> Option<Token<'a>> {
        if self.kind() == expected {
            return self.take();
        }
        self.unexpected(expected);
        None
    }
    fn unterminated(&mut self) {
        let Some(token) = self.take() else { return };
        self.diagnostics.push(diagnostic(
            "c4/unterminated",
            format!("unterminated {}", token.text),
            token.span,
        ));
    }
    fn recover(&mut self) {
        while !matches!(self.kind(), "NEWLINE" | "RBRACE" | "EOF") {
            if self.kind() == "UNTERMINATED" {
                self.unterminated();
            } else {
                self.at += 1;
            }
        }
    }
    fn direction(&mut self) -> Start<'a> {
        let direction = self.take().unwrap_or(Token {
            kind: "direction_tb",
            text: std::borrow::Cow::Borrowed(""),
            span: Span { start: 0, end: 0 },
        });
        let span = direction.span;
        self.newlines();
        if self.kind() != "EOF" {
            self.unexpected("EOF");
        }
        Start {
            span,
            kind: StartKind::Direction(Direction { span, direction }),
        }
    }
    fn mermaid_doc(&mut self) -> Start<'a> {
        let header = self.header();
        let _ = self.expect("NEWLINE");
        let statements = self.statements(0);
        let span = Span {
            start: header.span.start,
            end: statements.span.end.max(header.span.end),
        };
        let graph_config = GraphConfig {
            span,
            header,
            statements,
        };
        Start {
            span,
            kind: StartKind::MermaidDoc(MermaidDoc { span, graph_config }),
        }
    }
    fn header(&mut self) -> Token<'a> {
        if matches!(
            self.kind(),
            "C4_CONTEXT" | "C4_CONTAINER" | "C4_COMPONENT" | "C4_DYNAMIC" | "C4_DEPLOYMENT"
        ) {
            return self.take().unwrap_or(Token {
                kind: "C4_CONTEXT",
                text: std::borrow::Cow::Borrowed(""),
                span: self.span(),
            });
        }
        self.unexpected("C4_COMPONENT, C4_CONTAINER, C4_CONTEXT, C4_DEPLOYMENT, C4_DYNAMIC");
        Token {
            kind: "C4_CONTEXT",
            text: std::borrow::Cow::Borrowed(""),
            span: self.span(),
        }
    }
    fn statements(&mut self, depth: usize) -> Statements<'a> {
        let start = self.span().start;
        let mut items = Vec::new();
        self.newlines();
        while self.kind() != "EOF" {
            if self.closing_boundary(depth) {
                break;
            }
            let before = self.at;
            if let Some(statement) = self.statement_line(depth) {
                items.push(statement);
            }
            if self.at == before {
                self.at += 1;
            }
            self.newlines();
        }
        if depth == 0 && items.is_empty() && self.diagnostics.is_empty() {
            self.unexpected("diagramStatement, otherStatement");
        }
        let span = Span {
            start: items.first().map_or(start, |item| item.span().start),
            end: items.last().map_or(start, |item| item.span().end),
        };
        Statements { span, items }
    }
    fn statement_line(&mut self, depth: usize) -> Option<Statement<'a>> {
        let statement = self.statement(depth);
        if !matches!(self.kind(), "NEWLINE" | "RBRACE" | "EOF") {
            if statement.is_some() {
                self.unexpected("EOF, NEWLINE, RBRACE");
            }
            self.recover();
            return None;
        }
        if statement.is_none() {
            self.recover();
        }
        statement
    }
    fn closing_boundary(&mut self, depth: usize) -> bool {
        if self.kind() != "RBRACE" {
            return false;
        }
        if depth > 0 {
            return true;
        }
        self.unexpected("EOF");
        self.at += 1;
        self.newlines();
        self.kind() == "EOF"
    }
    fn statement(&mut self, depth: usize) -> Option<Statement<'a>> {
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
            return None;
        }
        if is_other(self.kind()) {
            return self.other().map(Statement::Other);
        }
        if MACROS.iter().any(|(_, kind, _)| *kind == self.kind()) {
            return self
                .diagram(depth)
                .map(|node| Statement::Diagram(Box::new(node)));
        }
        let token = self.take()?;
        self.recover();
        self.diagnostics.push(diagnostic(
            "c4/unknown-statement",
            format!("unknown statement {}", token.text),
            Span {
                start: token.span.start,
                end: self.end().max(token.span.end),
            },
        ));
        None
    }
    fn other(&mut self) -> Option<OtherStatement<'a>> {
        let token = self.take()?;
        let value = match token.kind {
            "acc_title" => self.expect("acc_title_value")?,
            "acc_descr" => self.expect("acc_descr_value")?,
            "title" | "accDescription" => self.text_value(&token)?,
            _ => token.clone(),
        };
        Some(OtherStatement {
            span: Span {
                start: token.span.start,
                end: value.span.end,
            },
            form: token.kind,
            value,
        })
    }
    fn diagram(&mut self, depth: usize) -> Option<DiagramStatement<'a>> {
        let macro_token = self.take()?;
        let attributes = self.attributes()?;
        let span = Span {
            start: macro_token.span.start,
            end: attributes.span.end,
        };
        if !is_boundary(macro_token.kind) {
            return Some(DiagramStatement {
                span,
                kind: DiagramStatementKind::Call {
                    macro_token,
                    attributes,
                },
            });
        }
        let start = BoundaryStart {
            span,
            macro_token,
            attributes,
        };
        let boundary = self.boundary(start, depth)?;
        Some(DiagramStatement {
            span: boundary.span,
            kind: DiagramStatementKind::Boundary(Box::new(boundary)),
        })
    }
    fn attributes(&mut self) -> Option<Attributes<'a>> {
        let open = self.expect("LPAREN")?;
        let mut items = Vec::new();
        while matches!(self.kind(), "STR" | "STR_KEY" | "ATTRIBUTE_EMPTY") {
            items.push(self.attribute()?);
        }
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
            return None;
        }
        if items.is_empty() {
            self.unexpected("ATTRIBUTE_EMPTY, STR, STR_KEY");
            return None;
        }
        let close = self.expect("RPAREN")?;
        Some(Attributes {
            span: Span {
                start: open.span.start,
                end: close.span.end,
            },
            items,
        })
    }
    fn attribute(&mut self) -> Option<Attribute<'a>> {
        let token = self.take()?;
        let start = token.span.start;
        let kind = match token.kind {
            "STR_KEY" => AttributeKind::Named {
                key: token,
                value: self.expect("STR_VALUE")?,
            },
            "ATTRIBUTE_EMPTY" => AttributeKind::Empty(token),
            _ => AttributeKind::Positional(token),
        };
        Some(Attribute {
            span: Span {
                start,
                end: self.end(),
            },
            kind,
        })
    }
    fn boundary(
        &mut self,
        start: BoundaryStart<'a>,
        depth: usize,
    ) -> Option<BoundaryStatement<'a>> {
        let brace = self.boundary_brace()?;
        if depth >= 64 {
            self.diagnostics.push(diagnostic(
                "limit/nesting-depth",
                "nesting depth exceeds 64".into(),
                brace.span,
            ));
            self.at = self.tokens.len();
            return None;
        }
        let begin = start.span.start;
        let start = BoundaryStartStatement {
            span: Span {
                start: begin,
                end: brace.span.end,
            },
            start,
            brace,
        };
        let starts_with_diagram = is_diagram(self.kind());
        if !starts_with_diagram && self.kind() != "EOF" {
            self.unexpected("diagramStatement");
        }
        let statements = self.statements(depth + 1);
        if self.kind() == "EOF" {
            self.open_boundary_error(start.brace.span);
            return None;
        }
        let close = self.expect("RBRACE")?;
        if !starts_with_diagram {
            return None;
        }
        let span = Span {
            start: begin,
            end: close.span.end,
        };
        let body = DiagramStatements {
            span: statements.span,
            items: statements.items,
        };
        let stop = BoundaryStopStatement {
            span: close.span,
            close,
        };
        Some(BoundaryStatement {
            span,
            start,
            body,
            stop,
        })
    }
    fn boundary_brace(&mut self) -> Option<Token<'a>> {
        if self.kind() == "NEWLINE" {
            self.at += 1;
            let brace = self.expect("LBRACE")?;
            if self.kind() == "NEWLINE" {
                self.at += 1;
            }
            return Some(brace);
        }
        let brace = self.expect("LBRACE")?;
        if self.kind() == "EOF" {
            self.open_boundary_error(brace.span);
            return None;
        }
        self.expect("NEWLINE")?;
        Some(brace)
    }
    fn open_boundary_error(&mut self, open: Span) {
        if self
            .diagnostics
            .iter()
            .any(|d| d.code == "limit/nesting-depth")
        {
            return;
        }
        self.diagnostics.push(diagnostic(
            "c4/unterminated",
            "unterminated {".into(),
            Span {
                start: open.start,
                end: self.source.len(),
            },
        ));
    }
}

fn is_other(kind: &str) -> bool {
    matches!(
        kind,
        "title" | "accDescription" | "acc_title" | "acc_descr" | "acc_descr_multiline_value"
    )
}
fn is_diagram(kind: &str) -> bool {
    MACROS.iter().any(|(_, token, _)| *token == kind)
}
fn is_boundary(kind: &str) -> bool {
    matches!(
        kind,
        "BOUNDARY"
            | "ENTERPRISE_BOUNDARY"
            | "SYSTEM_BOUNDARY"
            | "CONTAINER_BOUNDARY"
            | "NODE"
            | "NODE_L"
            | "NODE_R"
    )
}
impl<'a> Parser<'a> {
    fn text_value(&self, token: &Token<'a>) -> Option<Token<'a>> {
        let rest = token.text.strip_prefix(token.kind)?;
        let separator = rest.chars().next()?;
        let prefix = token.kind.len() + separator.len_utf8();
        let begin = self.cleaned.index(token.span.start) + prefix;
        let end = begin + token.text.get(prefix..)?.len();
        Some(Token {
            kind: token.kind,
            text: self.cleaned.cow(begin, end),
            span: Span {
                start: self.cleaned.offset(begin),
                end: token.span.end,
            },
        })
    }
}
