//! Recursive-descent parser for `spec/grammar/block.md`.
//!
//! Errors record one diagnostic and skip to the next physical line end outside quoted
//! text, or stop before the enclosing composite's `end`; a skipped statement creates no
//! node.

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    BlockStatement, ClassDefStatement, ColumnsStatement, CssClassStatement, Document, Link,
    LinkedNode, Node, NodeShapeNLabel, NodeStatement, SpaceStatement, Start, Statement,
    StatementKind, StyleStatement,
};
use super::lexer::{Token, lex};
use super::{C_NESTING, C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

const MAX_DEPTH: usize = 64;

const STATEMENT_STARTS: [&str; 8] = [
    "BLOCK_DIAGRAM_KEY",
    "COLUMNS",
    "NODE_ID",
    "SPACE_BLOCK",
    "class",
    "classDef",
    "id-block",
    "style",
];

pub struct Parsed<'a> {
    pub document: Start<'a>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse<'a>(source: &'a str, removed: &[Span]) -> Parsed<'a> {
    let mut parser = Parser {
        src: source,
        tokens: lex(source, removed),
        at: 0,
        depth: 0,
        diags: Vec::new(),
    };
    let header = parser.expect("BLOCK_DIAGRAM_KEY").unwrap_or(Token {
        kind: "BLOCK_DIAGRAM_KEY",
        text: "",
        span: Span { start: 0, end: 0 },
    });
    let document = parser.document();
    let end = parser.content_end(header.span.end);
    Parsed {
        document: Start {
            span: Span {
                start: header.span.start,
                end,
            },
            header,
            document,
        },
        diagnostics: parser.diags,
    }
}

struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token<'a>>,
    at: usize,
    depth: usize,
    diags: Vec<Diagnostic>,
}

fn joined(start: Span, end: Span) -> Span {
    Span {
        start: start.start,
        end: end.end,
    }
}

impl<'a> Parser<'a> {
    fn token(&self) -> Token<'a> {
        self.tokens.get(self.at).copied().unwrap_or(Token {
            kind: "EOF",
            text: "",
            span: Span {
                start: self.src.len(),
                end: self.src.len(),
            },
        })
    }

    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |token| token.kind)
    }

    fn take(&mut self) -> Token<'a> {
        let token = self.token();
        if self.at < self.tokens.len() {
            self.at += 1;
        }
        token
    }

    fn content_end(&self, floor: usize) -> usize {
        self.tokens
            .iter()
            .take(self.at)
            .filter(|token| token.kind != "EOF" && token.kind != "UNTERMINATED")
            .fold(floor, |end, token| end.max(token.span.end))
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diags.push(diagnostic(code, message, span));
    }

    fn raw(&self, span: Span) -> &'a str {
        &self.src[span.start..span.end]
    }

    fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        if token.kind == "UNTERMINATED" {
            self.unterminated(token);
            return;
        }
        let mut names = expected.to_vec();
        names.sort_unstable();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.raw(token.span),
            names.join(", ")
        );
        self.issue(C_UNEXPECTED, message, token.span);
    }

    fn unterminated(&mut self, opener: Token<'a>) {
        if self
            .diags
            .iter()
            .any(|d| d.code == C_UNTERMINATED || d.code == C_NESTING)
        {
            return;
        }
        let mut span = opener.span;
        if opener.kind != "UNTERMINATED" {
            span.end = self.src.len();
        }
        self.issue(
            C_UNTERMINATED,
            format!("unterminated {}", opener.text),
            span,
        );
    }

    fn expect(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return Some(self.take());
        }
        self.unexpected(&[kind]);
        None
    }

    fn line_end(&self, from: usize) -> usize {
        let tail = self.src.get(from..).unwrap_or("");
        tail.find(['\n', '\r'])
            .map_or(self.src.len(), |offset| from + offset)
    }

    fn closes_composite(&self) -> bool {
        self.depth > 0 && self.kind() == "end"
    }

    fn at_end(&self) -> bool {
        matches!(self.kind(), "EOF" | "UNTERMINATED")
    }

    fn recover(&mut self) {
        if self.at_end() || self.closes_composite() {
            return;
        }
        let token = self.take();
        let limit = self.line_end(token.span.end);
        while !self.at_end() && !self.closes_composite() && self.token().span.start < limit {
            self.take();
        }
    }

    fn unknown_statement(&mut self) {
        let first = self.token();
        if first.kind == "UNTERMINATED" {
            self.unterminated(first);
            return;
        }
        let limit = self.line_end(first.span.end);
        self.recover();
        let end = first.span.end.max(limit.min(self.token().span.start));
        let message = format!("unknown statement {}", self.raw(first.span));
        self.issue(
            C_UNKNOWN,
            message,
            Span {
                start: first.span.start,
                end,
            },
        );
    }

    fn document(&mut self) -> Document<'a> {
        let start = self.token().span.start;
        let mark = self.diags.len();
        let mut statements = Vec::new();
        while !self.at_end() && !self.closes_composite() {
            let before = self.at;
            match self.statement() {
                Some(statement) => statements.push(statement),
                None if self.at == before => self.unknown_statement(),
                None => {}
            }
        }
        if statements.is_empty() && self.diags.len() == mark {
            self.unexpected(&STATEMENT_STARTS);
        }
        let end = statements.last().map_or(start, |last| last.span.end);
        Document {
            span: Span { start, end },
            statements,
        }
    }

    fn statement(&mut self) -> Option<Statement<'a>> {
        let start = self.token().span.start;
        let kind = self.statement_kind()?;
        Some(Statement {
            span: Span {
                start,
                end: self.content_end(start),
            },
            kind,
        })
    }

    fn statement_kind(&mut self) -> Option<StatementKind<'a>> {
        match self.kind() {
            "NODE_ID" => self
                .node_statement()
                .map(|statement| StatementKind::Node(Box::new(statement))),
            "COLUMNS" => {
                let token = self.take();
                Some(StatementKind::Columns(ColumnsStatement {
                    span: token.span,
                    token,
                }))
            }
            "SPACE_BLOCK" => {
                let token = self.take();
                Some(StatementKind::Space(SpaceStatement {
                    span: token.span,
                    token,
                }))
            }
            "BLOCK_DIAGRAM_KEY" | "id-block" => self
                .block_statement()
                .map(|statement| StatementKind::Block(Box::new(statement))),
            "classDef" => self.class_def_statement().map(StatementKind::ClassDef),
            "class" => self.css_class_statement().map(StatementKind::CssClass),
            "style" => self.style_statement().map(StatementKind::Style),
            _ => None,
        }
    }

    fn fail(&mut self, expected: &[&str]) {
        self.unexpected(expected);
        self.recover();
    }

    fn expect_or_fail(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return Some(self.take());
        }
        self.fail(&[kind]);
        None
    }

    fn node_statement(&mut self) -> Option<NodeStatement<'a>> {
        let first = self.node()?;
        let size = (self.kind() == "SIZE").then(|| self.take());
        let mut links = Vec::new();
        while matches!(self.kind(), "LINK" | "START_LINK") {
            let link = self.link()?;
            let node = self.node()?;
            links.push(LinkedNode { link, node });
        }
        if self.kind() == "SIZE" {
            let mut expected = vec!["EOF", "LINK", "START_LINK", "end"];
            expected.extend(STATEMENT_STARTS);
            self.fail(&expected);
            return None;
        }
        let span = Span {
            start: first.span.start,
            end: self.content_end(first.span.end),
        };
        Some(NodeStatement {
            span,
            first,
            size,
            links,
        })
    }

    fn node(&mut self) -> Option<Node<'a>> {
        let id = self.expect_or_fail("NODE_ID")?;
        let shape = match self.kind() {
            "NODE_DSTART" => Some(self.shape()?),
            "BLOCK_ARROW_START" => Some(self.arrow_shape()?),
            _ => None,
        };
        let end = shape.as_ref().map_or(id.span.end, |shape| shape.span.end);
        Some(Node {
            span: Span {
                start: id.span.start,
                end,
            },
            id,
            shape,
        })
    }

    fn shape(&mut self) -> Option<NodeShapeNLabel<'a>> {
        let open = self.take();
        let label = self.expect_or_fail("STR")?;
        let close = self.expect_or_fail("NODE_DEND")?;
        Some(NodeShapeNLabel {
            span: joined(open.span, close.span),
            open,
            label,
            close,
            dirs: Vec::new(),
        })
    }

    fn arrow_shape(&mut self) -> Option<NodeShapeNLabel<'a>> {
        let open = self.take();
        let label = self.expect_or_fail("STR")?;
        let mut dirs = Vec::new();
        while self.kind() == "DIR" {
            dirs.push(self.take());
        }
        if dirs.is_empty() {
            self.fail(&["DIR"]);
            return None;
        }
        let close = self.arrow_end()?;
        Some(NodeShapeNLabel {
            span: joined(open.span, close.span),
            open,
            label,
            close,
            dirs,
        })
    }

    fn arrow_end(&mut self) -> Option<Token<'a>> {
        if self.kind() == "BLOCK_ARROW_END" {
            return Some(self.take());
        }
        self.fail(&["BLOCK_ARROW_END", "DIR"]);
        None
    }

    fn link(&mut self) -> Option<Link<'a>> {
        if self.kind() == "LINK" {
            let end = self.take();
            return Some(Link {
                span: end.span,
                start: None,
                label: None,
                end,
            });
        }
        let start = self.take();
        self.expect_or_fail("LINK_LABEL")?;
        let text = self.expect_or_fail("STR")?;
        let end = self.expect_or_fail("LINK")?;
        Some(Link {
            span: joined(start.span, end.span),
            start: Some(start),
            label: Some(text),
            end,
        })
    }

    fn block_statement(&mut self) -> Option<BlockStatement<'a>> {
        let keyword = self.take();
        if self.depth + 1 > MAX_DEPTH {
            self.issue(C_NESTING, "nesting depth exceeds 64".into(), keyword.span);
            self.skip_composite();
            return None;
        }
        let header = if keyword.kind == "id-block" {
            Some(self.node_statement()?)
        } else {
            None
        };
        self.depth += 1;
        let body = self.document();
        self.depth -= 1;
        if self.kind() != "end" {
            let opener = self.opener_of(keyword);
            self.unterminated(opener);
            return None;
        }
        let end = self.take();
        Some(BlockStatement {
            span: joined(keyword.span, end.span),
            keyword,
            header,
            body,
            end,
        })
    }

    fn opener_of(&self, keyword: Token<'a>) -> Token<'a> {
        if self.kind() == "UNTERMINATED" {
            return self.token();
        }
        keyword
    }

    fn skip_composite(&mut self) {
        let mut level = 1usize;
        while !self.at_end() {
            match self.kind() {
                "BLOCK_DIAGRAM_KEY" | "id-block" => level += 1,
                "end" => level -= 1,
                _ => {}
            }
            self.take();
            if level == 0 {
                return;
            }
        }
    }

    fn class_def_statement(&mut self) -> Option<ClassDefStatement<'a>> {
        let keyword = self.take();
        let id = self.token();
        if id.kind != "CLASSDEF_ID" {
            self.fail(&["CLASSDEF_ID", "DEFAULT"]);
            return None;
        }
        self.take();
        let style = self.expect_or_fail("CLASSDEF_STYLEOPTS")?;
        Some(ClassDefStatement {
            span: joined(keyword.span, style.span),
            keyword,
            id,
            style,
        })
    }

    fn css_class_statement(&mut self) -> Option<CssClassStatement<'a>> {
        let keyword = self.take();
        let ids = self.expect_or_fail("CLASSENTITY_IDS")?;
        let class = self.expect_or_fail("STYLECLASS")?;
        Some(CssClassStatement {
            span: joined(keyword.span, class.span),
            keyword,
            ids,
            class,
        })
    }

    fn style_statement(&mut self) -> Option<StyleStatement<'a>> {
        let keyword = self.take();
        let ids = self.expect_or_fail("STYLE_ENTITY_IDS")?;
        let style = self.expect_or_fail("STYLE_DEFINITION_DATA")?;
        Some(StyleStatement {
            span: joined(keyword.span, style.span),
            keyword,
            ids,
            style,
        })
    }
}
