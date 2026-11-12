//! Hand-written recursive-descent parser of the flowchart grammar, `flowchart-034`.
//!
//! One failed statement is dropped at its statement boundary (`flowchart-052`); the
//! parser never backtracks over a consumed token.

use crate::diag::{Diagnostic, Edit, Fix, FixSafety, Severity};
use crate::source::Span;
use crate::syntax::flowchart::ast::{
    AccDescr, AccDescrBlock, AccTitle, AlphaNum, ArrowText, ClassDefStatement, ClassStatement,
    ClickAction, ClickStatement, Direction, Document, EdgeText, GraphConfig, IdString, Label,
    LabelForm, Line, Link, LinkSelector, LinkStatement, LinkStyleStatement, NodeGroup, NumList,
    ShapeData, Statement, StyleStatement, StyledVertex, StylesOpt, Subgraph, Text, TextKind,
    TextNoTags, TrapCloser, Vertex, VertexStatement,
};
use crate::syntax::flowchart::diagnostic;
use crate::syntax::flowchart::lexer::Lexer;
use crate::syntax::flowchart::tokens::{
    TextVal, Token, TokenKind, is_alpha_num_token, is_id_token, is_text_no_tags_token,
};

const C_UNEXPECTED_TOKEN: &str = "flowchart/unexpected-token";
const C_UNKNOWN_STATEMENT: &str = "flowchart/unknown-statement";
const C_UNTERMINATED: &str = "flowchart/unterminated";
const C_UNCLOSED_BRACKET: &str = "flowchart/unclosed-node-bracket";
const C_ARROW_INVALID: &str = "flowchart/arrow-invalid";
const C_LINK_MARKER: &str = "flowchart/link-unsupported-marker";
const C_LABEL_DOUBLE_IN_DOUBLE: &str = "flowchart/label-double-in-double";
const C_LABEL_QUOTE_IN_UNQUOTED: &str = "flowchart/label-quote-in-unquoted";
const C_LABEL_PARENS_UNQUOTED: &str = "flowchart/label-parens-unquoted";
const C_LINK_MISSING: &str = "flowchart/link-missing";
const C_META_UNSUPPORTED: &str = "flowchart/meta-unsupported";
const C_END_WITHOUT_SUBGRAPH: &str = "flowchart/end-without-subgraph";
const C_NODE_MIXED_BRACKETS: &str = "flowchart/node-mixed-brackets";
const C_NODE_EMPTY: &str = "flowchart/node-empty";
const C_CLASS_MALFORMED: &str = "flowchart/class-malformed";
const C_LINKSTYLE_MULTILINE: &str = "flowchart/linkstyle-multiline";
const C_LINKSTYLE_RANGE: &str = "flowchart/linkstyle-range-not-supported";
const C_CLICK_EXTRA: &str = "flowchart/click-call-extra-text";

const SEPARATORS: [TokenKind; 3] = [TokenKind::Newline, TokenKind::Semi, TokenKind::Eof];

/// The tree of one parse, with the diagnostics it raised.
pub struct Parsed {
    pub document: Document,
    pub diagnostics: Vec<Diagnostic>,
}

struct Parser<'a> {
    src: &'a str,
    lexer: Lexer<'a>,
    cur: Token,
    prev: Token,
    diags: Vec<Diagnostic>,
    open_subgraphs: Vec<Span>,
    bracket_reported: bool,
}

/// Parses `src`, skipping the bytes of `removed`.
pub fn parse(src: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser::new(src, removed);
    let document = parser.parse_document();
    let mut diagnostics = std::mem::take(&mut parser.diags);
    if !parser.bracket_reported
        && let Some(diagnostic) = parser.lexer.end_state()
    {
        diagnostics.push(diagnostic);
    }
    diagnostics.extend(parser.lexer.into_diags());
    crate::diag::sort(&mut diagnostics);
    Parsed {
        document,
        diagnostics,
    }
}

impl<'a> Parser<'a> {
    fn new(src: &'a str, removed: &'a [Span]) -> Parser<'a> {
        let mut lexer = Lexer::new(src, removed);
        let cur = lexer.next_token();
        let prev = cur.clone();
        Parser {
            src,
            lexer,
            cur,
            prev,
            diags: Vec::new(),
            open_subgraphs: Vec::new(),
            bracket_reported: false,
        }
    }

    fn text<'s>(&'s self, token: &'s Token) -> &'s str {
        token.text(self.src)
    }

    fn raw(&self, span: Span) -> &'a str {
        self.src.get(span.start..span.end).unwrap_or("")
    }

    fn bump(&mut self) {
        let mut token = self.lexer.next_token();
        while token.kind == TokenKind::Space {
            token = self.lexer.next_token();
        }
        self.prev = std::mem::replace(&mut self.cur, token);
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.cur.kind == kind
    }

    fn at_separator(&self) -> bool {
        SEPARATORS.contains(&self.cur.kind)
    }

    fn eat(&mut self, kind: TokenKind) -> Option<Token> {
        if self.cur.kind != kind {
            return None;
        }
        let token = self.cur.clone();
        self.bump();
        Some(token)
    }

    fn raise(&mut self, code: &'static str, span: Span, message: impl Into<String>) {
        self.diags
            .push(diagnostic(code, Severity::Error, message.into(), span));
    }

    fn raise_with_fix(
        &mut self,
        code: &'static str,
        span: Span,
        message: impl Into<String>,
        title: &str,
        safety: FixSafety,
        edit: Edit,
    ) {
        let mut diagnostic = diagnostic(code, Severity::Error, message.into(), span);
        diagnostic.fixes.push(Fix {
            title: title.to_owned(),
            safety,
            edits: vec![edit],
        });
        self.diags.push(diagnostic);
    }

    fn unexpected(&mut self, kinds: &[TokenKind]) -> bool {
        if self.at(TokenKind::Eof) {
            return false;
        }
        let span = self.cur.span;
        let raw = self.raw(span);
        let mut names: Vec<&'static str> = kinds.iter().map(|k| k.as_str()).collect();
        names.sort_unstable();
        let message = format!("unexpected {raw}, expected one of: {}", names.join(", "));
        self.raise(C_UNEXPECTED_TOKEN, span, message);
        true
    }

    fn recover(&mut self) {
        let initial = self.cur.span;
        let boundary = self.lexer.abort_to_boundary(self.cur.span.start);
        if self.at_separator() {
            return;
        }
        let mut guard = 0usize;
        while !self.at_separator() {
            if self.cur.span.start >= boundary || guard > 4096 {
                break;
            }
            guard += 1;
            self.bump();
        }
        if matches!(self.cur.kind, TokenKind::Newline | TokenKind::Semi) {
            self.bump();
        }
        if !self.at(TokenKind::Eof) && self.cur.span == initial {
            self.bump();
        }
    }

    fn skip_separators(&mut self) {
        while matches!(self.cur.kind, TokenKind::Newline | TokenKind::Semi) {
            self.bump();
        }
    }

    fn parse_document(&mut self) -> Document {
        if self.at(TokenKind::Eof) {
            self.diags.push(diagnostic(
                "common/empty-source",
                Severity::Error,
                String::from("source is empty"),
                Span { start: 0, end: 0 },
            ));
            return Document {
                span: Span { start: 0, end: 0 },
                config: GraphConfig {
                    span: Span { start: 0, end: 0 },
                    keyword: Span { start: 0, end: 0 },
                    direction: None,
                },
                lines: Vec::new(),
            };
        }
        let config = self.parse_header();
        let mut lines = Vec::new();
        loop {
            self.skip_separators();
            if self.at(TokenKind::Eof) {
                break;
            }
            if let Some(line) = self.parse_statement() {
                lines.push(line);
            }
            if !self.at_separator() {
                self.recover();
            }
            self.skip_separators();
        }
        let span = lines.first().map_or(config.span, |first| Span {
            start: config.span.start.min(first.span.start),
            end: self.prev.span.end.max(first.span.end),
        });
        Document {
            span,
            config,
            lines,
        }
    }

    fn parse_header(&mut self) -> GraphConfig {
        if !self.at(TokenKind::Graph) {
            let token = self.cur.clone();
            let raw = self.raw(token.span).to_owned();
            self.raise(
                "common/unknown-diagram-kind",
                token.span,
                format!("unknown diagram kind {raw}"),
            );
            return GraphConfig {
                span: token.span,
                keyword: token.span,
                direction: None,
            };
        }
        let keyword = self.cur.span;
        self.bump();
        let mut end = keyword.end;
        let mut direction = None;
        if self.at(TokenKind::Dir) {
            direction = Some(self.cur.span);
            end = self.cur.span.end;
            self.bump();
        } else if self.at(TokenKind::Nodir) {
            end = self.cur.span.end.max(end);
            self.bump();
            return GraphConfig {
                span: Span {
                    start: keyword.start,
                    end,
                },
                keyword,
                direction,
            };
        }
        if self.at_separator() {
            self.bump();
        } else {
            let kinds = [
                TokenKind::Eof,
                TokenKind::Newline,
                TokenKind::Semi,
                TokenKind::Space,
            ];
            if self.unexpected(&kinds) {
                self.recover();
            }
        }
        GraphConfig {
            span: Span {
                start: keyword.start,
                end,
            },
            keyword,
            direction,
        }
    }

    fn parse_statement(&mut self) -> Option<Line> {
        let start = self.cur.span.start;
        let kind = match self.cur.kind {
            TokenKind::Style => self.parse_style(),
            TokenKind::ClassDef => self.parse_class_def(),
            TokenKind::Class => self.parse_class(),
            TokenKind::LinkStyle => self.parse_link_style(),
            TokenKind::Click => self.parse_click(),
            TokenKind::Subgraph => self.parse_subgraph(),
            TokenKind::End => self.parse_stray_end(),
            TokenKind::DirectionTb
            | TokenKind::DirectionBt
            | TokenKind::DirectionRl
            | TokenKind::DirectionLr
            | TokenKind::DirectionTd => self.parse_direction(),
            TokenKind::AccTitle => self.parse_acc_title(),
            TokenKind::AccDescr => self.parse_acc_descr(),
            TokenKind::AccDescrMultilineValue => self.parse_acc_descr_block(),
            _ if self.starts_node() => self.parse_vertex_statement(),
            _ => self.parse_unknown(),
        }?;
        let end = self.prev.span.end.max(start);
        Some(Line {
            span: Span { start, end },
            kind,
        })
    }

    fn starts_node(&self) -> bool {
        is_id_token(self.cur.kind) || label_form_of(self.cur.kind).is_some()
    }

    fn parse_unknown(&mut self) -> Option<Statement> {
        let first = self.cur.clone();
        let boundary = self.lexer.statement_boundary(first.span.start);
        let span = Span {
            start: first.span.start,
            end: boundary,
        };
        if matches!(self.text(&first), "title" | "author" | "date") {
            self.raise(
                C_META_UNSUPPORTED,
                span,
                String::from("A meta statement such as title appears in a flowchart"),
            );
        } else {
            let message = format!("unknown statement {}", self.raw(first.span));
            self.raise(C_UNKNOWN_STATEMENT, span, message);
        }
        self.recover();
        None
    }

    fn parse_direction(&mut self) -> Option<Statement> {
        let span = self.cur.span;
        self.bump();
        Some(Statement::Direction(Direction { span }))
    }

    fn parse_acc_title(&mut self) -> Option<Statement> {
        let keyword = self.cur.span;
        self.bump();
        let Some(value) = self.eat(TokenKind::AccTitleValue) else {
            if self.unexpected(&[TokenKind::AccTitleValue]) {
                self.recover();
            }
            return None;
        };
        Some(Statement::AccTitle(AccTitle {
            span: Span {
                start: keyword.start,
                end: value.span.end,
            },
            value: value.span,
        }))
    }

    fn parse_acc_descr(&mut self) -> Option<Statement> {
        let keyword = self.cur.span;
        self.bump();
        let Some(value) = self.eat(TokenKind::AccDescrValue) else {
            if self.unexpected(&[TokenKind::AccDescrValue]) {
                self.recover();
            }
            return None;
        };
        Some(Statement::AccDescr(AccDescr {
            span: Span {
                start: keyword.start,
                end: value.span.end,
            },
            value: value.span,
        }))
    }

    fn parse_acc_descr_block(&mut self) -> Option<Statement> {
        let start = self.cur.span.start;
        let mut end = start;
        while self.at(TokenKind::AccDescrMultilineValue) {
            end = self.cur.span.end;
            self.bump();
        }
        Some(Statement::AccDescrBlock(AccDescrBlock {
            span: Span { start, end },
            value: Span { start, end },
        }))
    }

    fn parse_style(&mut self) -> Option<Statement> {
        let keyword = self.cur.span;
        self.bump();
        let target = self.parse_id_string();
        let styles = self.parse_styles_opt()?;
        Some(Statement::Style(StyleStatement {
            span: Span {
                start: keyword.start,
                end: styles.span.end,
            },
            target,
            styles,
        }))
    }

    fn parse_class_def(&mut self) -> Option<Statement> {
        let keyword = self.cur.span;
        self.bump();
        let names = self.parse_id_string();
        let styles = self.parse_styles_opt()?;
        Some(Statement::ClassDef(ClassDefStatement {
            span: Span {
                start: keyword.start,
                end: styles.span.end,
            },
            names,
            styles,
        }))
    }

    fn parse_class(&mut self) -> Option<Statement> {
        let keyword = self.cur.span;
        self.bump();
        let targets = self.parse_id_string();
        let end = targets.span.end.max(keyword.end);
        if targets.text.is_empty() || self.at_separator() {
            self.raise(
                C_CLASS_MALFORMED,
                Span {
                    start: keyword.start,
                    end,
                },
                String::from("A class statement is missing node ids or the class name"),
            );
            self.recover();
            return None;
        }
        let class_name = self.parse_id_string();
        if class_name.text.is_empty() {
            self.raise(
                C_CLASS_MALFORMED,
                Span {
                    start: keyword.start,
                    end,
                },
                String::from("A class statement is missing node ids or the class name"),
            );
            self.recover();
            return None;
        }
        Some(Statement::Class(ClassStatement {
            span: Span {
                start: keyword.start,
                end: class_name.span.end,
            },
            targets,
            class_name,
        }))
    }

    fn parse_link_style(&mut self) -> Option<Statement> {
        let keyword = self.cur.span;
        self.bump();
        let selector = if let Some(token) = self.eat(TokenKind::Default) {
            LinkSelector::Default(token.span)
        } else {
            LinkSelector::NumList(self.parse_num_list()?)
        };
        let mut interpolate = None;
        if self.at(TokenKind::Interpolate) {
            self.bump();
            interpolate = Some(self.parse_alpha_num());
        }
        if self.at(TokenKind::Newline) {
            let after = self.cur.span.end;
            self.raise(
                C_LINKSTYLE_MULTILINE,
                Span {
                    start: after,
                    end: after,
                },
                String::from("The linkStyle style pairs are placed on a line after the indices"),
            );
            return None;
        }
        let styles = if self.at_separator() {
            None
        } else {
            Some(self.parse_styles_opt()?)
        };
        let end = styles
            .as_ref()
            .map_or_else(|| self.prev.span.end, |value| value.span.end)
            .max(
                interpolate
                    .as_ref()
                    .map_or(keyword.end, |value| value.span.end),
            );
        Some(Statement::LinkStyle(LinkStyleStatement {
            span: Span {
                start: keyword.start,
                end,
            },
            selector,
            interpolate,
            styles,
        }))
    }

    fn parse_num_list(&mut self) -> Option<NumList> {
        let Some(first) = self.eat(TokenKind::Num) else {
            if self.unexpected(&[TokenKind::Default, TokenKind::Num]) {
                self.recover();
            }
            return None;
        };
        let mut numbers = vec![first.span];
        loop {
            if self.at(TokenKind::Colon) {
                let span = self.cur.span;
                self.raise(
                    C_LINKSTYLE_RANGE,
                    span,
                    String::from("A range such as 0:3 is used in the linkStyle index list"),
                );
                self.recover();
                return None;
            }
            if !self.at(TokenKind::Comma) {
                break;
            }
            self.bump();
            let Some(next) = self.eat(TokenKind::Num) else {
                if self.unexpected(&[TokenKind::Num]) {
                    self.recover();
                }
                return None;
            };
            numbers.push(next.span);
        }
        let end = numbers.last().map_or(first.span.end, |span| span.end);
        Some(NumList {
            span: Span {
                start: first.span.start,
                end,
            },
            numbers,
        })
    }

    fn parse_styles_opt(&mut self) -> Option<StylesOpt> {
        let start = self.cur.span.start;
        let mut styles = Vec::new();
        loop {
            let style = self.parse_style_run();
            if style.is_empty() {
                let kinds = [
                    TokenKind::Brkt,
                    TokenKind::Colon,
                    TokenKind::NodeString,
                    TokenKind::Num,
                    TokenKind::Style,
                ];
                if self.unexpected(&kinds) {
                    self.recover();
                }
                return None;
            }
            styles.push(style);
            if !self.at(TokenKind::Comma) {
                break;
            }
            self.bump();
        }
        Some(StylesOpt {
            span: Span {
                start,
                end: self.prev.span.end.max(start),
            },
            styles,
        })
    }

    fn parse_style_run(&mut self) -> String {
        let mut out = String::new();
        while is_style_token(self.cur.kind) {
            let chunk = self.text(&self.cur).to_owned();
            out.push_str(&chunk);
            self.bump();
        }
        out
    }

    fn parse_click(&mut self) -> Option<Statement> {
        let keyword = self.cur.span;
        self.bump();
        if self.at_separator() {
            let kinds = [TokenKind::Click, TokenKind::Str, TokenKind::NodeString];
            if self.unexpected(&kinds) {
                self.recover();
            }
            return None;
        }
        let target = self.cur.span;
        self.bump();
        let action = self.parse_click_action()?;
        Some(Statement::Click(ClickStatement {
            span: Span {
                start: keyword.start,
                end: self.prev.span.end.max(keyword.end),
            },
            target,
            action,
        }))
    }

    fn parse_click_action(&mut self) -> Option<ClickAction> {
        if self.at(TokenKind::CallbackName) {
            return self.parse_callback();
        }
        let had_href = self.eat(TokenKind::Href).is_some();
        if self.at(TokenKind::Str) {
            return self.parse_link_action(had_href);
        }
        if had_href {
            if self.unexpected(&[TokenKind::Str]) {
                self.recover();
            }
            return None;
        }
        let name = self.parse_alpha_num();
        if name.text.is_empty() {
            let kinds = [
                TokenKind::CallbackName,
                TokenKind::Href,
                TokenKind::NodeString,
                TokenKind::Num,
                TokenKind::Str,
                TokenKind::UnicodeText,
            ];
            if self.unexpected(&kinds) {
                self.recover();
            }
            return None;
        }
        let tooltip = self.string_text();
        Some(ClickAction::PlainCall {
            name: name.text,
            tooltip,
        })
    }

    fn parse_callback(&mut self) -> Option<ClickAction> {
        let name = self.text(&self.cur).to_owned();
        self.bump();
        let args = if self.at(TokenKind::CallbackArgs) {
            let args = self.text(&self.cur).to_owned();
            self.bump();
            Some(args)
        } else {
            None
        };
        if self.at(TokenKind::LinkTarget) || (args.is_some() && self.at(TokenKind::Str)) {
            let span = self.cur.span;
            self.raise(
                C_CLICK_EXTRA,
                span,
                String::from(
                    "A click call statement carries tooltip or target text after call fn()",
                ),
            );
            self.recover();
            return None;
        }
        let tooltip = self.string_text();
        Some(ClickAction::Call {
            name,
            args,
            tooltip,
        })
    }

    fn parse_link_action(&mut self, had_href: bool) -> Option<ClickAction> {
        let _ = had_href;
        let href = self.text(&self.cur).to_owned();
        self.bump();
        let mut tooltip = None;
        let mut target = None;
        if self.at(TokenKind::Str) {
            tooltip = Some(self.text(&self.cur).to_owned());
            self.bump();
        }
        if self.at(TokenKind::LinkTarget) {
            target = Some(self.text(&self.cur).to_owned());
            self.bump();
        }
        Some(ClickAction::Link {
            href,
            tooltip,
            target,
        })
    }

    fn string_text(&mut self) -> Option<String> {
        let token = self.eat(TokenKind::Str)?;
        Some(self.text(&token).to_owned())
    }

    fn parse_alpha_num(&mut self) -> AlphaNum {
        let start = self.cur.span.start;
        let mut text = String::new();
        while is_alpha_num_token(self.cur.kind) {
            let chunk = self.text(&self.cur).to_owned();
            text.push_str(&chunk);
            self.bump();
        }
        AlphaNum {
            span: Span {
                start,
                end: self.prev.span.end.max(start),
            },
            text,
        }
    }

    fn parse_id_string(&mut self) -> IdString {
        let start = self.cur.span.start;
        let mut text = String::new();
        while is_id_token(self.cur.kind) {
            let chunk = self.text(&self.cur).to_owned();
            text.push_str(&chunk);
            self.bump();
        }
        IdString {
            span: Span {
                start,
                end: self.prev.span.end.max(start),
            },
            text,
        }
    }

    fn parse_stray_end(&mut self) -> Option<Statement> {
        let span = self.cur.span;
        let end = line_after(self.src, span.end);
        self.bump();
        self.raise_with_fix(
            C_END_WITHOUT_SUBGRAPH,
            span,
            String::from("end appears without a matching subgraph"),
            "Remove the stray end line",
            FixSafety::Unsafe,
            Edit {
                span: Span {
                    start: span.start,
                    end,
                },
                new_text: String::new(),
            },
        );
        None
    }

    fn parse_subgraph(&mut self) -> Option<Statement> {
        let keyword = self.cur.span;
        self.bump();
        self.open_subgraphs.push(keyword);
        let mut id = None;
        if !self.at_separator() && !self.at(TokenKind::Sqs) {
            id = Some(self.parse_text_no_tags());
        }
        let mut title = None;
        if self.at(TokenKind::Sqs) {
            self.bump();
            title = self.parse_text(&[TokenKind::Sqe]);
            if self.eat(TokenKind::Sqe).is_none() {
                if self.unexpected(&[TokenKind::Sqe]) {
                    self.recover_nested();
                }
                return None;
            }
        }
        if matches!(self.cur.kind, TokenKind::Newline | TokenKind::Semi) {
            self.bump();
        } else if !self.at(TokenKind::Eof) && !self.at(TokenKind::End) {
            let kinds = [
                TokenKind::Eof,
                TokenKind::Newline,
                TokenKind::Semi,
                TokenKind::Sqs,
            ];
            if self.unexpected(&kinds) {
                self.recover_nested();
                return None;
            }
        }
        let mut body = Vec::new();
        let end_span = loop {
            self.skip_separators();
            if self.at(TokenKind::Eof) {
                self.raise(
                    C_UNTERMINATED,
                    Span {
                        start: keyword.start,
                        end: self.src.len(),
                    },
                    String::from("unterminated subgraph"),
                );
                self.open_subgraphs.pop();
                return None;
            }
            if self.at(TokenKind::End) {
                let span = self.cur.span;
                self.bump();
                break span;
            }
            if let Some(line) = self.parse_statement() {
                body.push(line);
            }
            if !self.at_separator() {
                self.recover_nested();
            }
        };
        self.open_subgraphs.pop();
        Some(Statement::Subgraph(Subgraph {
            span: Span {
                start: keyword.start,
                end: end_span.end,
            },
            keyword,
            id,
            title,
            body,
            end_span: Some(end_span),
        }))
    }

    fn recover_nested(&mut self) {
        let boundary = self.lexer.abort_to_boundary(self.cur.span.start);
        let mut guard = 0usize;
        while !self.at_separator() && self.cur.span.start < boundary && guard < 4096 {
            guard += 1;
            self.bump();
        }
    }

    fn parse_text_no_tags(&mut self) -> TextNoTags {
        let start = self.cur.span.start;
        let mut text = String::new();
        while is_text_no_tags_token(self.cur.kind) {
            let chunk = self.text(&self.cur).to_owned();
            text.push_str(&chunk);
            self.bump();
        }
        let len = text.trim_end().len();
        text.truncate(len);
        TextNoTags {
            span: Span {
                start,
                end: self.prev.span.end.max(start),
            },
            text,
        }
    }

    fn parse_vertex_statement(&mut self) -> Option<Statement> {
        let start = self.cur.span.start;
        let mut first = self.parse_node_group()?;
        let mut rest: Vec<(Link, NodeGroup)> = Vec::new();
        loop {
            if self.at_separator() {
                break;
            }
            if self.starts_node() {
                self.raise_missing_link();
                self.recover();
                break;
            }
            if matches!(self.cur.kind, TokenKind::Minus) || self.at(TokenKind::TagStart) {
                self.raise_arrow_invalid();
                self.recover();
                break;
            }
            let Some(link) = self.parse_link() else {
                break;
            };
            if matches!(
                self.cur.kind,
                TokenKind::Link | TokenKind::StartLink | TokenKind::LinkId
            ) {
                self.raise_link_marker(&link);
            }
            let Some(next) = self.parse_node_group() else {
                break;
            };
            rest.push((link, next));
            if !self.starts_node() && !self.at(TokenKind::Amp) && !self.at(TokenKind::Minus) {
                first = NodeGroup {
                    span: first.span,
                    nodes: std::mem::take(&mut first.nodes),
                };
            }
            if self.at_separator() {
                break;
            }
        }
        let end = rest
            .last()
            .map_or_else(|| self.prev.span.end, |(_, group)| group.span.end);
        Some(Statement::Vertex(VertexStatement {
            span: Span {
                start,
                end: end.max(start),
            },
            first,
            rest,
        }))
    }

    fn raise_missing_link(&mut self) {
        let at = self.cur.span;
        self.raise_with_fix(
            C_LINK_MISSING,
            at,
            String::from("Two nodes appear on one line without a connecting arrow"),
            "Insert --> between the two nodes",
            FixSafety::Unsafe,
            Edit {
                span: Span {
                    start: at.start,
                    end: at.start,
                },
                new_text: String::from("--> "),
            },
        );
    }

    fn raise_arrow_invalid(&mut self) {
        let start = self.cur.span.start;
        let mut end = self.cur.span.end;
        if self.src.as_bytes().get(end) == Some(&b'>') {
            end += 1;
        }
        let span = Span { start, end };
        self.raise_with_fix(
            C_ARROW_INVALID,
            span,
            String::from("A single arrow -> is used in a flowchart"),
            "Replace -> with -->",
            FixSafety::Safe,
            Edit {
                span,
                new_text: String::from("-->"),
            },
        );
    }

    fn raise_link_marker(&mut self, link: &Link) {
        let span = Span {
            start: link.span.start,
            end: self.cur.span.end,
        };
        self.raise(
            C_LINK_MARKER,
            span,
            String::from("An inline link uses a one-sided end marker, such as --x--> or --o-->"),
        );
        self.bump();
    }

    fn parse_node_group(&mut self) -> Option<NodeGroup> {
        let start = self.cur.span.start;
        let mut nodes = vec![self.parse_styled_vertex()?];
        while self.at(TokenKind::Amp) {
            self.bump();
            {
                let node = self.parse_styled_vertex()?;
                nodes.push(node)
            }
        }
        Some(NodeGroup {
            span: Span {
                start,
                end: nodes.last().map_or(start, |node| node.span.end),
            },
            nodes,
        })
    }

    fn parse_styled_vertex(&mut self) -> Option<StyledVertex> {
        let vertex = self.parse_vertex()?;
        let mut class = None;
        if self.at(TokenKind::StyleSeparator) {
            self.bump();
            class = Some(self.parse_id_string());
        }
        let shape_data = if self.at(TokenKind::ShapeData) {
            self.parse_shape_data()
        } else {
            None
        };
        let end = shape_data
            .as_ref()
            .map_or(vertex.span.end, |data| data.span.end)
            .max(
                class
                    .as_ref()
                    .map_or(vertex.span.end, |value| value.span.end),
            );
        Some(StyledVertex {
            span: Span {
                start: vertex.span.start,
                end,
            },
            vertex,
            class,
            shape_data,
        })
    }

    fn parse_shape_data(&mut self) -> Option<ShapeData> {
        let start = self.cur.span.start;
        self.bump();
        let mut text = String::new();
        let mut end = start;
        loop {
            if !self.at(TokenKind::ShapeData) {
                return Some(ShapeData {
                    span: Span { start, end },
                    text,
                });
            }
            let token = self.cur.clone();
            let closes = matches!(token.text, TextVal::None);
            let chunk = self.text(&token).to_owned();
            end = token.span.end;
            self.bump();
            if closes {
                return Some(ShapeData {
                    span: Span { start, end },
                    text,
                });
            }
            text.push_str(&chunk);
        }
    }

    fn parse_vertex(&mut self) -> Option<Vertex> {
        let id = self.parse_id_string();
        let Some(form) = label_form_of(self.cur.kind) else {
            if id.text.is_empty() {
                let kinds = [
                    TokenKind::Num,
                    TokenKind::NodeString,
                    TokenKind::UnicodeText,
                    TokenKind::Ps,
                    TokenKind::Sqs,
                    TokenKind::DiamondStart,
                ];
                if self.unexpected(&kinds) {
                    self.recover();
                }
                return None;
            }
            let span = id.span;
            return Some(Vertex {
                span,
                id,
                label: None,
            });
        };
        if id.text.is_empty() {
            let kinds = [
                TokenKind::Num,
                TokenKind::NodeString,
                TokenKind::UnicodeText,
            ];
            if self.unexpected(&kinds) {
                self.recover();
            }
            return None;
        }
        let label = self.parse_label(form, &id);
        let end = label.as_ref().map_or(id.span.end, |value| value.span.end);
        Some(Vertex {
            span: Span {
                start: id.span.start,
                end,
            },
            id,
            label,
        })
    }

    fn parse_label(&mut self, form: LabelForm, id: &IdString) -> Option<Label> {
        let open = self.cur.span;
        self.bump();
        let mut pair_end = open.end;
        if form == LabelForm::Diamond2 || form == LabelForm::Round2 {
            pair_end = self.cur.span.end;
            self.bump();
        }
        if let LabelForm::RectProps { .. } = form {
            return self.parse_rect_props(open, pair_end);
        }
        let text = self.parse_text(&closer_kinds(&form));
        if !closer_kinds(&form).contains(&self.cur.kind) {
            return self.fail_label_close(open, pair_end, &form, id);
        }
        let close = self.cur.span;
        self.bump();
        let mut end = close.end;
        if matches!(form, LabelForm::Diamond2 | LabelForm::Round2)
            && self.at(closer_kinds(&form)[0])
        {
            end = self.cur.span.end;
            self.bump();
        }
        let mut text = text.unwrap_or(Text {
            span: Span {
                start: pair_end,
                end: close.start,
            },
            kind: TextKind::Plain,
            text: String::new(),
        });
        if text.text.is_empty() {
            self.raise_with_fix(
                C_NODE_EMPTY,
                Span {
                    start: id.span.start,
                    end,
                },
                String::from("A node shape has empty content, such as A[]"),
                "Remove the empty bracket pair",
                FixSafety::Safe,
                Edit {
                    span: Span {
                        start: pair_end,
                        end,
                    },
                    new_text: String::new(),
                },
            );
            text.span = Span {
                start: pair_end,
                end: close.start,
            };
        }
        Some(Label {
            span: Span {
                start: id.span.start,
                end,
            },
            form,
            text,
        })
    }

    fn fail_label_close(
        &mut self,
        open: Span,
        pair_end: usize,
        form: &LabelForm,
        id: &IdString,
    ) -> Option<Label> {
        if let Some(expected) = closer_char(self.cur.kind) {
            let at = self.cur.span;
            self.raise_with_fix(
                C_NODE_MIXED_BRACKETS,
                at,
                String::from("The opening and closing brackets of a node shape do not match"),
                "Close with the matching bracket",
                FixSafety::Safe,
                Edit {
                    span: at,
                    new_text: String::from(expected),
                },
            );
            self.recover();
            return None;
        }
        let end = self.lexer.statement_boundary(open.start);
        self.bracket_reported = true;
        let mut diagnostic = diagnostic(
            C_UNCLOSED_BRACKET,
            Severity::Error,
            format!("node bracket {} is never closed", self.raw(open)),
            Span {
                start: open.start,
                end,
            },
        );
        diagnostic.fixes.push(Fix {
            title: String::from("Add the closing bracket"),
            safety: FixSafety::Unsafe,
            edits: vec![Edit {
                span: Span { start: end, end },
                new_text: String::from(closer_text(form)),
            }],
        });
        self.diags.push(diagnostic);
        self.recover();
        let _ = (pair_end, id);
        None
    }

    fn parse_rect_props(&mut self, open: Span, pair_end: usize) -> Option<Label> {
        let field = self.expect_id_part(TokenKind::NodeString)?;
        self.expect_id_part(TokenKind::Colon)?;
        let value = self.expect_id_part(TokenKind::NodeString)?;
        self.expect_id_part(TokenKind::Pipe)?;
        let text = self.parse_text(&[TokenKind::Sqe]);
        if self.eat(TokenKind::Sqe).is_none() {
            if self.unexpected(&[TokenKind::Sqe]) {
                self.recover();
            }
            return None;
        }
        let close = self.prev.span;
        Some(Label {
            span: Span {
                start: open.start,
                end: close.end,
            },
            form: LabelForm::RectProps { field, value },
            text: text.unwrap_or(Text {
                span: Span {
                    start: pair_end,
                    end: close.start,
                },
                kind: TextKind::Plain,
                text: String::new(),
            }),
        })
    }

    fn expect_id_part(&mut self, kind: TokenKind) -> Option<String> {
        let Some(token) = self.eat(kind) else {
            if self.unexpected(&[kind]) {
                self.recover();
            }
            return None;
        };
        Some(self.text(&token).to_owned())
    }

    fn parse_text(&mut self, closers: &[TokenKind]) -> Option<Text> {
        let start = self.cur.span.start;
        let mut kind = TextKind::Plain;
        let mut text = String::new();
        let mut end = start;
        let mut depth = 0usize;
        let mut plain_before = false;
        let mut strings = 0usize;
        let mut quoted = false;
        loop {
            let current = self.cur.kind;
            if depth == 0 && closers.contains(&current) {
                break;
            }
            if self.at_separator() {
                break;
            }
            match current {
                TokenKind::Text
                | TokenKind::UnicodeText
                | TokenKind::TagStart
                | TokenKind::TagEnd => {
                    plain_before = true;
                    text.push_str(self.text(&self.cur));
                }
                TokenKind::Str => {
                    strings += 1;
                    quoted = true;
                    if plain_before {
                        let at = self.cur.span;
                        self.raise(
                            C_LABEL_QUOTE_IN_UNQUOTED,
                            Span {
                                start: at.start,
                                end: at.start,
                            },
                            String::from("A double quote appears inside an unquoted label"),
                        );
                    }
                    if strings > 1 {
                        let at = self.cur.span;
                        self.raise(
                            C_LABEL_DOUBLE_IN_DOUBLE,
                            Span {
                                start: at.start,
                                end: at.start,
                            },
                            String::from("A double-quoted label contains another double quote"),
                        );
                    }
                    kind = TextKind::String;
                    text.push_str(self.text(&self.cur));
                }
                TokenKind::MdStr => {
                    strings += 1;
                    quoted = true;
                    if plain_before {
                        let at = self.cur.span;
                        self.raise(
                            C_LABEL_QUOTE_IN_UNQUOTED,
                            Span {
                                start: at.start,
                                end: at.start,
                            },
                            String::from("A double quote appears inside an unquoted label"),
                        );
                    }
                    kind = TextKind::Markdown;
                    text.push_str(self.text(&self.cur));
                }
                TokenKind::Ps
                | TokenKind::Sqs
                | TokenKind::DiamondStart
                | TokenKind::EllipseStart
                | TokenKind::StadiumStart
                | TokenKind::SubroutineStart
                | TokenKind::CylinderStart
                | TokenKind::DoubleCircleStart
                | TokenKind::TrapStart
                | TokenKind::InvTrapStart
                | TokenKind::VertexWithPropsStart => {
                    if current == TokenKind::Ps && !quoted {
                        let at = self.cur.span;
                        self.raise(
                            C_LABEL_PARENS_UNQUOTED,
                            at,
                            String::from(
                                "An unquoted label contains an opening or closing parenthesis",
                            ),
                        );
                    }
                    depth += 1;
                    plain_before = true;
                    text.push_str(self.raw(self.cur.span));
                }
                TokenKind::Pe
                | TokenKind::Sqe
                | TokenKind::DiamondStop
                | TokenKind::EllipseEnd
                | TokenKind::StadiumEnd
                | TokenKind::SubroutineEnd
                | TokenKind::CylinderEnd
                | TokenKind::DoubleCircleEnd
                | TokenKind::TrapEnd
                | TokenKind::InvTrapEnd => {
                    if depth == 0 {
                        break;
                    }
                    if current == TokenKind::Pe && !quoted {
                        let at = self.cur.span;
                        self.raise(
                            C_LABEL_PARENS_UNQUOTED,
                            at,
                            String::from(
                                "An unquoted label contains an opening or closing parenthesis",
                            ),
                        );
                    }
                    depth -= 1;
                    text.push_str(self.raw(self.cur.span));
                }
                _ => break,
            }
            end = self.cur.span.end;
            self.bump();
        }
        if text.is_empty() && end == start {
            return None;
        }
        Some(Text {
            span: Span { start, end },
            kind,
            text,
        })
    }

    fn parse_link(&mut self) -> Option<Link> {
        let start = self.cur.span.start;
        let link_id = if self.at(TokenKind::LinkId) {
            let span = self.cur.span;
            self.bump();
            Some(span)
        } else {
            None
        };
        if self.at(TokenKind::Link) {
            let end_half = self.cur.span;
            self.bump();
            let mut arrow_text = None;
            if self.at(TokenKind::Pipe) {
                arrow_text = self.parse_arrow_text();
            }
            return Some(Link {
                span: Span {
                    start,
                    end: arrow_text
                        .as_ref()
                        .map_or(end_half.end, |value| value.span.end),
                },
                statement: LinkStatement {
                    span: Span {
                        start,
                        end: end_half.end,
                    },
                    link_id,
                    start: None,
                    end: end_half,
                },
                arrow_text,
                edge_text: None,
            });
        }
        if !self.at(TokenKind::StartLink) {
            let kinds = [TokenKind::Link, TokenKind::StartLink, TokenKind::LinkId];
            if self.unexpected(&kinds) {
                self.recover();
            }
            return None;
        }
        let start_half = self.cur.span;
        self.bump();
        let edge = self.parse_edge_text();
        let Some(end_half) = self.eat(TokenKind::Link) else {
            if self.unexpected(&[TokenKind::Link]) {
                self.recover();
            }
            return None;
        };
        let mut arrow_text = None;
        if self.at(TokenKind::Pipe) {
            arrow_text = self.parse_arrow_text();
        }
        Some(Link {
            span: Span {
                start,
                end: arrow_text
                    .as_ref()
                    .map_or(end_half.span.end, |value| value.span.end),
            },
            statement: LinkStatement {
                span: Span {
                    start,
                    end: end_half.span.end,
                },
                link_id,
                start: Some(start_half),
                end: end_half.span,
            },
            arrow_text,
            edge_text: edge,
        })
    }

    fn parse_edge_text(&mut self) -> Option<EdgeText> {
        let start = self.cur.span.start;
        let mut kind = TextKind::Plain;
        let mut text = String::new();
        let mut end = start;
        let mut any = false;
        loop {
            match self.cur.kind {
                TokenKind::EdgeText | TokenKind::UnicodeText => {
                    text.push_str(self.text(&self.cur));
                }
                TokenKind::Str => {
                    kind = TextKind::String;
                    text.push_str(self.text(&self.cur));
                }
                TokenKind::MdStr => {
                    kind = TextKind::Markdown;
                    text.push_str(self.text(&self.cur));
                }
                _ => break,
            }
            any = true;
            end = self.cur.span.end;
            self.bump();
        }
        any.then_some(EdgeText {
            span: Span { start, end },
            kind,
            text,
        })
    }

    fn parse_arrow_text(&mut self) -> Option<ArrowText> {
        let open = self.eat(TokenKind::Pipe)?;
        let text = self.parse_text(&[TokenKind::Pipe]);
        let Some(close) = self.eat(TokenKind::Pipe) else {
            if self.unexpected(&[TokenKind::Pipe]) {
                self.recover();
            }
            return None;
        };
        Some(ArrowText {
            span: Span {
                start: open.span.start,
                end: close.span.end,
            },
            text: text.unwrap_or(Text {
                span: Span {
                    start: close.span.start,
                    end: close.span.start,
                },
                kind: TextKind::Plain,
                text: String::new(),
            }),
        })
    }
}

fn is_style_token(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Num
            | TokenKind::NodeString
            | TokenKind::Colon
            | TokenKind::Brkt
            | TokenKind::Style
            | TokenKind::UnicodeText
            | TokenKind::Down
            | TokenKind::Minus
            | TokenKind::Mult
            | TokenKind::Amp
            | TokenKind::Space
    )
}

fn label_form_of(kind: TokenKind) -> Option<LabelForm> {
    match kind {
        TokenKind::Sqs => Some(LabelForm::Square),
        TokenKind::Ps => Some(LabelForm::Round),
        TokenKind::DoubleCircleStart => Some(LabelForm::Circle),
        TokenKind::EllipseStart => Some(LabelForm::Ellipse),
        TokenKind::StadiumStart => Some(LabelForm::Stadium),
        TokenKind::SubroutineStart => Some(LabelForm::Subroutine),
        TokenKind::CylinderStart => Some(LabelForm::Cylinder),
        TokenKind::DiamondStart => Some(LabelForm::Diamond),
        TokenKind::TagEnd => Some(LabelForm::Odd),
        TokenKind::TrapStart => Some(LabelForm::Trap {
            closer: TrapCloser::Trap,
        }),
        TokenKind::InvTrapStart => Some(LabelForm::InvTrap {
            closer: TrapCloser::InvTrap,
        }),
        TokenKind::VertexWithPropsStart => Some(LabelForm::RectProps {
            field: String::new(),
            value: String::new(),
        }),
        _ => None,
    }
}

fn closer_kinds(form: &LabelForm) -> Vec<TokenKind> {
    match form {
        LabelForm::Square | LabelForm::Odd => vec![TokenKind::Sqe],
        LabelForm::Round => vec![TokenKind::Pe],
        LabelForm::Round2 => vec![TokenKind::Pe],
        LabelForm::Circle => vec![TokenKind::DoubleCircleEnd],
        LabelForm::Ellipse => vec![TokenKind::EllipseEnd],
        LabelForm::Stadium => vec![TokenKind::StadiumEnd],
        LabelForm::Subroutine => vec![TokenKind::SubroutineEnd],
        LabelForm::Cylinder => vec![TokenKind::CylinderEnd],
        LabelForm::Diamond | LabelForm::Diamond2 => vec![TokenKind::DiamondStop],
        LabelForm::RectProps { .. } => vec![TokenKind::Sqe],
        LabelForm::Trap { .. } => vec![TokenKind::TrapEnd, TokenKind::InvTrapEnd],
        LabelForm::InvTrap { .. } => vec![TokenKind::InvTrapEnd, TokenKind::TrapEnd],
    }
}

fn closer_char(kind: TokenKind) -> Option<&'static str> {
    match kind {
        TokenKind::Pe => Some(")"),
        TokenKind::Sqe => Some("]"),
        TokenKind::DiamondStop => Some("}"),
        _ => None,
    }
}

fn closer_text(form: &LabelForm) -> &'static str {
    match form {
        LabelForm::Square | LabelForm::Odd => "]",
        LabelForm::Round | LabelForm::Round2 => ")",
        LabelForm::Circle => ")))",
        LabelForm::Ellipse => "-)",
        LabelForm::Stadium => "])",
        LabelForm::Subroutine => "]]",
        LabelForm::Cylinder => ")]",
        LabelForm::Diamond | LabelForm::Diamond2 => "}",
        LabelForm::RectProps { .. } => "]",
        LabelForm::Trap { .. } => "\\]",
        LabelForm::InvTrap { .. } => "/]",
    }
}

fn line_after(src: &str, from: usize) -> usize {
    let bytes = src.as_bytes();
    let mut end = from;
    while end < bytes.len() && bytes[end] != b'\n' && bytes[end] != b'\r' {
        end += 1;
    }
    if end < bytes.len() && bytes[end] == b'\r' {
        end += 1;
    }
    if end < bytes.len() && bytes[end] == b'\n' {
        end += 1;
    }
    end
}
