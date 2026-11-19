use super::ast::{Document, Item, Node, ShapeData, Start, Statement, Stop, Token};
use super::lexer::{
    K_CLASS, K_END, K_EOF, K_ICON, K_KANBAN, K_NL, K_NODE_DESCR, K_NODE_END, K_NODE_ID,
    K_NODE_START, K_SHAPE_DATA, K_SPACE_LINE, K_SPACE_LIST, K_UNTERMINATED, Scanner, is_separator,
};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};
use crate::diag::Diagnostic;
use crate::source::Span;

const START_TOKENS: [&str; 2] = [K_KANBAN, K_SPACE_LINE];
const STATEMENT_TOKENS: [&str; 6] = [
    K_CLASS,
    K_ICON,
    K_NODE_START,
    K_NODE_ID,
    K_SPACE_LINE,
    K_SPACE_LIST,
];
const STOP_TOKENS: [&str; 3] = [K_EOF, K_NL, K_SPACE_LINE];
const NODE_STOP_TOKENS: [&str; 4] = [K_EOF, K_NL, K_SHAPE_DATA, K_SPACE_LINE];
const INDENTED_TOKENS: [&str; 7] = [
    K_CLASS,
    K_EOF,
    K_ICON,
    K_NL,
    K_NODE_START,
    K_NODE_ID,
    K_SPACE_LINE,
];

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser {
        src: source,
        scan: Scanner::new(source, removed),
        tok: Token::new(K_END, "", Span { start: 0, end: 0 }),
        diags: Vec::new(),
        halted: false,
    };
    parser.advance();
    let document = parser.start();
    Parsed {
        document,
        diagnostics: parser.diags,
    }
}

struct Parser<'a> {
    src: &'a str,
    scan: Scanner,
    tok: Token,
    diags: Vec<Diagnostic>,
    halted: bool,
}

impl Parser<'_> {
    fn advance(&mut self) {
        self.tok = self.scan.next();
        if self.tok.kind != K_UNTERMINATED {
            return;
        }
        let message = format!("unterminated {}", self.tok.text);
        self.diags
            .push(diagnostic(C_UNTERMINATED, message, self.tok.span));
        self.halted = true;
        let end = self.src.len();
        self.tok = Token::new(K_END, "", Span { start: end, end });
    }

    fn take(&mut self) -> Token {
        let token = self.tok.clone();
        self.advance();
        token
    }

    fn describe(&self, token: &Token) -> String {
        if token.span.start == token.span.end {
            return "end of input".to_owned();
        }
        self.src
            .get(token.span.start..token.span.end)
            .unwrap_or("")
            .to_owned()
    }

    fn unexpected(&mut self, expected: &[&str]) {
        if self.halted {
            return;
        }
        let mut names = expected.to_vec();
        names.sort_unstable();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.describe(&self.tok),
            names.join(", ")
        );
        self.diags
            .push(diagnostic(C_UNEXPECTED, message, self.tok.span));
    }

    fn recover(&mut self, mut content_end: usize) -> usize {
        let kind = self.tok.kind;
        if !is_separator(kind) {
            content_end = content_end.max(self.tok.span.end);
        }
        if kind == K_END {
            return content_end;
        }
        if !ends_line(&self.tok) {
            content_end = self.scan.skip_line(content_end);
        }
        self.advance();
        if self.tok.kind == K_EOF {
            self.advance();
        }
        content_end
    }

    fn expect(&mut self, kind: &'static str) -> Option<Token> {
        if self.tok.kind == kind {
            return Some(self.take());
        }
        self.unexpected(&[kind]);
        self.recover(self.tok.span.start);
        None
    }

    fn start(&mut self) -> Start {
        let leading = if self.tok.kind == K_SPACE_LINE {
            self.space_lines()
        } else {
            Vec::new()
        };
        if self.tok.kind != K_KANBAN {
            self.unexpected(&START_TOKENS);
            return Start {
                span: Span {
                    start: self.tok.span.start,
                    end: self.src.len(),
                },
                leading,
                header: None,
                document: Document {
                    span: Span { start: 0, end: 0 },
                    items: Vec::new(),
                },
            };
        }
        let header = self.take();
        if self.tok.kind == K_NL {
            self.advance();
        }
        let document = self.document();
        let mut span = Span {
            start: header.span.start,
            end: document.span.end.max(header.span.end),
        };
        if let Some(first) = leading.first() {
            span.start = first.span.start;
        }
        Start {
            span,
            leading,
            header: Some(header),
            document,
        }
    }

    fn space_lines(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        while self.tok.kind == K_SPACE_LINE || (!tokens.is_empty() && self.tok.kind == K_NL) {
            tokens.push(self.take());
        }
        tokens
    }

    fn document(&mut self) -> Document {
        let at = self.tok.span.start;
        let mut doc = Document {
            span: Span { start: at, end: at },
            items: Vec::new(),
        };
        while self.tok.kind != K_END {
            let Some(statement) = self.statement() else {
                continue;
            };
            let expected = if statement.node.is_some() {
                &NODE_STOP_TOKENS[..]
            } else {
                &STOP_TOKENS[..]
            };
            let stop = self.stop(expected).unwrap_or(Stop {
                span: Span { start: 0, end: 0 },
                tokens: Vec::new(),
            });
            doc.span.end = statement.span.end.max(stop.span.end);
            doc.items.push(Item { statement, stop });
        }
        doc
    }

    fn statement(&mut self) -> Option<Statement> {
        match self.tok.kind {
            K_SPACE_LINE => {
                let blank = self.take();
                let mut statement = Statement::at(blank.span);
                statement.blank = Some(blank);
                Some(statement)
            }
            K_SPACE_LIST => {
                let indent = self.take();
                self.indented(indent)
            }
            K_NODE_ID | K_NODE_START => self.node_statement(None),
            K_ICON | K_CLASS => Some(self.decoration(None)),
            _ => {
                self.unknown_statement();
                None
            }
        }
    }

    fn indented(&mut self, indent: Token) -> Option<Statement> {
        match self.tok.kind {
            K_NODE_ID | K_NODE_START => self.node_statement(Some(indent)),
            K_ICON | K_CLASS => Some(self.decoration(Some(indent))),
            K_NL | K_EOF | K_SPACE_LINE => {
                let mut statement = Statement::at(indent.span);
                statement.indent = Some(indent);
                Some(statement)
            }
            _ => {
                self.unexpected(&INDENTED_TOKENS);
                self.recover(indent.span.end);
                None
            }
        }
    }

    fn node_statement(&mut self, indent: Option<Token>) -> Option<Statement> {
        let node = self.node()?;
        let mut span = node.span;
        if let Some(indent) = &indent {
            span.start = indent.span.start;
        }
        let mut statement = Statement::at(span);
        statement.indent = indent;
        statement.node = Some(node);
        if self.tok.kind == K_SHAPE_DATA {
            let data = self.shape_data();
            statement.span.end = statement.span.end.max(data.span.end);
            statement.data = Some(data);
        }
        Some(statement)
    }

    fn shape_data(&mut self) -> ShapeData {
        let mut data = ShapeData {
            span: self.tok.span,
            tokens: Vec::new(),
        };
        while self.tok.kind == K_SHAPE_DATA {
            let token = self.take();
            data.span.end = data.span.end.max(token.span.end);
            data.tokens.push(token);
        }
        data.span.end = data.span.end.max(self.scan.closed_at);
        if self.halted {
            data.span.end = self.src.len();
        }
        data
    }

    fn decoration(&mut self, indent: Option<Token>) -> Statement {
        let token = self.take();
        let mut statement = Statement::at(token.span);
        if let Some(indent) = &indent {
            statement.span.start = indent.span.start;
        }
        statement.indent = indent;
        if token.kind == K_ICON {
            statement.icon = Some(token);
        } else {
            statement.class = Some(token);
        }
        statement
    }

    fn node(&mut self) -> Option<Node> {
        let mut node = Node {
            span: self.tok.span,
            id: None,
            open: None,
            descr: None,
            close: None,
            description: super::ast::Description::Bare,
        };
        if self.tok.kind == K_NODE_ID {
            let id = self.take();
            node.span = id.span;
            node.id = Some(id);
            if self.tok.kind != K_NODE_START {
                return Some(node);
            }
        }
        let open = self.take();
        if node.id.is_none() {
            node.span = open.span;
        }
        node.open = Some(open);
        let descr = self.expect(K_NODE_DESCR)?;
        node.description = descr.quote;
        node.descr = Some(descr);
        let closing = self.expect(K_NODE_END)?;
        node.span.end = closing.span.end;
        node.close = Some(closing);
        Some(node)
    }

    fn stop(&mut self, expected: &[&str]) -> Option<Stop> {
        if !matches!(self.tok.kind, K_NL | K_EOF | K_SPACE_LINE) {
            self.unexpected(expected);
            self.recover(self.tok.span.start);
            return None;
        }
        let first = self.take();
        let mut stop = Stop {
            span: first.span,
            tokens: vec![first],
        };
        while self.tok.kind == K_NL || self.tok.kind == K_EOF {
            let token = self.take();
            stop.span.end = token.span.end;
            stop.tokens.push(token);
        }
        Some(stop)
    }

    fn unknown_statement(&mut self) {
        let first = self.tok.clone();
        if first.kind == K_NL || first.kind == K_EOF {
            self.unexpected(&STATEMENT_TOKENS);
            self.recover(first.span.start);
            return;
        }
        let end = self.recover(first.span.end);
        let message = format!("unknown statement {}", self.describe(&first));
        self.diags.push(diagnostic(
            C_UNKNOWN,
            message,
            Span {
                start: first.span.start,
                end,
            },
        ));
    }
}

fn ends_line(token: &Token) -> bool {
    match token.kind {
        K_NL | K_EOF => true,
        K_SPACE_LINE => token.text.ends_with('\n') || token.text.ends_with('\r'),
        _ => false,
    }
}
