use super::ast::{Document, Item, Start, Statement, Stop, Token};
use super::lexer::{
    K_END, K_EOF, K_ISHIKAWA, K_NL, K_SPACE_LINE, K_SPACE_LIST, K_TEXT, Scanner, is_separator,
};
use super::{C_UNEXPECTED, C_UNKNOWN, diagnostic};
use crate::diag::Diagnostic;
use crate::source::Span;

const START_TOKENS: [&str; 2] = [K_ISHIKAWA, K_SPACE_LINE];
const STATEMENT_TOKENS: [&str; 3] = [K_SPACE_LINE, K_SPACE_LIST, K_TEXT];
const STOP_TOKENS: [&str; 3] = [K_EOF, K_NL, K_SPACE_LINE];
const INDENTED_TOKENS: [&str; 4] = [K_EOF, K_NL, K_SPACE_LINE, K_TEXT];

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
}

impl Parser<'_> {
    fn advance(&mut self) {
        self.tok = self.scan.next();
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

    fn start(&mut self) -> Start {
        let leading = if self.tok.kind == K_SPACE_LINE {
            self.space_lines()
        } else {
            Vec::new()
        };
        if self.tok.kind != K_ISHIKAWA {
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
            let stop = self.stop().unwrap_or(Stop {
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
            K_TEXT => Some(self.text_statement(None)),
            _ => {
                self.unknown_statement();
                None
            }
        }
    }

    fn indented(&mut self, indent: Token) -> Option<Statement> {
        match self.tok.kind {
            K_TEXT => Some(self.text_statement(Some(indent))),
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

    fn text_statement(&mut self, indent: Option<Token>) -> Statement {
        let text = self.take();
        let mut statement = Statement::at(text.span);
        if let Some(indent) = &indent {
            statement.span.start = indent.span.start;
        }
        statement.indent = indent;
        statement.text = Some(text);
        statement
    }

    fn stop(&mut self) -> Option<Stop> {
        if !matches!(self.tok.kind, K_NL | K_EOF | K_SPACE_LINE) {
            self.unexpected(&STOP_TOKENS);
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
