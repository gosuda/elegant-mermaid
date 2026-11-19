use super::ast::{Token, TreeNode, TreeView};
use super::lexer::{
    K_ACC_DESCR, K_ACC_TITLE, K_BARE, K_CLASS, K_DESC, K_EOF, K_HEADER, K_ICON, K_INDENT,
    K_INVALID, K_QUOTED, K_TITLE, K_UNTERMINATED, Scanner,
};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};
use crate::diag::Diagnostic;
use crate::source::Span;

const HEADER_TOKENS: [&str; 1] = [K_HEADER];
const META_TOKENS: [&str; 7] = [
    K_ACC_DESCR,
    K_ACC_TITLE,
    K_BARE,
    K_EOF,
    K_INDENT,
    K_QUOTED,
    K_TITLE,
];
const NODE_TOKENS: [&str; 7] = [K_BARE, K_CLASS, K_DESC, K_EOF, K_ICON, K_INDENT, K_QUOTED];
const NAME_TOKENS: [&str; 2] = [K_BARE, K_QUOTED];

pub struct Parsed {
    pub document: TreeView,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let (scan, diags) = Scanner::new(source, removed);
    let mut parser = Parser {
        src: source,
        scan,
        tok: Token::end_of(Span { start: 0, end: 0 }, 0),
        last: 0,
        diags,
        halted: false,
    };
    parser.advance();
    let document = parser.tree_view();
    Parsed {
        document,
        diagnostics: parser.diags,
    }
}

struct Parser<'a> {
    src: &'a str,
    scan: Scanner,
    tok: Token,
    last: usize,
    diags: Vec<Diagnostic>,
    halted: bool,
}

impl Parser<'_> {
    fn advance(&mut self) {
        loop {
            self.tok = self.scan.next();
            match self.tok.kind {
                K_INVALID => self.skip_invalid(),
                K_UNTERMINATED => {
                    let message = format!("unterminated {}", self.tok.text);
                    self.diags
                        .push(diagnostic(C_UNTERMINATED, message, self.tok.span));
                    self.halted = true;
                    let end = self.src.len();
                    self.tok = Token::end_of(Span { start: end, end }, self.scan.text.len());
                    return;
                }
                _ => return,
            }
        }
    }

    fn skip_invalid(&mut self) {
        let end = self.scan.line_end(self.tok.to);
        let span = Span {
            start: self.tok.span.start,
            end: self.scan.finish(end).max(self.tok.span.end),
        };
        let message = format!("unknown statement {}", self.tok.text);
        self.diags.push(diagnostic(C_UNKNOWN, message, span));
        self.scan.at = end;
    }

    fn take(&mut self) -> Token {
        let token = self.tok.clone();
        self.last = self.last.max(token.span.end);
        self.advance();
        token
    }

    fn describe(&self, token: &Token) -> String {
        if token.span.start == token.span.end {
            return "end of input".to_owned();
        }
        String::from_utf8_lossy(
            self.src
                .as_bytes()
                .get(token.span.start..token.span.end)
                .unwrap_or(&[]),
        )
        .into_owned()
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

    fn recover(&mut self) {
        if self.tok.kind != K_EOF {
            self.scan.at = self.scan.at.max(self.scan.line_end(self.tok.to));
        }
        self.advance();
    }

    fn tree_view(&mut self) -> TreeView {
        let mut tv = TreeView {
            span: Span { start: 0, end: 0 },
            header: None,
            title: None,
            acc_title: None,
            acc_descr: None,
            nodes: Vec::new(),
        };
        if self.tok.kind != K_HEADER {
            self.unexpected(&HEADER_TOKENS);
            tv.span = Span {
                start: self.tok.span.start,
                end: self.src.len(),
            };
            return tv;
        }
        let header = self.take();
        let header_span = header.span;
        tv.header = Some(header);
        self.metadata(&mut tv);
        while self.tok.kind != K_EOF {
            if let Some(node) = self.node(tv.nodes.len()) {
                tv.nodes.push(node);
            }
        }
        tv.span = Span {
            start: header_span.start,
            end: self.last.max(header_span.end),
        };
        tv
    }

    fn metadata(&mut self, tv: &mut TreeView) {
        loop {
            let token = self.tok.clone();
            match token.kind {
                K_ACC_DESCR => tv.acc_descr = Some(token),
                K_ACC_TITLE => tv.acc_title = Some(token),
                K_TITLE => tv.title = Some(token),
                _ => return,
            }
            self.take();
        }
    }

    fn node(&mut self, parsed: usize) -> Option<TreeNode> {
        let mut indent = None;
        let mut start = None;
        if self.tok.kind == K_INDENT {
            let token = self.take();
            start = Some(token.span);
            indent = Some(token);
        }
        if self.tok.kind != K_QUOTED && self.tok.kind != K_BARE {
            let expected: &[&str] = match (&indent, parsed) {
                (Some(_), _) => &NAME_TOKENS,
                (None, 0) => &META_TOKENS,
                (None, _) => &NODE_TOKENS,
            };
            self.unexpected(expected);
            self.recover();
            return None;
        }
        let name = self.take();
        let span = start.unwrap_or(name.span);
        let mut node = TreeNode {
            span,
            indent,
            name,
            class: None,
            icon: None,
            desc: None,
        };
        self.annotations(&mut node);
        node.span.end = node.span.end.max(self.last);
        Some(node)
    }

    fn annotations(&mut self, node: &mut TreeNode) {
        loop {
            let token = self.tok.clone();
            match token.kind {
                K_CLASS => node.class = Some(token),
                K_ICON => node.icon = Some(token),
                K_DESC => node.desc = Some(token),
                _ => return,
            }
            self.take();
        }
    }
}
