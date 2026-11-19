use super::ast::{Expression, Meta, MetaKind, Notation, Rule, Start, Token, Value};
use super::lexer::{equal_fold_ascii, header_of, lex};
use super::text::{meta_acc_descr, meta_acc_title, meta_title};
use crate::{diag::Diagnostic, source::Span};

const CODE_NESTING: &str = "limit/nesting-depth";
const CODE_UNEXPECTED: &str = "railroad/unexpected-token";
const CODE_UNKNOWN: &str = "railroad/unknown-statement";
const CODE_UNTERMINATED: &str = "railroad/unterminated";

const MAX_DEPTH: i64 = 64;

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let notation = notation_of(source, removed);
    let mut parser = Parser {
        src: source,
        tokens: lex(source, removed, notation),
        n: notation,
        at: 0,
        depth: 0,
        diags: Vec::new(),
    };
    let document = parser.document();
    Parsed {
        document,
        diagnostics: parser.diags,
    }
}

fn notation_of(text: &str, removed: &[Span]) -> Notation {
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if let Some(end) = removed_end(removed, i) {
            i = end;
            continue;
        }
        if !matches!(bytes[i], b' ' | b'\t' | b'\r' | b'\n') {
            break;
        }
        i += 1;
    }
    Notation::ALL
        .into_iter()
        .find(|&notation| {
            let header = header_of(notation);
            bytes
                .get(i..i + header.len())
                .is_some_and(|candidate| equal_fold_ascii(candidate, header))
        })
        .unwrap_or(Notation::Constructor)
}

fn removed_end(removed: &[Span], at: usize) -> Option<usize> {
    removed
        .iter()
        .find(|span| span.start <= at && at < span.end)
        .map(|span| span.end)
}

fn operators(notation: Notation) -> &'static [&'static str] {
    match notation {
        Notation::Constructor | Notation::Abnf => &["="],
        Notation::Ebnf => &["=", "::="],
        Notation::Peg => &["<-"],
    }
}

fn id_name(notation: Notation) -> &'static str {
    match notation {
        Notation::Constructor => "RR_ID",
        Notation::Ebnf => "EBNF_ID",
        Notation::Abnf => "ABNF_RULENAME",
        Notation::Peg => "PEG_ID",
    }
}

fn string_name(notation: Notation) -> &'static str {
    match notation {
        Notation::Constructor => "RR_STRING",
        Notation::Ebnf => "EBNF_STRING",
        Notation::Abnf => "ABNF_STRING",
        Notation::Peg => "PEG_STRING",
    }
}

fn meta_kind(kind: &str) -> Option<MetaKind> {
    match kind {
        "TITLE" => Some(MetaKind::Title),
        "ACC_TITLE" => Some(MetaKind::AccTitle),
        "ACC_DESCR" => Some(MetaKind::AccDescr),
        _ => None,
    }
}

pub(super) fn diagnostic(code: &'static str, message: String, span: Span) -> Diagnostic {
    Diagnostic {
        code,
        severity: crate::diag::Severity::Error,
        message,
        span,
        related: Vec::new(),
        help: crate::r#gen::diagnostics::DIAGNOSTICS
            .iter()
            .find(|row| row.code == code)
            .map_or("", |row| row.help)
            .into(),
        fixes: Vec::new(),
    }
}

pub(super) struct Parser<'a> {
    pub(super) src: &'a str,
    pub(super) tokens: Vec<Token>,
    pub(super) n: Notation,
    pub(super) at: usize,
    pub(super) depth: i64,
    pub(super) diags: Vec<Diagnostic>,
}

impl Parser<'_> {
    pub(super) fn tok(&self) -> &Token {
        &self.tokens[self.at.min(self.tokens.len() - 1)]
    }

    pub(super) fn kind(&self) -> &str {
        &self.tok().kind
    }

    pub(super) fn take(&mut self) -> Token {
        let token = self.tok().clone();
        if self.at < self.tokens.len() - 1 {
            self.at += 1;
        }
        token
    }

    pub(super) fn last_end(&self) -> usize {
        if self.at == 0 {
            return 0;
        }
        self.tokens
            .get(self.at.min(self.tokens.len()) - 1)
            .map_or(0, |token| token.span.end)
    }

    pub(super) fn since(&self, start: usize) -> Span {
        Span {
            start,
            end: self.last_end().max(start),
        }
    }

    fn halt(&mut self) {
        self.at = self.tokens.len() - 1;
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diags.push(diagnostic(code, message, span));
    }

    fn name(&self, kind: &str) -> String {
        match kind {
            "HEADER" => header_of(self.n).to_owned(),
            "ID" => id_name(self.n).to_owned(),
            "STRING" => string_name(self.n).to_owned(),
            "SPECIAL" => "EBNF_SPECIAL_SEQUENCE".to_owned(),
            "NUMVAL" => "ABNF_NUMVAL".to_owned(),
            "REPEAT" => "ABNF_REPEAT".to_owned(),
            "EXACT_REPEAT" => "ABNF_EXACT_REPEAT".to_owned(),
            other => other.to_owned(),
        }
    }

    fn display(&self, token: &Token) -> String {
        if token.kind == "EOF" {
            return "EOF".to_owned();
        }
        let bytes = self
            .src
            .as_bytes()
            .get(token.span.start..token.span.end)
            .unwrap_or(&[]);
        String::from_utf8_lossy(bytes).into_owned()
    }

    pub(super) fn fail(&mut self, expected: &[&str]) {
        let token = self.tok().clone();
        if token.kind == "UNTERMINATED" {
            self.issue(
                CODE_UNTERMINATED,
                format!("unterminated {}", token.text),
                token.span,
            );
            self.halt();
            return;
        }
        let mut names: Vec<String> = expected.iter().map(|kind| self.name(kind)).collect();
        names.sort();
        names.dedup();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.display(&token),
            names.join(", ")
        );
        self.issue(CODE_UNEXPECTED, message, token.span);
    }

    pub(super) fn expect(&mut self, kind: &str, expected: &[&str]) -> Option<Token> {
        if self.kind() == kind {
            return Some(self.take());
        }
        if expected.is_empty() {
            self.fail(&[kind]);
        } else {
            self.fail(expected);
        }
        None
    }

    pub(super) fn enter(&mut self, at: &Token) -> bool {
        if self.depth >= MAX_DEPTH {
            self.issue(CODE_NESTING, "nesting depth exceeds 64".to_owned(), at.span);
            self.halt();
            return false;
        }
        self.depth += 1;
        true
    }

    fn document(&mut self) -> Start {
        let at = self.tok().span.start;
        let header = self.expect("HEADER", &[]).unwrap_or_else(|| Token {
            kind: "HEADER".to_owned(),
            text: String::new(),
            span: Span { start: at, end: at },
        });
        let mut start = Start {
            span: Span { start: 0, end: 0 },
            header,
            notation: self.n,
            meta: Vec::new(),
            rules: Vec::new(),
        };
        while self.kind() != "EOF" {
            self.statement(&mut start);
        }
        start.span = Span {
            start: start.header.span.start,
            end: self.src.len(),
        };
        start
    }

    fn statement(&mut self, start: &mut Start) {
        let token = self.tok().clone();
        if let Some(kind) = meta_kind(&token.kind).filter(|_| start.rules.is_empty()) {
            self.take();
            start.meta.push(Meta {
                span: token.span,
                kind,
                value: self.meta_value(kind, &token),
            });
            return;
        }
        match token.kind.as_str() {
            "ID" => {
                if let Some(rule) = self.rule(start.rules.len()) {
                    start.rules.push(rule);
                }
            }
            "UNTERMINATED" => self.fail(&[]),
            _ => self.unknown_statement(),
        }
    }

    fn meta_value(&self, kind: MetaKind, token: &Token) -> String {
        match kind {
            MetaKind::Title => meta_title(&token.text, self.n),
            MetaKind::AccTitle => meta_acc_title(&token.text),
            MetaKind::AccDescr => meta_acc_descr(&token.text),
        }
    }

    fn unknown_statement(&mut self) {
        let first = self.take();
        if meta_kind(&first.kind).is_none() {
            self.resync();
        }
        let span = Span {
            start: first.span.start,
            end: self.last_end().max(first.span.end),
        };
        let message = format!("unknown statement {}", self.display(&first));
        self.issue(CODE_UNKNOWN, message, span);
    }

    fn rule(&mut self, index: usize) -> Option<Rule> {
        self.depth = 0;
        let name = self.take();
        if let Some(body) = self.after_name()
            && let Some(semicolon) = self.expect(";", &[])
        {
            return Some(Rule {
                span: Span {
                    start: name.span.start,
                    end: semicolon.span.end,
                },
                index,
                name: Value {
                    span: name.span,
                    text: name.text,
                },
                body,
            });
        }
        self.resync();
        None
    }

    fn after_name(&mut self) -> Option<Expression> {
        let accepted = operators(self.n);
        if !accepted.contains(&self.kind()) {
            self.fail(accepted);
            return None;
        }
        self.take();
        self.body()
    }

    fn body(&mut self) -> Option<Expression> {
        match self.n {
            Notation::Ebnf => self.ebnf_choice().map(Expression::Ebnf),
            Notation::Abnf => self.abnf_alternation().map(Expression::Abnf),
            Notation::Peg => self.peg_choice().map(Expression::Peg),
            Notation::Constructor => self.railroad_expr(),
        }
    }

    fn resync(&mut self) {
        if self.n == Notation::Abnf {
            while self.kind() != "EOF" && !self.rule_starts_here() {
                self.at += 1;
            }
            return;
        }
        let mut depth = 0_i64;
        loop {
            match self.kind() {
                "EOF" | "UNTERMINATED" => return,
                ";" if depth == 0 => {
                    self.at += 1;
                    return;
                }
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth = (depth - 1).max(0),
                _ => {}
            }
            self.at += 1;
        }
    }

    fn rule_starts_here(&self) -> bool {
        let token = self.tok();
        let follows_equals = self
            .tokens
            .get(self.at + 1)
            .is_some_and(|next| next.kind == "=");
        if token.kind != "ID" || !follows_equals {
            return false;
        }
        let before = self.src.as_bytes().get(..token.span.start).unwrap_or(&[]);
        for &byte in before.iter().rev() {
            match byte {
                b' ' | b'\t' => {}
                b'\n' | b'\r' => return true,
                _ => return false,
            }
        }
        true
    }
}
