//! Lexer for the sankey grammar of `spec/grammar/sankey.md`.
//!
//! The source is first reduced to cells: removed spans vanish, every run of CR and LF
//! becomes one LF cell, and JavaScript white space at both ends is trimmed. Three modes
//! follow the upstream jison lexer: the header, the CSV body, and a quoted field.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: &'static str,
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Initial,
    Csv,
    Escaped,
}

const HEADERS: [&str; 2] = ["sankey-beta", "sankey"];

#[derive(Debug, Clone, Copy)]
struct Cell {
    ch: char,
    span: Span,
}

struct Scanner {
    cells: Vec<Cell>,
    at: usize,
    end: usize,
    opener: usize,
    modes: Vec<Mode>,
    tokens: Vec<Token>,
}

pub fn lex(source: &str, removed: &[Span]) -> Vec<Token> {
    Scanner {
        cells: prepare(source, removed),
        at: 0,
        end: source.len(),
        opener: 0,
        modes: vec![Mode::Initial],
        tokens: Vec::new(),
    }
    .run()
}

fn js_space(c: char) -> bool {
    matches!(
        c,
        '\t' | '\n'
            | '\u{b}'
            | '\u{c}'
            | '\r'
            | ' '
            | '\u{a0}'
            | '\u{1680}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
            | '\u{feff}'
            | '\u{2000}'..='\u{200a}'
    )
}

fn push_cell(out: &mut Vec<Cell>, ch: char, span: Span) {
    if ch != '\n' && ch != '\r' {
        out.push(Cell { ch, span });
        return;
    }
    match out.last_mut() {
        Some(last) if last.ch == '\n' => last.span.end = span.end,
        _ => out.push(Cell { ch: '\n', span }),
    }
}

fn prepare(source: &str, removed: &[Span]) -> Vec<Cell> {
    let mut out = Vec::new();
    let mut next = 0;
    let mut at = 0;
    while at < source.len() {
        while removed.get(next).is_some_and(|span| span.end <= at) {
            next += 1;
        }
        if let Some(span) = removed.get(next).filter(|span| span.start <= at) {
            at = span.end.max(at + 1);
            continue;
        }
        let Some(ch) = source.get(at..).and_then(|rest| rest.chars().next()) else {
            break;
        };
        let span = Span {
            start: at,
            end: at + ch.len_utf8(),
        };
        at = span.end;
        push_cell(&mut out, ch, span);
    }
    trim(out)
}

fn trim(cells: Vec<Cell>) -> Vec<Cell> {
    let lo = cells.iter().take_while(|cell| js_space(cell.ch)).count();
    let hi = cells.len()
        - cells[lo..]
            .iter()
            .rev()
            .take_while(|cell| js_space(cell.ch))
            .count();
    cells[lo..hi].to_vec()
}

fn is_text_data(c: char) -> bool {
    matches!(c, '\u{20}'..='\u{21}' | '\u{23}'..='\u{2b}' | '\u{2d}'..='\u{7e}')
}

impl Scanner {
    fn mode(&self) -> Mode {
        self.modes.last().copied().unwrap_or(Mode::Initial)
    }

    fn char_at(&self, at: usize) -> Option<char> {
        self.cells.get(at).map(|cell| cell.ch)
    }

    fn quote_at(&self, at: usize) -> bool {
        self.char_at(at) == Some('"')
    }

    fn span_of(&self, from: usize, to: usize) -> Span {
        let start = self
            .cells
            .get(from)
            .map_or(self.end, |cell| cell.span.start);
        let end = to
            .checked_sub(1)
            .and_then(|last| self.cells.get(last))
            .map_or(start, |cell| cell.span.end);
        Span { start, end }
    }

    fn text(&self, from: usize, to: usize) -> String {
        self.cells
            .get(from..to)
            .unwrap_or_default()
            .iter()
            .map(|cell| cell.ch)
            .collect()
    }

    fn emit(&mut self, kind: &'static str, length: usize) {
        let to = self.at + length;
        let token = Token {
            kind,
            text: self.text(self.at, to),
            span: self.span_of(self.at, to),
        };
        self.tokens.push(token);
        self.at = to;
    }

    fn run(mut self) -> Vec<Token> {
        while self.at < self.cells.len() {
            if self.mode() == Mode::Escaped {
                self.lex_escaped();
            } else {
                self.lex_plain();
            }
        }
        if self.mode() == Mode::Escaped {
            let start = self
                .cells
                .get(self.opener)
                .map_or(self.end, |cell| cell.span.start);
            self.tokens.push(Token {
                kind: "UNTERMINATED",
                text: "\"".to_owned(),
                span: Span {
                    start,
                    end: self.end,
                },
            });
        } else {
            self.tokens.push(Token {
                kind: "EOF",
                text: String::new(),
                span: Span {
                    start: self.end,
                    end: self.end,
                },
            });
        }
        self.tokens
    }

    fn matches(&self, word: &str) -> bool {
        word.chars()
            .enumerate()
            .all(|(i, ch)| self.char_at(self.at + i) == Some(ch))
    }

    fn lex_header(&mut self) -> bool {
        for word in HEADERS {
            if self.matches(word) {
                self.emit("SANKEY", word.len());
                self.modes.push(Mode::Csv);
                return true;
            }
        }
        false
    }

    fn lex_plain(&mut self) {
        if self.mode() == Mode::Initial && self.lex_header() {
            return;
        }
        match self.char_at(self.at) {
            Some('\n') => self.emit("NEWLINE", 1),
            Some(',') => self.emit("COMMA", 1),
            Some('"') => {
                self.opener = self.at;
                self.emit("DQUOTE", 1);
                self.modes.push(Mode::Escaped);
            }
            Some(c) if is_text_data(c) => {
                let run = self.text_run();
                self.emit("NON_ESCAPED_TEXT", run);
            }
            _ => self.emit("INVALID", 1),
        }
    }

    fn text_run(&self) -> usize {
        (self.at..self.cells.len())
            .take_while(|&i| self.char_at(i).is_some_and(is_text_data))
            .count()
    }

    fn lex_escaped(&mut self) {
        if self.quote_at(self.at) && !self.quote_at(self.at + 1) {
            self.emit("DQUOTE", 1);
            self.modes.pop();
            return;
        }
        let run = self.escaped_run();
        if run > 0 {
            self.emit("ESCAPED_TEXT", run);
        } else {
            self.emit("INVALID", 1);
        }
    }

    fn escaped_run(&self) -> usize {
        let mut at = self.at;
        while let Some(c) = self.char_at(at) {
            if is_text_data(c) || c == ',' || c == '\n' {
                at += 1;
            } else if c == '"' && self.quote_at(at + 1) {
                at += 2;
            } else {
                break;
            }
        }
        at - self.at
    }
}
