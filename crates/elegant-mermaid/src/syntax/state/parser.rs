use super::{
    ast::*,
    diagnostic,
    lexer::{Token, lex},
};
use crate::{diag::Diagnostic, source::Span};

pub struct Parsed<'a> {
    pub document: Start<'a>,
    pub diagnostics: Vec<Diagnostic>,
}
pub fn parse<'a>(source: &'a str, removed: &[Span]) -> Parsed<'a> {
    let mut p = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        diagnostics: Vec::new(),
    };
    while p.kind() == "NL" {
        p.at += 1;
    }
    let header = p.expect("SD").unwrap_or(Token {
        kind: "SD",
        text: "",
        span: Span { start: 0, end: 0 },
    });
    let body_start = header.span.end;
    let document = p.document(0, body_start);
    if p.kind() == "STRUCT_STOP" {
        p.unexpected("EOF");
    }
    Parsed {
        document: Start {
            span: Span {
                start: header.span.start,
                end: source.len(),
            },
            header,
            document,
        },
        diagnostics: p.diagnostics,
    }
}
struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token<'a>>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}
impl<'a> Parser<'a> {
    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |t| t.kind)
    }
    fn take(&mut self) -> Option<Token<'a>> {
        let t = self.tokens.get(self.at)?.clone();
        self.at += 1;
        Some(t)
    }
    fn end(&self) -> usize {
        self.tokens
            .get(self.at.saturating_sub(1))
            .map_or(0, |t| t.span.end)
    }
    fn unexpected(&mut self, expected: &str) {
        let span = self.tokens.get(self.at).map_or(
            Span {
                start: self.source.len(),
                end: self.source.len(),
            },
            |t| t.span,
        );
        self.diagnostics.push(diagnostic(
            "state/unexpected-token",
            format!(
                "unexpected {}, expected one of: {expected}",
                &self.source[span.start..span.end]
            ),
            span,
        ));
    }
    fn expect(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return self.take();
        }
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
        } else {
            self.unexpected(kind);
        }
        None
    }
    fn unterminated(&mut self) {
        if let Some(t) = self.take() {
            self.diagnostics.push(diagnostic(
                "state/unterminated",
                format!("unterminated {}", t.text),
                Span {
                    start: t.span.start,
                    end: self.source.len(),
                },
            ));
        }
    }
    fn recover(&mut self) {
        while !matches!(self.kind(), "EOF" | "NL" | "STRUCT_STOP") {
            if self.kind() == "UNTERMINATED"
                && !self
                    .diagnostics
                    .last()
                    .is_some_and(|d| d.code == "state/multiword-state-name")
            {
                self.unterminated();
            } else {
                self.at += 1;
            }
        }
    }
    fn document(&mut self, depth: usize, start: usize) -> Document<'a> {
        let mut lines = Vec::new();
        while !matches!(self.kind(), "EOF" | "STRUCT_STOP") {
            if self.kind() == "NL" {
                if let Some(t) = self.take() {
                    lines.push(Line {
                        span: t.span,
                        statement: None,
                    });
                }
                continue;
            }
            let before = self.at;
            let errors = self.diagnostics.len();
            let statement = self.statement(depth);
            let invalid_tail = matches!(
                self.kind(),
                "-->" | "INVALID" | "STYLE_SEPARATOR" | "DESCR" | "STRING" | "AS" | "STRUCT_START"
            );
            if invalid_tail && self.diagnostics.len() == errors {
                self.unexpected("NL, STRUCT_STOP");
            }
            if invalid_tail || statement.is_none() {
                self.recover();
            } else if let Some(statement) = statement {
                lines.push(Line {
                    span: statement.span,
                    statement: Some(statement),
                });
            }
            if self.at == before {
                self.at += 1;
            }
        }
        let span = Span {
            start: lines.first().map_or(start, |l| l.span.start),
            end: lines.last().map_or(start, |l| l.span.end),
        };
        Document { span, lines }
    }
    fn id(&mut self) -> Option<IdStatement<'a>> {
        if !matches!(self.kind(), "ID" | "EDGE_STATE") {
            self.unexpected("EDGE_STATE, ID");
            return None;
        }
        let id = self.take()?;
        let css_class = if self.kind() == "STYLE_SEPARATOR" {
            self.at += 1;
            Some(self.expect("ID")?)
        } else {
            None
        };
        Some(IdStatement {
            span: Span {
                start: id.span.start,
                end: self.end(),
            },
            id,
            css_class,
        })
    }
    fn body(&mut self, depth: usize) -> Option<(Document<'a>, (Span, Span))> {
        let open = self.expect("STRUCT_START")?;
        if depth >= 64 {
            self.diagnostics.push(diagnostic(
                "limit/nesting-depth",
                "nesting depth exceeds 64".into(),
                open.span,
            ));
            self.at = self.tokens.len();
            return None;
        }
        let body = self.document(depth + 1, open.span.end);
        if self.kind() == "EOF" {
            if !self
                .diagnostics
                .last()
                .is_some_and(|d| d.code == "limit/nesting-depth")
            {
                self.diagnostics.push(diagnostic(
                    "state/unterminated",
                    "unterminated {".into(),
                    Span {
                        start: open.span.start,
                        end: self.source.len(),
                    },
                ));
            }
            return None;
        }
        let close = self.expect("STRUCT_STOP")?;
        Some((body, (open.span, close.span)))
    }
    fn statement(&mut self, depth: usize) -> Option<Statement<'a>> {
        let start = self.tokens.get(self.at)?.span.start;
        let kind = match self.kind() {
            "ID" | "EDGE_STATE" => self.named()?,
            "COMPOSIT_STATE" | "STATE_DESCR" => self.composite(depth)?,
            "FORK" | "JOIN" | "CHOICE" | "CONCURRENT" | "HIDE_EMPTY" | "scale" => self.symbol()?,
            "note" => self.note()?,
            "classDef" | "style" | "class" => self.styles(start)?,
            "CLICK" => self.click()?,
            _ => self.directive()?,
        };
        Some(Statement {
            span: Span {
                start,
                end: self.end(),
            },
            kind,
        })
    }
    fn symbol(&mut self) -> Option<StatementKind<'a>> {
        let id = self.take()?;
        Some(match id.kind {
            "CONCURRENT" => StatementKind::Concurrent,
            "HIDE_EMPTY" => StatementKind::HideEmpty,
            "scale" => StatementKind::Scale(self.expect("WIDTH")?),
            _ => {
                let stereotype = match id.kind {
                    "FORK" => Stereotype::Fork,
                    "JOIN" => Stereotype::Join,
                    _ => Stereotype::Choice,
                };
                StatementKind::Stereotype { id, stereotype }
            }
        })
    }
    fn directive(&mut self) -> Option<StatementKind<'a>> {
        match self.kind() {
            "acc_title" | "acc_descr" => {
                let title = self.kind() == "acc_title";
                self.at += 1;
                let value = self.expect(if title {
                    "acc_title_value"
                } else {
                    "acc_descr_value"
                })?;
                Some(StatementKind::Accessibility { title, value })
            }
            "acc_descr_multiline_value" => Some(StatementKind::Accessibility {
                title: false,
                value: self.take()?,
            }),
            "direction_tb" | "direction_bt" | "direction_rl" | "direction_lr" => {
                let t = self.take()?;
                let value = match t.kind {
                    "direction_tb" => "TB",
                    "direction_bt" => "BT",
                    "direction_rl" => "RL",
                    _ => "LR",
                };
                Some(StatementKind::Direction(Direction {
                    span: t.span,
                    value,
                }))
            }
            "MULTIWORD" => {
                let t = self.take()?;
                self.diagnostics.push(diagnostic(
                    "state/multiword-state-name",
                    format!("state name must be a single word: {}", t.text),
                    t.span,
                ));
                None
            }
            "UNTERMINATED" => {
                self.unterminated();
                None
            }
            _ => {
                let t = self.take()?;
                self.recover();
                self.diagnostics.push(diagnostic(
                    "state/unknown-statement",
                    format!(
                        "unknown statement {}",
                        &self.source[t.span.start..t.span.end]
                    ),
                    Span {
                        start: t.span.start,
                        end: self.end(),
                    },
                ));
                None
            }
        }
    }
    fn named(&mut self) -> Option<StatementKind<'a>> {
        let from = self.id()?;
        if self.kind() == "-->" {
            let arrow = self.take()?;
            let to = self.id()?;
            let description = if self.kind() == "DESCR" {
                self.take()
            } else {
                None
            };
            return Some(StatementKind::Transition {
                from,
                arrow,
                to,
                description,
            });
        }
        let description = if self.kind() == "DESCR" {
            self.take()
        } else {
            None
        };
        Some(StatementKind::Id {
            id: from,
            description,
        })
    }
    fn composite(&mut self, depth: usize) -> Option<StatementKind<'a>> {
        let first = self.take()?;
        let (id, description) = if first.kind == "STATE_DESCR" {
            self.expect("AS")?;
            (self.expect("ID")?, Some(first))
        } else {
            (first, None)
        };
        if self.kind() == "NL"
            && self
                .tokens
                .get(self.at + 1)
                .is_some_and(|t| t.kind == "STRUCT_START")
        {
            self.at += 1;
        }
        let (body, delimiters) = if self.kind() == "STRUCT_START" {
            let (body, delimiters) = self.body(depth)?;
            (Some(body), Some(delimiters))
        } else {
            (None, None)
        };
        Some(StatementKind::Composite {
            id,
            description,
            body,
            delimiters,
        })
    }
    fn note(&mut self) -> Option<StatementKind<'a>> {
        self.at += 1;
        if self.kind() == "NOTE_TEXT" {
            let text = self.take()?;
            self.expect("AS")?;
            let id = self.expect("ID")?;
            return Some(StatementKind::FloatingNote { text, id });
        }
        if !matches!(self.kind(), "left_of" | "right_of") {
            self.unexpected("NOTE_TEXT, left_of, right_of");
            return None;
        }
        let t = self.take()?;
        let position = NotePosition {
            span: t.span,
            value: t.kind,
        };
        let target = self.expect("ID")?;
        let text = self.expect("NOTE_TEXT")?;
        Some(StatementKind::Note {
            position,
            target,
            text,
        })
    }
    fn styles(&mut self, start: usize) -> Option<StatementKind<'a>> {
        let kind = self.take()?.kind;
        match kind {
            "classDef" => {
                if !matches!(self.kind(), "CLASSDEF_ID" | "DEFAULT") {
                    self.unexpected("CLASSDEF_ID, DEFAULT");
                    return None;
                }
                let id = self.take()?;
                let styles = self.expect("CLASSDEF_STYLEOPTS")?;
                Some(StatementKind::ClassDef(ClassDefStatement {
                    span: Span {
                        start,
                        end: self.end(),
                    },
                    id,
                    styles,
                }))
            }
            "style" => {
                let targets = self.expect("STYLE_IDS")?;
                let styles = self.expect("STYLEDEF_STYLEOPTS")?;
                Some(StatementKind::Style(StyleStatement {
                    span: Span {
                        start,
                        end: self.end(),
                    },
                    targets,
                    styles,
                }))
            }
            _ => {
                let targets = self.expect("CLASSENTITY_IDS")?;
                let class = self.expect("STYLECLASS")?;
                Some(StatementKind::CssClass(CssClassStatement {
                    span: Span {
                        start,
                        end: self.end(),
                    },
                    targets,
                    class,
                }))
            }
        }
    }
    fn click(&mut self) -> Option<StatementKind<'a>> {
        self.at += 1;
        let target = self.id()?;
        let href = self.kind() == "HREF";
        if href {
            self.at += 1;
        }
        let url = self.expect("STRING")?;
        let tooltip = if href {
            None
        } else {
            Some(self.expect("STRING")?)
        };
        if self.kind() != "EOF" && self.kind() != "NL" {
            self.unexpected("NL");
            return None;
        }
        Some(StatementKind::Click {
            target,
            url,
            tooltip,
        })
    }
}
