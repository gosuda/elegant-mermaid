//! Recursive-descent parser for the xychart grammar (`spec/grammar/xychart.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Accessibility, AxisStatement, BandData, DataPoint, Document, Header, Number, PlotData,
    PlotStatement, Range, Start, Statement, StatementKind, Text, Title,
};
use super::lexer::{Token, lex};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

const TEXT_STARTS: &[&str] = &[
    "ALPHA",
    "AMP",
    "BRKT",
    "DOT",
    "EQUALS",
    "MD_STR",
    "MINUS",
    "MULT",
    "NUM",
    "PLUS",
    "STR",
    "UNDERSCORE",
];

const ALPHA_NUM_TOKENS: &[&str] = &[
    "AMP",
    "NUM",
    "ALPHA",
    "PLUS",
    "EQUALS",
    "MULT",
    "DOT",
    "BRKT",
    "MINUS",
    "UNDERSCORE",
];

pub struct Parsed<'a> {
    pub document: Start<'a>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse<'a>(source: &'a str, removed: &[Span]) -> Parsed<'a> {
    let mut parser = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        diagnostics: Vec::new(),
    };
    let document = parser.start();
    Parsed {
        document,
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token<'a>>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Parser<'a> {
    fn token(&self) -> Token<'a> {
        self.tokens.get(self.at).cloned().unwrap_or(Token {
            kind: "EOF",
            text: "",
            span: Span {
                start: self.source.len(),
                end: self.source.len(),
            },
        })
    }

    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |t| t.kind)
    }

    fn take(&mut self) -> Token<'a> {
        let token = self.token();
        if self.at < self.tokens.len() {
            self.at += 1;
        }
        token
    }

    fn last_end(&self) -> usize {
        self.at
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or(0, |t| t.span.end)
    }

    fn raw(&self, span: Span) -> &'a str {
        self.source.get(span.start..span.end).unwrap_or("")
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        if token.kind == "UNTERMINATED" {
            self.unterminated(&token);
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
        let end = self.last_end();
        self.recover(end);
    }

    fn unterminated(&mut self, token: &Token<'a>) {
        self.issue(
            C_UNTERMINATED,
            format!("unterminated {}", token.text),
            token.span,
        );
        self.take();
    }

    fn line_break_between(&self, from: usize, to: usize) -> bool {
        self.source
            .get(from.min(to)..to)
            .is_some_and(|between| between.contains(['\n', '\r']))
    }

    fn boundary(&self, previous_end: usize) -> bool {
        let token = self.token();
        matches!(token.kind, "NEWLINE" | "SEMI" | "EOF" | "UNTERMINATED")
            || self.line_break_between(previous_end, token.span.start)
    }

    fn recover(&mut self, mut previous_end: usize) {
        while !self.boundary(previous_end) {
            previous_end = self.take().span.end;
        }
    }

    fn start(&mut self) -> Start<'a> {
        let first = self.token().span.start;
        let mut headers = Vec::new();
        loop {
            match self.kind() {
                "NEWLINE" | "SEMI" => {
                    self.take();
                }
                "XYCHART" => headers.push(self.header()),
                _ => break,
            }
        }
        let document = self.document();
        Start {
            span: Span {
                start: first,
                end: self.source.len(),
            },
            headers,
            document,
        }
    }

    fn header(&mut self) -> Header<'a> {
        let keyword = self.take();
        let mut header = Header {
            span: keyword.span,
            keyword,
            orientation: None,
        };
        if self.kind() == "CHART_ORIENTATION" {
            let orientation = self.take();
            header.span.end = orientation.span.end;
            header.orientation = Some(orientation);
        }
        header
    }

    fn document(&mut self) -> Document<'a> {
        let start = self.token().span.start;
        let mut statements: Vec<Statement<'a>> = Vec::new();
        loop {
            match self.kind() {
                "EOF" => break,
                "UNTERMINATED" => {
                    let token = self.token();
                    self.unterminated(&token);
                    continue;
                }
                "NEWLINE" | "SEMI" => {
                    self.take();
                    continue;
                }
                _ => {}
            }
            let before = self.at;
            if let Some(kind) = self.statement() {
                statements.push(Statement {
                    span: statement_span(&kind),
                    kind,
                });
            } else if self.at == before {
                self.unknown_statement();
            }
        }
        let end = statements
            .iter()
            .map(|s| s.span.end)
            .fold(start, usize::max);
        Document {
            span: Span { start, end },
            statements,
        }
    }

    fn unknown_statement(&mut self) {
        let first = self.take();
        let mut end = first.span.end;
        while !self.boundary(end) {
            end = self.take().span.end;
        }
        let message = format!("unknown statement {}", first.text);
        self.issue(
            C_UNKNOWN,
            message,
            Span {
                start: first.span.start,
                end,
            },
        );
    }

    fn statement(&mut self) -> Option<StatementKind<'a>> {
        match self.kind() {
            "title" => self.title().map(StatementKind::Title),
            "X_AXIS" | "Y_AXIS" => self.axis().map(StatementKind::Axis),
            "LINE" | "BAR" => self.plot().map(StatementKind::Plot),
            "acc_title" | "acc_descr" => self.accessibility().map(StatementKind::Accessibility),
            "acc_descr_multiline_value" => {
                let value = self.take();
                Some(StatementKind::Accessibility(Accessibility {
                    span: value.span,
                    title: false,
                    multiline: true,
                    value,
                }))
            }
            _ => None,
        }
    }

    fn accessibility(&mut self) -> Option<Accessibility<'a>> {
        let keyword = self.take();
        let value_kind = if keyword.kind == "acc_title" {
            "acc_title_value"
        } else {
            "acc_descr_value"
        };
        if self.kind() != value_kind {
            self.unexpected(&[value_kind]);
            return None;
        }
        let value = self.take();
        Some(Accessibility {
            span: Span {
                start: keyword.span.start,
                end: value.span.end,
            },
            title: keyword.kind == "acc_title",
            multiline: false,
            value,
        })
    }

    fn title(&mut self) -> Option<Title> {
        let keyword = self.take();
        let text = self.text(TEXT_STARTS)?;
        Some(Title {
            span: Span {
                start: keyword.span.start,
                end: text.span.end,
            },
            text,
        })
    }

    fn text(&mut self, expected: &[&str]) -> Option<Text> {
        if matches!(self.kind(), "STR" | "MD_STR") {
            let token = self.take();
            return Some(Text {
                span: token.span,
                value: token.text.to_owned(),
                markdown: token.kind == "MD_STR",
            });
        }
        if !ALPHA_NUM_TOKENS.contains(&self.kind()) {
            self.unexpected(expected);
            return None;
        }
        let first = self.token();
        let mut value = String::new();
        let mut end = first.span.end;
        while ALPHA_NUM_TOKENS.contains(&self.kind()) {
            let token = self.take();
            value.push_str(token.text);
            end = token.span.end;
        }
        Some(Text {
            span: Span {
                start: first.span.start,
                end,
            },
            value,
            markdown: false,
        })
    }

    fn starts_text(&self) -> bool {
        TEXT_STARTS.contains(&self.kind())
    }

    fn axis(&mut self) -> Option<AxisStatement<'a>> {
        let keyword = self.take();
        let y = keyword.kind == "Y_AXIS";
        let mut axis = AxisStatement {
            span: keyword.span,
            y,
            title: None,
            band: None,
            range: None,
        };
        let mut expected = vec!["NUMBER_WITH_DECIMAL"];
        expected.extend_from_slice(TEXT_STARTS);
        if !y {
            expected.push("SQUARE_BRACES_START");
        }
        let starts_band = !y && self.kind() == "SQUARE_BRACES_START";
        if !self.starts_text() && self.kind() != "NUMBER_WITH_DECIMAL" && !starts_band {
            self.unexpected(&expected);
            return None;
        }
        if self.starts_text() {
            let title = self.text(TEXT_STARTS)?;
            axis.span.end = title.span.end;
            axis.title = Some(title);
        }
        if self.kind() == "NUMBER_WITH_DECIMAL" {
            let range = self.range_data()?;
            axis.span.end = range.span.end;
            axis.range = Some(range);
        } else if !y && self.kind() == "SQUARE_BRACES_START" {
            let band = self.band_data()?;
            axis.span.end = band.span.end;
            axis.band = Some(band);
        }
        Some(axis)
    }

    fn number(&mut self) -> Option<Number<'a>> {
        if self.kind() != "NUMBER_WITH_DECIMAL" {
            self.unexpected(&["NUMBER_WITH_DECIMAL"]);
            return None;
        }
        let token = self.take();
        Some(Number {
            span: token.span,
            text: token.text,
        })
    }

    fn range_data(&mut self) -> Option<Range<'a>> {
        let min = self.number()?;
        if self.kind() != "ARROW_DELIMITER" {
            self.unexpected(&["ARROW_DELIMITER"]);
            return None;
        }
        self.take();
        let max = self.number()?;
        Some(Range {
            span: Span {
                start: min.span.start,
                end: max.span.end,
            },
            min,
            max,
        })
    }

    fn band_data(&mut self) -> Option<BandData> {
        let open = self.take();
        let mut band = BandData {
            span: open.span,
            categories: Vec::new(),
        };
        loop {
            if self.kind() == "EOF" {
                self.unterminated_list(&open, &[]);
                return None;
            }
            band.categories.push(self.text(TEXT_STARTS)?);
            match self.kind() {
                "COMMA" => {
                    self.take();
                }
                "SQUARE_BRACES_END" => {
                    band.span.end = self.take().span.end;
                    return Some(band);
                }
                _ => {
                    self.unterminated_list(&open, &["COMMA", "SQUARE_BRACES_END"]);
                    return None;
                }
            }
        }
    }

    fn unterminated_list(&mut self, open: &Token<'a>, expected: &[&str]) {
        if self.kind() == "EOF" {
            self.issue(
                C_UNTERMINATED,
                format!("unterminated {}", open.text),
                Span {
                    start: open.span.start,
                    end: self.source.len(),
                },
            );
            return;
        }
        self.unexpected(expected);
    }

    fn plot(&mut self) -> Option<PlotStatement<'a>> {
        let keyword = self.take();
        let mut title = None;
        if self.starts_text() {
            title = Some(self.text(TEXT_STARTS)?);
        }
        if self.kind() != "SQUARE_BRACES_START" {
            self.unexpected(&["SQUARE_BRACES_START"]);
            return None;
        }
        let data = self.plot_data()?;
        Some(PlotStatement {
            span: Span {
                start: keyword.span.start,
                end: data.span.end,
            },
            line: keyword.kind == "LINE",
            title,
            data,
        })
    }

    fn plot_data(&mut self) -> Option<PlotData<'a>> {
        let open = self.take();
        let mut data = PlotData {
            span: open.span,
            points: Vec::new(),
        };
        loop {
            data.points.push(self.data_point(&open)?);
            match self.kind() {
                "COMMA" => {
                    self.take();
                }
                "SQUARE_BRACES_END" => {
                    data.span.end = self.take().span.end;
                    return Some(data);
                }
                _ => {
                    self.unterminated_list(&open, &["COMMA", "SQUARE_BRACES_END"]);
                    return None;
                }
            }
        }
    }

    fn data_point(&mut self, open: &Token<'a>) -> Option<DataPoint<'a>> {
        if self.kind() == "EOF" {
            self.unterminated_list(open, &[]);
            return None;
        }
        let number = self.number()?;
        let mut point = DataPoint {
            span: number.span,
            number,
            label: None,
        };
        if self.kind() == "STR" {
            let token = self.take();
            point.span.end = token.span.end;
            point.label = Some(Text {
                span: token.span,
                value: token.text.to_owned(),
                markdown: false,
            });
        }
        Some(point)
    }
}

fn statement_span(kind: &StatementKind<'_>) -> Span {
    match kind {
        StatementKind::Title(k) => k.span,
        StatementKind::Axis(k) => k.span,
        StatementKind::Plot(k) => k.span,
        StatementKind::Accessibility(k) => k.span,
    }
}
