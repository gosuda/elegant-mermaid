use super::ast::*;
use crate::{
    diag::{Diagnostic, Severity},
    source::Span,
};

type ParseResult<'a> = Result<Expr<'a>, Failure<'a>>;

enum Failure<'a> {
    Syntax(&'static str),
    Unsupported(&'a str),
    Depth(Span),
}

impl Failure<'_> {
    fn into_diagnostic(self, source: &str) -> Diagnostic {
        let (code, severity, message, span, help) = match self {
            Self::Syntax(reason) => (
                "math/syntax",
                Severity::Error,
                format!("invalid math syntax: {reason}"),
                Span {
                    start: 0,
                    end: source.len(),
                },
                "The source text is shown as written.",
            ),
            Self::Unsupported(name) => (
                "math/unsupported-command",
                Severity::Warning,
                format!("unsupported math command \\{name}"),
                Span {
                    start: 0,
                    end: source.len(),
                },
                "The source text is shown as written.",
            ),
            Self::Depth(span) => (
                "limit/nesting-depth",
                Severity::Error,
                "nesting depth exceeds 64".into(),
                span,
                "Reduce the nesting to 64 levels or fewer.",
            ),
        };
        Diagnostic {
            code,
            severity,
            message,
            span,
            related: Vec::new(),
            help: help.into(),
            fixes: Vec::new(),
        }
    }
}

/// Parses formula content, without the surrounding `$$`. A failed formula is
/// one borrowed literal expression; diagnostic spans cover that whole formula.
pub fn parse(source: &str) -> Parsed<'_> {
    let mut parser = Parser { source, offset: 0 };
    let result = parser.row(Stop::End, 0, None, Mode::Math);
    let (expression, diagnostics) = match result {
        Ok(expression) => (expression, Vec::new()),
        Err(failure) => (
            Expr {
                span: Span {
                    start: 0,
                    end: source.len(),
                },
                kind: ExprKind::Literal(source),
            },
            vec![failure.into_diagnostic(source)],
        ),
    };
    Parsed {
        source,
        expression,
        diagnostics,
    }
}

#[derive(Clone, Copy)]
enum Stop {
    End,
    Brace,
    Index,
    Right,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Math,
    Text,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Binding {
    Atom,
    Group,
}

struct Parser<'a> {
    source: &'a str,
    offset: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<char> {
        self.source[self.offset..].chars().next()
    }
    fn take(&mut self) -> Option<char> {
        let character = self.peek()?;
        self.offset += character.len_utf8();
        Some(character)
    }
    fn whitespace(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.take();
        }
    }
    fn right(&self) -> bool {
        self.source[self.offset..]
            .strip_prefix("\\right")
            .is_some_and(|tail| !tail.starts_with(|c: char| c.is_ascii_alphabetic()))
    }
    fn nested(&self, depth: usize) -> Result<usize, Failure<'a>> {
        if depth >= 64 {
            Err(Failure::Depth(Span {
                start: self.offset,
                end: self.offset + self.peek().map_or(0, char::len_utf8),
            }))
        } else {
            Ok(depth + 1)
        }
    }
    fn row(&mut self, stop: Stop, depth: usize, font: Option<Font>, mode: Mode) -> ParseResult<'a> {
        let start = self.offset;
        let mut children = Vec::new();
        loop {
            if mode == Mode::Math {
                self.whitespace();
            }
            let Some(character) = self.peek() else {
                if !matches!(stop, Stop::End) {
                    return Err(Failure::Syntax("unclosed group or delimiter"));
                }
                break;
            };
            if matches!(stop, Stop::Brace) && character == '}'
                || matches!(stop, Stop::Index) && character == ']'
                || matches!(stop, Stop::Right) && self.right()
            {
                break;
            }
            if character == '}' {
                return Err(Failure::Syntax("unmatched closing brace"));
            }
            if mode == Mode::Math && matches!(character, '^' | '_') {
                return Err(Failure::Syntax("script has no base"));
            }
            let atom = self.atom(depth, font, mode)?;
            children.push(if mode == Mode::Text {
                atom
            } else {
                self.scripts(atom, depth, font)?
            });
        }
        Ok(Expr {
            span: Span {
                start,
                end: self.offset,
            },
            kind: ExprKind::Row(children),
        })
    }
    fn group(&mut self, depth: usize, font: Option<Font>, mode: Mode) -> ParseResult<'a> {
        let next = self.nested(depth)?;
        let start = self.offset;
        self.take();
        let body = self.row(Stop::Brace, next, font, mode)?;
        self.take();
        Ok(Expr {
            span: Span {
                start,
                end: self.offset,
            },
            kind: ExprKind::Group(Box::new(body)),
        })
    }
    fn argument(
        &mut self,
        depth: usize,
        font: Option<Font>,
        mode: Mode,
        binding: Binding,
    ) -> ParseResult<'a> {
        self.whitespace();
        match self.peek() {
            Some('{') => self.group(depth, font, mode),
            None | Some('}' | '^' | '_') => Err(Failure::Syntax("missing argument")),
            _ if self.right() || binding == Binding::Group => {
                Err(Failure::Syntax("missing braced argument"))
            }
            _ => {
                let next = self.nested(depth)?;
                self.atom(next, font, mode)
            }
        }
    }
    fn scripts(&mut self, base: Expr<'a>, depth: usize, font: Option<Font>) -> ParseResult<'a> {
        let mut superscript = None;
        let mut subscript = None;
        loop {
            self.whitespace();
            let Some(marker @ ('^' | '_')) = self.peek() else {
                break;
            };
            self.take();
            let target = if marker == '^' {
                &mut superscript
            } else {
                &mut subscript
            };
            if target.is_some() {
                return Err(Failure::Syntax("duplicate script"));
            }
            *target = Some(Box::new(self.argument(
                depth,
                font,
                Mode::Math,
                Binding::Atom,
            )?));
        }
        if superscript.is_none() && subscript.is_none() {
            return Ok(base);
        }
        Ok(Expr {
            span: Span {
                start: base.span.start,
                end: self.offset,
            },
            kind: ExprKind::Scripts {
                base: Box::new(base),
                superscript,
                subscript,
            },
        })
    }
    fn atom(&mut self, depth: usize, font: Option<Font>, mode: Mode) -> ParseResult<'a> {
        let start = self.offset;
        if self.peek() == Some('{') {
            return self.group(depth, font, mode);
        }
        let Some(character) = self.take() else {
            return Err(Failure::Syntax("missing argument"));
        };
        let kind = if character == '\\' {
            self.command(depth, font, mode)?
        } else if character == '=' && mode == Mode::Math {
            ExprKind::Symbol {
                command: &self.source[start..self.offset],
                character,
                class: SymbolClass::Relation,
                font: font.unwrap_or(Font::Roman),
            }
        } else {
            ExprKind::Glyph {
                character,
                font: font.unwrap_or(if character.is_ascii_alphabetic() {
                    Font::Italic
                } else {
                    Font::Roman
                }),
            }
        };
        Ok(Expr {
            span: Span {
                start,
                end: self.offset,
            },
            kind,
        })
    }
    fn command(
        &mut self,
        depth: usize,
        font: Option<Font>,
        mode: Mode,
    ) -> Result<ExprKind<'a>, Failure<'a>> {
        let start = self.offset;
        if self.peek().is_some_and(|c| c.is_ascii_alphabetic()) {
            while self.peek().is_some_and(|c| c.is_ascii_alphabetic()) {
                self.take();
            }
        } else {
            self.take();
        }
        if self.offset == start {
            return Err(Failure::Syntax("missing command"));
        }
        let name = &self.source[start..self.offset];
        if name.len() == 1
            && name.as_bytes()[0].is_ascii_punctuation()
            && !matches!(name, "," | ";")
        {
            let character = name
                .chars()
                .next()
                .ok_or(Failure::Syntax("missing command"))?;
            return Ok(ExprKind::Glyph {
                character,
                font: font.unwrap_or(Font::Roman),
            });
        }
        match name {
            "frac" if mode == Mode::Math => Ok(ExprKind::Fraction {
                numerator: Box::new(self.argument(depth, font, Mode::Math, Binding::Group)?),
                denominator: Box::new(self.argument(depth, font, Mode::Math, Binding::Group)?),
            }),
            "sqrt" if mode == Mode::Math => {
                self.whitespace();
                let index = if self.peek() == Some('[') {
                    let next = self.nested(depth)?;
                    self.take();
                    let index = self.row(Stop::Index, next, font, Mode::Math)?;
                    self.take();
                    Some(Box::new(index))
                } else {
                    None
                };
                Ok(ExprKind::Radical {
                    index,
                    radicand: Box::new(self.argument(depth, font, Mode::Math, Binding::Group)?),
                })
            }
            "left" if mode == Mode::Math => {
                let next = self.nested(depth)?;
                let left = self.delimiter()?;
                let body = self.row(Stop::Right, next, font, Mode::Math)?;
                self.offset += "\\right".len();
                let right = self.delimiter()?;
                Ok(ExprKind::Delimited {
                    left,
                    body: Box::new(body),
                    right,
                })
            }
            "right" if mode == Mode::Math => {
                Err(Failure::Syntax("right delimiter has no left delimiter"))
            }
            "mathbf" | "mathit" | "mathrm" if mode == Mode::Math => {
                let selected = match name {
                    "mathbf" => Font::Bold,
                    "mathit" => Font::Italic,
                    _ => Font::Roman,
                };
                Ok(ExprKind::Styled {
                    font: selected,
                    body: Box::new(self.argument(
                        depth,
                        Some(selected),
                        Mode::Math,
                        Binding::Group,
                    )?),
                })
            }
            "text" if mode == Mode::Math => Ok(ExprKind::Text {
                body: Box::new(self.argument(
                    depth,
                    Some(Font::Roman),
                    Mode::Text,
                    Binding::Group,
                )?),
            }),
            "," => Ok(ExprKind::Space(Space::Thin)),
            ";" => Ok(ExprKind::Space(Space::Medium)),
            "quad" => Ok(ExprKind::Space(Space::Quad)),
            "lim" => Ok(ExprKind::Limit {
                font: font.unwrap_or(Font::Roman),
            }),
            _ => {
                if let Some((character, class)) = symbol(name) {
                    Ok(ExprKind::Symbol {
                        command: name,
                        character,
                        class,
                        font: font.unwrap_or(Font::Roman),
                    })
                } else {
                    Err(Failure::Unsupported(name))
                }
            }
        }
    }
    fn delimiter(&mut self) -> Result<Delimiter, Failure<'a>> {
        self.whitespace();
        let escaped = self.peek() == Some('\\');
        if escaped {
            self.take();
        }
        match (escaped, self.take()) {
            (false, Some('(')) => Ok(Delimiter::LeftParen),
            (false, Some(')')) => Ok(Delimiter::RightParen),
            (false, Some('[')) => Ok(Delimiter::LeftBracket),
            (false, Some(']')) => Ok(Delimiter::RightBracket),
            (true, Some('{')) => Ok(Delimiter::LeftBrace),
            (true, Some('}')) => Ok(Delimiter::RightBrace),
            (false, Some('|')) => Ok(Delimiter::Bar),
            (false, Some('.')) => Ok(Delimiter::Invisible),
            _ => Err(Failure::Syntax("missing or invalid delimiter")),
        }
    }
}

fn symbol(name: &str) -> Option<(char, SymbolClass)> {
    use SymbolClass::*;
    let result = match name {
        "sum" => ('∑', Sum),
        "prod" => ('∏', Product),
        "int" => ('∫', Integral),
        "infty" => ('∞', Ordinary),
        "pm" => ('±', Binary),
        "times" => ('×', Binary),
        "div" => ('÷', Binary),
        "cdot" => ('⋅', Binary),
        "le" => ('≤', Relation),
        "ge" => ('≥', Relation),
        "ne" => ('≠', Relation),
        "approx" => ('≈', Relation),
        "to" => ('→', Relation),
        "leftarrow" => ('←', Relation),
        "Rightarrow" => ('⇒', Relation),
        "Leftrightarrow" => ('⇔', Relation),
        _ => {
            let table = crate::r#gen::mathgreek::MATH_GREEK;
            let index = table.binary_search_by_key(&name, |row| row.name).ok()?;
            return char::from_u32(table[index].codepoint).map(|character| (character, Greek));
        }
    };
    Some(result)
}
