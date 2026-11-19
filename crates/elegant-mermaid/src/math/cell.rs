use super::syntax::{Delimiter, Expr, ExprKind, Space, SymbolClass};
use crate::cells::Charset;
use crate::r#gen::scripts::{SCRIPTS, Script};

/// Linear form of a math expression for the cell profile (`spec/math.md`, math-31).
pub fn linear(expression: &super::syntax::Expr<'_>, charset: crate::cells::Charset) -> String {
    let mut out = String::new();
    write(&mut out, expression, charset);
    out
}

fn write(out: &mut String, expression: &Expr<'_>, charset: Charset) {
    match &expression.kind {
        ExprKind::Literal(source) => out.push_str(source),
        ExprKind::Row(children) => {
            for child in children {
                write(out, child, charset);
            }
        }
        ExprKind::Group(body) | ExprKind::Styled { body, .. } | ExprKind::Text { body } => {
            write(out, body, charset)
        }
        ExprKind::Glyph { character, .. } => out.push(*character),
        ExprKind::Limit { .. } => out.push_str("lim"),
        ExprKind::Symbol {
            command,
            character,
            class,
            ..
        } => match charset {
            Charset::Unicode => out.push(*character),
            Charset::Ascii => out.push_str(ascii(command, *class)),
        },
        ExprKind::Fraction {
            numerator,
            denominator,
        } => {
            out.push('(');
            write(out, numerator, charset);
            out.push_str(")/(");
            write(out, denominator, charset);
            out.push(')');
        }
        ExprKind::Scripts {
            base,
            superscript,
            subscript,
        } => {
            write(out, base, charset);
            if let Some(superscript) = superscript {
                script(out, superscript, charset, '^', |row| row.sup);
            }
            if let Some(subscript) = subscript {
                script(out, subscript, charset, '_', |row| row.sub);
            }
        }
        ExprKind::Radical { index, radicand } => radical(out, index.as_deref(), radicand, charset),
        ExprKind::Delimited { left, body, right } => {
            delimiter(out, *left);
            write(out, body, charset);
            delimiter(out, *right);
        }
        ExprKind::Space(space) => match space {
            Space::Thin => {}
            Space::Medium => out.push(' '),
            Space::Quad => out.push_str("  "),
        },
    }
}

fn script(
    out: &mut String,
    content: &Expr<'_>,
    charset: Charset,
    marker: char,
    field: fn(&Script) -> u32,
) {
    let mut rendered = String::new();
    write(&mut rendered, content, charset);
    if charset != Charset::Unicode || !convert(out, &rendered, field) {
        out.push(marker);
        out.push('(');
        out.push_str(&rendered);
        out.push(')');
    }
}

fn radical(out: &mut String, index: Option<&Expr<'_>>, radicand: &Expr<'_>, charset: Charset) {
    if let Some(index) = index {
        let mut rendered = String::new();
        write(&mut rendered, index, charset);
        if charset != Charset::Unicode || !convert(out, &rendered, |row| row.sup) {
            out.push('[');
            out.push_str(&rendered);
            out.push(']');
        }
    }
    out.push_str(if charset == Charset::Unicode {
        "√("
    } else {
        "sqrt("
    });
    write(out, radicand, charset);
    out.push(')');
}

fn ascii(command: &str, class: SymbolClass) -> &str {
    match class {
        SymbolClass::Greek => command,
        SymbolClass::Sum => "sum",
        SymbolClass::Product => "prod",
        SymbolClass::Integral => "int",
        SymbolClass::Ordinary => "inf",
        SymbolClass::Binary => match command {
            "pm" => "+-",
            "times" => "x",
            "div" => "/",
            _ => ".",
        },
        SymbolClass::Relation => match command {
            "le" => "<=",
            "ge" => ">=",
            "ne" => "!=",
            "approx" => "~=",
            "to" => "->",
            "leftarrow" => "<-",
            "Rightarrow" => "=>",
            "Leftrightarrow" => "<=>",
            _ => "=",
        },
    }
}

fn convert(out: &mut String, rendered: &str, field: fn(&Script) -> u32) -> bool {
    let start = out.len();
    for character in rendered.chars() {
        let Ok(index) = SCRIPTS.binary_search_by_key(&u32::from(character), |row| row.base) else {
            out.truncate(start);
            return false;
        };
        let codepoint = field(&SCRIPTS[index]);
        if codepoint == 0 {
            out.truncate(start);
            return false;
        }
        let Some(mapped) = char::from_u32(codepoint) else {
            out.truncate(start);
            return false;
        };
        out.push(mapped);
    }
    true
}

fn delimiter(out: &mut String, delimiter: Delimiter) {
    let character = match delimiter {
        Delimiter::LeftParen => '(',
        Delimiter::RightParen => ')',
        Delimiter::LeftBracket => '[',
        Delimiter::RightBracket => ']',
        Delimiter::LeftBrace => '{',
        Delimiter::RightBrace => '}',
        Delimiter::Bar => '|',
        Delimiter::Invisible => return,
    };
    out.push(character);
}

#[cfg(test)]
mod tests;
