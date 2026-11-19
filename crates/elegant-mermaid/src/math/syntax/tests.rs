use super::*;
use crate::{diag::Severity, source::Span};

fn row<'tree, 'src>(expression: &'tree Expr<'src>) -> Result<&'tree [Expr<'src>], &'static str> {
    match &expression.kind {
        ExprKind::Row(children) => Ok(children),
        _ => Err("expected horizontal concatenation"),
    }
}

#[test]
fn default_fonts_and_greek_are_distinct() -> Result<(), &'static str> {
    let parsed = parse("x2α\\alpha=\\infty");
    assert!(
        parsed.diagnostics.is_empty(),
        "default-font formula must parse: {parsed:?}"
    );
    let children = row(&parsed.expression)?;
    assert!(
        matches!(
            children[0].kind,
            ExprKind::Glyph {
                character: 'x',
                font: Font::Italic
            }
        ),
        "Latin x must default to italic for vector layout: {:?}",
        children[0]
    );
    assert!(
        matches!(
            children[1].kind,
            ExprKind::Glyph {
                character: '2',
                font: Font::Roman
            }
        ),
        "digit 2 must default to upright: {:?}",
        children[1]
    );
    assert!(
        matches!(
            children[2].kind,
            ExprKind::Glyph {
                character: 'α',
                font: Font::Roman
            }
        ),
        "literal Greek must remain upright: {:?}",
        children[2]
    );
    assert!(
        matches!(
            children[3].kind,
            ExprKind::Symbol {
                command: "alpha",
                character: 'α',
                class: SymbolClass::Greek,
                font: Font::Roman
            }
        ),
        "Greek command must retain its name, scalar and upright font: {:?}",
        children[3]
    );
    assert!(
        matches!(
            children[4].kind,
            ExprKind::Symbol {
                class: SymbolClass::Relation,
                ..
            }
        ),
        "equals must carry relation spacing semantics: {:?}",
        children[4]
    );
    assert_eq!(children[3].span, Span { start: 4, end: 10 });
    Ok(())
}

#[test]
fn fractions_and_scripts_bind_to_one_atom_or_group() -> Result<(), &'static str> {
    let parsed = parse(r"ab^23_{ij}+\frac{x}{y}");
    assert!(
        parsed.diagnostics.is_empty(),
        "atom/group binding formula must parse: {parsed:?}"
    );
    let children = row(&parsed.expression)?;
    assert!(
        matches!(children[0].kind, ExprKind::Glyph { character: 'a', .. }),
        "leading a must stay outside b's script: {:?}",
        children[0]
    );
    let ExprKind::Scripts {
        base,
        superscript: Some(sup),
        subscript: None,
    } = &children[1].kind
    else {
        return Err("b must take only the next scalar as its exponent");
    };
    assert!(
        matches!(base.kind, ExprKind::Glyph { character: 'b', .. }),
        "superscript base must be b, not preceding row: {base:?}"
    );
    assert!(
        matches!(sup.kind, ExprKind::Glyph { character: '2', .. }),
        "unbraced exponent must consume only 2: {sup:?}"
    );
    let ExprKind::Scripts {
        subscript: Some(sub),
        ..
    } = &children[2].kind
    else {
        return Err("the subscript belongs to 3, not b");
    };
    assert!(
        matches!(sub.kind, ExprKind::Group(_)),
        "braces must bind ij as one subscript: {sub:?}"
    );
    assert!(
        matches!(children[4].kind, ExprKind::Fraction { .. }),
        "fraction must remain a separate row atom after scripts: {:?}",
        children[4]
    );
    let paired = parse("x_{1}^{2}");
    assert!(
        matches!(
            &row(&paired.expression)?[0].kind,
            ExprKind::Scripts {
                superscript: Some(_),
                subscript: Some(_),
                ..
            }
        ),
        "paired scripts must share one base for box placement: {paired:?}"
    );
    Ok(())
}

#[test]
fn radicals_preserve_optional_index() -> Result<(), &'static str> {
    for (source, indexed) in [(r"\sqrt{x}", false), (r"\sqrt[n+1]{x}", true)] {
        let parsed = parse(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "radical formula {source:?} must parse: {parsed:?}"
        );
        let ExprKind::Radical { index, radicand } = &row(&parsed.expression)?[0].kind else {
            return Err("expected radical");
        };
        assert_eq!(index.is_some(), indexed);
        assert!(
            matches!(radicand.kind, ExprKind::Group(_)),
            "radicand must retain its braced argument in {source:?}: {radicand:?}"
        );
    }
    Ok(())
}

#[test]
fn explicit_fonts_and_text_keep_semantics() -> Result<(), &'static str> {
    for (source, expected) in [
        (r"\mathbf{x1}", Font::Bold),
        (r"\mathit{x1}", Font::Italic),
        (r"\mathrm{x1}", Font::Roman),
    ] {
        let parsed = parse(source);
        let ExprKind::Styled { font, body } = &row(&parsed.expression)?[0].kind else {
            return Err("expected styled group");
        };
        assert_eq!(*font, expected);
        let ExprKind::Group(content) = &body.kind else {
            return Err("expected braced font argument");
        };
        for item in row(content)? {
            assert!(
                matches!(item.kind, ExprKind::Glyph { font, .. } if font == expected),
                "font command in {source:?} must apply {expected:?} to every glyph: {item:?}"
            );
        }
    }
    let parsed = parse(r"\text{a b_^\$}");
    assert!(
        parsed.diagnostics.is_empty(),
        "text with spaces, script punctuation and escaped dollar must parse: {parsed:?}"
    );
    let ExprKind::Text { body } = &row(&parsed.expression)?[0].kind else {
        return Err("expected text");
    };
    let ExprKind::Group(content) = &body.kind else {
        return Err("expected text group");
    };
    assert_eq!(row(content)?.len(), 6);
    assert!(
        row(content)?.iter().all(|item| matches!(
            item.kind,
            ExprKind::Glyph {
                font: Font::Roman,
                ..
            }
        )),
        "text content must remain upright literal glyphs for both consumers: {content:?}"
    );
    Ok(())
}

#[test]
fn every_delimiter_shape_is_typed() -> Result<(), &'static str> {
    for (left, right, l, r) in [
        ("(", ")", Delimiter::LeftParen, Delimiter::RightParen),
        ("[", "]", Delimiter::LeftBracket, Delimiter::RightBracket),
        (r"\{", r"\}", Delimiter::LeftBrace, Delimiter::RightBrace),
        ("|", "|", Delimiter::Bar, Delimiter::Bar),
        (".", ".", Delimiter::Invisible, Delimiter::Invisible),
    ] {
        let source = format!("\\left{left}x\\right{right}");
        let parsed = parse(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "delimiter formula {source:?} must parse: {parsed:?}"
        );
        assert!(
            matches!(&row(&parsed.expression)?[0].kind, ExprKind::Delimited { left, right, .. } if *left == l && *right == r),
            "delimiter shapes {l:?}/{r:?} must survive for path layout in {source:?}: {:?}",
            parsed.expression
        );
    }
    Ok(())
}

#[test]
fn closed_symbols_are_retained() -> Result<(), &'static str> {
    let parsed = parse(
        r"\sum\prod\int\lim\pm\times\div\cdot\le\ge\ne\approx\to\leftarrow\Rightarrow\Leftrightarrow",
    );
    assert!(
        parsed.diagnostics.is_empty(),
        "all normative operator commands must parse: {parsed:?}"
    );
    let children = row(&parsed.expression)?;
    assert!(
        matches!(
            children[0].kind,
            ExprKind::Symbol {
                class: SymbolClass::Sum,
                ..
            }
        ),
        "sum must retain above/below limit classification: {:?}",
        children[0]
    );
    assert!(
        matches!(
            children[1].kind,
            ExprKind::Symbol {
                class: SymbolClass::Product,
                ..
            }
        ),
        "product must retain above/below limit classification: {:?}",
        children[1]
    );
    assert!(
        matches!(
            children[2].kind,
            ExprKind::Symbol {
                class: SymbolClass::Integral,
                ..
            }
        ),
        "integral must retain right-side script classification: {:?}",
        children[2]
    );
    assert!(
        matches!(children[3].kind, ExprKind::Limit { font: Font::Roman }),
        "lim must be upright text with below-limit semantics: {:?}",
        children[3]
    );
    assert!(
        children[4..8].iter().all(|node| matches!(
            node.kind,
            ExprKind::Symbol {
                class: SymbolClass::Binary,
                ..
            }
        )),
        "pm/times/div/cdot must receive binary spacing: {:?}",
        &children[4..8]
    );
    assert!(
        children[8..16].iter().all(|node| matches!(
            node.kind,
            ExprKind::Symbol {
                class: SymbolClass::Relation,
                ..
            }
        )),
        "relation commands must receive relation spacing: {:?}",
        &children[8..16]
    );
    Ok(())
}

#[test]
fn fixed_spaces_are_retained() -> Result<(), &'static str> {
    let parsed = parse(r"\,\;\quad");
    assert!(
        parsed.diagnostics.is_empty(),
        "all fixed-space commands must parse: {parsed:?}"
    );
    let children = row(&parsed.expression)?;
    assert!(
        matches!(children[0].kind, ExprKind::Space(Space::Thin)),
        "comma space must remain Thin for vector/cell width selection: {:?}",
        children[0]
    );
    assert!(
        matches!(children[1].kind, ExprKind::Space(Space::Medium)),
        "semicolon space must remain Medium for vector/cell width selection: {:?}",
        children[1]
    );
    assert!(
        matches!(children[2].kind, ExprKind::Space(Space::Quad)),
        "quad space must retain its distinct width: {:?}",
        children[2]
    );
    Ok(())
}

#[test]
fn escapes_and_entities_are_not_reinterpreted() -> Result<(), &'static str> {
    let parsed = parse(r"\$\{\}\_\^\\#alpha;");
    assert!(
        parsed.diagnostics.is_empty(),
        "escaped punctuation and literal entity spelling must parse: {parsed:?}"
    );
    let characters: String = row(&parsed.expression)?
        .iter()
        .filter_map(|node| match node.kind {
            ExprKind::Glyph { character, .. } => Some(character),
            _ => None,
        })
        .collect();
    assert_eq!(characters, "$ {}_^\\#alpha;".replace(' ', ""));
    Ok(())
}

#[test]
fn unsupported_commands_fallback_to_entire_borrowed_source() {
    for command in [
        "unknown",
        "omicron",
        "varpi",
        "varrho",
        "varsigma",
        "alphabeta",
    ] {
        let source = format!("α+\\{command}+x");
        let parsed = parse(&source);
        assert!(
            matches!(parsed.expression.kind, ExprKind::Literal(text) if text == source),
            "unsupported command must preserve entire {source:?} as literal, not a partial AST: {:?}",
            parsed.expression
        );
        assert_eq!(parsed.diagnostics.len(), 1);
        let diagnostic = &parsed.diagnostics[0];
        assert_eq!(diagnostic.code, "math/unsupported-command");
        assert_eq!(diagnostic.severity, Severity::Warning);
        assert_eq!(
            diagnostic.message,
            format!("unsupported math command \\{command}")
        );
        assert_eq!(diagnostic.help, "The source text is shown as written.");
        assert_eq!(
            diagnostic.span,
            Span {
                start: 0,
                end: source.len()
            }
        );
    }
}

#[test]
fn malformed_constructs_report_whole_formula_span() {
    for source in [
        "{x",
        "x}",
        r"\frac{x}",
        r"\frac x{y}",
        r"\sqrt",
        r"\sqrt[2{x}",
        "x^",
        "x_",
        "^x",
        "x^1^2",
        r"\left(x",
        r"\right)",
        r"\left x\right)",
        "\\",
    ] {
        let parsed = parse(source);
        assert!(
            matches!(parsed.expression.kind, ExprKind::Literal(text) if text == source),
            "malformed {source:?} must preserve the entire formula as literal: {:?}",
            parsed.expression
        );
        let diagnostic = &parsed.diagnostics[0];
        assert_eq!(diagnostic.code, "math/syntax", "{source}");
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(
            diagnostic.message.starts_with("invalid math syntax: "),
            "syntax failure in {source:?} must carry normative reason prefix: {diagnostic:?}"
        );
        assert_eq!(
            diagnostic.span,
            Span {
                start: 0,
                end: source.len()
            }
        );
        assert_eq!(diagnostic.help, "The source text is shown as written.");
    }
}

#[test]
fn nesting_limit_is_not_a_silent_cap() {
    let accepted = format!("{}x{}", "{".repeat(64), "}".repeat(64));
    let accepted_parse = parse(&accepted);
    assert!(
        accepted_parse.diagnostics.is_empty(),
        "64 nested groups must remain within the supported depth: source {accepted:?}, result {accepted_parse:?}"
    );
    let rejected = format!("{{{accepted}}}");
    let parsed = parse(&rejected);
    assert_eq!(parsed.diagnostics[0].code, "limit/nesting-depth");
    assert_eq!(parsed.diagnostics[0].span, Span { start: 64, end: 65 });
}

#[test]
fn every_normative_greek_name_is_supported_upright() -> Result<(), &'static str> {
    for name in [
        "alpha",
        "beta",
        "gamma",
        "delta",
        "epsilon",
        "varepsilon",
        "zeta",
        "eta",
        "theta",
        "vartheta",
        "iota",
        "kappa",
        "lambda",
        "mu",
        "nu",
        "xi",
        "pi",
        "rho",
        "sigma",
        "tau",
        "upsilon",
        "phi",
        "varphi",
        "chi",
        "psi",
        "omega",
        "Gamma",
        "Delta",
        "Theta",
        "Lambda",
        "Xi",
        "Pi",
        "Sigma",
        "Upsilon",
        "Phi",
        "Psi",
        "Omega",
    ] {
        let source = format!("\\{name}");
        let parsed = parse(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "normative Greek command {name:?} must parse: {parsed:?}"
        );
        assert!(
            matches!(
                row(&parsed.expression)?[0].kind,
                ExprKind::Symbol {
                    class: SymbolClass::Greek,
                    font: Font::Roman,
                    ..
                }
            ),
            "Greek command {name:?} must retain upright Greek classification: {:?}",
            parsed.expression
        );
    }
    Ok(())
}
