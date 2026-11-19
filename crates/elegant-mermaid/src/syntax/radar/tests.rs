use super::ast::{Curve, Start};
use super::lexer::{id_length, number_length};
use super::parser::{Parsed, parse};
use crate::diag::Diagnostic;
use crate::source::Span;

type Check = Result<(), &'static str>;

fn parsed(source: &str) -> Parsed {
    parse(source, &[])
}

fn clean(source: &str) -> Result<Start, &'static str> {
    let result = parsed(source);
    if result.diagnostics.is_empty() {
        Ok(result.document)
    } else {
        Err("unexpected diagnostics")
    }
}

fn messages(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

fn numbers(curve: &Curve) -> Vec<&str> {
    curve
        .entries
        .iter()
        .map(|entry| entry.number().text.as_str())
        .collect()
}

#[test]
fn header_forms() -> Check {
    for (source, header) in [
        ("radar-beta\naxis A", "radar-beta"),
        ("radar-beta:\naxis A", "radar-beta:"),
        ("radar-beta :\naxis A", "radar-beta"),
        ("radar-beta\n\n\naxis A", "radar-beta"),
        ("\n\nradar-beta", "radar-beta"),
        ("radar-beta axis A", "radar-beta"),
        ("radar-beta %% c\naxis A", "radar-beta"),
    ] {
        let start = clean(source)?;
        assert_eq!(start.header.kind, header, "{source}");
    }
    Ok(())
}

#[test]
fn header_needs_boundary() -> Check {
    for source in [
        "radar-betax",
        "radar-beta{",
        "radar-beta-1\n",
        "Radar-Beta\n",
    ] {
        let result = parsed(source);
        let first = result.diagnostics.first().ok_or("no diagnostic")?;
        assert_eq!(first.code, "radar/unexpected-token", "{source}");
    }
    Ok(())
}

#[test]
fn statement_forms() -> Check {
    let start = clean(
        "radar-beta\ntitle  My   radar\naccTitle: t\naccDescr: d %% c\n\
         axis m[\"Math\"], s['Sci'], plain\n\
         curve a[\"Alice\"]{85, 90.5, 0}, b{\n  1,\n  2,\n  3\n}\n\
         curve k { m: 1, s 2, plain: 3 }\n\
         showLegend false, ticks 3\nmax 8 min 0\ngraticule polygon\n",
    )?;
    assert_eq!(start.title.as_ref().ok_or("title")?.value, "My radar");
    assert_eq!(start.acc_title.as_ref().ok_or("accTitle")?.value, "t");
    assert_eq!(start.acc_descr.as_ref().ok_or("accDescr")?.value, "d");
    assert_eq!(start.axes.len(), 3);
    let label = |index: usize| {
        start.axes[index]
            .label
            .as_ref()
            .map(|l| l.value.text.as_str())
    };
    assert_eq!(label(0), Some("Math"));
    assert_eq!(label(1), Some("Sci"));
    assert_eq!(label(2), None);
    assert_eq!(start.curves.len(), 3);
    assert_eq!(numbers(&start.curves[0]), ["85", "90.5", "0"]);
    assert_eq!(numbers(&start.curves[1]), ["1", "2", "3"]);
    for (entry, name) in start.curves[2].entries.iter().zip(["m", "s", "plain"]) {
        assert_eq!(entry.reference().ok_or("keyed")?.text, name);
    }
    let options: Vec<String> = start
        .options
        .iter()
        .map(|o| format!("{}={}", o.name.kind, o.value.text))
        .collect();
    assert_eq!(
        options,
        [
            "showLegend=false",
            "ticks=3",
            "max=8",
            "min=0",
            "graticule=polygon"
        ]
    );
    Ok(())
}

#[test]
fn spans() -> Check {
    let source = "radar-beta\naxis A[\"x\"] , B\ncurve c{1, 2}  %% tail\nmax 5\n";
    let start = clean(source)?;
    assert_eq!(start.axes[0].span, Span { start: 16, end: 22 });
    assert_eq!(start.axes[1].span, Span { start: 25, end: 26 });
    assert_eq!(start.curves[0].span, Span { start: 33, end: 40 });
    assert_eq!(
        start.span,
        Span {
            start: 0,
            end: source.len() - 1
        }
    );
    assert_eq!(start.options[0].span, Span { start: 50, end: 55 });
    Ok(())
}

#[test]
fn number_token_follows_the_authority_pattern() {
    for (source, want) in [
        ("0", 1),
        ("7", 1),
        ("42", 2),
        ("1.5", 3),
        ("0.5", 3),
        ("12.25", 5),
        ("01", 1),
        ("007", 1),
        ("1.", 0),
        ("12.", 1),
        (".5", 0),
        ("1.2.3", 0),
        ("1.25.3", 3),
        ("x", 0),
    ] {
        assert_eq!(number_length(source), want, "{source}");
    }
}

#[test]
fn identifier_token_follows_the_authority_pattern() {
    for (source, want) in [
        ("a", 1),
        ("a-b", 3),
        ("a-", 1),
        ("a--", 1),
        ("a-b-", 3),
        ("_x", 2),
        ("3d", 2),
        ("-a", 0),
        ("a.b", 1),
        ("é", 0),
    ] {
        assert_eq!(id_length(source), want, "{source}");
    }
}

#[test]
fn keywords_yield_to_longer_identifiers() -> Check {
    let start = clean("radar-beta\naxis maximum, axis-1, ticks2\n")?;
    assert_eq!(start.axes.len(), 3);
    for source in [
        "radar-beta\naxis axis\n",
        "radar-beta\naxis max\n",
        "radar-beta\naxis true\n",
        "radar-beta\ncurve circle {1}\n",
        "radar-beta\naxis 3d\n",
    ] {
        assert!(!parsed(source).diagnostics.is_empty(), "{source}");
    }
    Ok(())
}

#[test]
fn string_escapes() -> Check {
    let text = |source: &str| -> Result<String, &'static str> {
        let start = clean(source)?;
        let label = start.axes[0].label.as_ref().ok_or("label")?;
        Ok(label.value.text.clone())
    };
    assert_eq!(
        text("radar-beta\naxis A[\"a\\\"b\\nc\\\\d\\q\"]\n")?,
        "a\"b\nc\\dq"
    );
    assert_eq!(text("radar-beta\naxis A[\"two\nlines\"]\n")?, "two\nlines");
    assert!(
        !parsed("radar-beta\naxis A[\"x\\\ny\"]\n")
            .diagnostics
            .is_empty()
    );
    Ok(())
}

#[test]
fn curve_entry_rules() {
    for (source, want) in [
        (
            "radar-beta\ncurve c {}\n",
            "radar/unexpected-token: unexpected }, expected one of: ID, NUMBER",
        ),
        (
            "radar-beta\ncurve c {1,}\n",
            "radar/unexpected-token: unexpected }, expected one of: NUMBER",
        ),
        (
            "radar-beta\ncurve c {A 1, 2}\n",
            "radar/unexpected-token: unexpected 2, expected one of: ID",
        ),
        (
            "radar-beta\ncurve c {1, B 2}\n",
            "radar/unexpected-token: unexpected B, expected one of: NUMBER",
        ),
        (
            "radar-beta\ncurve c {1\n,2}\n",
            "radar/unexpected-token: unexpected ,, expected one of: }",
        ),
        (
            "radar-beta\ncurve c 1\n",
            "radar/unexpected-token: unexpected 1, expected one of: {",
        ),
        (
            "radar-beta\ncurve c {-3}\n",
            "radar/unexpected-token: unexpected -, expected one of: ID, NUMBER",
        ),
        (
            "radar-beta\ncurve c {01}\n",
            "radar/unexpected-token: unexpected 1, expected one of: }",
        ),
        (
            "radar-beta\nshowLegend yes\n",
            "radar/unexpected-token: unexpected yes, expected one of: BOOLEAN",
        ),
        (
            "radar-beta\ngraticule square\n",
            "radar/unexpected-token: unexpected square, expected one of: GRATICULE",
        ),
        (
            "radar-beta\ntitlefoo\n",
            "radar/unexpected-token: unexpected foo, expected one of: EOF, NEWLINE",
        ),
        (
            "radar-beta\naxis A,\n",
            "radar/unexpected-token: unexpected \n, expected one of: ID",
        ),
        (
            "radar-beta\naxis A; axis B\n",
            "radar/unknown-statement: unknown statement ;",
        ),
    ] {
        let found = messages(&parsed(source).diagnostics);
        assert!(found.iter().any(|m| m == want), "{source}: {found:?}");
    }
}

#[test]
fn recovery_continues_after_a_rejected_statement() -> Check {
    let result = parsed("radar-beta\naxis A, 5\ncurve c {1,}\ncurve ok {2}\naxis B\n");
    assert_eq!(
        messages(&result.diagnostics),
        [
            "radar/unexpected-token: unexpected 5, expected one of: ID",
            "radar/unexpected-token: unexpected }, expected one of: NUMBER",
        ]
    );
    assert_eq!(result.document.axes.len(), 2);
    assert_eq!(result.document.curves.len(), 1);
    assert_eq!(result.document.curves[0].name.text, "ok");
    Ok(())
}

#[test]
fn recovery_inside_braces_stops_at_the_closing_brace() -> Check {
    let result = parsed("radar-beta\ncurve c {1,\n  oops 2,\n  3} axis B\n");
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.document.axes.len(), 1);
    assert_eq!(result.document.axes[0].name.text, "B");
    Ok(())
}

#[test]
fn unknown_statement_spans_the_line() -> Check {
    let result = parsed("radar-beta\nfoo bar \"baz\"\naxis A\n");
    assert_eq!(
        messages(&result.diagnostics),
        ["radar/unknown-statement: unknown statement foo"]
    );
    assert_eq!(result.diagnostics[0].span, Span { start: 11, end: 24 });
    assert_eq!(result.document.axes.len(), 1);
    Ok(())
}

#[test]
fn unknown_statement_skips_curve_braces() -> Check {
    let result = parsed("radar-beta\nfoo {\n1}\naxis A\n");
    assert_eq!(
        messages(&result.diagnostics),
        ["radar/unknown-statement: unknown statement foo"]
    );
    assert_eq!(result.diagnostics[0].span, Span { start: 11, end: 19 });
    assert_eq!(result.document.axes.len(), 1);
    Ok(())
}

#[test]
fn unterminated_produces_only_the_opener_diagnostic() {
    for (source, opener) in [
        ("radar-beta\naxis A[\"abc", Span { start: 18, end: 22 }),
        (
            "radar-beta\naxis A['abc\naxis B",
            Span { start: 18, end: 29 },
        ),
        (
            "radar-beta\naccDescr {\nnever closed",
            Span { start: 20, end: 34 },
        ),
        ("radar-beta\naxis A[\"x\\", Span { start: 18, end: 21 }),
    ] {
        let result = parsed(source);
        assert_eq!(result.diagnostics.len(), 1, "{source}");
        assert_eq!(result.diagnostics[0].code, "radar/unterminated", "{source}");
        assert_eq!(result.diagnostics[0].span, opener, "{source}");
    }
}

#[test]
fn metadata_values() -> Check {
    let start = clean(
        "radar-beta\ntitle   My   diagram \naccTitle:  T\t\t t \naccDescr: d %% c\n\
         accDescr {\n  one   two\n\n  three  \n}\ntitle\n",
    )?;
    assert_eq!(start.title.as_ref().ok_or("title")?.value, "");
    assert_eq!(start.acc_title.as_ref().ok_or("accTitle")?.value, "T t");
    assert_eq!(
        start.acc_descr.as_ref().ok_or("accDescr")?.value,
        "one two\nthree"
    );
    Ok(())
}

#[test]
fn comments_and_line_endings() -> Check {
    let start = clean(
        "radar-beta\r\n%% only a comment\r\naxis A %% trailing\r\n\r\ncurve c {1}\raxis B\n",
    )?;
    assert_eq!(start.axes.len(), 2);
    assert_eq!(start.curves.len(), 1);
    Ok(())
}

#[test]
fn removed_spans_are_skipped() -> Check {
    let source = "---\ntitle: x\n---\nradar-beta\naxis A\n";
    let result = parse(source, &[Span { start: 0, end: 17 }]);
    assert!(result.diagnostics.is_empty());
    assert_eq!(result.document.header.kind, "radar-beta");
    assert_eq!(result.document.axes.len(), 1);
    Ok(())
}

#[test]
fn nested_braces_do_not_recurse() {
    let source = format!("radar-beta\ncurve c {{{}\n", "{".repeat(4096));
    assert!(!parsed(&source).diagnostics.is_empty());
}
