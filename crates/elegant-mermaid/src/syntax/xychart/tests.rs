use super::ast::{AxisStatement, PlotStatement, Start, StatementKind, Title};
use super::parse;
use crate::source::Span;

type Check = Result<(), &'static str>;

const FULL: &str = "xychart-beta horizontal\n  title \"Sales\"\n  x-axis Months [jan, \"feb x\", mar]\n  y-axis \"Revenue\" 0 --> 10.5\n  bar [1, 2.5, -3]\n  line \"L\" [3 \"p\", 4]\n";

fn clean(source: &str) -> Result<Start<'_>, &'static str> {
    let parsed = parse(source, &[]);
    if parsed.diagnostics.is_empty() {
        Ok(parsed.document)
    } else {
        Err("unexpected diagnostics")
    }
}

fn kind_at<'a, 'b>(
    start: &'b Start<'a>,
    index: usize,
) -> Result<&'b StatementKind<'a>, &'static str> {
    start
        .document
        .statements
        .get(index)
        .map(|statement| &statement.kind)
        .ok_or("missing statement")
}

fn title_at<'b>(start: &'b Start<'_>, index: usize) -> Result<&'b Title, &'static str> {
    match kind_at(start, index)? {
        StatementKind::Title(title) => Ok(title),
        _ => Err("not a title"),
    }
}

fn axis_at<'a, 'b>(
    start: &'b Start<'a>,
    index: usize,
) -> Result<&'b AxisStatement<'a>, &'static str> {
    match kind_at(start, index)? {
        StatementKind::Axis(axis) => Ok(axis),
        _ => Err("not an axis"),
    }
}

fn plot_at<'a, 'b>(
    start: &'b Start<'a>,
    index: usize,
) -> Result<&'b PlotStatement<'a>, &'static str> {
    match kind_at(start, index)? {
        StatementKind::Plot(plot) => Ok(plot),
        _ => Err("not a plot"),
    }
}

#[test]
fn header_and_title() -> Check {
    let start = clean(FULL)?;
    assert_eq!(start.headers.len(), 1);
    let orientation = start.headers[0]
        .orientation
        .as_ref()
        .ok_or("no orientation")?;
    assert_eq!(orientation.text, "horizontal");
    assert_eq!(start.document.statements.len(), 5);
    assert_eq!(title_at(&start, 0)?.text.value, "Sales");
    Ok(())
}

#[test]
fn axis_statements() -> Check {
    let start = clean(FULL)?;
    let x = axis_at(&start, 1)?;
    assert!(!x.y);
    assert_eq!(x.title.as_ref().ok_or("no title")?.value, "Months");
    let band = x.band.as_ref().ok_or("no band")?;
    assert_eq!(band.categories.len(), 3);
    assert_eq!(band.categories[1].value, "feb x");
    let y = axis_at(&start, 2)?;
    assert!(y.y);
    assert_eq!(y.range.as_ref().ok_or("no range")?.max.text, "10.5");
    Ok(())
}

#[test]
fn plot_statements() -> Check {
    let start = clean(FULL)?;
    let bar = plot_at(&start, 3)?;
    assert!(!bar.line);
    assert!(bar.title.is_none());
    assert_eq!(bar.data.points[2].number.text, "-3");
    let line = plot_at(&start, 4)?;
    assert!(line.line);
    assert_eq!(line.title.as_ref().ok_or("no title")?.value, "L");
    let labelled = line.data.points[0].label.as_ref().ok_or("no label")?;
    assert_eq!(labelled.value, "p");
    assert!(line.data.points[1].label.is_none());
    Ok(())
}

#[test]
fn semicolon_separates_statements_on_one_line() -> Check {
    let start = clean("xychart\ntitle T; x-axis [a, b]; bar [1, 2]\n")?;
    assert_eq!(start.document.statements.len(), 3);
    Ok(())
}

#[test]
fn unquoted_text_concatenates_tokens_without_spaces() -> Check {
    let start = clean("xychart\ntitle Sales 2024_Q1 & more\n")?;
    assert_eq!(title_at(&start, 0)?.text.value, "Sales2024_Q1&more");
    Ok(())
}

#[test]
fn markdown_text_keeps_its_kind() -> Check {
    let start = clean("xychart\ntitle \"`*bold*`\"\n")?;
    let text = &title_at(&start, 0)?.text;
    assert!(text.markdown);
    assert_eq!(text.value, "*bold*");
    Ok(())
}

#[test]
fn accessibility_statements() -> Check {
    let start =
        clean("xychart\naccTitle: A title\naccDescr: A line\naccDescr {\nmulti\nline\n}\n")?;
    assert_eq!(start.document.statements.len(), 3);
    assert!(matches!(kind_at(&start, 0)?, StatementKind::Accessibility(a) if a.title));
    assert!(matches!(kind_at(&start, 2)?, StatementKind::Accessibility(a) if a.multiline));
    Ok(())
}

#[test]
fn axis_modes_pop_at_line_end() -> Check {
    let start = clean("xychart\nx-axis 1 --> 5\nbar [1,2]\ny-axis 2 --> 3\n")?;
    assert_eq!(start.document.statements.len(), 3);
    Ok(())
}

#[test]
fn keywords_require_a_word_boundary() {
    let parsed = parse("xychart\nbarx [1]\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.diagnostics[0].code, "xychart/unknown-statement");
}

struct Case {
    name: &'static str,
    source: &'static str,
    code: &'static str,
    message: &'static str,
    span: Span,
}

const Y_BAND: &str = "unexpected [, expected one of: ALPHA, AMP, BRKT, DOT, EQUALS, MD_STR, MINUS, MULT, NUM, NUMBER_WITH_DECIMAL, PLUS, STR, UNDERSCORE";

const CASES: [Case; 6] = [
    Case {
        name: "trailing comma",
        source: "xychart\nbar [1, ]\n",
        code: "xychart/unexpected-token",
        message: "unexpected ], expected one of: NUMBER_WITH_DECIMAL",
        span: Span { start: 16, end: 17 },
    },
    Case {
        name: "y band",
        source: "xychart\ny-axis [a, b]\n",
        code: "xychart/unexpected-token",
        message: Y_BAND,
        span: Span { start: 15, end: 16 },
    },
    Case {
        name: "unknown",
        source: "xychart\nfoo bar\nbar [1]\n",
        code: "xychart/unknown-statement",
        message: "unknown statement foo",
        span: Span { start: 8, end: 15 },
    },
    Case {
        name: "open string",
        source: "xychart\ntitle \"abc\n",
        code: "xychart/unterminated",
        message: "unterminated \"",
        span: Span { start: 14, end: 19 },
    },
    Case {
        name: "open list",
        source: "xychart\nbar [1, 2",
        code: "xychart/unterminated",
        message: "unterminated [",
        span: Span { start: 12, end: 17 },
    },
    Case {
        name: "open description",
        source: "xychart\naccDescr {\nnever",
        code: "xychart/unterminated",
        message: "unterminated {",
        span: Span { start: 17, end: 24 },
    },
];

#[test]
fn diagnostics_carry_message_and_span() -> Check {
    for case in &CASES {
        let parsed = parse(case.source, &[]);
        let first = parsed.diagnostics.first().ok_or(case.name)?;
        assert_eq!(first.code, case.code, "{}", case.name);
        assert_eq!(first.span, case.span, "{}", case.name);
        assert_eq!(first.message, case.message, "{}", case.name);
    }
    Ok(())
}

#[test]
fn recovery_continues_after_an_unexpected_token() -> Check {
    let parsed = parse("xychart\nbar [1, ]\nline [2]\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.document.document.statements.len(), 1);
    assert!(plot_at(&parsed.document, 0)?.line);
    Ok(())
}
