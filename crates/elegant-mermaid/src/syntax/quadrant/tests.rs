use std::path::{Path, PathBuf};

use super::ast::{
    AxisDetails, ClassDefStatement, Points, QuadrantDetails, Start, StatementKind, Title,
};
use super::parse;
use crate::diag::Diagnostic;
use crate::source::Span;

type Check = Result<(), String>;

fn parsed(source: &str) -> (Start<'_>, Vec<Diagnostic>) {
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    let result = parse(source, &removed);
    (result.document, result.diagnostics)
}

fn clean(source: &str) -> Result<Start<'_>, String> {
    let (start, diagnostics) = parsed(source);
    if diagnostics.is_empty() {
        Ok(start)
    } else {
        Err(format!("unexpected diagnostics for {source:?}"))
    }
}

fn statements<'a, 'b>(start: &'b Start<'a>) -> Vec<&'b StatementKind<'a>> {
    start
        .document
        .lines
        .iter()
        .filter_map(|line| line.statement.kind.as_ref())
        .collect()
}

fn title_at<'b>(kinds: &[&'b StatementKind<'_>], at: usize) -> Result<&'b Title<'b>, String> {
    match kinds.get(at) {
        Some(StatementKind::Title(title)) => Ok(title),
        _ => Err(format!("statement {at} is not a title")),
    }
}

fn axis_at<'b, 'a>(
    kinds: &[&'b StatementKind<'a>],
    at: usize,
) -> Result<&'b AxisDetails<'a>, String> {
    match kinds.get(at) {
        Some(StatementKind::AxisDetails(axis)) => Ok(axis),
        _ => Err(format!("statement {at} is not an axis")),
    }
}

fn quadrant_at<'b>(
    kinds: &[&'b StatementKind<'_>],
    at: usize,
) -> Result<&'b QuadrantDetails, String> {
    match kinds.get(at) {
        Some(StatementKind::QuadrantDetails(details)) => Ok(details),
        _ => Err(format!("statement {at} is not a quadrant text")),
    }
}

fn points_at<'b, 'a>(kinds: &[&'b StatementKind<'a>], at: usize) -> Result<&'b Points<'a>, String> {
    match kinds.get(at) {
        Some(StatementKind::Points(points)) => Ok(points),
        _ => Err(format!("statement {at} is not a point")),
    }
}

fn corpus_files() -> Result<Vec<PathBuf>, std::io::Error> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/quadrant");
    let mut out = Vec::new();
    for source in std::fs::read_dir(root)? {
        for file in std::fs::read_dir(source?.path())? {
            out.push(file?.path());
        }
    }
    out.sort();
    Ok(out)
}

#[test]
fn corpus_parses_without_diagnostics() -> Check {
    let files = corpus_files().map_err(|e| e.to_string())?;
    assert!(!files.is_empty());
    for path in files {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        let (_, diagnostics) = parsed(&source);
        assert!(diagnostics.is_empty(), "{}", path.display());
    }
    Ok(())
}

const CHART: &str = "quadrantChart\n  title Reach and engagement\n  x-axis Low Reach --> High Reach\n  y-axis Low --> High\n  quadrant-1 We should expand\n  quadrant-4 Re-evaluate\n  Campaign A: [0.3, 0.6]\n  Campaign B:::hot: [0.45, 0.23] radius: 20, color: #ff0000\n  classDef hot color: #908342, radius : 10\n";

#[test]
fn chart_header_title_and_axes() -> Check {
    let start = clean(CHART)?;
    assert_eq!(start.header.kind, "QUADRANT");
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 8);
    assert_eq!(title_at(&kinds, 0)?.value.text, " Reach and engagement");
    let x = axis_at(&kinds, 1)?;
    assert!(!x.y);
    assert_eq!(x.first.value, "Low Reach");
    assert_eq!(
        x.second.as_ref().map(|t| t.value.as_str()),
        Some("High Reach")
    );
    assert!(x.delimiter.is_some());
    assert!(axis_at(&kinds, 2)?.y);
    Ok(())
}

#[test]
fn chart_quadrant_texts_and_points() -> Check {
    let start = clean(CHART)?;
    let kinds = statements(&start);
    let q1 = quadrant_at(&kinds, 3)?;
    assert_eq!((q1.number, q1.text.value.as_str()), (1, "We should expand"));
    assert_eq!(quadrant_at(&kinds, 4)?.number, 4);
    let a = points_at(&kinds, 5)?;
    assert_eq!(a.text.value, "Campaign A");
    assert!(a.class.is_none() && a.styles.is_none());
    assert_eq!((a.point_x.text, a.point_y.text), ("0.3", "0.6"));
    Ok(())
}

#[test]
fn chart_styles_and_class_definition() -> Check {
    let start = clean(CHART)?;
    let kinds = statements(&start);
    let b = points_at(&kinds, 6)?;
    assert_eq!(b.class.as_ref().map(|t| t.text), Some("hot"));
    let styles = b.styles.as_ref().ok_or("no styles")?;
    let texts: Vec<&str> = styles.styles.iter().map(|s| s.text.as_str()).collect();
    assert_eq!(texts, ["radius: 20", " color: #ff0000"]);
    let Some(StatementKind::ClassDef(ClassDefStatement { name, styles, .. })) = kinds.get(7) else {
        return Err("not a classDef".into());
    };
    assert_eq!(name.text, "hot");
    assert_eq!(styles.styles.len(), 2);
    Ok(())
}

#[test]
fn header_alone_is_valid() -> Check {
    for source in [
        "quadrantChart",
        "quadrantChart\n",
        "  \n; quadrantChart  \n\n",
        "QUADRANTCHART\n",
    ] {
        let start = clean(source)?;
        assert!(statements(&start).is_empty(), "{source:?}");
    }
    Ok(())
}

#[test]
fn axis_delimiter_variants() -> Check {
    let start = clean("quadrantChart\nx-axis Left -->\ny-axis Only\nx-axis Wide ---> Right\n")?;
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 3);
    let trailing = axis_at(&kinds, 0)?;
    assert!(trailing.delimiter.is_some() && trailing.second.is_none());
    assert!(axis_at(&kinds, 1)?.delimiter.is_none());
    assert_eq!(
        axis_at(&kinds, 2)?
            .second
            .as_ref()
            .map(|t| t.value.as_str()),
        Some("Right")
    );
    Ok(())
}

#[test]
fn quoted_and_markdown_text_keep_their_kind() -> Check {
    let start =
        clean("quadrantChart\nquadrant-2 \"(plain) text\"\nquadrant-3 \"`*bold*\ntwo`\"\n")?;
    let kinds = statements(&start);
    let plain = &quadrant_at(&kinds, 0)?.text;
    assert!(!plain.markdown);
    assert_eq!(plain.value, "(plain) text");
    assert_eq!(plain.span.end - plain.span.start, plain.value.len() + 2);
    assert_eq!(plain.content.end - plain.content.start, plain.value.len());
    let markdown = &quadrant_at(&kinds, 1)?.text;
    assert!(markdown.markdown);
    assert_eq!(markdown.value, "*bold*\ntwo");
    Ok(())
}

#[test]
fn coordinate_wildcard_accepts_any_character_after_zero() -> Check {
    let start = clean("quadrantChart\nA: [0,5, 0x7]\nB: [1, 0]\n")?;
    let kinds = statements(&start);
    assert_eq!(points_at(&kinds, 0)?.point_x.text, "0,5");
    assert_eq!(points_at(&kinds, 0)?.point_y.text, "0x7");
    assert_eq!(points_at(&kinds, 1)?.point_x.text, "1");
    Ok(())
}

#[test]
fn keywords_are_case_insensitive() -> Check {
    let start = clean(
        "quadrantchart\nTITLE Up\nX-AXIS A --> B\nQuadrant-3 Z\nCLASSDEF c radius: 1\nACCTITLE: t\nAccDescr: d\n",
    )?;
    assert_eq!(statements(&start).len(), 6);
    Ok(())
}

#[test]
fn semicolon_and_comments_separate_statements() -> Check {
    let start = clean(
        "quadrantChart\ntitle T; x-axis kept\nx-axis A; y-axis B\n%% comment\nquadrant-1 Q %% trailing\n",
    )?;
    assert_eq!(statements(&start).len(), 4);
    Ok(())
}

#[test]
fn accessibility_statements() -> Check {
    let start =
        clean("quadrantChart\naccTitle: A title\naccDescr: A line\naccDescr {\nmulti\nline\n}\n")?;
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 3);
    assert!(matches!(kinds[0], StatementKind::Accessibility(a) if a.title));
    assert!(matches!(kinds[2], StatementKind::Accessibility(a) if a.multiline));
    Ok(())
}

#[test]
fn title_at_end_of_input_has_an_empty_value() -> Check {
    let start = clean("quadrantChart\ntitle")?;
    assert_eq!(title_at(&statements(&start), 0)?.value.text, "");
    Ok(())
}

#[test]
fn line_spans_include_the_terminator_and_statements_do_not() -> Check {
    let source = "quadrantChart\n title Hello\n\nx-axis A\n";
    let start = clean(source)?;
    let line = start.document.lines.get(1).ok_or("missing line")?;
    assert_eq!(
        source.get(line.statement.span.start + 1..line.statement.span.end),
        Some("title Hello")
    );
    assert_eq!(
        source.get(line.eol.span.start..line.eol.span.end),
        Some("\n\n")
    );
    assert_eq!(line.eol.span.end, line.span.end);
    Ok(())
}

#[test]
fn diagnostics_have_codes_spans_and_messages() {
    let cases: [(&str, &str, &str, &str, usize, usize); 12] = [
        (
            "missing point",
            "quadrantChart\nCampaign A\n",
            "quadrant/unexpected-token",
            "unexpected \n, expected one of: ALPHA, AMP, BRKT, COMMA, DOT, EQUALS, MINUS, MULT, NUM, PLUS, PUNCTUATION, SPACE, UNDERSCORE, UNICODE_TEXT, class_name, point_start",
            24,
            25,
        ),
        (
            "missing coordinate",
            "quadrantChart\nA: [\n",
            "quadrant/unterminated",
            "unterminated [",
            17,
            19,
        ),
        (
            "open point",
            "quadrantChart\nA: [0.1, 0.2",
            "quadrant/unterminated",
            "unterminated [",
            17,
            26,
        ),
        (
            "unclosed point bracket",
            "quadrantChart\nA: [0.1, 0.2\nB: [0.3, 0.4]\n",
            "quadrant/unexpected-token",
            "unexpected end of line, expected one of: EOF, NEWLINE, SEMI",
            26,
            26,
        ),
        (
            "open class name",
            "quadrantChart\nA:::",
            "quadrant/unterminated",
            "unterminated :::",
            15,
            18,
        ),
        (
            "trailing comma style",
            "quadrantChart\nA: [0.1, 0.2] radius: 3,\n",
            "quadrant/unexpected-token",
            "unexpected \n, expected one of: ALPHA, BRKT, COLON, MINUS, NUM, SPACE",
            38,
            39,
        ),
        (
            "unknown",
            "quadrantChart\n- foo\nx-axis A\n",
            "quadrant/unknown-statement",
            "unknown statement -",
            14,
            19,
        ),
        (
            "punctuation",
            "quadrantChart\nquadrant-1 (x)\n",
            "quadrant/unexpected-token",
            "unexpected (, expected one of: ALPHA, AMP, BRKT, COMMA, DOT, EQUALS, MD_STR, MULT, NUM, PLUS, PUNCTUATION, STR, UNDERSCORE, UNICODE_TEXT",
            25,
            26,
        ),
        (
            "open string",
            "quadrantChart\nx-axis \"abc\n",
            "quadrant/unterminated",
            "unterminated \"",
            21,
            26,
        ),
        (
            "open markdown",
            "quadrantChart\nx-axis \"`abc\n",
            "quadrant/unterminated",
            "unterminated \"`",
            21,
            27,
        ),
        (
            "open description",
            "quadrantChart\naccDescr {\nnever",
            "quadrant/unterminated",
            "unterminated {",
            23,
            30,
        ),
        (
            "two headers",
            "quadrantChart\nquadrantChart\n",
            "quadrant/unknown-statement",
            "unknown statement quadrantChart",
            14,
            27,
        ),
    ];
    for (name, source, code, message, start, end) in cases {
        let (_, diagnostics) = parsed(source);
        let first = diagnostics.first();
        assert_eq!(first.map(|d| d.code), Some(code), "{name}");
        assert_eq!(first.map(|d| d.span), Some(Span { start, end }), "{name}");
        assert_eq!(first.map(|d| d.message.as_str()), Some(message), "{name}");
    }
}

#[test]
fn recovery_continues_after_an_unexpected_token() -> Check {
    let (start, diagnostics) = parsed("quadrantChart\nA: [0.1\ntitle Kept\n");
    assert_eq!(diagnostics.len(), 1);
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 1);
    assert_eq!(title_at(&kinds, 0)?.value.text, " Kept");
    Ok(())
}

#[test]
fn lexical_error_inside_a_point_resynchronises() {
    let (start, diagnostics) = parsed("quadrantChart\nA: [1.0, 0.2]\nB: [0.2, 0.3]\n");
    assert_eq!(
        diagnostics.first().map(|d| d.code),
        Some("quadrant/unexpected-token")
    );
    assert!(!statements(&start).is_empty());
}

#[test]
fn quoted_text_takes_a_tail_of_tokens() -> Check {
    let start = clean("quadrantChart\nx-axis \"Low\" -- more --> \"High\"\n")?;
    let kinds = statements(&start);
    let axis = axis_at(&kinds, 0)?;
    assert_eq!(axis.first.value, "Low -- more");
    assert_eq!(axis.second.as_ref().map(|t| t.value.as_str()), Some("High"));
    Ok(())
}

#[test]
fn entities_are_opaque_text() -> Check {
    let start = clean("quadrantChart\nquadrant-1 Fish #amp; Chips #35; x\n")?;
    assert_eq!(
        quadrant_at(&statements(&start), 0)?.text.value,
        "Fish #amp; Chips #35; x"
    );
    Ok(())
}

#[test]
fn bare_hash_and_semicolon_still_split() -> Check {
    let start = clean("quadrantChart\nquadrant-1 a #b ; quadrant-2 c\n")?;
    assert_eq!(statements(&start).len(), 2);
    Ok(())
}

#[test]
fn trailing_semicolon_of_a_colour_line_is_dropped() -> Check {
    let start = clean("quadrantChart\nclassDef k color:#fff;\nA:::k: [0.1, 0.2]\n")?;
    assert_eq!(statements(&start).len(), 2);
    let (_, diagnostics) = parsed("quadrantChart\nclassDef k color: #fff;\n");
    assert!(!diagnostics.is_empty());
    Ok(())
}

#[test]
fn carriage_return_ends_line_values() -> Check {
    let start = clean("quadrantChart\rtitle One\rquadrant-1 Q\r\ntitle Two\r\n")?;
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 3);
    assert_eq!(title_at(&kinds, 0)?.value.text, " One");
    assert_eq!(title_at(&kinds, 2)?.value.text, " Two");
    Ok(())
}

#[test]
fn accessibility_value_needs_text_before_the_end() {
    for source in ["quadrantChart\naccTitle:", "quadrantChart\naccDescr: \n"] {
        let (_, diagnostics) = parsed(source);
        assert_eq!(diagnostics.len(), 1, "{source:?}");
        assert_eq!(
            diagnostics.first().map(|d| d.code),
            Some("quadrant/unexpected-token")
        );
    }
}
