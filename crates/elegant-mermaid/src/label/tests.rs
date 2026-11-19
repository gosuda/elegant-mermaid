use super::{Segment, parse};
use crate::source::Span;

fn runs(source: &str) -> Vec<(String, bool, bool)> {
    parse(source)
        .lines
        .into_iter()
        .flat_map(|line| line.segments)
        .map(|segment| match segment {
            Segment::Text(run) => (run.text.to_owned(), run.bold, run.italic),
            Segment::Math(formula) => (format!("MATH:{}", formula.source), false, false),
        })
        .collect()
}

#[test]
fn emphasis_is_flat_and_closes_at_nearest_identical_delimiter() {
    assert_eq!(
        runs("**bold _literal_** *ital* _also_"),
        vec![
            ("bold _literal_".into(), true, false),
            (" ".into(), false, false),
            ("ital".into(), false, true),
            (" ".into(), false, false),
            ("also".into(), false, true),
        ],
        "inner emphasis markers must remain literal inside a styled run"
    );
    assert_eq!(
        runs("*a*b*c"),
        vec![("a".into(), false, true), ("b*c".into(), false, false)],
        "first matching star closes the opener; unmatched final star remains"
    );
    assert_eq!(
        runs("**open*"),
        vec![("**open*".into(), false, false)],
        "an unmatched bold opener is not reparsed as italic"
    );
}

#[test]
fn unicode_intraword_underscores_are_not_emphasis() {
    assert_eq!(
        runs("é_猫_９ _猫🙂_"),
        vec![
            ("é_猫_９ ".into(), false, false),
            ("猫🙂".into(), false, true),
        ],
        "letters and digits on both sides protect underscores across Unicode scripts"
    );
    for source in [
        "a_\u{0558}_b",
        "\u{0558}_a_b",
        "a_b_\u{0558}",
        "a_²_b",
        "a_Ⅻ_b",
        "a_\u{0345}_b",
        "a_Ⓐ_b",
    ] {
        assert_eq!(
            runs(source),
            vec![(source.into(), false, false)],
            "pinned Alphabetic and numeric scalars must protect underscores: {source}"
        );
    }
}

#[test]
fn escapes_keep_exact_provenance_without_copying_text() {
    let label = parse(r"é\*\_\\\$\a");
    let values: Vec<_> = label.lines[0]
        .segments
        .iter()
        .map(|segment| match segment {
            Segment::Text(run) => (run.text, run.span, run.bold, run.italic),
            Segment::Math(_) => unreachable!("escaped dollars cannot open math"),
        })
        .collect();
    assert_eq!(
        values,
        vec![
            ("é", Span { start: 0, end: 2 }, false, false),
            ("*", Span { start: 2, end: 4 }, false, false),
            ("_", Span { start: 4, end: 6 }, false, false),
            ("\\", Span { start: 6, end: 8 }, false, false),
            ("$", Span { start: 8, end: 10 }, false, false),
            (r"\a", Span { start: 10, end: 12 }, false, false),
        ],
        "each removed slash must remain recoverable from its content span"
    );
}

#[test]
fn accepted_break_tags_preserve_empty_lines_and_physical_newlines() {
    let label = parse("a<BR><br/><Br />b\r\nc\rd\ne<br>");
    let lines: Vec<Vec<&str>> = label
        .lines
        .iter()
        .map(|line| {
            line.segments
                .iter()
                .map(|segment| match segment {
                    Segment::Text(run) => run.text,
                    Segment::Math(_) => unreachable!("fixture contains no math"),
                })
                .collect()
        })
        .collect();
    assert_eq!(
        lines,
        vec![vec!["a"], vec![], vec![], vec!["b\r\nc\rd\ne"], vec![]],
        "br tags alone force wrapping lines, including empty leading/trailing parts"
    );
    assert_eq!(label.lines[0].break_span, Some(Span { start: 1, end: 5 }));
    assert_eq!(
        runs("*a<br>b*"),
        vec![("*a".into(), false, false), ("b*".into(), false, false)],
        "emphasis cannot cross a logical line break"
    );
    assert_eq!(
        runs("*a\nb*"),
        vec![("*a\nb*".into(), false, false)],
        "physical lines also bound emphasis"
    );
}

#[test]
fn unsupported_markup_and_entities_stay_literal() {
    let literal =
        "`code` [link](url) ![image](url) # heading - item <b>tag</b> &amp; #169; <br  />";
    assert_eq!(
        runs(literal),
        vec![(literal.into(), false, false)],
        "unsupported constructs and named/numeric entities are not interpreted or decoded"
    );
}

#[test]
fn quoted_adjacent_math_preserves_formula_and_absolute_byte_spans() {
    let label = parse("\"é$$x\\$+y$$tail$$z$$\"");
    let segments = &label.lines[0].segments;
    assert_eq!(
        segments[0],
        Segment::Text(super::Text {
            text: "\"é",
            bold: false,
            italic: false,
            span: Span { start: 0, end: 3 }
        })
    );
    assert_eq!(
        segments[1],
        Segment::Math(super::Math {
            source: r"x\$+y",
            span: Span { start: 3, end: 12 },
            formula_span: Span { start: 5, end: 10 },
        }),
        "TeX escape bytes must pass unchanged to the math parser"
    );
    assert_eq!(
        segments[2],
        Segment::Text(super::Text {
            text: "tail",
            bold: false,
            italic: false,
            span: Span { start: 12, end: 16 }
        })
    );
    assert_eq!(
        segments[3],
        Segment::Math(super::Math {
            source: "z",
            span: Span { start: 16, end: 21 },
            formula_span: Span { start: 18, end: 19 }
        })
    );
}

#[test]
fn unmatched_and_escaped_dollars_do_not_disappear() {
    assert_eq!(
        runs("$single $$unclosed"),
        vec![("$single $$unclosed".into(), false, false)]
    );
    assert_eq!(
        runs(r"\$$x"),
        vec![("$".into(), false, false), ("$x".into(), false, false)]
    );
    assert_eq!(
        runs("a$$$$b"),
        vec![
            ("a".into(), false, false),
            ("MATH:".into(), false, false),
            ("b".into(), false, false)
        ],
        "a closed empty formula is still a math segment"
    );
    assert_eq!(
        runs(r"*a\*b*"),
        vec![
            ("a".into(), false, true),
            ("*".into(), false, true),
            ("b".into(), false, true)
        ],
        "escaped delimiter must not close emphasis"
    );
}
