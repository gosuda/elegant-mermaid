//! Focused styled-measurement semantics: mixed weights, style through wrap,
//! breaks and escapes, literal unsupported markup, opaque math, and the
//! whole-string ceiling oracle.

use super::super::width::scaled_width;
use crate::geom::GeomError;
use crate::math::syntax as math_syntax;
use crate::math::vector;
use crate::measure::{Metric, Role, Weight, advance_sum, styled_lines, styled_width, upem, wrap};

type RenderedRun = (String, bool, bool);
type MeasuredLine = (String, i32, Vec<RenderedRun>);

fn vector(text: &str, weight: Weight) -> Result<i32, GeomError> {
    let units = advance_sum(text, weight)?;
    i32::try_from(scaled_width(units, 14, weight)?).map_err(|_| GeomError::Overflow)
}

fn label_metric() -> Metric {
    Metric::for_role(Role::Label)
}

fn line_shapes(lines: &[crate::measure::StyledLine<'_>]) -> Vec<MeasuredLine> {
    lines
        .iter()
        .map(|line| {
            (
                line.text.clone(),
                line.width,
                line.runs
                    .iter()
                    .map(|run| (run.text.to_string(), run.bold, run.italic))
                    .collect(),
            )
        })
        .collect()
}

fn oracle_width(runs: &[(&str, Weight)]) -> Result<i32, GeomError> {
    assert_eq!(
        upem(Weight::Regular),
        upem(Weight::Semibold),
        "oracle assumes equal upem; production rounds once without it"
    );
    let mut total = 0i64;
    for (text, weight) in runs {
        total += advance_sum(text, *weight)?;
    }
    i32::try_from(scaled_width(total, 14, Weight::Regular)?).map_err(|_| GeomError::Overflow)
}

#[test]
fn mixed_weight_uses_style_advances() -> Result<(), GeomError> {
    let metric = label_metric();
    let width = styled_width("*i* x", metric)?;
    let expected = oracle_width(&[("i", Weight::Regular), (" x", Weight::Semibold)])?;
    assert_eq!(width, expected);
    let raw = vector("*i* x", Weight::Semibold)?;
    assert_ne!(width, raw, "delimiters must not be measured");
    Ok(())
}

#[test]
fn mixed_weights_round_once_for_the_whole_line() -> Result<(), GeomError> {
    let metric = label_metric();
    assert_eq!(
        upem(Weight::Regular),
        upem(Weight::Semibold),
        "witness assumes equal upem; production stays one-ceiling without it"
    );
    let width = styled_width("*A* **A**", metric)?;
    let total = advance_sum("A", Weight::Regular)? + advance_sum(" A", Weight::Semibold)?;
    let expected = i32::try_from(scaled_width(total, 14, Weight::Regular)?)
        .map_err(|_| GeomError::Overflow)?;
    assert_eq!(width, expected);
    let by_group = scaled_width(advance_sum("A", Weight::Regular)?, 14, Weight::Regular)?
        + scaled_width(advance_sum(" A", Weight::Semibold)?, 14, Weight::Semibold)?;
    assert_ne!(
        i64::from(expected),
        by_group,
        "witness must distinguish whole-line rounding from group rounding"
    );
    Ok(())
}

#[test]
fn equal_weight_groups_share_one_ceiling() -> Result<(), GeomError> {
    let metric = label_metric();
    assert_eq!(
        styled_width(r"a\*b", metric)?,
        vector("a*b", Weight::Semibold)?
    );
    assert_eq!(
        styled_width("**a** b", metric)?,
        vector("a b", Weight::Semibold)?
    );
    let width = styled_width("**b** *i*", metric)?;
    assert_eq!(
        width,
        oracle_width(&[("b ", Weight::Semibold), ("i", Weight::Regular)])?
    );
    Ok(())
}

#[test]
fn plain_labels_match_wrap_parity() -> Result<(), GeomError> {
    let cases = [
        ("", 40),
        (" ", 40),
        ("a b", 40),
        ("a<br/>b", 40),
        ("a<br/><br/>b", 40),
        ("alpha beta gamma", 8),
        ("alpha beta gamma", 400),
        ("日本語 テキスト", 6),
    ];
    for metric in [label_metric(), Metric::Cell] {
        for (text, target) in cases {
            let plain = wrap(text, target, metric)?;
            let styled = styled_lines(text, target, metric)?;
            let plain: Vec<_> = plain.iter().map(|l| (l.text, l.width)).collect();
            let styled: Vec<_> = styled.iter().map(|l| (l.text.as_str(), l.width)).collect();
            assert_eq!(styled, plain, "plain parity for {text:?} at {target}");
        }
    }
    Ok(())
}

#[test]
fn style_survives_wrap() -> Result<(), GeomError> {
    let lines = styled_lines("**alpha beta gamma**", 6, Metric::Cell)?;
    assert!(
        lines.len() >= 3,
        "long bold label must wrap: {:?}",
        line_shapes(&lines)
    );
    for line in &lines {
        assert!(
            !line.runs.is_empty(),
            "wrapped bold line must retain its styled runs: {line:?}"
        );
        for run in &line.runs {
            assert!(run.bold, "run lost bold: {:?}", run);
            assert!(!run.text.contains('*'), "delimiter leaked: {:?}", run);
        }
        let joined: String = line.runs.iter().map(|run| run.text).collect();
        assert_eq!(joined, line.text);
        let width: i32 = line.runs.iter().map(|run| run.width).sum();
        assert_eq!(width, line.width);
    }
    assert_eq!(
        lines
            .iter()
            .map(|l| l.text.as_str())
            .collect::<Vec<_>>()
            .join(" "),
        "alpha beta gamma"
    );
    Ok(())
}

#[test]
fn br_and_escape_edges() -> Result<(), GeomError> {
    let lines = styled_lines("a**b**<br>c *d*", i32::MAX, label_metric())?;
    let first = oracle_width(&[("ab", Weight::Semibold)])?;
    let second = oracle_width(&[("c ", Weight::Semibold), ("d", Weight::Regular)])?;
    assert_eq!(
        line_shapes(&lines),
        vec![
            (
                "ab".into(),
                first,
                vec![
                    ("a".to_string(), false, false),
                    ("b".to_string(), true, false)
                ],
            ),
            (
                "c d".into(),
                second,
                vec![
                    ("c ".to_string(), false, false),
                    ("d".to_string(), false, true)
                ],
            ),
        ],
    );
    let escaped = styled_lines(r"a\*b \_c", i32::MAX, label_metric())?;
    assert_eq!(escaped.len(), 1);
    assert_eq!(escaped[0].text, "a*b _c");
    assert_eq!(
        escaped[0].width,
        oracle_width(&[("a*b _c", Weight::Semibold)])?
    );
    Ok(())
}

#[test]
fn unsupported_markup_stays_literal() -> Result<(), GeomError> {
    let metric = label_metric();
    for text in ["<b>x</b> &amp; `code`", "**unclosed", "snake_case _tail"] {
        let lines = styled_lines(text, i32::MAX, metric)?;
        let rendered = lines
            .iter()
            .map(|l| l.text.as_str())
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(rendered, text, "literal form changed: {text:?}");
    }
    let forced = styled_lines("<BR />after", 4000, metric)?;
    assert_eq!(line_shapes(&forced).len(), 2);
    assert_eq!(forced[0].text, "");
    assert_eq!(forced[1].text, "after");
    Ok(())
}

#[test]
fn math_stays_opaque_literal() -> Result<(), GeomError> {
    let metric = label_metric();
    let text = "**b** $$\\frac{a}{b}$$";
    let lines = styled_lines(text, i32::MAX, metric)?;
    assert_eq!(lines.len(), 1);
    let rendered = r"b $$\frac{a}{b}$$";
    let styled_chars = lines[0]
        .runs
        .iter()
        .flat_map(|run| run.text.chars().map(move |c| (c, run.bold, run.italic)));
    let expected = rendered
        .chars()
        .enumerate()
        .map(|(at, c)| (c, at == 0, false));
    assert!(
        styled_chars.eq(expected),
        "opaque math must retain text and styles"
    );
    let formula = vector::layout(&math_syntax::parse(r"\frac{a}{b}").expression, 14)?;
    let expected_width = oracle_width(&[("b ", Weight::Semibold)])? + formula.w;
    assert_eq!(lines[0].width, expected_width);
    Ok(())
}

#[test]
fn configured_styled_runs_use_the_same_font_factor_as_their_line() -> Result<(), GeomError> {
    for text in [
        "From $$x(t)$$ to $$y(t)$$",
        "**From** $$x$$ *to* $$y$$",
        "$$x(t)$$",
    ] {
        let base = styled_lines(text, i32::MAX, label_metric())?;
        let configured = styled_lines(text, i32::MAX, label_metric().with_font_family())?;
        assert_eq!(base.len(), 1, "{text}");
        assert_eq!(configured.len(), 1, "{text}");
        assert_eq!(
            configured[0].width,
            crate::measure::apply_font_family_factor(base[0].width)?,
            "{text}"
        );
        assert_eq!(base[0].runs.len(), configured[0].runs.len(), "{text}");
        for (before, after) in base[0].runs.iter().zip(&configured[0].runs) {
            assert_eq!(before.text, after.text);
            assert_eq!(
                before.math, after.math,
                "formula outlines use their own metrics"
            );
            let width = if before.math.is_some() {
                before.width
            } else {
                crate::measure::apply_font_family_factor(before.width)?
            };
            assert_eq!(after.width, width, "{text}: {}", before.text);
        }
    }
    Ok(())
}

#[test]
fn cell_profile_ignores_style() -> Result<(), GeomError> {
    let lines = styled_lines("**ab** cd", 400, Metric::Cell)?;
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text, "ab cd");
    assert_eq!(lines[0].width, crate::measure::cell_width("ab cd")?);
    Ok(())
}

#[test]
fn source_slices_cover_rendered_text() -> Result<(), GeomError> {
    for text in ["a b", "alpha beta", "日本語 テキスト"] {
        for line in styled_lines(text, 6, Metric::Cell)? {
            assert_eq!(&text[line.source.start..line.source.end], line.text);
        }
    }
    let text = "**alpha beta** c";
    let lines = styled_lines(text, i32::MAX, label_metric())?;
    assert_eq!(lines.len(), 1);
    assert_eq!(
        &text[lines[0].source.start..lines[0].source.end],
        "alpha beta** c"
    );
    Ok(())
}

#[test]
fn clusters_survive_style_boundaries() -> Result<(), GeomError> {
    let zwj_emoji = "\u{1f469}\u{200d}\u{1f469}";
    let styled = styled_lines("**\u{1f469}**\u{200d}\u{1f469}", 1, Metric::Cell)?;
    let plain = styled_lines(zwj_emoji, 1, Metric::Cell)?;
    assert_eq!(styled.len(), 1);
    assert_eq!(plain.len(), 1);
    let joined: String = styled[0].runs.iter().map(|run| run.text).collect();
    assert_eq!(joined, zwj_emoji);
    let flattened: Vec<(char, bool, bool)> = styled[0]
        .runs
        .iter()
        .flat_map(|run| {
            let style = (run.bold, run.italic);
            run.text.chars().map(move |c| (c, style.0, style.1))
        })
        .collect();
    assert_eq!(
        flattened,
        vec![
            ('\u{1f469}', true, false),
            ('\u{200d}', false, false),
            ('\u{1f469}', false, false),
        ],
        "styling must follow its own source span inside one atomic cluster"
    );
    assert_eq!(styled[0].width, plain[0].width);
    assert_eq!(styled[0].width, crate::measure::cell_width(zwj_emoji)?);
    let marked = styled_lines("**a**\u{0301}", 400, Metric::Cell)?;
    assert_eq!(marked.len(), 1);
    let marked_joined: String = marked[0].runs.iter().map(|run| run.text).collect();
    assert_eq!(marked_joined, "a\u{0301}");
    let marked_flat: Vec<(char, bool, bool)> = marked[0]
        .runs
        .iter()
        .flat_map(|run| {
            let style = (run.bold, run.italic);
            run.text.chars().map(move |c| (c, style.0, style.1))
        })
        .collect();
    assert_eq!(
        marked_flat,
        vec![('a', true, false), ('\u{0301}', false, false)]
    );
    assert_eq!(marked[0].width, crate::measure::cell_width("a\u{0301}")?);
    Ok(())
}

#[test]
fn cell_controls_preserve_original_emphasis_boundaries() -> Result<(), GeomError> {
    for source in ["**a\nb**", "*a\rb*", "_a\r\nb_"] {
        let lines = styled_lines(source, i32::MAX, Metric::Cell)?;
        let expected: String = source
            .chars()
            .map(|c| if c.is_control() { '\u{fffd}' } else { c })
            .collect();
        assert_eq!(lines.len(), 1);
        assert_eq!(lines[0].text, expected);
        assert!(lines[0].runs.iter().all(|run| !run.bold && !run.italic));
        assert_eq!(
            lines[0].source,
            crate::source::Span {
                start: 0,
                end: source.len()
            }
        );
    }
    Ok(())
}

#[test]
fn cell_replacement_spans_cover_original_scalars() -> Result<(), GeomError> {
    let source = "**a\u{0085}\r\nb**";
    let lines = styled_lines(source, 1, Metric::Cell)?;
    let expected = [("\u{fffd}", 3, 5), ("\u{fffd}", 5, 6), ("\u{fffd}", 6, 7)];
    assert_eq!(
        lines
            .iter()
            .map(|line| line.text.as_str())
            .collect::<String>(),
        "**a\u{fffd}\u{fffd}\u{fffd}b**"
    );
    for line in &lines {
        assert!(line.source.end <= source.len());
        assert!(source.is_char_boundary(line.source.start));
        assert!(source.is_char_boundary(line.source.end));
    }
    for (text, start, end) in expected {
        let line = lines
            .iter()
            .find(|line| line.source.start == start)
            .ok_or(GeomError::Domain)?;
        assert_eq!(line.text, text);
        assert_eq!(line.source.end, end);
    }
    Ok(())
}

#[test]
fn sanitized_clusters_are_global_before_wrapping() -> Result<(), GeomError> {
    let source = "*\0*\u{0301}x";
    let lines = styled_lines(source, 1, Metric::Cell)?;
    assert_eq!(
        lines
            .iter()
            .map(|line| line.text.as_str())
            .collect::<Vec<_>>(),
        ["\u{fffd}\u{0301}", "x"]
    );
    assert_eq!(lines[0].width, 1);
    assert!(lines[0].runs[0].italic);
    assert!(!lines[0].runs[1].italic);
    assert_eq!(lines[0].source, crate::source::Span { start: 1, end: 5 });
    let vector = styled_lines(source, i32::MAX, label_metric())?;
    assert_eq!(vector[0].text, "\0\u{0301}x");
    Ok(())
}
