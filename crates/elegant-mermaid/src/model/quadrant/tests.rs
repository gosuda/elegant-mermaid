use std::path::{Path, PathBuf};

use super::{Model, NO_RADIUS, resolve};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;
use crate::syntax::quadrant::parse;

type Check = Result<(), String>;

fn resolved(source: &str) -> Result<(Model, Vec<Diagnostic>), String> {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    if !parsed.diagnostics.is_empty() {
        return Err(format!("parser diagnostics for {source:?}"));
    }
    Ok(resolve(source, &parsed.document))
}

fn model(source: &str) -> Result<Model, String> {
    let (model, diagnostics) = resolved(source)?;
    if diagnostics.is_empty() {
        Ok(model)
    } else {
        Err(format!("resolver diagnostics for {source:?}"))
    }
}

fn point(model: &Model, at: usize) -> Result<&super::Point, String> {
    model.points.get(at).ok_or_else(|| format!("no point {at}"))
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
fn corpus_resolves_without_diagnostics() -> Check {
    let files = corpus_files().map_err(|e| e.to_string())?;
    assert!(!files.is_empty());
    for path in files {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        let (_, diagnostics) = resolved(&source)?;
        assert!(diagnostics.is_empty(), "{}", path.display());
    }
    Ok(())
}

#[test]
fn axis_texts_fill_low_then_high() -> Check {
    let m = model("quadrantChart\nx-axis Low Reach --> High Reach\ny-axis Low --> High\n")?;
    assert_eq!(
        (&m.x_left[..], &m.x_right[..], &m.y_bottom[..], &m.y_top[..]),
        ("Low Reach", "High Reach", "Low", "High")
    );
    Ok(())
}

#[test]
fn trailing_delimiter_appends_an_arrow_and_keeps_the_other_field() -> Check {
    let m = model("quadrantChart\nx-axis A --> B\nx-axis Left -->\ny-axis Solo\n")?;
    assert_eq!(m.x_left, "Left \u{27f6}");
    assert_eq!(m.x_right, "B");
    assert_eq!(m.y_bottom, "Solo");
    assert_eq!(m.y_top, "");
    Ok(())
}

#[test]
fn quadrant_texts_follow_their_number() -> Check {
    let m = model("quadrantChart\nquadrant-3 Third\nquadrant-1  First  \nquadrant-1 \"Again\"\n")?;
    assert_eq!(m.quadrants, ["Again", "", "Third", ""].map(String::from));
    Ok(())
}

#[test]
fn coordinates_are_thousandths() -> Check {
    let m =
        model("quadrantChart\nA: [0.3, 0.6]\nB: [1, 0]\nC: [0.12345, 0.9999]\nD: [0,5, 0x7]\n")?;
    let got: Vec<(i64, i64)> = m.points.iter().map(|p| (p.x, p.y)).collect();
    assert_eq!(got, [(300, 600), (1000, 0), (123, 1000), (500, 700)]);
    Ok(())
}

#[test]
fn points_keep_declaration_order_and_duplicates() -> Check {
    let m = model("quadrantChart\nA: [0.1, 0.1]\nA: [0.2, 0.2]\nB:::c1: [0.3, 0.3]\n")?;
    assert_eq!(m.points.len(), 3);
    assert_eq!(point(&m, 1)?.x, 200);
    assert_eq!(point(&m, 2)?.class, "c1");
    Ok(())
}

#[test]
fn inline_styles_override_class_styles_and_late_classes_apply() -> Check {
    let m = model(
        "quadrantChart\nA:::hot: [0.1, 0.1] radius: 3\nB:::hot: [0.2, 0.2]\nC:::none: [0.3, 0.3]\nclassDef hot color: #abc, radius: 20, stroke-width: 4px\n",
    )?;
    let (a, b, c) = (point(&m, 0)?, point(&m, 1)?, point(&m, 2)?);
    assert_eq!(
        (a.radius, a.color.as_str(), a.stroke_width.as_str()),
        (3, "#abc", "4px")
    );
    assert_eq!(b.radius, 20);
    assert_eq!((c.radius, c.color.as_str()), (NO_RADIUS, ""));
    Ok(())
}

#[test]
fn later_class_definition_replaces_the_whole_earlier_one() -> Check {
    let m = model(
        "quadrantChart\nclassDef k radius: 9, color: #fff\nclassDef k stroke-color: #000000\nA:::k: [0.1, 0.1]\n",
    )?;
    let first = point(&m, 0)?;
    assert_eq!((first.radius, first.color.as_str()), (NO_RADIUS, ""));
    assert_eq!(first.stroke_color, "#000000");
    Ok(())
}

#[test]
fn repeated_key_takes_the_last_value() -> Check {
    let m = model("quadrantChart\nA: [0.1, 0.1] radius: 1, radius: 2\n")?;
    assert_eq!(point(&m, 0)?.radius, 2);
    Ok(())
}

#[test]
fn style_diagnostics() -> Check {
    let cases: [(&str, &str, &str, &str, usize, usize); 7] = [
        (
            "radius word",
            "radius: big",
            "quadrant/invalid-radius",
            "value for radius big is invalid, please use a valid number",
            8,
            11,
        ),
        (
            "radius missing",
            "radius",
            "quadrant/invalid-radius",
            "value for radius undefined is invalid, please use a valid number",
            6,
            6,
        ),
        (
            "radius empty",
            "radius:",
            "quadrant/invalid-radius",
            "value for radius  is invalid, please use a valid number",
            7,
            7,
        ),
        (
            "color",
            "color: #12",
            "quadrant/invalid-color",
            "value for color #12 is invalid, please use a valid hex code",
            7,
            10,
        ),
        (
            "stroke color",
            "stroke-color : red",
            "quadrant/invalid-stroke-color",
            "value for stroke-color red is invalid, please use a valid hex code",
            15,
            18,
        ),
        (
            "stroke width",
            "stroke-width: 3",
            "quadrant/invalid-stroke-width",
            "value for stroke-width 3 is invalid, please use a valid number of pixels (eg. 10px)",
            14,
            15,
        ),
        (
            "unknown key",
            "Radius: 3",
            "quadrant/unsupported-style",
            "style named Radius is not supported.",
            0,
            6,
        ),
    ];
    let prefix = "quadrantChart\nA: [0.1, 0.1] ";
    for (name, style, code, message, start, end) in cases {
        let (_, diagnostics) = resolved(&format!("{prefix}{style}\n"))?;
        assert_eq!(diagnostics.len(), 1, "{name}");
        let first = diagnostics.first().ok_or("no diagnostic")?;
        assert_eq!(first.code, code, "{name}");
        assert_eq!(first.message, message, "{name}");
        assert_eq!(
            first.span,
            Span {
                start: prefix.len() + start,
                end: prefix.len() + end
            },
            "{name}"
        );
    }
    Ok(())
}

#[test]
fn class_def_styles_are_validated_too() -> Check {
    let (_, diagnostics) = resolved("quadrantChart\nclassDef k radius: x, size: 1\n")?;
    let codes: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
    assert_eq!(
        codes,
        ["quadrant/invalid-radius", "quadrant/unsupported-style"]
    );
    Ok(())
}

#[test]
fn titles_and_accessibility_are_trimmed_and_replaced() -> Check {
    let m = model(
        "quadrantChart\ntitle   First  \ntitle Second\naccTitle:  T1 \naccDescr: D1\naccDescr {\n D2 \n}\n",
    )?;
    assert_eq!(
        (&m.title[..], &m.acc_title[..], &m.acc_descr[..]),
        ("Second", "T1", "D2")
    );
    Ok(())
}

#[test]
fn frontmatter_title_is_overridden_by_a_statement() -> Check {
    assert_eq!(
        model("---\ntitle: From front\n---\nquadrantChart\n")?.title,
        "From front"
    );
    assert_eq!(
        model("---\ntitle: From front\n---\nquadrantChart\ntitle Later\n")?.title,
        "Later"
    );
    Ok(())
}

#[test]
fn honoured_config_keys_are_kept_sorted_and_range_checked() -> Check {
    let source = "---\nconfig:\n  quadrantChart:\n    chartWidth: 900\n    chartHeight: 0\n    titleFontSize: 30\n    unknownKey: 3\n    pointRadius: 7\n    quadrantPadding: 2.5\n    xAxisPosition: bottom\n---\n%%{init: {\"quadrantChart\": {\"chartWidth\": 400, \"titlePadding\": 3}}}%%\nquadrantChart\n";
    let m = model(source)?;
    let keys: Vec<&str> = m.config.keys().map(String::as_str).collect();
    assert_eq!(
        keys,
        ["chartWidth", "pointRadius", "titleFontSize", "titlePadding"]
    );
    assert_eq!(m.config.get("chartWidth"), Some(&400));
    Ok(())
}

#[test]
fn entities_decode_in_labels() -> Check {
    let m = model("quadrantChart\ntitle a #35; b #amp; c\nquadrant-1 \"x #bogus; y #62; z\"\n")?;
    assert_eq!(m.title, "a # b & c");
    assert_eq!(
        m.quadrants.first().map(String::as_str),
        Some("x #bogus; y > z")
    );
    Ok(())
}
