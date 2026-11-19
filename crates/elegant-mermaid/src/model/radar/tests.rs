use super::{Graticule, Model, resolve, thousandths};
use crate::diag::{Diagnostic, Severity};
use crate::scene::DumpValue;
use crate::syntax::preprocess::preprocess;
use crate::syntax::radar::parse;

type Check = Result<(), &'static str>;

fn resolved(text: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(text).removed;
    let parsed = parse(text, &removed);
    let (model, semantic) = resolve(text, &parsed.document);
    let mut all = parsed.diagnostics;
    all.extend(semantic);
    (model, all)
}

fn codes(diagnostics: &[Diagnostic]) -> Vec<&'static str> {
    diagnostics.iter().map(|d| d.code).collect()
}

fn error_count(diagnostics: &[Diagnostic]) -> usize {
    diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .count()
}

fn config_of(model: &Model) -> Vec<(&str, i64)> {
    model
        .config
        .iter()
        .map(|(key, value)| match value {
            DumpValue::Integer(n) => (key.as_str(), *n),
            _ => (key.as_str(), i64::MIN),
        })
        .collect()
}

const ACCEPTANCE: &[(&str, &str, bool)] = &[
    ("float", "radar-beta\n axis A, B\n curve c {1.5, 2}\n", true),
    (
        "max float",
        "radar-beta\n axis A, B\n curve c {1, 2}\n max 2.5\n",
        true,
    ),
    ("colon header", "radar-beta:\n axis A, B\n", true),
    ("colon sep", "radar-beta :\n axis A, B\n", true),
    ("header only", "radar-beta\n", true),
    ("no newline", "radar-beta", true),
    ("axis same line", "radar-beta axis A, B", true),
    (
        "two statements one line",
        "radar-beta\n axis A curve c {1,2}\n",
        true,
    ),
    ("semicolon", "radar-beta\n axis A; axis B\n", false),
    (
        "curve name true",
        "radar-beta\n axis A\n curve true {1}\n",
        false,
    ),
    (
        "curve name circle",
        "radar-beta\n axis A\n curve circle {1}\n",
        false,
    ),
    ("axis name 3d", "radar-beta\n axis 3d\n", false),
    (
        "axis name a-b",
        "radar-beta\n axis a-b, c_d\n curve x {1,2}\n",
        true,
    ),
    ("axis name dash end", "radar-beta\n axis a-\n", false),
    ("axis keyword name", "radar-beta\n axis axis\n", false),
    ("axis name max", "radar-beta\n axis max, min\n", false),
    ("trailing comma", "radar-beta\n axis A,\n", false),
    (
        "entry newline",
        "radar-beta\n axis A, B\n curve c {\n 1,\n 2\n }\n",
        true,
    ),
    (
        "entry newline before comma",
        "radar-beta\n axis A, B\n curve c {\n 1\n ,2\n }\n",
        false,
    ),
    ("mix", "radar-beta\n axis A, B\n curve c {A 1, 2}\n", false),
    ("mix2", "radar-beta\n axis A, B\n curve c {1, B 2}\n", false),
    (
        "detailed colon",
        "radar-beta\n axis A, B\n curve c {A: 1, B: 2}\n",
        true,
    ),
    ("empty entries", "radar-beta\n axis A\n curve c {}\n", false),
    (
        "trailing comma entries",
        "radar-beta\n axis A\n curve c {1,}\n",
        false,
    ),
    (
        "unknown axis ref",
        "radar-beta\n axis A\n curve c {Z: 1}\n",
        false,
    ),
    (
        "unknown extra axis ref",
        "radar-beta\n axis A\n curve c {A: 1, Z: 1}\n",
        true,
    ),
    (
        "curve before axis",
        "radar-beta\n curve c {A: 1}\n axis A\n",
        true,
    ),
    (
        "curve before axis positional",
        "radar-beta\n curve c {1}\n axis A\n",
        true,
    ),
    (
        "options",
        "radar-beta\n axis A\n showLegend false\n ticks 3, max 5, min 1\n",
        true,
    ),
    (
        "options comma",
        "radar-beta\n axis A\n curve c {2}\n ticks 3, max 5\n",
        true,
    ),
    (
        "showLegend bad",
        "radar-beta\n axis A\n showLegend yes\n",
        false,
    ),
    (
        "graticule bad",
        "radar-beta\n axis A\n graticule square\n",
        false,
    ),
    (
        "ticks zero",
        "radar-beta\n axis A\n curve c {1}\n ticks 0\n",
        true,
    ),
    (
        "ticks frac",
        "radar-beta\n axis A\n curve c {1}\n ticks 2.5\n",
        true,
    ),
    (
        "ticks big",
        "radar-beta\n axis A\n curve c {1}\n ticks 100\n",
        true,
    ),
    (
        "title acc",
        "radar-beta\n title Foo\n accTitle: t\n accDescr: d\n axis A\n",
        true,
    ),
    ("title no space", "radar-beta\n titlefoo\n axis A\n", false),
    (
        "label empty",
        "radar-beta\n axis A[\"\"]\n curve c[\"\"]{1}\n",
        true,
    ),
    ("label single quote", "radar-beta\n axis A['x y']\n", true),
    ("label no quotes", "radar-beta\n axis A[x]\n", false),
    (
        "comment",
        "radar-beta %% hi\n axis A %% c\n %% full\n curve c {1} %% x\n",
        true,
    ),
    ("leading blank", "\n\nradar-beta\n axis A\n", true),
    (
        "int leading zero",
        "radar-beta\n axis A\n curve c {01}\n",
        false,
    ),
    ("int 0.5", "radar-beta\n axis A\n curve c {0.5}\n", true),
    ("int 1.", "radar-beta\n axis A\n curve c {1.}\n", false),
    ("int .5", "radar-beta\n axis A\n curve c {.5}\n", false),
    (
        "curve no braces",
        "radar-beta\n axis A\n curve c 1\n",
        false,
    ),
    ("axis no names", "radar-beta\n axis\n", false),
    (
        "detailed no colon",
        "radar-beta\n axis A\n curve c {A 1}\n",
        true,
    ),
    (
        "detailed repeated",
        "radar-beta\n axis A, B\n curve c {A: 1, A: 2, B: 3}\n",
        true,
    ),
    (
        "many on one line",
        "radar-beta\n axis A curve c {1} showLegend true\n",
        true,
    ),
    ("ticks neg", "radar-beta\n axis A\n ticks -1\n", false),
    ("id with dot", "radar-beta\n axis A.B\n", false),
    ("unicode name", "radar-beta\n axis é\n", false),
    ("crlf", "radar-beta\r\n axis A\r\n curve c {1}\r\n", true),
    ("lone cr", "radar-beta\r axis A\r curve c {1}\r", true),
    (
        "subset",
        "radar-beta\n axis A, B, C\n curve c {A: 1, B: 4}\n",
        false,
    ),
];

#[test]
fn acceptance_matches_the_upstream_parser() {
    for (name, source, accept) in ACCEPTANCE {
        let (_, diagnostics) = resolved(source);
        assert_eq!(
            *accept,
            error_count(&diagnostics) == 0,
            "{name}: {diagnostics:?}"
        );
    }
}

const VERDICT_SCRIPT: &str = "import json\nv=json.load(open('corpus/verdicts.json'))\nd={r['path'] for r in json.load(open('corpus/divergences.json'))}\nfor p,r in v.items():\n if p.startswith('corpus/radar/') and p not in d: print(str(int(r['accept']))+' '+p)";

#[test]
fn corpus_verdicts() -> std::io::Result<()> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let result = std::process::Command::new("python3")
        .arg("-c")
        .arg(VERDICT_SCRIPT)
        .current_dir(&root)
        .output()?;
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let mut mismatches = Vec::new();
    let mut count = 0;
    for line in String::from_utf8_lossy(&result.stdout).lines() {
        let Some((accept, path)) = line.split_once(' ') else {
            continue;
        };
        let source = std::fs::read_to_string(root.join(path))?;
        count += 1;
        let (_, diagnostics) = resolved(&source);
        if (error_count(&diagnostics) == 0) != (accept == "1") {
            mismatches.push(format!("{path}: expected {accept}, got {diagnostics:?}"));
        }
    }
    assert!(count > 0, "radar corpus was empty");
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
    Ok(())
}

#[test]
fn labels_default_to_names_only() {
    let (m, diagnostics) =
        resolved("radar-beta\naxis A[\"\"], B, C[\"See\"]\ncurve x[\"\"]{1,2,3}, y{3,2,1}\n");
    assert_eq!(error_count(&diagnostics), 0);
    let axes: Vec<&str> = m.axes.iter().map(|a| a.label.as_str()).collect();
    let curves: Vec<&str> = m.curves.iter().map(|c| c.label.as_str()).collect();
    assert_eq!(axes, ["", "B", "See"]);
    assert_eq!(curves, ["", "y"]);
}

#[test]
fn positional_curves_keep_all_values() {
    let (m, diagnostics) = resolved("radar-beta\naxis A, B\ncurve x{1,2,3.0005}, y{4}\n");
    assert_eq!(error_count(&diagnostics), 0);
    assert_eq!(m.curves[0].values, [1000, 2000, 3001]);
    assert_eq!(m.curves[1].values, [4000]);
}

#[test]
fn keyed_curves_follow_axis_order_and_first_entry_wins() {
    let (m, diagnostics) =
        resolved("radar-beta\ncurve k{C: 9, A 1, B: 2, A: 7, D: 5}\naxis A, B, C\n");
    assert_eq!(error_count(&diagnostics), 0);
    assert_eq!(m.curves[0].values, [1000, 2000, 9000]);
}

#[test]
fn duplicate_axes_stay_ordered() {
    let (m, diagnostics) = resolved("radar-beta\naxis A, A\ncurve k{A: 3}\n");
    assert_eq!(error_count(&diagnostics), 0);
    assert_eq!(m.axes.len(), 2);
    assert_eq!(m.curves[0].values, [3000, 3000]);
}

#[test]
fn keyed_curve_errors() {
    let (_, diagnostics) = resolved("radar-beta\ncurve k{A: 1}\n");
    assert_eq!(codes(&diagnostics), ["radar/axes-required"]);
    assert_eq!(diagnostics[0].message, "keyed curve requires declared axes");
    let (_, diagnostics) = resolved("radar-beta\naxis A, b[\"Bee\"]\ncurve k{A: 1}\n");
    assert_eq!(codes(&diagnostics), ["radar/missing-axis-entry"]);
    assert_eq!(diagnostics[0].message, "missing entry for axis Bee");
    assert_eq!(diagnostics[0].span.start, 34);
}

#[test]
fn options_last_declaration_wins() {
    let (m, diagnostics) = resolved(
        "radar-beta\naxis A\ncurve c{1}\nshowLegend false\nticks 3\nticks 4, max 9, max 8\nmin 1\ngraticule polygon\ngraticule circle\nshowLegend true\n",
    );
    assert!(diagnostics.is_empty());
    let o = &m.options;
    assert!(o.show_legend);
    assert_eq!(o.ticks, 4000);
    assert!(o.has_max);
    assert_eq!(o.max, 8000);
    assert_eq!(o.min, 1000);
    assert_eq!(o.graticule, Graticule::Circle);
}

#[test]
fn option_defaults() {
    let (m, diagnostics) = resolved("radar-beta\naxis A\ncurve c{1}\n");
    assert!(diagnostics.is_empty());
    let o = &m.options;
    assert!(o.show_legend);
    assert_eq!(o.ticks, 5000);
    assert!(!o.has_max);
    assert_eq!((o.max, o.min), (0, 0));
    assert_eq!(o.graticule, Graticule::Circle);
}

#[test]
fn ticks_above_the_cap_are_clamped() {
    let (m, diagnostics) = resolved("radar-beta\naxis A\ncurve c{1}\nticks 33\n");
    assert_eq!(codes(&diagnostics), ["radar/ticks-clamped"]);
    assert_eq!(diagnostics[0].severity, Severity::Warning);
    assert_eq!(diagnostics[0].message, "ticks 33 exceeds 32; using 32");
    assert_eq!(m.options.ticks, 32000);
    let (m, diagnostics) = resolved("radar-beta\naxis A\ncurve c{1}\nticks 32\n");
    assert!(diagnostics.is_empty());
    assert_eq!(m.options.ticks, 32000);
    let (m, diagnostics) = resolved("radar-beta\naxis A\ncurve c{1}\nticks 0\n");
    assert!(diagnostics.is_empty());
    assert_eq!(m.options.ticks, 0);
}

#[test]
fn empty_range() -> Check {
    let (_, diagnostics) = resolved("radar-beta\naxis A\ncurve c{0}\n");
    assert_eq!(codes(&diagnostics), ["radar/empty-range"]);
    assert_eq!(diagnostics[0].severity, Severity::Error);
    assert_eq!(diagnostics[0].span.start, 0);
    let (_, diagnostics) = resolved("radar-beta\naxis A\ncurve c{4}\nmin 4\n");
    assert_eq!(codes(&diagnostics), ["radar/empty-range"]);
    assert_eq!(diagnostics[0].span.start, 33);
    let (_, diagnostics) = resolved("radar-beta\naxis A\ncurve c{4}\nmin 1\nmax 1\n");
    assert_eq!(codes(&diagnostics), ["radar/empty-range"]);
    assert_eq!(diagnostics[0].span.start, 39);
    let (_, diagnostics) = resolved("radar-beta\naxis A\nmax 0\n");
    assert_eq!(codes(&diagnostics), ["radar/empty-range"]);
    let (_, diagnostics) = resolved("radar-beta\naxis A\n");
    assert!(diagnostics.is_empty());
    let (_, diagnostics) = resolved("radar-beta\naxis A\ncurve c{-1}\n");
    assert!(!diagnostics.is_empty());
    Ok(())
}

#[test]
fn metadata_and_frontmatter() {
    let (m, diagnostics) = resolved("---\ntitle: Front\n---\nradar-beta\naxis A\n");
    assert!(diagnostics.is_empty());
    assert_eq!(m.title, "Front");
    let (m, diagnostics) = resolved(
        "---\ntitle: Front\n---\nradar-beta\ntitle  Body #amp; x\naccTitle: at\naccDescr: ad\naxis A\n",
    );
    assert!(diagnostics.is_empty());
    assert_eq!(m.title, "Body & x");
    assert_eq!(m.acc_title, "at");
    assert_eq!(m.acc_descr, "ad");
    let (m, diagnostics) = resolved("---\ntitle: Front\n---\nradar-beta\ntitle\naxis A\n");
    assert!(diagnostics.is_empty());
    assert_eq!(m.title, "Front");
}

#[test]
fn config_keys() {
    let (m, diagnostics) = resolved(
        "---\nconfig:\n  radar:\n    width: 400\n    height: 0\n    marginTop: 100\n    curveTension: 0.1\n    axisScaleFactor: 0.5\n---\nradar-beta\naxis A\n",
    );
    assert!(diagnostics.is_empty());
    assert_eq!(
        config_of(&m),
        [("curveTension", 100), ("marginTop", 100), ("width", 400)]
    );
    let (m, diagnostics) = resolved(
        "%%{init: {\"radar\": {\"width\": 500, \"curveTension\": 1, \"marginRight\": 7}}}%%\nradar-beta\naxis A\n",
    );
    assert!(diagnostics.is_empty());
    assert_eq!(
        config_of(&m),
        [("curveTension", 1000), ("marginRight", 7), ("width", 500)]
    );
    let (m, diagnostics) = resolved(
        "---\nconfig:\n  radar:\n    curveTension: 1.5\n    width: -3\n---\nradar-beta\naxis A\n",
    );
    assert!(diagnostics.is_empty());
    assert!(m.config.is_empty());
}

#[test]
fn thousandths_rounds_half_up() {
    for (literal, want) in [
        ("0", 0),
        ("7", 7000),
        ("0.5", 500),
        ("1.0005", 1001),
        ("1.0004", 1000),
        ("12.3456", 12346),
        ("0.0005", 1),
        ("100", 100_000),
    ] {
        assert_eq!(thousandths(literal), want, "{literal}");
    }
}
