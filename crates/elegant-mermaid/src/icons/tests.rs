use super::*;
use crate::scene::{Group, PathCommand, check_groups};
use crate::{
    LayoutOptions, Profile, RenderError, Severity, SvgOptions, layout_with_diagnostics, parse,
    render_svg,
};

type TestResult = Result<(), Box<dyn std::error::Error>>;

const SOURCE: &str = "flowchart LR\n  A@{ icon: 'x:none', label: 'Gone' } --> B[Plain]\n";

const PACK: &str = r#"{
  "prefix": "t",
  "width": 24,
  "height": 24,
  "icons": {
    "box": {"body": "<path d=\"M0 0h24v24H0z\"/>"},
    "wide": {"width": 32, "height": 16, "body": "<path d='M0 0h32v16H0z'/>"},
    "bad": {"body": "<circle cx=\"1\" cy=\"1\" r=\"1\"/>"},
    "arc": {"body": "<path d=\"M0 0A1 1 0 0 1 2 2\"/>"}
  }
}"#;

fn run(
    source: &str,
    packs: &[&str],
    profile: Profile,
) -> Result<(Scene, Vec<Diagnostic>), Box<dyn std::error::Error>> {
    let icon_packs = packs
        .iter()
        .map(|pack| parse_icon_pack(pack))
        .collect::<Result<Vec<_>, _>>()?;
    let options = LayoutOptions {
        profile,
        icon_packs,
        ..LayoutOptions::default()
    };
    Ok(layout_with_diagnostics(&parse(source), &options)?)
}

fn node<'a>(scene: &'a Scene, id: &str) -> Result<&'a Group, Box<dyn std::error::Error>> {
    Ok(scene
        .items()
        .iter()
        .find(|g| g.role == GroupRole::Node && g.owner == id)
        .ok_or("missing node group")?)
}

fn rect_of(scene: &Scene, id: &str) -> Result<Rect, Box<dyn std::error::Error>> {
    Ok(scene
        .boxes()
        .iter()
        .find(|b| b.id == id)
        .map(|b| b.rect)
        .ok_or("missing box")?)
}

fn icon_notes(diagnostics: &[Diagnostic]) -> Vec<&Diagnostic> {
    diagnostics
        .iter()
        .filter(|d| d.code == "icon/pack-missing")
        .collect()
}

fn paths(group: &Group) -> Vec<&PathItem> {
    group
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Path(path) => Some(path),
            _ => None,
        })
        .collect()
}

fn question_marks(group: &Group) -> usize {
    paths(group)
        .iter()
        .filter(|path| {
            path.commands
                .iter()
                .any(|command| matches!(command, PathCommand::Curve { .. }))
        })
        .count()
}

#[test]
fn icon_pack_missing() -> TestResult {
    let (scene, diagnostics) = run(SOURCE, &[], Profile::Vector)?;
    let notes = icon_notes(&diagnostics);
    assert_eq!(notes.len(), 1, "{diagnostics:?}");
    let note = notes[0];
    assert_eq!(note.severity, Severity::Info);
    assert_eq!(note.message, "icon x:none is not available");
    assert_eq!(
        note.help,
        "The diagram draws the unknown icon in its place."
    );
    assert!(SOURCE[note.span.start..note.span.end].contains("x:none"));
    let group = node(&scene, "A")?;
    assert_eq!(question_marks(group), 1);
    assert_eq!(paths(group).len(), 1);
    assert_eq!(question_marks(node(&scene, "B")?), 0);
    assert_eq!(check_groups(scene.items(), scene.dump_part()), Ok(()));
    Ok(())
}

#[test]
fn icon_pack_missing_in_cells() -> TestResult {
    let (cell, cell_diagnostics) = run(SOURCE, &[], Profile::Cell)?;
    assert_eq!(icon_notes(&cell_diagnostics).len(), 1);
    let rect = rect_of(&cell, "A")?;
    let symbols: Vec<_> = node(&cell, "A")?
        .items
        .iter()
        .filter_map(|item| match item {
            Item::SymbolRef(symbol) => Some(symbol),
            _ => None,
        })
        .collect();
    assert_eq!(symbols.len(), 1);
    assert_eq!(symbols[0].symbol.as_str(), "unknown");
    assert_eq!(symbols[0].style, ShapeStyle::Ink);
    assert_eq!(
        symbols[0].at,
        Point {
            x: rect.x + rect.w / 2,
            y: rect.y
        }
    );
    assert_eq!(check_groups(cell.items(), cell.dump_part()), Ok(()));
    Ok(())
}

#[test]
fn icon_pack_missing_covers_absent_unsupported_and_unprefixed_icons() -> TestResult {
    for (name, expected) in [
        ("t:nothing", true),
        ("other:box", true),
        ("box", true),
        ("t:bad", true),
        ("t:arc", true),
        ("t:box", false),
    ] {
        let source = format!("flowchart LR\n  A@{{ icon: '{name}', label: 'L' }}\n");
        let (scene, diagnostics) = run(&source, &[PACK], Profile::Vector)?;
        let notes = icon_notes(&diagnostics);
        assert_eq!(!notes.is_empty(), expected, "{name}");
        if expected {
            assert_eq!(notes[0].message, format!("icon {name} is not available"));
            assert_eq!(question_marks(node(&scene, "A")?), 1, "{name}");
        } else {
            assert_eq!(question_marks(node(&scene, "A")?), 0, "{name}");
        }
    }
    Ok(())
}

#[test]
fn icon_pack_draws_supported_icons_scaled_and_centred() -> TestResult {
    for (name, vertical, drop) in [("t:box", 0, 1536), ("t:wide", 384, 768)] {
        let source = format!("flowchart LR\n  A@{{ icon: '{name}', label: 'L' }}\n");
        let (scene, diagnostics) = run(&source, &[PACK], Profile::Vector)?;
        assert!(icon_notes(&diagnostics).is_empty(), "{name}");
        let rect = rect_of(&scene, "A")?;
        let (x, y) = (rect.x + rect.w / 2 - 768, rect.y - 768 + vertical);
        let group = node(&scene, "A")?;
        let drawn = paths(group);
        assert_eq!(drawn.len(), 1, "{name}");
        assert_eq!(drawn[0].shape, Shape::plain(ShapeStyle::Ink));
        assert_eq!(
            drawn[0].commands,
            [
                PathCommand::Move(Point { x, y }),
                PathCommand::Line(Point { x: x + 1536, y }),
                PathCommand::Line(Point {
                    x: x + 1536,
                    y: y + drop
                }),
                PathCommand::Line(Point { x, y: y + drop }),
                PathCommand::Close,
            ],
            "{name}"
        );
        assert_eq!(question_marks(group), 0);
        assert_eq!(check_groups(scene.items(), scene.dump_part()), Ok(()));
    }
    Ok(())
}

#[test]
fn icon_pack_cell_profile_draws_one_unknown_symbol_in_ink() -> TestResult {
    let source = "flowchart LR\n  A@{ icon: 't:box', label: 'L' }\n";
    let (scene, diagnostics) = run(source, &[PACK], Profile::Cell)?;
    assert!(icon_notes(&diagnostics).is_empty());
    let styles: Vec<_> = node(&scene, "A")?
        .items
        .iter()
        .filter_map(|item| match item {
            Item::SymbolRef(symbol) => Some((symbol.symbol.as_str(), symbol.style)),
            _ => None,
        })
        .collect();
    assert_eq!(styles, [("unknown", ShapeStyle::Ink)]);
    Ok(())
}

#[test]
fn icon_pack_first_matching_pack_wins_and_svg_draws_the_path() -> TestResult {
    let other = r#"{"prefix":"t","icons":{"box":{"width":16,"height":16,"body":"<path d='M0 0L16 0L16 16Z'/>"}}}"#;
    let source = "flowchart LR\n  A@{ icon: 't:box', label: 'L' }\n";
    let first = run(source, &[PACK, other], Profile::Vector)?.0;
    let second = run(source, &[other, PACK], Profile::Vector)?.0;
    assert_ne!(
        paths(node(&first, "A")?)[0].commands,
        paths(node(&second, "A")?)[0].commands
    );
    let options = SvgOptions {
        layout: LayoutOptions {
            icon_packs: vec![parse_icon_pack(PACK)?],
            ..LayoutOptions::default()
        },
        ..SvgOptions::default()
    };
    let svg = render_svg(&parse(source), &options)?;
    assert!(svg.contains("<path class='emd-s-ink' d='M "), "{svg}");
    assert!(svg.contains(" Z'"), "{svg}");
    Ok(())
}

#[test]
fn icon_pack_defaults_come_from_the_pack_level() -> TestResult {
    let pack = parse_icon_pack(
        r#"{"prefix":"d","left":2,"top":4,"icons":{"a":{"body":"<path d='M2 4h16v16H2z'/>"}}}"#,
    )?;
    assert_eq!(pack.prefix(), "d");
    assert!(pack.contains("a"));
    assert!(!pack.contains("b"));
    let icon = pack.icons.get("a").ok_or("icon a")?;
    assert_eq!(
        (icon.left, icon.top, icon.width, icon.height),
        (
            2 * path::SCALE,
            4 * path::SCALE,
            16 * path::SCALE,
            16 * path::SCALE
        )
    );
    Ok(())
}

#[test]
fn icon_pack_rejects_malformed_documents() {
    for source in [
        "",
        "[]",
        "{}",
        r#"{"prefix":"","icons":{}}"#,
        r#"{"prefix":1,"icons":{}}"#,
        r#"{"prefix":"p"}"#,
        r#"{"prefix":"p","icons":[]}"#,
        r#"{"prefix":"p","icons":{"a":1}}"#,
        r#"{"prefix":"p","icons":{"a":{}}}"#,
        r#"{"prefix":"p","icons":{"a":{"body":1}}}"#,
        r#"{"prefix":"p","icons":{"a":{"body":"","width":0}}}"#,
        r#"{"prefix":"p","icons":{"a":{"body":"","height":"x"}}}"#,
        r#"{"prefix":"p","width":-1,"icons":{}}"#,
        r#"{"prefix":"p","icons":{}} trailing"#,
    ] {
        assert!(
            matches!(
                parse_icon_pack(source),
                Err(IconPackError::Malformed { .. })
            ),
            "{source:?}"
        );
    }
    assert_eq!(
        parse_icon_pack(r#"{"prefix":"p","icons":{}}"#).map(|p| p.prefix().to_owned()),
        Ok("p".to_owned())
    );
}

fn nested_arrays(levels: usize) -> String {
    format!(
        r#"{{"prefix":"p","x":{}{},"icons":{{}}}}"#,
        "[".repeat(levels),
        "]".repeat(levels)
    )
}

#[test]
fn icon_pack_reasons_are_fixed() {
    let cases: Vec<(&str, String, &str)> = vec![
        (
            "empty",
            String::new(),
            "invalid JSON at byte 0: expected a value",
        ),
        ("array root", "[]".into(), "the root must be an object"),
        (
            "no prefix",
            r#"{"icons":{}}"#.into(),
            "missing string prefix",
        ),
        (
            "numeric prefix",
            r#"{"prefix":5,"icons":{}}"#.into(),
            "missing string prefix",
        ),
        (
            "capitalised key",
            r#"{"Prefix":"p","icons":{}}"#.into(),
            "missing string prefix",
        ),
        (
            "empty prefix",
            r#"{"prefix":"","icons":{}}"#.into(),
            "the prefix must not be empty",
        ),
        (
            "last duplicate wins",
            r#"{"prefix":"p","prefix":"","icons":{}}"#.into(),
            "the prefix must not be empty",
        ),
        (
            "no icons",
            r#"{"prefix":"p"}"#.into(),
            "missing icons object",
        ),
        (
            "icons array",
            r#"{"prefix":"p","icons":[]}"#.into(),
            "missing icons object",
        ),
        (
            "null icon",
            r#"{"prefix":"p","icons":{"a":null}}"#.into(),
            "icon a must be an object",
        ),
        (
            "no body",
            r#"{"prefix":"p","icons":{"a":{}}}"#.into(),
            "icon a needs a string body",
        ),
        (
            "first bad icon",
            r#"{"prefix":"p","icons":{"b":{"body":5},"a":{}}}"#.into(),
            "icon b needs a string body",
        ),
        (
            "string width",
            r#"{"prefix":"p","icons":{"a":{"body":"","width":"16"}}}"#.into(),
            "width must be a number",
        ),
        (
            "null default width",
            r#"{"prefix":"p","width":null,"icons":{}}"#.into(),
            "width must be a number",
        ),
        (
            "exponent width",
            r#"{"prefix":"p","icons":{"a":{"body":"","width":1e1}}}"#.into(),
            "width is out of range",
        ),
        (
            "seven digit height",
            r#"{"prefix":"p","icons":{"a":{"body":"","height":1000000}}}"#.into(),
            "height is out of range",
        ),
        (
            "seven fraction digits",
            r#"{"prefix":"p","left":0.0000001,"icons":{}}"#.into(),
            "left is out of range",
        ),
        (
            "zero default size",
            r#"{"prefix":"p","height":0,"icons":{}}"#.into(),
            "the default size must be positive",
        ),
        (
            "negative icon width",
            r#"{"prefix":"p","icons":{"a":{"body":"","width":-1}}}"#.into(),
            "icon a needs a positive size",
        ),
        (
            "trailing content",
            r#"{"prefix":"p","icons":{}} x"#.into(),
            "invalid JSON at byte 26: trailing content",
        ),
        (
            "leading zero",
            r#"{"prefix":"p","width":016,"icons":{}}"#.into(),
            "invalid JSON at byte 23: expected ',' or '}'",
        ),
        (
            "unpaired surrogate",
            r#"{"prefix":"\ud800","icons":{}}"#.into(),
            "invalid JSON at byte 17: unpaired surrogate",
        ),
        (
            "bad escape",
            r#"{"prefix":"p\q","icons":{}}"#.into(),
            "invalid JSON at byte 14: invalid escape",
        ),
        (
            "control character",
            "{\"prefix\":\"a\nb\",\"icons\":{}}".into(),
            "invalid JSON at byte 13: control character in string",
        ),
        (
            "trailing comma",
            r#"{"prefix":"p","icons":{},}"#.into(),
            "invalid JSON at byte 25: expected a member name",
        ),
        (
            "nesting of 65 levels",
            nested_arrays(64),
            "invalid JSON at byte 81: nesting is too deep",
        ),
    ];
    for (name, source, reason) in cases {
        assert_eq!(
            parse_icon_pack(&source).map(|_| ()),
            Err(IconPackError::Malformed {
                reason: reason.to_owned()
            }),
            "{name}"
        );
    }
}

#[test]
fn icon_pack_accepts_the_shared_valid_documents() {
    for (name, source) in [
        ("nesting of 64 levels", nested_arrays(63)),
        (
            "last duplicate wins",
            r#"{"prefix":"","prefix":"p","icons":{}}"#.to_owned(),
        ),
        (
            "decimal size",
            r#"{"prefix":"p","icons":{"a":{"body":"","width":16.5,"left":-3}}}"#.to_owned(),
        ),
        (
            "escaped prefix",
            r#"{"prefix":"\u0070","icons":{}}"#.to_owned(),
        ),
        (
            "unknown members",
            r#"{"prefix":"p","aliases":{},"icons":{}}"#.to_owned(),
        ),
    ] {
        assert!(parse_icon_pack(&source).is_ok(), "{name}");
    }
}

#[test]
fn icon_pack_icons_outside_flowchart_nodes_are_not_referenced() -> TestResult {
    let (_, diagnostics) = run("flowchart LR\n  A --> B\n", &[], Profile::Vector)?;
    assert!(icon_notes(&diagnostics).is_empty());
    assert!(matches!(
        layout_with_diagnostics(&parse(""), &LayoutOptions::default()),
        Err(RenderError::InvalidDocument { .. })
    ));
    Ok(())
}

fn round_half_up(a: i128, b: i128) -> i128 {
    (2 * a + b).div_euclid(2 * b)
}

fn micro(text: &str) -> i128 {
    let (sign, rest) = text.strip_prefix('-').map_or((1, text), |rest| (-1, rest));
    let (whole, fraction) = rest.split_once('.').unwrap_or((rest, ""));
    let digits: i128 = format!("{whole}{fraction}").parse().unwrap_or(0);
    let places = u32::try_from(fraction.len()).unwrap_or(0);
    sign * round_half_up(digits * 1_000_000, 10_i128.pow(places))
}

struct Case {
    width: &'static str,
    height: &'static str,
    left: &'static str,
    top: &'static str,
    from: (&'static str, &'static str),
    to: (&'static str, &'static str),
}

const fn case(
    size: (&'static str, &'static str),
    offset: (&'static str, &'static str),
    from: (&'static str, &'static str),
    to: (&'static str, &'static str),
) -> Case {
    Case {
        width: size.0,
        height: size.1,
        left: offset.0,
        top: offset.1,
        from,
        to,
    }
}

fn case_pack(c: &Case) -> String {
    let body = format!(
        "<path d=\\\"M{} {}L{} {}z\\\"/>",
        c.from.0, c.from.1, c.to.0, c.to.1
    );
    format!(
        r#"{{"prefix":"p","icons":{{"a":{{"body":"{body}","width":{},"height":{},"left":{},"top":{}}}}}}}"#,
        c.width, c.height, c.left, c.top
    )
}

fn expected_corners(c: &Case, at: Point) -> Option<Vec<PathCommand>> {
    let (width, height) = (micro(c.width), micro(c.height));
    let side = width.max(height);
    if side < 1_000_000 {
        return None;
    }
    let scale = round_half_up(1536 * 1_000_000, side).max(1);
    let unit = |v: i128| round_half_up(v * scale, 1_000_000);
    let origin = |at: i32, size: i128| i128::from(at) + (1536 - unit(size)).div_euclid(2);
    let (ox, oy) = (origin(at.x, width), origin(at.y, height));
    let point = |(x, y): (&str, &str)| -> Option<Point> {
        Some(Point {
            x: i32::try_from(ox + unit(micro(x) - micro(c.left))).ok()?,
            y: i32::try_from(oy + unit(micro(y) - micro(c.top))).ok()?,
        })
    };
    Some(vec![
        PathCommand::Move(point(c.from)?),
        PathCommand::Line(point(c.to)?),
        PathCommand::Close,
    ])
}

fn drawn_commands(pack: &IconPack, at: Point) -> Option<Vec<Vec<PathCommand>>> {
    let icon = pack.icons.get("a")?;
    drawn(icon, at).map(|items| {
        items
            .into_iter()
            .filter_map(|item| match item {
                Item::Path(path) => Some(path.commands),
                _ => None,
            })
            .collect()
    })
}

#[test]
fn icon_scale_and_origin() -> TestResult {
    let at = Point { x: 100, y: -50 };
    let cases = [
        case(("24", "24"), ("0", "0"), ("0", "0"), ("24", "24")),
        case(("20", "20"), ("0", "0"), ("0", "0"), ("20", "20")),
        case(("28", "28"), ("0", "0"), ("3", "5"), ("25.5", "27")),
        case(("32", "16"), ("0", "0"), ("0", "0"), ("32", "16")),
        case(("16", "32"), ("0", "0"), ("1.5", "2.25"), ("9", "30.125")),
        case(
            ("17.5", "17.5"),
            ("0", "0"),
            ("0.000001", "0.0000005"),
            ("17.5", "17.499999"),
        ),
        case(
            ("1792", "1792"),
            ("0", "0"),
            ("100", "200"),
            ("1700", "1790"),
        ),
        case(
            ("1536", "1536"),
            ("0", "0"),
            ("100", "200"),
            ("1500", "1500"),
        ),
        case(
            ("1024", "1024"),
            ("0", "0"),
            ("100", "200"),
            ("1000", "1000"),
        ),
        case(("8", "4"), ("2", "2"), ("2", "2"), ("10", "6")),
        case(("24", "24"), ("-3", "4.5"), ("-3", "4.5"), ("21", "28.5")),
        case(("1", "1"), ("0", "0"), ("0", "0"), ("1", "1")),
        case(
            ("999999", "999999"),
            ("0", "0"),
            ("0", "0"),
            ("999999", "1"),
        ),
        case(("0.999999", "0.5"), ("0", "0"), ("0", "0"), ("1", "1")),
        case(("0.5", "0.5"), ("0", "0"), ("0", "0"), ("0.5", "0.5")),
    ];
    for c in &cases {
        let pack = parse_icon_pack(&case_pack(c))?;
        let got = drawn_commands(&pack, at);
        let want = expected_corners(c, at).map(|commands| vec![commands]);
        assert_eq!(got, want, "{:?}", (c.width, c.height, c.left, c.top));
    }
    Ok(())
}

#[test]
fn icon_result_outside_int32_is_unsupported() -> TestResult {
    let pack = parse_icon_pack(
        r#"{"prefix":"p","icons":{"a":{"body":"<path d=\"M0 0h20v20z\"/>","width":20,"height":20}}}"#,
    )?;
    for (at, supported) in [
        (
            Point {
                x: i32::MAX - 1538,
                y: 0,
            },
            true,
        ),
        (
            Point {
                x: i32::MAX - 1537,
                y: 0,
            },
            false,
        ),
        (
            Point {
                x: i32::MIN + 2,
                y: 0,
            },
            true,
        ),
        (
            Point {
                x: i32::MIN + 1,
                y: 0,
            },
            false,
        ),
        (
            Point {
                x: 0,
                y: i32::MAX - 1538,
            },
            true,
        ),
        (
            Point {
                x: 0,
                y: i32::MAX - 1537,
            },
            false,
        ),
        (
            Point {
                x: 0,
                y: i32::MIN + 2,
            },
            true,
        ),
        (
            Point {
                x: 0,
                y: i32::MIN + 1,
            },
            false,
        ),
    ] {
        assert_eq!(drawn_commands(&pack, at).is_some(), supported, "{at:?}");
    }
    Ok(())
}

fn pack_drawing(data: &str) -> Result<Option<Vec<PathCommand>>, Box<dyn std::error::Error>> {
    let json = format!(
        r#"{{"prefix":"p","width":24,"height":24,"icons":{{"a":{{"body":"<path d=\"{data}\"/>"}}}}}}"#
    );
    let pack = parse_icon_pack(&json)?;
    Ok(drawn_commands(&pack, Point { x: 0, y: 0 }).and_then(|mut paths| paths.pop()))
}

#[test]
fn icon_quadratic_to_cubic() -> TestResult {
    let scale = 64;
    let third =
        |a: i32, c: i32| i32::try_from(round_half_up(i128::from(a + 2 * c), 3)).unwrap_or(0);
    let (from, control, to) = (
        (2 * scale, 3 * scale),
        (10 * scale, 20 * scale),
        (7 * scale, scale),
    );
    let want = vec![
        PathCommand::Move(Point {
            x: from.0,
            y: from.1,
        }),
        PathCommand::Curve {
            c1: Point {
                x: third(from.0, control.0),
                y: third(from.1, control.1),
            },
            c2: Point {
                x: third(to.0, control.0),
                y: third(to.1, control.1),
            },
            to: Point { x: to.0, y: to.1 },
        },
    ];
    assert_eq!(pack_drawing("M2 3Q10 20 7 1")?, Some(want));
    Ok(())
}

#[test]
fn icon_relative_and_smooth_commands() -> TestResult {
    for (relative, absolute) in [
        ("m1 1l2 3h4v5z", "M1 1L3 4L7 4L7 9Z"),
        ("M1 1 2 3 4 5", "M1 1L2 3L4 5"),
        ("m1 1 2 3 4 5", "m1 1l2 3l4 5"),
        (
            "m1 1c1 2 3 4 5 6s7 8 9 10",
            "M1 1C2 3 4 5 6 7C8 9 13 15 15 17",
        ),
        (
            "M0 0C1 2 3 4 5 6S9 10 11 12",
            "M0 0C1 2 3 4 5 6C7 8 9 10 11 12",
        ),
        ("M0 0S9 10 11 12", "M0 0C0 0 9 10 11 12"),
        ("M0 0Q3 3 5 1T9 1", "M0 0Q3 3 5 1Q7 -1 9 1"),
        ("M0 0T9 1", "M0 0Q0 0 9 1"),
        ("M0 0Q3 3 5 1S9 10 11 12", "M0 0Q3 3 5 1C5 1 9 10 11 12"),
        ("M0 0C1 2 3 4 5 6T9 1", "M0 0C1 2 3 4 5 6Q5 6 9 1"),
        ("M2 2L6 6zm3 3l1 1", "M2 2L6 6ZM5 5L6 6"),
        ("M2 2 6 6z l1 1", "M2 2L6 6ZL3 3"),
        ("m1 1q2 2 4 0t4 0", "M1 1Q3 3 5 1Q7 -1 9 1"),
    ] {
        let (r, a) = (pack_drawing(relative)?, pack_drawing(absolute)?);
        assert!(r.is_some(), "{relative}");
        assert_eq!(r, a, "{relative} against {absolute}");
    }
    Ok(())
}

fn json_string(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if u32::from(c) < 0x20 => out.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[test]
fn icon_bodies() -> TestResult {
    let path = r#"<path d="M0 0h8v8z"/>"#;
    let cases: Vec<(&str, String, Option<usize>)> = vec![
        ("blank", String::new(), Some(0)),
        ("white space only", " \t\r\n\u{c}".into(), Some(0)),
        ("one path", path.into(), Some(1)),
        ("two paths", format!("{path}{path}"), Some(2)),
        (
            "ASCII space between",
            format!("{path} \t\r\n\u{c}{path}"),
            Some(2),
        ),
        (
            "explicit close",
            r#"<path d="M0 0h8v8z"></path>"#.into(),
            Some(1),
        ),
        (
            "fill currentColor",
            r#"<path fill="currentColor" d='M0 0h8v8z'/>"#.into(),
            Some(1),
        ),
        (
            "adjacent attributes",
            r#"<path d="M0 0h8v8z"fill="currentColor"/>"#.into(),
            Some(1),
        ),
        (
            "last d wins",
            r#"<path d="bad" d="M0 0h8v8z"/>"#.into(),
            Some(1),
        ),
        (
            "no-break space between",
            format!("{path}\u{a0}{path}"),
            None,
        ),
        ("leading no-break space", format!("\u{a0}{path}"), None),
        ("text after", format!("{path}text"), None),
        (
            "other element",
            r#"<circle cx="1" cy="1" r="1"/>"#.into(),
            None,
        ),
        ("group", format!("<g>{path}</g>"), None),
        (
            "other attribute",
            r#"<path fill-rule="evenodd" d="M0 0h8v8z"/>"#.into(),
            None,
        ),
        (
            "fill colour",
            r#"<path fill="red" d="M0 0h8v8z"/>"#.into(),
            None,
        ),
        (
            "stroke",
            r#"<path stroke="red" d="M0 0h8v8z"/>"#.into(),
            None,
        ),
        ("no d", r#"<path fill="currentColor"/>"#.into(), None),
        ("empty d", r#"<path d=""/>"#.into(), None),
        (
            "space in close",
            r#"<path d="M0 0h8v8z"> </path>"#.into(),
            None,
        ),
        (
            "space before equals",
            r#"<path d ="M0 0h8v8z"/>"#.into(),
            None,
        ),
        (
            "space after equals",
            r#"<path d= "M0 0h8v8z"/>"#.into(),
            None,
        ),
        (
            "no space after name",
            r#"<pathd="M0 0h8v8z"/>"#.into(),
            None,
        ),
        ("unquoted", "<path d=M0/>".into(), None),
        ("unclosed", r#"<path d="M0 0h8v8z""#.into(), None),
        ("open without close", r#"<path d="M0 0h8v8z">"#.into(), None),
        ("comment", format!("<!-- c -->{path}"), None),
        ("arc", r#"<path d="M0 0A1 1 0 0 1 2 2"/>"#.into(), None),
        ("starts with L", r#"<path d="L1 1"/>"#.into(), None),
        ("double comma", r#"<path d="M0,,0h8v8z"/>"#.into(), None),
        (
            "comma then command",
            r#"<path d="M0 0,h8v8z"/>"#.into(),
            Some(1),
        ),
        (
            "comma before first number",
            r#"<path d="M,0 0h8v8z"/>"#.into(),
            Some(1),
        ),
        (
            "number after close",
            r#"<path d="M0 0z 1 1"/>"#.into(),
            None,
        ),
        (
            "one of two bad",
            format!(r#"{path}<path d="M0 0A1 1"/>"#),
            None,
        ),
    ];
    for (name, body, paths) in cases {
        let json = format!(
            r#"{{"prefix":"p","width":24,"height":24,"icons":{{"a":{{"body":{}}}}}}}"#,
            json_string(&body)
        );
        let pack = parse_icon_pack(&json)?;
        let got = drawn_commands(&pack, Point { x: 0, y: 0 }).map(|paths| paths.len());
        assert_eq!(got, paths, "{name}");
    }
    Ok(())
}

const SQUARE_PACK: &str = r#"{"prefix":"t","width":24,"height":24,"icons":{"box":{"body":"<path d=\"M0 0h24v24H0z\"/>"},"bad":{"body":"<circle cx=\"1\" cy=\"1\" r=\"1\"/>"}}}"#;
const SMALL_PACK: &str = r#"{"prefix":"t","width":16,"height":16,"icons":{"box":{"body":"<path d=\"M0 0h16v16z\"/>"},"bad":{"body":"<path d=\"M0 0h16v16z\"/>"}}}"#;
const TRIANGLE_PACK: &str =
    r#"{"prefix":"t","width":24,"height":24,"icons":{"box":{"body":"<path d=\"M0 0h24v24z\"/>"}}}"#;

fn flow(name: &str) -> String {
    format!("flowchart LR\n  A@{{ icon: '{name}', label: 'L' }}\n")
}

#[test]
fn icon_resolution() -> TestResult {
    let cases: [(&str, &[&str], bool); 11] = [
        ("t:box", &[SQUARE_PACK], false),
        ("t:nothing", &[SQUARE_PACK], true),
        ("other:box", &[SQUARE_PACK], true),
        ("box", &[SQUARE_PACK], true),
        ("cloud", &[SQUARE_PACK], true),
        ("unknown", &[SQUARE_PACK], true),
        ("t:bad", &[SQUARE_PACK], true),
        ("t:box", &[], true),
        ("t:bad", &[SQUARE_PACK, SMALL_PACK], true),
        ("t:bad", &[SMALL_PACK, SQUARE_PACK], false),
        ("t:box", &[SMALL_PACK, SQUARE_PACK], false),
    ];
    for (name, packs, note) in cases {
        for profile in [Profile::Vector, Profile::Cell] {
            let (_, diagnostics) = run(&flow(name), packs, profile)?;
            let notes = icon_notes(&diagnostics);
            assert_eq!(notes.len(), usize::from(note), "{name} {profile:?}");
            for found in notes {
                assert_eq!(found.message, format!("icon {name} is not available"));
                assert_eq!(found.severity, Severity::Info);
                assert!(found.span.end > found.span.start);
            }
        }
    }
    let corners = |packs: &[&str]| -> Result<usize, Box<dyn std::error::Error>> {
        let (scene, _) = run(&flow("t:box"), packs, Profile::Vector)?;
        Ok(paths(node(&scene, "A")?)[0].commands.len())
    };
    assert_eq!(corners(&[SQUARE_PACK, TRIANGLE_PACK])?, 5);
    assert_eq!(corners(&[TRIANGLE_PACK, SQUARE_PACK])?, 4);
    Ok(())
}

fn points_of(commands: &[PathCommand]) -> Vec<Point> {
    commands
        .iter()
        .flat_map(|command| match command {
            PathCommand::Move(p) | PathCommand::Line(p) => vec![*p],
            PathCommand::Curve { c1, c2, to } => vec![*c1, *c2, *to],
            PathCommand::Close | PathCommand::Arc { .. } => Vec::new(),
        })
        .collect()
}

#[test]
fn icon_placement() -> TestResult {
    let (scene, _) = run(&flow("t:box"), &[SQUARE_PACK], Profile::Vector)?;
    let rect = rect_of(&scene, "A")?;
    let centre = rect.x + rect.w / 2;
    let corners = [
        Point {
            x: centre - 768,
            y: rect.y - 768,
        },
        Point {
            x: centre + 768,
            y: rect.y - 768,
        },
        Point {
            x: centre + 768,
            y: rect.y + 768,
        },
        Point {
            x: centre - 768,
            y: rect.y + 768,
        },
    ];
    let group = node(&scene, "A")?;
    assert_eq!(points_of(&paths(group)[0].commands), corners);
    let overlay_at = group
        .items
        .iter()
        .position(|item| item.class() != crate::scene::ItemClass::Shape)
        .ok_or("no overlay")?;
    assert!(
        group.items[..overlay_at]
            .iter()
            .any(|item| matches!(item, Item::Path(_)))
    );

    let (cell, _) = run(&flow("t:box"), &[SQUARE_PACK], Profile::Cell)?;
    let rect = rect_of(&cell, "A")?;
    let symbols: Vec<_> = node(&cell, "A")?
        .items
        .iter()
        .filter_map(|item| match item {
            Item::SymbolRef(symbol) => Some((symbol.symbol.as_str(), symbol.style, symbol.at)),
            _ => None,
        })
        .collect();
    let at = Point {
        x: rect.x + rect.w / 2,
        y: rect.y,
    };
    assert_eq!(symbols, [("unknown", ShapeStyle::Ink, at)]);

    let (missing, _) = run(&flow("x:none"), &[], Profile::Vector)?;
    let rect = rect_of(&missing, "A")?;
    let glyph = points_of(&paths(node(&missing, "A")?)[0].commands);
    let (min_x, max_x) = (
        glyph.iter().map(|p| p.x).min(),
        glyph.iter().map(|p| p.x).max(),
    );
    let (min_y, max_y) = (
        glyph.iter().map(|p| p.y).min(),
        glyph.iter().map(|p| p.y).max(),
    );
    let (min_x, max_x, min_y, max_y) = (
        min_x.ok_or("no points")?,
        max_x.ok_or("no points")?,
        min_y.ok_or("no points")?,
        max_y.ok_or("no points")?,
    );
    let (left, top) = (rect.x + rect.w / 2 - 768, rect.y - 768);
    assert!(min_x >= left && max_x <= left + 1536 && min_y >= top && max_y <= top + 1536);
    assert!(((min_x - left) - (left + 1536 - max_x)).abs() <= 1);
    assert!(((min_y - top) - (top + 1536 - max_y)).abs() <= 1);
    Ok(())
}
