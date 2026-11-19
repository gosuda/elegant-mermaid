use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use super::scale::{Linear, band_position, clamp, format_number, ticks};
use crate::DiagramKind;
use crate::geom::{GeomError, Rect, Size};
use crate::layout::families::layout;
use crate::model::Resolved;
use crate::scene::{DumpOptions, Item, Profile, Scene, SceneBox, SceneLabel, ShapeStyle, TextItem};

fn steps(from: i64, step: i64, count: usize) -> Vec<i64> {
    (0..count)
        .map(|i| from + i64::try_from(i).unwrap_or(0) * step)
        .collect()
}

#[test]
fn ticks_follow_the_d3_rule() -> Result<(), GeomError> {
    let cases: [(&str, i64, i64, Vec<i64>); 10] = [
        ("unit steps", 0, 10000, steps(0, 1000, 11)),
        ("ten per tick", 0, 100000, steps(0, 10000, 11)),
        ("twos", 0, 198200, steps(0, 20000, 10)),
        ("fives", 4000000, 11000000, steps(4000000, 500000, 15)),
        ("negative twos", -10000, 10000, steps(-10000, 2000, 11)),
        ("fractional fives", 0, 500, steps(0, 50, 11)),
        ("sub unit domain", 0, 5, steps(0, 1, 6)),
        (
            "misaligned start rounds up",
            1500,
            9500,
            steps(2000, 1000, 8),
        ),
        ("no span", 7000, 7000, vec![7000]),
        ("reversed", 10000, 0, steps(10000, -1000, 11)),
    ];
    for (name, lo, hi, want) in cases {
        let got = ticks(lo, hi)?;
        assert!(!got.capped, "{name}");
        assert_eq!(got.values, want, "{name}");
    }
    Ok(())
}

#[test]
fn tick_count_never_exceeds_twice_the_request() -> Result<(), GeomError> {
    let mut lo = -50000i64;
    while lo < 50000 {
        let mut span = 1i64;
        while span < 3_000_000_000 {
            let got = ticks(lo, lo + span)?;
            assert!(!got.capped);
            assert!(got.values.len() <= 21);
            assert!(got.values.first().is_some_and(|first| *first >= lo));
            assert!(got.values.last().is_some_and(|last| *last <= lo + span));
            span = span * 3 + 1;
        }
        lo += 7919;
    }
    Ok(())
}

#[test]
fn ticks_reject_spans_above_int32() {
    let error = ticks(0, i64::from(i32::MAX) + 1).err();
    assert_eq!(error, Some(GeomError::Overflow));
}

#[test]
fn format_number_trims_trailing_zeros() {
    let cases = [
        (0, "0"),
        (1500, "1.5"),
        (-2500, "-2.5"),
        (5, "0.005"),
        (-5, "-0.005"),
        (100000, "100"),
        (1100, "1.1"),
        (120, "0.12"),
    ];
    for (value, want) in cases {
        assert_eq!(format_number(value), want);
    }
}

#[test]
fn linear_map_floors_and_handles_reversed_domains() {
    let forward = Linear {
        d0: 0,
        d1: 3,
        r0: 0,
        r1: 10,
    };
    assert_eq!(forward.map(1), 3);
    assert_eq!(forward.map(3), 10);
    let reversed = Linear {
        d0: 3,
        d1: 0,
        r0: 0,
        r1: 10,
    };
    assert_eq!(reversed.map(1), 6);
    assert_eq!(
        Linear {
            d0: 0,
            d1: 3,
            r0: 0,
            r1: -10
        }
        .map(1),
        -4
    );
}

#[test]
fn linear_map_of_a_zero_width_domain_is_the_range_midpoint() {
    assert_eq!(
        Linear {
            d0: 5,
            d1: 5,
            r0: 0,
            r1: 9
        }
        .map(5),
        4
    );
    assert_eq!(
        Linear {
            d0: 5,
            d1: 5,
            r0: -3,
            r1: 0
        }
        .map(77),
        -2
    );
}

#[test]
fn band_positions_are_evenly_spaced_and_a_single_category_centres() {
    let at = |i, n| band_position(i, n, 100, 110);
    assert_eq!(
        [at(0, 4), at(1, 4), at(2, 4), at(3, 4)],
        [100, 103, 106, 110]
    );
    assert_eq!(at(0, 1), 105);
    assert_eq!((at(0, 2), at(1, 2)), (100, 110));
}

#[test]
fn clamp_orders_its_bounds() {
    assert_eq!(clamp(9, 5, 2), 5);
    assert_eq!(clamp(-9, 5, 2), 2);
    assert_eq!(clamp(3, 2, 5), 3);
}

fn parse_model(source: &str) -> (Option<Resolved>, Vec<crate::Diagnostic>) {
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    Resolved::parse(DiagramKind::Xychart, source, &removed)
}

fn scene_of(source: &str, profile: Profile) -> Result<Scene, String> {
    let (model, diagnostics) = parse_model(source);
    if !diagnostics.is_empty() {
        return Err(format!("rejected source: {diagnostics:?}"));
    }
    let input = model
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|e| e.to_string())?;
    let (scene, _) = layout(&input).map_err(|e| e.to_string())?;
    Ok(scene)
}

fn box_of<'a>(scene: &'a Scene, id: &str) -> Result<&'a SceneBox, String> {
    scene
        .boxes()
        .iter()
        .find(|b| b.id == id)
        .ok_or_else(|| format!("no box {id}"))
}

fn label_of<'a>(scene: &'a Scene, id: &str) -> Result<&'a SceneLabel, String> {
    scene
        .labels()
        .iter()
        .find(|l| l.id == id)
        .ok_or_else(|| format!("no label {id}"))
}

fn shown(label: &SceneLabel) -> bool {
    label.rect.w != 0 || label.rect.h != 0
}

fn frontmatter(config: &str) -> String {
    format!("---\nconfig:\n  xyChart:\n{config}---\nxychart\n")
}

#[test]
fn canvas_is_the_configured_size() -> Result<(), String> {
    let plain = "xychart\nbar [1]\n";
    let sized = format!(
        "{}bar [1]\n",
        frontmatter("    width: 1000\n    height: 320\n")
    );
    let cases = [
        (
            plain,
            Profile::Vector,
            Size {
                w: 700 * 64,
                h: 500 * 64,
            },
        ),
        (plain, Profile::Cell, Size { w: 88, h: 32 }),
        (
            &sized,
            Profile::Vector,
            Size {
                w: 1000 * 64,
                h: 320 * 64,
            },
        ),
        (&sized, Profile::Cell, Size { w: 125, h: 20 }),
    ];
    for (source, profile, want) in cases {
        assert_eq!(scene_of(source, profile)?.canvas(), want, "{profile:?}");
    }
    Ok(())
}

fn right(r: Rect) -> i64 {
    i64::from(r.x) + i64::from(r.w)
}

#[test]
fn bar_width_follows_the_outer_padding_rule() -> Result<(), String> {
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = scene_of("xychart\nx-axis [a, b]\nbar [1, 2]\n", profile)?;
        let plot = box_of(&scene, "plot")?.rect;
        let first = box_of(&scene, "p0.b0")?.rect;
        let second = box_of(&scene, "p0.b1")?.rect;
        let half = i64::from(first.w / 2);
        let outer = i64::from(first.x) + half - i64::from(plot.x);
        assert_eq!(outer, right(plot) - (i64::from(second.x) + half));
        let tick_distance = (i64::from(plot.w) - 2 * outer) / 2;
        let mut want = (2 * outer).min(tick_distance) * 950 / 1000;
        if profile == Profile::Cell {
            want = want.max(1);
        }
        assert_eq!(want, i64::from(first.w), "{profile:?}");
        assert_eq!(first.w, second.w);
    }
    Ok(())
}

#[test]
fn bars_raise_the_outer_padding_to_seventy_percent_of_a_tick() -> Result<(), String> {
    let source = format!(
        "{}x-axis [a, b]\nbar [1, 2]\n",
        frontmatter("    xAxis:\n      showLabel: false\n")
    );
    let scene = scene_of(&source, Profile::Vector)?;
    let plot = box_of(&scene, "plot")?.rect;
    let first = box_of(&scene, "p0.b0")?.rect;
    let outer = i64::from(first.x) + i64::from(first.w / 2) - i64::from(plot.x);
    assert_eq!(outer, i64::from(plot.w) / 2 * 700 / 2000);
    Ok(())
}

#[test]
fn line_boxes_cover_their_points_inside_the_plot() -> Result<(), String> {
    let scene = scene_of(
        "xychart\nx-axis [a, b, c]\nline [1, 5, 3]\n",
        Profile::Vector,
    )?;
    let plot = box_of(&scene, "plot")?.rect;
    let line = box_of(&scene, "p0")?;
    assert_eq!(line.parent, "plot");
    let r = line.rect;
    assert!(r.x >= plot.x && r.y >= plot.y);
    assert!(right(r) <= right(plot));
    assert!(i64::from(r.y) + i64::from(r.h) <= i64::from(plot.y) + i64::from(plot.h));
    assert!(r.w > 0 && r.h > 0);
    Ok(())
}

#[test]
fn values_outside_the_explicit_range_stay_inside_the_plot() -> Result<(), String> {
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = scene_of(
            "xychart\nx-axis [a, b]\ny-axis 0 --> 10\nbar [500, -500]\n",
            profile,
        )?;
        let plot = box_of(&scene, "plot")?.rect;
        for id in ["p0.b0", "p0.b1"] {
            let b = box_of(&scene, id)?.rect;
            assert!(b.y >= plot.y);
            assert!(b.y + b.h <= plot.y + plot.h);
        }
    }
    Ok(())
}

#[test]
fn absent_values_have_no_box_and_break_the_line() -> Result<(), String> {
    let scene = scene_of(
        "xychart\nx-axis [a, b, c]\nbar [1]\nline [1, 2, 3]\n",
        Profile::Vector,
    )?;
    let ids: Vec<&str> = scene.boxes().iter().map(|b| b.id.as_str()).collect();
    assert_eq!(ids, ["plot", "p0.b0", "p1"]);
    Ok(())
}

#[test]
fn horizontal_orientation_puts_categories_left_and_values_on_top() -> Result<(), String> {
    let scene = scene_of(
        "xychart horizontal\nx-axis [first, second]\ny-axis 0 --> 10\nbar [3, 7]\n",
        Profile::Vector,
    )?;
    let plot = box_of(&scene, "plot")?.rect;
    let category = label_of(&scene, "x.t0")?.rect;
    let value = label_of(&scene, "y.t0")?.rect;
    assert!(category.x + category.w < plot.x);
    assert!(value.y + value.h < plot.y + 1);
    assert!(plot.x <= box_of(&scene, "p0.b0")?.rect.x);
    let longer = box_of(&scene, "p0.b1")?.rect;
    let shorter = box_of(&scene, "p0.b0")?.rect;
    assert!(longer.w > shorter.w);
    assert_eq!(shorter.x, longer.x);
    Ok(())
}

#[test]
fn plot_keeps_an_edge_cell_on_a_one_row_cell_canvas() -> Result<(), String> {
    let source = format!("{}line [0]\n", frontmatter("    height: 1\n"));
    let scene = scene_of(&source, Profile::Cell)?;
    let plot = box_of(&scene, "plot")?.rect;
    assert_eq!((plot.h, scene.canvas().h), (1, 1));
    let line = box_of(&scene, "p0")?.rect;
    assert!(line.y >= plot.y && line.y + line.h <= plot.y + plot.h);
    assert_eq!(scene.validate().map_err(|e| e.to_string())?, None);
    Ok(())
}

#[test]
fn hidden_x_axis_labels_keep_zero_rectangles() -> Result<(), String> {
    let source = format!(
        "{}x-axis [a, b]\nbar [1, 2]\n",
        frontmatter("    xAxis:\n      showLabel: false\n")
    );
    let scene = scene_of(&source, Profile::Vector)?;
    assert!(!shown(label_of(&scene, "x.t0")?));
    assert!(shown(label_of(&scene, "y.t0")?));
    Ok(())
}

#[test]
fn chart_title_is_dropped_when_the_chart_is_too_short() -> Result<(), String> {
    let body = "title \"T\"\nbar [1]\n";
    let short = format!("{}{body}", frontmatter("    height: 40\n"));
    let tall = format!("{}{body}", frontmatter("    height: 500\n"));
    assert!(!shown(label_of(
        &scene_of(&short, Profile::Vector)?,
        "title"
    )?));
    assert!(shown(label_of(
        &scene_of(&tall, Profile::Vector)?,
        "title"
    )?));
    Ok(())
}

#[test]
fn plots_without_titles_get_numbered_legend_labels() -> Result<(), String> {
    let scene = scene_of(
        "xychart\nx-axis [a]\nbar [1]\nline \"Named\" [2]\nbar [3]\n",
        Profile::Vector,
    )?;
    assert_eq!(label_of(&scene, "legend.0")?.text, "Series 1");
    assert_eq!(label_of(&scene, "legend.1")?.text, "Named");
    assert_eq!(label_of(&scene, "legend.2")?.text, "Series 3");
    assert!(shown(label_of(&scene, "legend.0")?));
    Ok(())
}

#[test]
fn legend_that_does_not_fit_beside_the_plot_overlays_it() -> Result<(), String> {
    let source = format!(
        "{}x-axis [a]\nbar \"a very long series title indeed\" [1]\n",
        frontmatter("    width: 120\n")
    );
    let scene = scene_of(&source, Profile::Vector)?;
    let plot = box_of(&scene, "plot")?.rect;
    let legend = label_of(&scene, "legend.0")?;
    assert!(shown(legend));
    assert_eq!(right(plot), i64::from(scene.canvas().w));
    assert!(legend.rect.x >= 0);
    assert!(legend.rect.x < plot.x + plot.w);
    Ok(())
}

#[test]
fn legend_beside_the_plot_takes_its_width() -> Result<(), String> {
    let scene = scene_of("xychart\nx-axis [a]\nbar \"S\" [1]\n", Profile::Vector)?;
    let plot = box_of(&scene, "plot")?.rect;
    let legend = label_of(&scene, "legend.0")?;
    assert!(legend.rect.x >= plot.x + plot.w);
    assert!(plot.x + plot.w < scene.canvas().w);
    Ok(())
}

#[test]
fn tick_labels_of_the_cell_profile_never_overlap() -> Result<(), String> {
    let source = format!(
        "{}x-axis [a, b]\nbar [1, 2000]\n",
        frontmatter("    height: 40\n")
    );
    let scene = scene_of(&source, Profile::Cell)?;
    let mut rows = BTreeSet::new();
    for label in scene.labels() {
        if label.id.starts_with("y.t") && shown(label) {
            assert!(rows.insert(label.rect.y));
        }
    }
    assert!(!rows.is_empty());
    Ok(())
}

#[test]
fn overflowing_values_are_rejected() {
    assert!(scene_of("xychart\nx-axis [a]\nbar [99999999999]\n", Profile::Vector).is_err());
}

fn corpus_files() -> Result<Vec<PathBuf>, std::io::Error> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/xychart");
    let mut paths = Vec::new();
    for source in std::fs::read_dir(root)? {
        for file in std::fs::read_dir(source?.path())? {
            let path = file?.path();
            if path.extension().is_some_and(|ext| ext == "mmd") {
                paths.push(path);
            }
        }
    }
    paths.sort();
    assert!(!paths.is_empty());
    Ok(paths)
}

fn accepted(source: &str) -> bool {
    parse_model(source).1.is_empty()
}

fn assert_valid(path: &Path, source: &str, profile: Profile) -> Result<(), String> {
    let scene = scene_of(source, profile)?;
    let clause = scene.validate().map_err(|e| e.to_string())?;
    assert!(clause.is_none(), "{path:?} {profile:?}: {clause:?}");
    if profile == Profile::Cell {
        let rendered =
            crate::cells::render::render(&scene, &crate::cells::render::Options::default())
                .map_err(|e| e.to_string())?;
        assert_eq!(rendered.refused_clusters, 0, "{path:?}");
    }
    Ok(())
}

#[test]
fn corpus_scenes_are_valid() -> Result<(), String> {
    for path in corpus_files().map_err(|e| e.to_string())? {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        if !accepted(&source) {
            continue;
        }
        for profile in [Profile::Vector, Profile::Cell] {
            assert_valid(&path, &source, profile)?;
        }
    }
    Ok(())
}

fn series_used(scene: &Scene) -> BTreeSet<u8> {
    let mut used = BTreeSet::new();
    for group in scene.items() {
        for item in &group.items {
            let shape = match item {
                Item::Rect(r) => r.shape,
                Item::Path(p) => p.shape,
                _ => continue,
            };
            if matches!(shape.style, ShapeStyle::Series | ShapeStyle::SeriesLine) {
                used.insert(shape.series);
            }
        }
    }
    used
}

fn texts(scene: &Scene) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for group in scene.items() {
        for item in &group.items {
            if let Item::Text(TextItem { lines, .. }) = item {
                let flat: Vec<String> = lines
                    .iter()
                    .map(|line| line.iter().map(|run| run.text.as_str()).collect())
                    .collect();
                out.insert(flat.join("\n"));
            }
        }
    }
    out
}

fn plot_titles(source: &str) -> Vec<String> {
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    let parsed = crate::syntax::xychart::parse(source, &removed);
    let (model, _) = crate::model::xychart::resolve(source, &parsed.document);
    model.plots.into_iter().map(|plot| plot.title).collect()
}

#[test]
fn series_labels() -> Result<(), String> {
    for path in corpus_files().map_err(|e| e.to_string())? {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        if !accepted(&source) {
            continue;
        }
        let titles = plot_titles(&source);
        for profile in [Profile::Vector, Profile::Cell] {
            let scene = scene_of(&source, profile)?;
            let (used, labels) = (series_used(&scene), texts(&scene));
            assert_eq!(used.len(), titles.len().min(12), "{path:?}");
            for (i, title) in titles.iter().enumerate() {
                let series = u8::try_from(i % 12).unwrap_or(0);
                assert!(used.contains(&series), "{path:?} series {i}");
                assert!(
                    labels.contains(&super::series_title(i, title)),
                    "{path:?} {profile:?}: series {i} has no label"
                );
            }
        }
    }
    Ok(())
}
