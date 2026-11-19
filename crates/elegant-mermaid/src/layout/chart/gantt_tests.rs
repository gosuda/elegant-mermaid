use std::path::{Path, PathBuf};

use crate::DiagramKind;
use crate::geom::{Rect, Size};
use crate::layout::families::layout;
use crate::model::Resolved;
use crate::scene::{
    DumpOptions, GroupRole, Item, Profile, Scene, SceneBox, SceneLabel, ShapeStyle,
};

type Check = Result<(), String>;

const ONE_ROW: i32 = 1536;
const BAR: i32 = 1280;
const TOP: i32 = 3200;
const PLOT_LEFT: i32 = 4800;
const PLOT_WIDTH: i32 = 67200;

fn parse_model(source: &str) -> (Option<Resolved>, Vec<crate::Diagnostic>) {
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    Resolved::parse(DiagramKind::Gantt, source, &removed)
}

fn has_error(diagnostics: &[crate::Diagnostic]) -> bool {
    diagnostics
        .iter()
        .any(|d| d.severity == crate::Severity::Error)
}

fn laid_out(
    source: &str,
    profile: Profile,
) -> Result<(Scene, Vec<crate::diag::Diagnostic>), String> {
    let (model, diagnostics) = parse_model(source);
    if has_error(&diagnostics) {
        return Err(format!("rejected source: {diagnostics:?}"));
    }
    let input = model
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|e| e.to_string())?;
    layout(&input).map_err(|e| e.to_string())
}

fn scene_of(source: &str, profile: Profile) -> Result<Scene, String> {
    Ok(laid_out(source, profile)?.0)
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

fn label_texts(scene: &Scene, prefix: &str) -> Vec<String> {
    scene
        .labels()
        .iter()
        .filter(|l| l.id.starts_with(prefix))
        .map(|l| l.text.clone())
        .collect()
}

fn bands(scene: &Scene) -> Vec<Rect> {
    scene
        .items()
        .iter()
        .filter(|g| g.role == GroupRole::Decor)
        .flat_map(|g| &g.items)
        .filter_map(|item| match item {
            Item::Rect(r) if r.shape.style == ShapeStyle::Band => Some(r.rect),
            _ => None,
        })
        .collect()
}

fn corpus_files() -> Result<Vec<PathBuf>, std::io::Error> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/gantt");
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

fn assert_valid(path: &Path, source: &str, profile: Profile) -> Check {
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
fn corpus_scenes_are_valid() -> Check {
    for path in corpus_files().map_err(|e| e.to_string())? {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        if has_error(&parse_model(&source).1) {
            continue;
        }
        for profile in [Profile::Vector, Profile::Cell] {
            assert_valid(&path, &source, profile)?;
        }
    }
    Ok(())
}

#[test]
fn vector_geometry_follows_the_time_scale() -> Check {
    let source =
        "gantt\ndateFormat YYYY-MM-DD\nsection A\nOne :a, 2014-01-01, 30d\nTwo :after a, 10d\n";
    let s = scene_of(source, Profile::Vector)?;
    let rect = |x, y, w, h| Rect { x, y, w, h };
    assert_eq!(
        box_of(&s, "plot")?.rect,
        rect(0, TOP, 76800, 2 * ONE_ROW + ONE_ROW)
    );
    assert_eq!(box_of(&s, "s0")?.rect, rect(0, TOP, 76800, ONE_ROW));
    assert_eq!(
        box_of(&s, "t0")?.rect,
        rect(PLOT_LEFT, TOP + ONE_ROW, PLOT_WIDTH * 30 / 40, BAR)
    );
    assert_eq!(
        box_of(&s, "t1")?.rect,
        rect(
            PLOT_LEFT + PLOT_WIDTH * 30 / 40,
            TOP + 2 * ONE_ROW,
            PLOT_WIDTH * 10 / 40,
            BAR
        )
    );
    assert_eq!(
        s.canvas(),
        Size {
            w: 76800,
            h: TOP + 3 * ONE_ROW + TOP
        }
    );
    Ok(())
}

#[test]
fn auto_ticks_use_a_two_day_step() -> Check {
    let s = scene_of(
        "gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, 30d\n",
        Profile::Vector,
    )?;
    let ticks = label_texts(&s, "x.t");
    assert_eq!(ticks.len(), 16);
    assert_eq!(ticks[..3], ["2014-01-01", "2014-01-03", "2014-01-05"]);
    assert_eq!(ticks[15], "2014-01-31");
    Ok(())
}

#[test]
fn explicit_week_ticks_honour_the_weekday() -> Check {
    let source = "gantt\ndateFormat YYYY-MM-DD\nweekday monday\ntickInterval 2week\nOne :a, 2014-01-01, 30d\n";
    let s = scene_of(source, Profile::Vector)?;
    assert_eq!(label_texts(&s, "x.t"), ["2014-01-13", "2014-01-27"]);
    let s = scene_of(&source.replacen("2week", "1week", 1), Profile::Vector)?;
    assert_eq!(
        label_texts(&s, "x.t"),
        ["2014-01-06", "2014-01-13", "2014-01-20", "2014-01-27"]
    );
    Ok(())
}

#[test]
fn an_excluded_weekend_is_one_band() -> Check {
    let s = scene_of(
        "gantt\ndateFormat YYYY-MM-DD\nexcludes weekends\nOne :a, 2014-01-03, 3d\n",
        Profile::Vector,
    )?;
    let day = PLOT_WIDTH / 5;
    assert_eq!(
        bands(&s),
        [Rect {
            x: PLOT_LEFT + day,
            y: TOP,
            w: 2 * day,
            h: ONE_ROW
        }]
    );
    Ok(())
}

#[test]
fn a_bar_ends_before_trailing_excluded_days() -> Check {
    let s = scene_of(
        "gantt\ndateFormat YYYY-MM-DD\nexcludes weekends\nOne :a, 2014-01-03, 1d\nTwo :b, 2014-01-03, 3d\n",
        Profile::Vector,
    )?;
    let (one, two) = (box_of(&s, "t0")?.rect, box_of(&s, "t1")?.rect);
    assert_eq!((one.x, two.x), (PLOT_LEFT, PLOT_LEFT));
    assert!(one.w < two.w);
    assert_eq!(one.w, PLOT_WIDTH / 5);
    Ok(())
}

#[test]
fn milestone_and_vertical_marker_geometry() -> Check {
    let source = "gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, 10d\nMark :milestone, m, 2014-01-06, 0d\nLine :vert, v, 2014-01-11, 0d\n";
    let s = scene_of(source, Profile::Vector)?;
    let mark = box_of(&s, "t1")?.rect;
    assert_eq!((mark.w, mark.h), (BAR, BAR));
    assert_eq!(mark.x, PLOT_LEFT + PLOT_WIDTH / 2 - 640);
    let vert = box_of(&s, "t2")?.rect;
    assert_eq!(vert.w, 128);
    assert_eq!(vert.x, PLOT_LEFT + PLOT_WIDTH - 64);
    assert_eq!(vert.h, 2 * ONE_ROW);
    assert_eq!(label_texts(&s, "t"), ["One", "Mark", "Line"]);
    assert!(label_of(&s, "t2.label")?.rect.y > s.canvas().h - TOP);
    Ok(())
}

#[test]
fn tag_styles_follow_the_precedence() -> Check {
    let source = "gantt\ndateFormat YYYY-MM-DD\nsection S\nA :crit, done, 2014-01-01, 1d\nB :done, active, 2014-01-02, 1d\nC :active, 2014-01-03, 1d\nD :2014-01-04, 1d\n";
    let s = scene_of(source, Profile::Vector)?;
    let styles: Vec<ShapeStyle> = s
        .items()
        .iter()
        .filter(|g| g.role == GroupRole::Node && g.owner.starts_with('t'))
        .flat_map(|g| &g.items)
        .filter_map(|item| match item {
            Item::Rect(r) if r.shape.style != ShapeStyle::Plate => Some(r.shape.style),
            _ => None,
        })
        .collect();
    assert_eq!(
        styles,
        [
            ShapeStyle::Error,
            ShapeStyle::Success,
            ShapeStyle::Note,
            ShapeStyle::Series
        ]
    );
    Ok(())
}

#[test]
fn a_cell_top_axis_keeps_the_title_row_free() -> Check {
    let s = scene_of(
        "gantt\ntitle T\ndateFormat YYYY-MM-DD\ntopAxis\nOne :a, 2014-01-01, 30d\n",
        Profile::Cell,
    )?;
    assert!(!label_texts(&s, "xt.t").is_empty());
    for label in s.labels().iter().filter(|l| l.id.starts_with("xt.t")) {
        if !label.lines.is_empty() {
            assert_eq!(label.rect.y, 1);
        }
    }
    let rendered = crate::cells::render::render(&s, &crate::cells::render::Options::default())
        .map_err(|e| e.to_string())?;
    assert_eq!(rendered.refused_clusters, 0);
    Ok(())
}

#[test]
fn the_tick_budget_raises_one_diagnostic() -> Check {
    let (_, diagnostics) = laid_out(
        "gantt\ndateFormat YYYY-MM-DD\nOne :a, 0001-01-01, 90000y\n",
        Profile::Vector,
    )?;
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "layout/budget-exhausted");
    Ok(())
}

#[test]
fn an_empty_diagram_lays_out() -> Check {
    for profile in [Profile::Vector, Profile::Cell] {
        let s = scene_of("gantt\ntitle Empty\n", profile)?;
        assert!(s.validate().map_err(|e| e.to_string())?.is_none());
        assert_eq!(label_texts(&s, "x.t")[0], "1970-01-01");
    }
    Ok(())
}

#[test]
fn config_pixels_beyond_the_model_bound_are_rejected() -> Check {
    let source = "gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, 1d\n";
    let (model, diagnostics) = parse_model(source);
    assert!(!has_error(&diagnostics), "{diagnostics:?}");
    let mut input = model
        .ok_or("no model")?
        .input(Profile::Vector, DumpOptions::default())
        .map_err(|e| e.to_string())?;
    input.options.config.insert(
        "topPadding".to_owned(),
        crate::scene::DumpValue::Integer(99_999_999),
    );
    assert!(matches!(
        layout(&input),
        Err(crate::error::RenderError::Overflow)
    ));
    Ok(())
}
