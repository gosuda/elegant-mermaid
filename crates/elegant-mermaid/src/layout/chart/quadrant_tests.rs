use std::path::{Path, PathBuf};

use super::{NO_POINT_RADIUS, Quadrant, QuadrantPoint, quadrant_skeleton};
use crate::DiagramKind;
use crate::geom::{Rect, floor_div};
use crate::layout::families::layout;
use crate::model::Resolved;
use crate::scene::{DumpOptions, Item, Profile, Scene};

type Check = Result<(), String>;

fn parse_model(source: &str) -> (Option<Resolved>, Vec<crate::Diagnostic>) {
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    Resolved::parse(DiagramKind::Quadrant, source, &removed)
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

fn rect_of(scene: &Scene, id: &str) -> Result<Rect, String> {
    scene
        .boxes()
        .iter()
        .find(|b| b.id == id)
        .map(|b| b.rect)
        .ok_or_else(|| format!("no box {id}"))
}

fn ellipses(scene: &Scene) -> Vec<(i32, i32, i32, i32)> {
    scene
        .items()
        .iter()
        .flat_map(|group| group.items.iter())
        .filter_map(|item| match item {
            Item::Ellipse(e) => Some((e.cx, e.cy, e.rx, e.ry)),
            _ => None,
        })
        .collect()
}

fn corpus_files() -> Result<Vec<PathBuf>, std::io::Error> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/quadrant");
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
    Ok(paths)
}

#[test]
fn corpus_scenes_are_valid() -> Check {
    let mut accepted = 0;
    for path in corpus_files().map_err(|e| e.to_string())? {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        if !parse_model(&source).1.is_empty() {
            continue;
        }
        accepted += 1;
        for profile in [Profile::Vector, Profile::Cell] {
            let scene = scene_of(&source, profile)?;
            let clause = scene.validate().map_err(|e| e.to_string())?;
            assert!(clause.is_none(), "{path:?} {profile:?}: {clause:?}");
            if profile == Profile::Cell {
                let rendered =
                    crate::cells::render::render(&scene, &crate::cells::render::Options::default())
                        .map_err(|e| e.to_string())?;
                assert_eq!(rendered.refused_clusters, 0, "{path:?}");
            }
        }
    }
    assert!(accepted > 20);
    Ok(())
}

#[test]
fn tiles_partition_the_plot() -> Check {
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = scene_of(
            "quadrantChart\n  x-axis A --> B\n  y-axis C --> D\n  quadrant-1 one\n",
            profile,
        )?;
        let plot = rect_of(&scene, "plot")?;
        let tiles: Vec<Rect> = ["q1", "q2", "q3", "q4"]
            .iter()
            .map(|id| rect_of(&scene, id))
            .collect::<Result<_, _>>()?;
        let area: i64 = tiles.iter().map(|r| i64::from(r.w) * i64::from(r.h)).sum();
        assert_eq!(area, i64::from(plot.w) * i64::from(plot.h), "{profile:?}");
        for (i, a) in tiles.iter().enumerate() {
            for b in &tiles[..i] {
                assert!(!crate::geom::intersects(*a, *b).map_err(|e| e.to_string())?);
            }
        }
        let [q1, q2, q3, q4] = tiles[..] else {
            return Err("four tiles".into());
        };
        assert!(q1.x > q2.x && q1.y == q2.y);
        assert!(q3.x == q2.x && q3.y > q2.y);
        assert!(q4.x == q1.x && q4.y == q3.y);
    }
    Ok(())
}

#[test]
fn vector_points_follow_the_unit_square() -> Check {
    let scene = scene_of(
        "quadrantChart\n  A: [0, 0]\n  B: [1, 1]\n  C: [0.5, 0.25]\n",
        Profile::Vector,
    )?;
    let plot = rect_of(&scene, "plot")?;
    let (x, y, w, h) = (
        i64::from(plot.x),
        i64::from(plot.y),
        i64::from(plot.w),
        i64::from(plot.h),
    );
    let want = [
        (x, y + h),
        (x + w, y),
        (
            x + floor_div(500 * w, 1000),
            y + h - floor_div(250 * h, 1000),
        ),
    ];
    let dots = ellipses(&scene);
    assert_eq!(dots.len(), 3);
    for ((cx, cy, rx, ry), (wx, wy)) in dots.into_iter().zip(want) {
        assert_eq!((i64::from(cx), i64::from(cy)), (wx, wy));
        assert_eq!((rx, ry), (320, 320));
    }
    Ok(())
}

#[test]
fn cell_points_stay_inside_the_frame() -> Check {
    let scene = scene_of("quadrantChart\n  A: [0, 0]\n  B: [1, 1]\n", Profile::Cell)?;
    let plot = rect_of(&scene, "plot")?;
    for (cx, cy, _, _) in ellipses(&scene) {
        assert!(cx > plot.x && cx < plot.x + plot.w - 1);
        assert!(cy > plot.y && cy < plot.y + plot.h - 1);
    }
    Ok(())
}

#[test]
fn config_sets_the_canvas() -> Check {
    let source = "%%{init: {\"quadrantChart\": {\"chartWidth\": 800, \"chartHeight\": 600}}}%%\nquadrantChart\n  A: [0.5, 0.5]\n";
    let vector = scene_of(source, Profile::Vector)?;
    assert_eq!((vector.canvas().w, vector.canvas().h), (800 * 64, 600 * 64));
    let cell = scene_of(source, Profile::Cell)?;
    assert_eq!((cell.canvas().w, cell.canvas().h), (100, 38));
    Ok(())
}

#[test]
fn labels_avoid_dividers_in_cells() -> Check {
    let source = "quadrantChart\n  title T\n  x-axis Low --> High\n  y-axis Low --> High\n  Centre point label: [0.5, 0.5]\n  Wide label near the edge: [0.95, 0.9]\n";
    let scene = scene_of(source, Profile::Cell)?;
    let rendered = crate::cells::render::render(&scene, &crate::cells::render::Options::default())
        .map_err(|e| e.to_string())?;
    assert_eq!(rendered.refused_clusters, 0);
    assert!(scene.labels().iter().all(|label| !label.lines.is_empty()));
    Ok(())
}

#[test]
fn a_chart_without_labels_still_lays_out() -> Check {
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = scene_of("quadrantChart\n", profile)?;
        assert!(scene.labels().is_empty());
        assert_eq!(scene.boxes().len(), 5);
        assert!(scene.validate().map_err(|e| e.to_string())?.is_none());
    }
    Ok(())
}

#[test]
fn skeleton_lists_the_ids_of_the_laid_out_dump() {
    let quadrant = Quadrant {
        title: "T".into(),
        tiles: ["a".into(), String::new(), "c".into(), String::new()],
        x_left: "l".into(),
        points: vec![QuadrantPoint {
            x: 1,
            y: 2,
            radius: NO_POINT_RADIUS,
            label: "p".into(),
        }],
        ..Quadrant::default()
    };
    let skeleton = quadrant_skeleton(&quadrant);
    let boxes: Vec<&str> = skeleton.boxes.iter().map(|b| b.id.as_str()).collect();
    let labels: Vec<&str> = skeleton.labels.iter().map(|l| l.id.as_str()).collect();
    assert_eq!(boxes, ["plot", "q1", "q2", "q3", "q4", "p0"]);
    assert_eq!(
        labels,
        ["title", "x.left", "q1.label", "q3.label", "p0.label"]
    );
}
