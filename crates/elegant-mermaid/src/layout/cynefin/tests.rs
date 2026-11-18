use std::path::Path;

use super::layout;
use crate::cells::{self, Options};
use crate::model::Resolved;
use crate::scene::{DumpOptions, Item, Profile, Scene, SceneBox};
use crate::{DiagramKind, Severity};

type Check = Result<(), String>;

const FULL: &str = "cynefin-beta\n  title Sorting\n  complex\n  \"probe\"\n  \"sense\"\n  complicated\n  \"analyse\"\n  clear\n  \"categorise\"\n  chaotic\n  \"act\"\n  confusion\n  \"unknown\"\n  complex --> complicated : \"learned\"\n  clear --> chaotic\n";

fn scene_of(source: &str, profile: Profile) -> Result<Scene, String> {
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    let (model, diagnostics) = Resolved::parse(DiagramKind::Cynefin, source, &removed);
    if let Some(error) = diagnostics.iter().find(|d| d.severity == Severity::Error) {
        return Err(format!("rejected source: {}", error.message));
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

fn text_contents(scene: &Scene) -> Vec<String> {
    scene
        .items()
        .iter()
        .flat_map(|group| group.items.iter())
        .filter_map(|item| match item {
            Item::Text(text) => Some(
                text.lines
                    .iter()
                    .map(|line| line.iter().map(|run| run.text.as_str()).collect::<String>())
                    .collect::<Vec<_>>()
                    .join("\n"),
            ),
            _ => None,
        })
        .collect()
}

#[test]
fn corpus_scenes_are_valid() -> Check {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/cynefin");
    let mut count = 0;
    for dir in std::fs::read_dir(root).map_err(|e| e.to_string())? {
        let dir = dir.map_err(|e| e.to_string())?.path();
        for file in std::fs::read_dir(dir).map_err(|e| e.to_string())? {
            let path = file.map_err(|e| e.to_string())?.path();
            let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
            for profile in [Profile::Vector, Profile::Cell] {
                let scene = scene_of(&source, profile)?;
                assert_eq!(scene.check(), Ok(true), "{path:?} {profile:?}");
                if profile == Profile::Cell {
                    let result =
                        cells::render(&scene, &Options::default()).map_err(|e| e.to_string())?;
                    assert_eq!(result.refused_clusters, 0, "{path:?}");
                }
            }
            count += 1;
        }
    }
    assert!(count >= 15);
    Ok(())
}

#[test]
fn domain_boxes_stay_inside_their_quadrant() -> Check {
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = scene_of(FULL, profile)?;
        let (hw, hh) = (scene.canvas().w / 2, scene.canvas().h / 2);
        let complex = box_of(&scene, "complex")?.rect;
        let complicated = box_of(&scene, "complicated")?.rect;
        let clear = box_of(&scene, "clear")?.rect;
        let chaotic = box_of(&scene, "chaotic")?.rect;
        assert!(complex.x + complex.w <= hw && complex.y + complex.h <= hh);
        assert!(complicated.x >= hw && complicated.y + complicated.h <= hh);
        assert!(clear.x >= hw && clear.y >= hh);
        assert!(chaotic.x + chaotic.w <= hw && chaotic.y >= hh);
    }
    Ok(())
}

#[test]
fn confusion_sits_on_the_centre() -> Check {
    let scene = scene_of(FULL, Profile::Vector)?;
    let confusion = box_of(&scene, "confusion")?.rect;
    let centre = confusion.x + confusion.w / 2;
    assert!((centre - scene.canvas().w / 2).abs() <= 1);
    Ok(())
}

#[test]
fn domain_order_keeps_declarations_then_adds_missing() -> Check {
    let scene = scene_of("cynefin-beta\nchaotic\n\"x\"\ncomplex\n", Profile::Vector)?;
    let ids: Vec<&str> = scene.boxes().iter().map(|b| b.id.as_str()).collect();
    assert_eq!(
        ids,
        [
            "frame",
            "chaotic",
            "complex",
            "complicated",
            "clear",
            "confusion"
        ]
    );
    Ok(())
}

#[test]
fn transitions_become_orthogonal_routes_and_self_loops_are_dropped() -> Check {
    let scene = scene_of(FULL, Profile::Vector)?;
    assert_eq!(scene.routes().len(), 2);
    assert!(
        scene
            .routes()
            .iter()
            .all(|r| r.orthogonal && r.points.len() >= 2)
    );
    assert_eq!(scene.routes()[0].from, "complex");
    assert_eq!(scene.routes()[1].to, "chaotic");
    let texts = text_contents(&scene);
    for want in ["learned", "Sorting", "Confusion"] {
        assert!(texts.iter().any(|t| t == want), "{want}");
    }
    let looped = scene_of(
        "cynefin-beta\ncomplex --> complex\ncomplex --> clear\n",
        Profile::Vector,
    )?;
    assert_eq!(looped.routes().len(), 1);
    Ok(())
}

#[test]
fn fold_is_deterministic_per_seed_and_straight_without_amplitude() -> Check {
    let with = |config: &str| {
        scene_of(
            &format!("---\nconfig:\n  cynefin:\n{config}---\n{FULL}"),
            Profile::Vector,
        )
    };
    let a = with("    seed: 7\n")?;
    let b = with("    seed: 7\n")?;
    let c = with("    seed: 8\n")?;
    assert_eq!(a, b);
    assert_ne!(a, c);
    let straight = with("    boundaryAmplitude: 0\n")?;
    assert_eq!(straight.check(), Ok(true));
    Ok(())
}

#[test]
fn canvas_follows_config_in_each_profile() -> Check {
    let source = "---\nconfig:\n  cynefin:\n    width: 640\n    height: 480\n---\ncynefin-beta\n";
    let vector = scene_of(source, Profile::Vector)?;
    assert_eq!((vector.canvas().w, vector.canvas().h), (640 * 64, 480 * 64));
    let cell = scene_of(source, Profile::Cell)?;
    assert_eq!((cell.canvas().w, cell.canvas().h), (80, 30));
    Ok(())
}

#[test]
fn canvas_grows_to_hold_overflow() -> Check {
    let mut source = String::from(
        "---\nconfig:\n  cynefin:\n    width: 200\n    height: 120\n---\ncynefin-beta\ncomplex\n",
    );
    for _ in 0..12 {
        source.push_str("\"a very long item label that overflows the quadrant\"\n");
    }
    let scene = scene_of(&source, Profile::Vector)?;
    let complex = box_of(&scene, "complex")?.rect;
    assert!(complex.y + complex.h <= scene.canvas().h);
    assert!(scene.canvas().h > 120 * 64);
    assert_eq!(scene.check(), Ok(true));
    Ok(())
}

const DENSE: &str = "cynefin-beta\n  complex\n  \"alpha\"\n  complicated\n  \"beta\"\n  clear\n  \"gamma\"\n  chaotic\n  \"delta\"\n  confusion\n  \"epsilon\"\n  complex --> clear : \"diagonal one\"\n  complicated --> chaotic : \"diagonal two\"\n  clear --> complex\n  chaotic --> complicated\n  complex --> confusion : \"in\"\n  confusion --> clear : \"out\"\n";

fn route_hits_box(points: &[crate::geom::Point], rect: crate::geom::Rect) -> bool {
    points.windows(2).any(|pair| {
        let (a, b) = (pair[0], pair[1]);
        a.x.min(b.x) <= rect.x + rect.w
            && a.x.max(b.x) >= rect.x
            && a.y.min(b.y) <= rect.y + rect.h
            && a.y.max(b.y) >= rect.y
    })
}

#[test]
fn routes_avoid_the_other_domain_boxes() -> Check {
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = scene_of(DENSE, profile)?;
        assert_eq!(scene.routes().len(), 6);
        for route in scene.routes() {
            for b in scene.boxes() {
                if b.id == "frame" || b.id == route.from || b.id == route.to {
                    continue;
                }
                assert!(
                    !route_hits_box(&route.points, b.rect),
                    "{profile:?} route {} crosses box {}",
                    route.id,
                    b.id
                );
            }
        }
    }
    Ok(())
}

#[test]
fn dense_cell_render_keeps_every_label() -> Check {
    let scene = scene_of(DENSE, Profile::Cell)?;
    let result = cells::render(&scene, &Options::default()).map_err(|e| e.to_string())?;
    assert_eq!(result.refused_clusters, 0);
    let rows: Vec<Vec<char>> = result.text.lines().map(|r| r.chars().collect()).collect();
    for label in scene.labels() {
        let (x, y, w) = (
            label.rect.x as usize,
            label.rect.y as usize,
            label.rect.w as usize,
        );
        let row = rows.get(y).ok_or("label row is missing")?;
        let printed: String = row.iter().skip(x).take(w).collect();
        assert_eq!(printed, label.lines.concat(), "label {}", label.id);
    }
    Ok(())
}

#[test]
fn route_labels_avoid_domain_boxes() -> Check {
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = scene_of(DENSE, profile)?;
        for label in scene.labels().iter().filter(|l| l.id.starts_with('e')) {
            for b in scene.boxes().iter().filter(|b| b.id != "frame") {
                let (l, r) = (label.rect, b.rect);
                let apart =
                    l.x + l.w <= r.x || r.x + r.w <= l.x || l.y + l.h <= r.y || r.y + r.h <= l.y;
                assert!(
                    apart,
                    "{profile:?} label {} overlaps box {}",
                    label.id, b.id
                );
            }
        }
    }
    Ok(())
}

#[test]
fn odd_frame_quadrants_tile_without_overlap() -> Check {
    let source = "---\nconfig:\n  cynefin:\n    width: 801\n    height: 609\n---\ncynefin-beta\n";
    for (profile, w, h) in [
        (Profile::Vector, 801 * 64, 609 * 64),
        (Profile::Cell, 101, 39),
    ] {
        let scene = scene_of(source, profile)?;
        let decor = scene.items().first().ok_or("missing decor")?;
        let bands: Vec<_> = decor
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Rect(item) => Some(item.rect),
                _ => None,
            })
            .take(4)
            .collect();
        assert_eq!(bands.len(), 4);
        let (near_w, near_h) = (w / 2, h / 2);
        let expected = [
            (0, 0, near_w, near_h),
            (near_w, 0, w - near_w, near_h),
            (near_w, near_h, w - near_w, h - near_h),
            (0, near_h, near_w, h - near_h),
        ];
        for (rect, expected) in bands.iter().zip(expected) {
            assert_eq!((rect.x, rect.y, rect.w, rect.h), expected);
        }
        let area: i64 = bands.iter().map(|r| i64::from(r.w) * i64::from(r.h)).sum();
        assert_eq!(area, i64::from(w) * i64::from(h));
    }
    Ok(())
}
