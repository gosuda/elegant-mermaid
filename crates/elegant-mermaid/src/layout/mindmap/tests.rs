use crate::DiagramKind;
use crate::geom::{Point, Rect, Size, polyline_hits_rect};
use crate::layout::families::layout;
use crate::layout::input::Input;
use crate::layout::modeldump::model_dump;
use crate::model::Resolved;
use crate::scene::{DumpOptions, Limits, Profile, Scene};

const DEMO: &str = "mindmap\n  root((Root))\n    A\n      A1\n    B[Square]\n    C\n";

fn input_of(src: &str, profile: Profile, options: DumpOptions) -> Result<Input, &'static str> {
    let pre = crate::syntax::preprocess::preprocess(src);
    let (model, diagnostics) = Resolved::parse(DiagramKind::Mindmap, src, &pre.removed);
    if !diagnostics.is_empty() {
        return Err("source has diagnostics");
    }
    model
        .ok_or("no model")?
        .input(profile, options)
        .map_err(|_| "input failed")
}

fn scene_of(src: &str, profile: Profile) -> Result<Scene, &'static str> {
    let input = input_of(src, profile, DumpOptions::default())?;
    let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
    let violated = scene.validate().map_err(|_| "validate failed")?;
    assert!(violated.is_none(), "{violated:?}");
    Ok(scene)
}

fn rects(scene: &Scene) -> Vec<Rect> {
    scene.boxes().iter().map(|b| b.rect).collect()
}

fn points(scene: &Scene) -> Vec<Vec<Point>> {
    scene.routes().iter().map(|r| r.points.clone()).collect()
}

fn r(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn p(x: i32, y: i32) -> Point {
    Point { x, y }
}

#[test]
fn cell_geometry() -> Result<(), &'static str> {
    let scene = scene_of(DEMO, Profile::Cell)?;
    assert_eq!(scene.canvas(), Size { w: 35, h: 9 });
    assert_eq!(
        rects(&scene),
        [
            r(13, 3, 6, 3),
            r(23, 1, 3, 3),
            r(30, 1, 4, 3),
            r(1, 3, 8, 3),
            r(23, 5, 3, 3)
        ]
    );
    assert_eq!(
        points(&scene),
        [
            vec![p(19, 4), p(21, 4), p(21, 2), p(23, 2)],
            vec![p(26, 2), p(30, 2)],
            vec![p(13, 4), p(9, 4)],
            vec![p(19, 4), p(21, 4), p(21, 6), p(23, 6)],
        ]
    );
    Ok(())
}

#[test]
fn vector_geometry() -> Result<(), &'static str> {
    let scene = scene_of(DEMO, Profile::Vector)?;
    assert_eq!(scene.canvas(), Size { w: 21614, h: 8448 });
    assert_eq!(
        rects(&scene),
        [
            r(7955, 2944, 3272, 2560),
            r(13787, 1024, 1932, 2560),
            r(18279, 1024, 2311, 2560),
            r(1024, 2944, 4371, 2560),
            r(13787, 4864, 1941, 2560)
        ]
    );
    assert_eq!(
        points(&scene),
        [
            vec![
                p(11227, 4224),
                p(12507, 4224),
                p(12507, 2304),
                p(13787, 2304)
            ],
            vec![p(15719, 2304), p(18279, 2304)],
            vec![p(7955, 4224), p(5395, 4224)],
            vec![
                p(11227, 4224),
                p(12507, 4224),
                p(12507, 6144),
                p(13787, 6144)
            ],
        ]
    );
    Ok(())
}

#[test]
fn model_dump_names_boxes_routes_and_labels() -> Result<(), &'static str> {
    let dump = model_dump(&input_of(DEMO, Profile::Vector, DumpOptions::default())?);
    for needle in [
        r#"{"id":"n0","role":"node","parent":"","exclusive":true,"shape":"mindmapCircle"}"#,
        r#"{"id":"n3","role":"node","parent":"","exclusive":true}"#,
        r#"{"id":"e2","from":"n0","to":"n3","orthogonal":true,"marker_end":"none"}"#,
        r#"{"id":"n3.label","owner":"n3","text":"Square","lines":[]}"#,
    ] {
        assert!(dump.contains(needle), "{needle} missing from {dump}");
    }
    assert_eq!(dump.matches(r#""role":"node""#).count(), 5);
    Ok(())
}

#[test]
fn profiles_share_identities() -> Result<(), &'static str> {
    let vector = scene_of(DEMO, Profile::Vector)?;
    let cell = scene_of(DEMO, Profile::Cell)?;
    let ids = |s: &Scene| -> (Vec<String>, Vec<(String, String)>) {
        (
            s.boxes().iter().map(|b| b.id.clone()).collect(),
            s.routes()
                .iter()
                .map(|r| (r.id.clone(), r.from.clone()))
                .collect(),
        )
    };
    assert_eq!(ids(&vector), ids(&cell));
    Ok(())
}

#[test]
fn config_overrides_apply_to_the_vector_profile_only() -> Result<(), &'static str> {
    let long = "a long label that wraps past the maximum width of the node";
    let configured = format!(
        "---\nconfig:\n  mindmap:\n    padding: 20\n    maxNodeWidth: 100\n---\nmindmap\n  root\n    {long}\n"
    );
    let plain = format!("mindmap\n  root\n    {long}\n");
    let vector = scene_of(&configured, Profile::Vector)?;
    assert!(vector.boxes()[1].rect.w <= 100 * 64);
    assert_eq!(vector.boxes()[0].rect.h, 2 * 20 * 64 + 1280);
    let baseline = scene_of(&plain, Profile::Vector)?;
    assert_ne!(baseline.boxes()[0].rect.h, vector.boxes()[0].rect.h);
    let cell = scene_of(&configured, Profile::Cell)?;
    assert_eq!(scene_of(&plain, Profile::Cell)?.canvas(), cell.canvas());
    Ok(())
}

#[test]
fn limits_reject_oversized_models() -> Result<(), &'static str> {
    let source = "mindmap\n  root\n    n0\n    n1\n    n2\n    n3\n    n4\n";
    let options = DumpOptions {
        limits: Limits {
            max_nodes: 3,
            ..Limits::default()
        },
        ..DumpOptions::default()
    };
    let input = input_of(source, Profile::Vector, options)?;
    assert!(layout(&input).is_err());
    Ok(())
}

#[test]
fn routes_stay_off_foreign_boxes() -> Result<(), &'static str> {
    let mut source = String::from("mindmap\n  root\n");
    for i in 0..4 {
        source.push_str(&format!(
            "    wide branch number {i} with a long caption\n      x\n        y\n      zz\n    s\n      t\n"
        ));
    }
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = scene_of(&source, profile)?;
        for route in scene.routes() {
            for b in scene.boxes() {
                if b.id == route.from || b.id == route.to {
                    continue;
                }
                let hit = polyline_hits_rect(&route.points, b.rect).map_err(|_| "geometry")?;
                assert!(!hit, "route {} crosses {}", route.id, b.id);
            }
        }
    }
    Ok(())
}
