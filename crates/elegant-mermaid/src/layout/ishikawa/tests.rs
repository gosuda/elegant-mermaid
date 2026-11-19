use std::collections::BTreeMap;

use super::KIND;
use crate::DiagramKind;
use crate::geom::{Rect, Size};
use crate::layout::families::layout;
use crate::layout::input::{Box, Input, Route, Spacing};
use crate::layout::layered::LayoutError;
use crate::layout::modeldump::model_dump;
use crate::model::Resolved;
use crate::scene::{
    BoxRole, Direction, DumpOptions, GroupRole, Item, Limits, MarkerAxis, Profile, Scene,
};

const DEMO: &str =
    "ishikawa-beta\n  Blurry Photo\n    Process\n      Out of focus\n      Shaky\n    User\n";
const PROFILES: [Profile; 2] = [Profile::Vector, Profile::Cell];

fn input_of(src: &str, profile: Profile, options: DumpOptions) -> Result<Input, &'static str> {
    let pre = crate::syntax::preprocess::preprocess(src);
    let (model, diagnostics) = Resolved::parse(DiagramKind::Ishikawa, src, &pre.removed);
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

#[test]
fn model_dump_names_boxes_anchors_and_routes() -> Result<(), &'static str> {
    let dump = model_dump(&input_of(DEMO, Profile::Vector, DumpOptions::default())?);
    for needle in [
        r#"{"id":"n0","role":"node","parent":"","exclusive":true,"shape":"effect"}"#,
        r#"{"id":"n3","role":"node","parent":"","exclusive":true,"shape":"cause:2"}"#,
        r#"{"id":"a0","role":"node","parent":"","exclusive":false,"shape":"anchor"}"#,
        r#"{"id":"e0","from":"a0","to":"n0","orthogonal":true,"marker_end":"none"}"#,
        r#"{"id":"e1","from":"a1","to":"n1","orthogonal":false,"marker_start":"point","marker_end":"none"}"#,
        r#"{"id":"e3","from":"a3","to":"n3","orthogonal":true,"marker_start":"point","marker_end":"none"}"#,
        r#"{"id":"n2.label","owner":"n2","text":"Out of focus","lines":[]}"#,
    ] {
        assert!(dump.contains(needle), "{needle} missing from {dump}");
    }
    assert_eq!(dump.matches(r#""role":"node""#).count(), 10);
    Ok(())
}

#[test]
fn layout_keeps_anchors_on_route_starts() -> Result<(), &'static str> {
    for profile in PROFILES {
        let scene = scene_of(DEMO, profile)?;
        assert_eq!(scene.boxes().len(), 10);
        for (k, route) in scene.routes().iter().enumerate() {
            let anchor = &scene.boxes()[5 + k];
            assert_eq!(route.from, anchor.id);
            let start = route.points[0];
            assert_eq!(
                anchor.rect,
                Rect {
                    x: start.x,
                    y: start.y,
                    w: 0,
                    h: 0
                }
            );
            assert!(!anchor.exclusive);
            assert_eq!(scene.boxes()[k].id, route.to);
        }
    }
    Ok(())
}

#[test]
fn spine_ends_on_the_head_and_ribs_meet_the_spine() -> Result<(), &'static str> {
    for profile in PROFILES {
        let scene = scene_of(DEMO, profile)?;
        let spine = &scene.routes()[0].points;
        let head = scene.boxes()[0].rect;
        assert_eq!(head.x, spine[1].x);
        assert_eq!(spine[0].y, spine[1].y);
        let centre = f64::from(head.y) + f64::from(head.h) / 2.0;
        assert!((centre - f64::from(spine[1].y)).abs() <= 1.0);
        assert_eq!(spine[0].y, scene.routes()[1].points[0].y);
        assert_eq!(spine[0].y, scene.routes()[4].points[0].y);
        assert!(scene.routes()[1].points[1].y < spine[0].y);
        assert!(scene.routes()[4].points[1].y > spine[0].y);
    }
    Ok(())
}

#[test]
fn profiles_share_identities() -> Result<(), &'static str> {
    let vector = scene_of(DEMO, Profile::Vector)?;
    let cell = scene_of(DEMO, Profile::Cell)?;
    let ids = |s: &Scene| -> (Vec<String>, Vec<(String, String, bool)>) {
        (
            s.boxes().iter().map(|b| b.id.clone()).collect(),
            s.routes()
                .iter()
                .map(|r| (r.id.clone(), r.from.clone(), r.orthogonal))
                .collect(),
        )
    };
    assert_eq!(ids(&vector), ids(&cell));
    Ok(())
}

#[test]
fn effect_only_has_no_routes() -> Result<(), &'static str> {
    for profile in PROFILES {
        let scene = scene_of("ishikawa-beta\n  Problem\n", profile)?;
        assert_eq!(scene.boxes().len(), 1);
        assert!(scene.routes().is_empty());
        assert_eq!(scene.items().len(), 1);
    }
    Ok(())
}

#[test]
fn header_only_is_an_empty_canvas() -> Result<(), &'static str> {
    let scene = scene_of("ishikawa-beta\n", Profile::Cell)?;
    assert!(scene.boxes().is_empty());
    assert_eq!(scene.canvas(), Size { w: 2, h: 2 });
    Ok(())
}

#[test]
fn scene_draws_arrows_toward_the_spine() -> Result<(), &'static str> {
    let scene = scene_of(DEMO, Profile::Cell)?;
    let edge = scene
        .items()
        .iter()
        .find(|g| g.owner == "e1")
        .ok_or("no e1 group")?;
    assert_eq!(edge.items.len(), 2);
    let Item::MarkerRef(marker) = &edge.items[1] else {
        return Err("no marker");
    };
    assert_eq!(marker.marker.as_str(), "point");
    assert_eq!(marker.at, scene.routes()[1].points[0]);
    assert_eq!(marker.axis, MarkerAxis::PlusY);
    let spine = scene
        .items()
        .iter()
        .find(|g| g.owner == "e0")
        .ok_or("no e0 group")?;
    assert_eq!(spine.items.len(), 1);
    Ok(())
}

#[test]
fn only_head_and_causes_are_outlined() -> Result<(), &'static str> {
    let scene = scene_of(DEMO, Profile::Vector)?;
    let items: BTreeMap<&str, usize> = scene
        .items()
        .iter()
        .filter(|g| g.role == GroupRole::Node)
        .map(|g| (g.owner.as_str(), g.items.len()))
        .collect();
    let want: BTreeMap<&str, usize> = [("n0", 2), ("n1", 2), ("n2", 1), ("n3", 1), ("n4", 2)]
        .into_iter()
        .collect();
    assert_eq!(items, want);
    Ok(())
}

#[test]
fn wraps_long_labels_without_breaking_clearance() -> Result<(), &'static str> {
    let src = format!(
        "ishikawa-beta\n  A problem with a rather long effect statement that wraps\n    Category with a long caption {}\n      sub cause {}\n      second\n",
        "word ".repeat(20),
        "longer ".repeat(15)
    );
    for profile in PROFILES {
        let scene = scene_of(&src, profile)?;
        assert!(scene.boxes()[2].rect.h > scene.boxes()[3].rect.h);
    }
    Ok(())
}

#[test]
fn limits_reject_oversized_models() -> Result<(), &'static str> {
    let mut source = String::from("ishikawa-beta\n  e\n");
    for i in 0..5 {
        source.push_str(&format!("    c{i}\n"));
    }
    let options = DumpOptions {
        limits: Limits {
            max_nodes: 3,
            ..Limits::default()
        },
        ..DumpOptions::default()
    };
    let input = input_of(&source, Profile::Vector, options)?;
    assert!(layout(&input).is_err());
    Ok(())
}

fn bare(boxes: &[(&str, &str)], routes: &[(&str, &str, &str)]) -> Input {
    Input {
        kind: KIND,
        profile: Profile::Cell,
        direction: Direction::Tb,
        options: DumpOptions::default(),
        boxes: boxes
            .iter()
            .map(|(id, shape)| Box {
                id: (*id).to_owned(),
                role: BoxRole::Node,
                shape: (*shape).to_owned(),
                icon: false,
                parent: String::new(),
                exclusive: false,
                text: String::new(),
                direction: String::new(),
            })
            .collect(),
        routes: routes
            .iter()
            .map(|(id, from, to)| Route {
                id: (*id).to_owned(),
                from: (*from).to_owned(),
                to: (*to).to_owned(),
                orthogonal: false,
                marker_start: String::new(),
                marker_end: String::new(),
                line: "normal".to_owned(),
                min_length: 0,
                from_side: None,
                to_side: None,
            })
            .collect(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    }
}

#[test]
fn rejects_inputs_it_did_not_build() {
    let cases = [
        ("no effect", bare(&[("n0", "cause:1")], &[])),
        (
            "bad depth",
            bare(&[("n0", "effect"), ("n1", "cause:x")], &[]),
        ),
        (
            "depth gap",
            bare(&[("n0", "effect"), ("n1", "cause:2")], &[]),
        ),
        (
            "stray route",
            bare(&[("n0", "effect")], &[("e0", "a0", "n0")]),
        ),
        (
            "label last",
            bare(&[("a0", "anchor"), ("n0", "effect")], &[]),
        ),
        (
            "wrong anchor",
            bare(
                &[
                    ("n0", "effect"),
                    ("n1", "cause:1"),
                    ("x", "anchor"),
                    ("a1", "anchor"),
                ],
                &[("e0", "a1", "n0")],
            ),
        ),
    ];
    for (name, input) in cases {
        let got = super::layout(&input);
        assert!(
            matches!(got, Err(LayoutError::Domain)),
            "{name}: {:?}",
            got.map(|(s, _)| s.canvas())
        );
    }
}

#[test]
fn corpus_lays_out_and_validates() -> Result<(), String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/ishikawa");
    let mut checked = 0usize;
    for source in std::fs::read_dir(&root).map_err(|e| e.to_string())? {
        let dir = source.map_err(|e| e.to_string())?.path();
        for entry in std::fs::read_dir(&dir).map_err(|e| e.to_string())? {
            let text = std::fs::read_to_string(entry.map_err(|e| e.to_string())?.path())
                .map_err(|e| e.to_string())?;
            for profile in PROFILES {
                scene_of(&text, profile).map_err(String::from)?;
            }
            checked += 1;
        }
    }
    assert!(checked > 0, "corpus/ishikawa holds no file");
    Ok(())
}

struct Words {
    state: u32,
}

impl Words {
    fn draw(&mut self, n: usize) -> usize {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 17;
        self.state ^= self.state << 5;
        usize::try_from(self.state).unwrap_or(0) % n
    }
}

fn random_ishikawa(seed: u32) -> String {
    const WORDS: [&str; 12] = [
        "amber", "birch", "cedar", "delta", "ember", "fjord", "garnet", "harbor", "iris",
        "juniper", "kelp", "lumen",
    ];
    let mut w = Words { state: seed };
    let mut out = String::from("ishikawa-beta\n  effect ");
    out.push_str(WORDS[w.draw(WORDS.len())]);
    out.push('\n');
    let mut depth = 1usize;
    let lines = 1 + w.draw(30);
    for _ in 0..lines {
        depth = 1 + w.draw((depth + 1).min(6));
        out.push_str(&" ".repeat(2 + 2 * depth));
        for _ in 0..1 + w.draw(5) {
            out.push_str(WORDS[w.draw(WORDS.len())]);
            out.push(' ');
        }
        out.push('\n');
    }
    out
}

#[test]
fn random_diagrams_validate() -> Result<(), &'static str> {
    for seed in 1..=150 {
        let src = random_ishikawa(seed);
        for profile in PROFILES {
            scene_of(&src, profile)?;
        }
    }
    Ok(())
}

#[test]
fn routes_hold_orthogonal_flags_per_depth() -> Result<(), &'static str> {
    let scene = scene_of(DEMO, Profile::Cell)?;
    let flags: Vec<bool> = scene.routes().iter().map(|r| r.orthogonal).collect();
    assert_eq!(flags, [true, false, true, true, false]);
    Ok(())
}
