use super::{chart_of, from_venn, regions, unzigzag, zigzag};
use crate::DiagramKind;
use crate::layout::families::layout;
use crate::layout::input::{Box as InputBox, Input, Label as InputLabel};
use crate::model::Resolved;
use crate::model::venn as mv;
use crate::scene::{
    BoxRole, Direction, DumpOptions, EllipseItem, Item, Profile, Scene, ShapeStyle, TextRole,
};
use crate::syntax::preprocess::preprocess;

type Check = Result<(), String>;

const RADIUS: i32 = 7168;
const SAMPLE: &str = "venn-beta\n  title Skills\n  set A[\"Alpha\"]:10\n    text one\n  set B:6\n  set C:4\n  union A,B[\"Shared\"]:3\n    text two\n  union B,C:1\n";

fn model_of(source: &str) -> Result<mv::Model, String> {
    let removed = preprocess(source).removed;
    let (model, diagnostics) = mv::parse_and_resolve(source, &removed);
    if diagnostics.is_empty() {
        Ok(model)
    } else {
        Err(format!("rejected source: {diagnostics:?}"))
    }
}

fn input_of(source: &str, profile: Profile) -> Result<Input, String> {
    let removed = preprocess(source).removed;
    let (resolved, diagnostics) = Resolved::parse(DiagramKind::Venn, source, &removed);
    if !diagnostics.is_empty() {
        return Err(format!("rejected source: {diagnostics:?}"));
    }
    resolved
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|e| e.to_string())
}

fn scene_of(source: &str, profile: Profile) -> Result<Scene, String> {
    let input = input_of(source, profile)?;
    layout(&input)
        .map(|(scene, _)| scene)
        .map_err(|e| e.to_string())
}

fn circles(scene: &Scene) -> Vec<EllipseItem> {
    scene
        .items()
        .iter()
        .flat_map(|group| &group.items)
        .filter_map(|item| match item {
            Item::Ellipse(e) => Some(*e),
            _ => None,
        })
        .collect()
}

#[test]
fn zigzag_round_trips_signed_values() {
    for value in [
        0,
        1,
        -1,
        2,
        -2,
        2_147_483_647,
        -2_147_483_647,
        1 << 40,
        -(1 << 40),
    ] {
        assert_eq!(unzigzag(zigzag(value)), value);
    }
}

#[test]
fn input_encodes_the_model() -> Check {
    let model = model_of(SAMPLE)?;
    assert_eq!(model.subsets.len(), 5);
    assert_eq!(model.subsets[4].sets, ["B", "C"]);
    assert!(model.subsets[4].display.is_empty());
    let chart = super::payload(&model);
    assert_eq!(chart.overlaps.len(), 2);
    assert_eq!(chart.overlaps[1].value, 1000);
    assert_eq!(chart.regions.len(), 1);
    assert_eq!(chart.regions[0].label, "Shared");
    assert_eq!(chart.regions[0].texts, ["two"]);
    let input =
        from_venn(&model, Profile::Vector, DumpOptions::default()).map_err(|e| e.to_string())?;
    assert_eq!(input.kind, "venn");
    let boxes: Vec<String> = input
        .boxes
        .iter()
        .map(|b| format!("{}<{}", b.id, b.parent))
        .collect();
    assert_eq!(
        boxes,
        [
            "venn<",
            "set0<venn",
            "set1<venn",
            "set2<venn",
            "region0<venn"
        ]
    );
    let labels: Vec<String> = input
        .labels
        .iter()
        .map(|l| format!("{}={}", l.id, l.text))
        .collect();
    assert_eq!(
        labels,
        [
            "title=Skills",
            "set0.label=Alpha",
            "set0.t0=one",
            "set1.label=B",
            "set2.label=C",
            "region0.label=Shared",
            "region0.t0=two",
        ]
    );
    let sets: Vec<Vec<usize>> = input
        .region_sets
        .iter()
        .map(|s| s.regions.clone())
        .collect();
    assert_eq!(
        sets,
        [
            vec![0, 20000],
            vec![0, 12000],
            vec![0, 8000],
            vec![1, 0, 1, 6000],
            vec![1, 1, 2, 2000],
            vec![2, 0, 1],
        ]
    );
    Ok(())
}

#[test]
fn chart_of_decodes_what_the_input_encodes() -> Check {
    let model = model_of(SAMPLE)?;
    let input =
        from_venn(&model, Profile::Vector, DumpOptions::default()).map_err(|e| e.to_string())?;
    let decoded = chart_of(&input);
    assert_eq!(decoded.title, "Skills");
    assert_eq!(decoded.sets.len(), 3);
    assert_eq!(decoded.sets[0].label, "Alpha");
    assert_eq!(decoded.sets[0].texts, ["one"]);
    assert_eq!(decoded.overlaps.len(), 2);
    assert_eq!(decoded.regions.len(), 1);
    assert_eq!(decoded.regions[0].texts, ["two"]);
    assert_eq!(regions(&decoded).len(), input.region_sets.len());
    Ok(())
}

#[test]
fn both_profiles_give_the_same_input_and_scene() -> Check {
    let vector = scene_of(SAMPLE, Profile::Vector)?;
    let cell = scene_of(SAMPLE, Profile::Cell)?;
    assert_eq!(cell.profile(), Profile::Vector);
    assert_eq!(vector.dump(), cell.dump());
    Ok(())
}

#[test]
fn layout_is_valid_and_has_one_box_per_plan_box() -> Check {
    let scene = scene_of(SAMPLE, Profile::Vector)?;
    let ids: Vec<&str> = scene.boxes().iter().map(|b| b.id.as_str()).collect();
    assert_eq!(ids, ["venn", "set0", "set1", "set2", "region0"]);
    assert!(
        scene
            .boxes()
            .iter()
            .all(|b| b.role == BoxRole::Node && !b.exclusive)
    );
    assert_eq!(scene.dump_part().options.direction, Direction::Tb);
    assert_eq!(scene.validate().map_err(|e| e.to_string())?, None);
    Ok(())
}

#[test]
fn zero_sets_lay_out_an_empty_canvas() -> Check {
    let input = Input {
        kind: "venn",
        profile: Profile::Vector,
        direction: Direction::Tb,
        options: DumpOptions::default(),
        boxes: vec![InputBox {
            icon: false,
            id: "A".into(),
            role: BoxRole::Node,
            shape: String::new(),
            parent: String::new(),
            exclusive: true,
            text: String::new(),
            direction: String::new(),
        }],
        routes: Vec::new(),
        labels: vec![InputLabel {
            id: "x".into(),
            owner: "A".into(),
            role: TextRole::Label,
            text: String::new(),
        }],
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: crate::layout::input::Spacing::default(),
    };
    let (scene, _) = layout(&input).map_err(|e| e.to_string())?;
    assert_eq!(scene.boxes().len(), 1);
    assert_eq!(scene.boxes()[0].id, "venn");
    Ok(())
}

#[test]
fn more_than_three_sets_are_refused() -> Check {
    let mut input = input_of(SAMPLE, Profile::Vector)?;
    let first = input.region_sets[0].clone();
    input.region_sets.push(first);
    assert!(layout(&input).is_err());
    Ok(())
}

#[test]
fn single_set_is_one_centred_circle() -> Check {
    let scene = scene_of("venn-beta\n  set A:7\n", Profile::Vector)?;
    let cs = circles(&scene);
    assert_eq!(cs.len(), 1);
    assert_eq!(
        (cs[0].cx, cs[0].cy, cs[0].rx),
        (2 * RADIUS, 2 * RADIUS, RADIUS)
    );
    assert_eq!(
        (scene.canvas().w, scene.canvas().h),
        (4 * RADIUS, 4 * RADIUS)
    );
    Ok(())
}

#[test]
fn title_adds_a_band_above_the_circles() -> Check {
    let plain = scene_of("venn-beta\n  set A\n", Profile::Vector)?;
    let titled = scene_of("venn-beta\n  title Hello\n  set A\n", Profile::Vector)?;
    let band = titled.canvas().h - plain.canvas().h;
    assert!(band > 0);
    assert_eq!(circles(&plain)[0].cy + band, circles(&titled)[0].cy);
    Ok(())
}

#[test]
fn two_set_distance_follows_the_overlap() -> Check {
    let distance = |overlap: &str| -> Result<i32, String> {
        let source = format!("venn-beta\n  set A:10\n  set B:10\n  union A,B:{overlap}\n");
        let cs = circles(&scene_of(&source, Profile::Vector)?);
        assert_eq!(cs.len(), 2);
        Ok(cs[1].cx - cs[0].cx)
    };
    assert_eq!(distance("0")?, 2 * RADIUS);
    assert_eq!(distance("10")?, 0);
    let (disjoint, half, nearly) = (distance("1")?, distance("5")?, distance("9")?);
    assert!(half < disjoint);
    assert!(nearly < half);
    assert!(nearly > 0);
    Ok(())
}

#[test]
fn three_sets_use_the_fixed_arrangement() -> Check {
    let scene = scene_of(
        "venn-beta\n  set A:10\n  set B:10\n  set C:10\n",
        Profile::Vector,
    )?;
    let cs = circles(&scene);
    assert_eq!(cs.len(), 3);
    let at = |i: usize| (cs[i].cx, cs[i].cy);
    assert_eq!(at(0), (2 * RADIUS, RADIUS));
    assert_eq!(at(1), (2 * RADIUS + 6207, 2 * RADIUS + 3584));
    assert_eq!(at(2), (2 * RADIUS - 6207, 2 * RADIUS + 3584));
    Ok(())
}

#[test]
fn radii_follow_the_square_root_of_the_sizes() -> Check {
    let scene = scene_of("venn-beta\n  set A:4\n  set B:1\n", Profile::Vector)?;
    let cs = circles(&scene);
    assert_eq!((cs[0].rx, cs[1].rx), (RADIUS, RADIUS / 2));
    assert!(cs.iter().all(|c| c.rx == c.ry));
    Ok(())
}

#[test]
fn circles_are_series_tints_in_set_order() -> Check {
    let scene = scene_of(SAMPLE, Profile::Vector)?;
    for (i, c) in circles(&scene).iter().enumerate() {
        assert_eq!(usize::from(c.shape.series), i);
        assert_eq!(c.shape.style, ShapeStyle::SeriesTint);
    }
    Ok(())
}

#[test]
fn canvas_size_comes_from_the_config() -> Check {
    let scene = scene_of(
        "---\nconfig:\n  venn:\n    width: 400\n    height: 400\n---\nvenn-beta\n  set A\n",
        Profile::Vector,
    )?;
    assert_eq!(scene.canvas().w, 4 * 64 * 100);
    Ok(())
}

#[test]
fn oversized_values_are_refused() -> Check {
    let input = input_of("venn-beta\n  set A:99999999999\n", Profile::Vector);
    assert!(input.is_err());
    Ok(())
}

#[test]
fn small_canvas_keeps_measured_labels() -> Check {
    let scene = scene_of(
        "---\nconfig:\n  venn:\n    width: 4\n    height: 4\n---\nvenn-beta\nset A\nset B\nunion A,B[Z]\n",
        Profile::Vector,
    )?;
    assert_eq!(scene.boxes().len(), 4);
    assert_eq!(scene.labels().len(), 3);
    assert_eq!(scene.validate().map_err(|e| e.to_string())?, None);
    let canvas = scene.canvas();
    for (i, label) in scene.labels().iter().enumerate() {
        let r = label.rect;
        assert!(r.x >= 0 && r.y >= 0);
        assert!(i64::from(r.x) + i64::from(r.w) <= i64::from(canvas.w));
        assert!(i64::from(r.y) + i64::from(r.h) <= i64::from(canvas.h));
        for earlier in &scene.labels()[..i] {
            let b = earlier.rect;
            assert!(!(r.x < b.x + b.w && b.x < r.x + r.w && r.y < b.y + b.h && b.y < r.y + r.h));
        }
    }
    Ok(())
}
