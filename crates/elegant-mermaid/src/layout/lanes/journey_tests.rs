use super::journey_constants::constant;
use super::*;
use crate::geom::{contains, intersects};
use crate::layout::layered::LayoutError;
use crate::scene::{GroupRole, Item, PathCommand, Profile, ShapeStyle, TextRole};

const PROFILES: [Profile; 2] = [Profile::Vector, Profile::Cell];

fn line(profile: Profile) -> i32 {
    if profile == Profile::Cell { 1 } else { 1280 }
}

fn text(profile: Profile, w: i32, lines: i32) -> Text {
    Text {
        runs: Vec::new(),
        lines: vec!["t".to_owned()],
        w,
        h: lines * line(profile),
        role: TextRole::Label,
    }
}

fn konst(profile: Profile, name: &str) -> i32 {
    i32::try_from(constant(profile, name).unwrap()).unwrap()
}

fn task(id: &str, band: Option<usize>, score: i64, label: &Text) -> JourneyTask {
    JourneyTask {
        id: id.to_owned(),
        band,
        score,
        label: label.clone(),
        people: None,
    }
}

fn section(id: &str, label: &Text) -> JourneySection {
    JourneySection {
        id: id.to_owned(),
        label: label.clone(),
    }
}

fn fixture(profile: Profile) -> JourneyInput {
    let label = text(profile, 4, 1);
    JourneyInput {
        title: Some(JourneyTitle {
            id: "title".to_owned(),
            label: text(profile, 9, 1),
        }),
        sections: vec![section("s0", &label), section("s1", &label)],
        tasks: vec![
            task("t0", None, 2, &label),
            task("t1", Some(0), 5, &label),
            task("t2", Some(0), 1, &label),
            task("t3", Some(0), 3, &label),
            task("t4", Some(1), 4, &label),
        ],
        ..JourneyInput::default()
    }
}

fn plan(input: &JourneyInput, profile: Profile) -> JourneyResult {
    journey(input, profile).unwrap()
}

#[test]
fn task_columns_step_by_width_plus_gap() {
    for profile in PROFILES {
        let res = plan(&fixture(profile), profile);
        let width = konst(profile, "journey.task_width");
        let pitch = width + konst(profile, "journey.column_gap");
        for k in 1..res.tasks.len() {
            assert_eq!(res.tasks[k].x - res.tasks[k - 1].x, pitch);
            assert_eq!(res.tasks[k].y, res.tasks[0].y);
            assert_eq!(res.tasks[k].w, width);
        }
    }
}

#[test]
fn bands_span_their_tasks_at_the_top() {
    for profile in PROFILES {
        let res = plan(&fixture(profile), profile);
        let width = konst(profile, "journey.task_width");
        let gap = konst(profile, "journey.column_gap");
        assert_eq!(res.bands[0].x, res.tasks[1].x);
        assert_eq!(res.bands[0].w, 3 * width + 2 * gap);
        assert_eq!(res.bands[1].x, res.tasks[4].x);
        assert_eq!(res.bands[1].w, width);
        assert_eq!(res.bands[0].h, konst(profile, "journey.band_height"));
        assert_eq!(res.bands[0].y, res.bands[1].y);
        let step = konst(profile, "journey.score_step");
        assert_eq!(res.bands[0].y, res.title.y + res.title.h + step);
    }
}

#[test]
fn faces_sit_at_score_heights() {
    for profile in PROFILES {
        let input = fixture(profile);
        let res = plan(&input, profile);
        let step = konst(profile, "journey.score_step");
        let top = res.bands[0].y + res.bands[0].h;
        for (k, task) in input.tasks.iter().enumerate() {
            let score = i32::try_from(task.score).unwrap();
            assert_eq!(res.faces[k].y, top + (5 - score) * step + step);
            assert_eq!(res.faces[k].x, res.tasks[k].x + res.tasks[k].w / 2);
        }
        assert!(res.faces[1].y < res.faces[3].y);
        assert!(res.faces[3].y < res.faces[2].y);
        assert_eq!(res.tasks[0].y, top + (5 - 1 + 2) * step);
    }
}

#[test]
fn frames_enclose_band_and_tasks_and_never_overlap() {
    for profile in PROFILES {
        let res = plan(&fixture(profile), profile);
        for (b, members) in [vec![1, 2, 3], vec![4]].iter().enumerate() {
            let frame = res.frames[b];
            assert!(contains(frame, res.bands[b]).unwrap());
            for &k in members {
                assert!(contains(frame, res.tasks[k]).unwrap());
            }
        }
        assert!(!intersects(res.frames[0], res.frames[1]).unwrap());
    }
}

#[test]
fn task_without_band_has_no_frame() {
    let label = text(Profile::Cell, 4, 1);
    let input = JourneyInput {
        tasks: vec![task("t", None, 3, &label)],
        ..JourneyInput::default()
    };
    let res = plan(&input, Profile::Cell);
    assert!(res.frames.is_empty());
    assert_eq!(res.groups.len(), 1);
    assert_eq!(res.groups[0].role, GroupRole::Node);
}

#[test]
fn rejects_malformed_input() {
    let label = text(Profile::Vector, 4, 1);
    let tasks = |items: Vec<JourneyTask>| JourneyInput {
        tasks: items,
        ..JourneyInput::default()
    };
    let cases = [
        tasks(vec![task("t", None, 6, &label)]),
        tasks(vec![task("t", None, 0, &label)]),
        tasks(vec![task("t", Some(0), 3, &label)]),
        JourneyInput {
            sections: vec![section("s", &label)],
            ..JourneyInput::default()
        },
        JourneyInput {
            sections: vec![section("s", &label)],
            tasks: vec![
                task("a", Some(0), 3, &label),
                task("b", None, 3, &label),
                task("c", Some(0), 3, &label),
            ],
            ..JourneyInput::default()
        },
    ];
    for input in &cases {
        assert!(matches!(
            journey(input, Profile::Vector),
            Err(LayoutError::Domain)
        ));
    }
}

#[test]
fn tall_text_grows_band_and_cards() {
    let profile = Profile::Vector;
    let mut input = fixture(profile);
    let base = plan(&input, profile);
    input.tasks[1].people = Some(text(profile, 6, 1));
    input.sections[0].label = text(profile, 4, 5);
    let grown = plan(&input, profile);
    assert!(grown.bands[0].h > base.bands[0].h);
    assert!(grown.tasks[0].h > base.tasks[0].h);
    assert_eq!(grown.bands[0].h, grown.bands[1].h);
    assert_eq!(grown.tasks[0].h, grown.tasks[4].h);
    let pad = konst(profile, "node_pad_y") + konst(profile, "node_border");
    assert_eq!(grown.bands[0].h, 5 * line(profile) + 2 * pad);
    assert_eq!(grown.tasks[1].h, 2 * line(profile) + 2 * pad);
}

#[test]
fn canvas_is_extent_plus_margin_on_each_side() {
    for profile in PROFILES {
        let res = plan(&fixture(profile), profile);
        let margin = konst(profile, "canvas_margin");
        assert_eq!(res.title.x, margin);
        assert_eq!(res.title.y, margin);
        let last = *res.tasks.last().unwrap();
        assert_eq!(res.canvas.w, last.x + last.w + margin);
        assert_eq!(res.canvas.h, last.y + last.h + margin);
    }
}

fn first_shape(item: &Item) -> Option<(ShapeStyle, u8)> {
    match item {
        Item::RoundRect(round) => Some((round.shape.style, round.shape.series)),
        _ => None,
    }
}

#[test]
fn paint_order_and_styles() {
    let res = plan(&fixture(Profile::Vector), Profile::Vector);
    let roles: Vec<GroupRole> = res.groups.iter().map(|g| g.role).collect();
    let mut want = vec![GroupRole::Group; 2];
    want.extend([GroupRole::Node; 6]);
    assert_eq!(roles, want);
    assert_eq!(res.groups[1].owner, "s1");
    assert_eq!(
        first_shape(&res.groups[1].items[0]),
        Some((ShapeStyle::SeriesTint, 1))
    );
    assert_eq!(
        first_shape(&res.groups[3].items[0]).map(|shape| shape.0),
        Some(ShapeStyle::Node)
    );
    assert_eq!(
        first_shape(&res.groups[4].items[0]),
        Some((ShapeStyle::SeriesTint, 0))
    );
}

#[test]
fn face_expression_follows_the_score_midpoint() {
    let res = plan(&fixture(Profile::Vector), Profile::Vector);
    let sweep = |task: usize| match &res.groups[3 + task].items[4] {
        Item::Path(path) => match path.commands[1] {
            PathCommand::Arc { sweep, .. } => Some(sweep),
            _ => None,
        },
        _ => None,
    };
    assert_eq!(sweep(0), Some(-32768));
    assert_eq!(sweep(1), Some(32768));
    assert!(matches!(res.groups[3 + 3].items[4], Item::Polyline(_)));
}

#[test]
fn cell_face_is_one_ring_symbol() {
    let input = fixture(Profile::Cell);
    let res = plan(&input, Profile::Cell);
    let symbols: Vec<&str> = res
        .groups
        .iter()
        .flat_map(|group| &group.items)
        .filter_map(|item| match item {
            Item::SymbolRef(symbol) => Some(symbol.symbol.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(symbols.len(), input.tasks.len());
    assert!(symbols.iter().all(|name| *name == "ring"));
}

#[test]
fn overrides_replace_profile_defaults() {
    let mut input = fixture(Profile::Vector);
    input.task_width = 20000;
    input.column_gap = 1000;
    input.task_height = 5000;
    input.band_height = 4000;
    let res = plan(&input, Profile::Vector);
    assert_eq!(res.tasks[1].x - res.tasks[0].x, 21000);
    assert_eq!(res.tasks[0].w, 20000);
    assert_eq!(res.tasks[0].h, 5000);
    assert_eq!(res.bands[0].h, 4000);
}
