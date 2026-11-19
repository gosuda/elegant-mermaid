use super::*;
use crate::diag::Severity;
use crate::model::Resolved;
use crate::scene::{GroupRole, Item};
use crate::syntax::preprocess::preprocess;

const SAMPLE: &str = "timeline\n\
    title History\n\
    1 : first : second\n\
    section Early\n\
    2 : third\n\
    \x20 : fourth\n\
    3\n\
    section Late\n\
    4 : fifth\n";

fn input(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let removed = preprocess(source).removed;
    let (model, diagnostics) = Resolved::parse(crate::DiagramKind::Timeline, source, &removed);
    if diagnostics.iter().any(|d| d.severity == Severity::Error) {
        return Err("source has errors");
    }
    model
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|_| "input failed")
}

#[test]
fn input_encodes_the_model() -> Result<(), &'static str> {
    let input = input(SAMPLE, Profile::Vector)?;
    assert_eq!(input.direction, Direction::Lr);
    let boxes: Vec<String> = input
        .boxes
        .iter()
        .map(|b| format!("{}|{}|{}", b.id, b.shape, b.text))
        .collect();
    assert_eq!(
        boxes,
        [
            "title|title|History",
            "s0|section|Early",
            "s1|section|Late",
            "p0|period|1",
            "p0.e0|event|first",
            "p0.e1|event|second",
            "p1|period:0|2",
            "p1.e0|event|third",
            "p1.e1|event|fourth",
            "p2|period:0|3",
            "p3|period:1|4",
            "p3.e0|event|fifth",
        ]
    );
    let routes: Vec<String> = input
        .routes
        .iter()
        .map(|r| format!("{}|{}>{}|{}", r.id, r.from, r.to, r.line))
        .collect();
    assert_eq!(
        routes,
        [
            "e0|p0>p0.e0|dotted",
            "e1|p0.e0>p0.e1|dotted",
            "e2|p1>p1.e0|dotted",
            "e3|p1.e0>p1.e1|dotted",
            "e4|p3>p3.e0|dotted",
        ]
    );
    Ok(())
}

#[test]
fn vertical_fans_every_event_from_its_period() -> Result<(), &'static str> {
    let input = input("timeline TD\np : a : b : c\n", Profile::Cell)?;
    assert_eq!(input.direction, Direction::Tb);
    let routes: Vec<String> = input
        .routes
        .iter()
        .map(|r| format!("{}>{}", r.from, r.to))
        .collect();
    assert_eq!(routes, ["p0>p0.e0", "p0>p0.e1", "p0>p0.e2"]);
    Ok(())
}

#[test]
fn ids_stay_unique() -> Result<(), &'static str> {
    let input = input(
        "timeline\ntitle title\nsection s0\np0 : p0.e0 : e0\n",
        Profile::Cell,
    )?;
    let mut seen = std::collections::BTreeSet::new();
    for b in &input.boxes {
        assert_ne!(b.text, b.id);
        assert!(seen.insert(b.id.clone()), "{}", b.id);
    }
    for r in &input.routes {
        assert!(seen.insert(r.id.clone()), "{}", r.id);
    }
    Ok(())
}

#[test]
fn layout_satisfies_the_hard_constraints() -> Result<(), &'static str> {
    let long = "a very long section name that has to wrap over several lines of the band";
    for source in [
        SAMPLE.to_owned(),
        SAMPLE.replacen("timeline\n", "timeline TD\n", 1),
        "timeline\n".to_owned(),
        "timeline\ntitle only\n".to_owned(),
        "timeline\nsection empty\nsection also empty\n".to_owned(),
        format!("timeline\nsection {long}\n1 : x\n"),
        format!("timeline TD\nsection {long}\n1 : x : y\n"),
        format!("timeline\n2002 : {}\n", "wide ".repeat(40)),
        "timeline\n: orphan\n1\n".to_owned(),
    ] {
        for profile in [Profile::Vector, Profile::Cell] {
            let removed = preprocess(&source).removed;
            let (model, _) = Resolved::parse(crate::DiagramKind::Timeline, &source, &removed);
            let input = model
                .ok_or("no model")?
                .input(profile, DumpOptions::default())
                .map_err(|_| "input failed")?;
            let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
            let clause = scene.validate().map_err(|_| "validate failed")?;
            assert!(clause.is_none(), "{source:?} {profile:?}: {clause:?}");
        }
    }
    Ok(())
}

#[test]
fn rejects_malformed_input() {
    let base = || Input {
        kind: KIND,
        profile: Profile::Vector,
        direction: Direction::Lr,
        options: DumpOptions::default(),
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    };
    let shaped = |id: &str, shape: &str| card_box(id, shape, "");
    let cases: Vec<(&str, Vec<InputBox>, Vec<InputRoute>)> = vec![
        ("unknown shape", vec![shaped("x", "bar")], Vec::new()),
        (
            "bad section index",
            vec![shaped("p", "period:x")],
            Vec::new(),
        ),
        (
            "section out of set",
            vec![shaped("p", "period:3")],
            Vec::new(),
        ),
        ("event first", vec![shaped("e", "event")], Vec::new()),
        (
            "unlinked event",
            vec![shaped("p", "period"), shaped("e", "event")],
            Vec::new(),
        ),
        (
            "stray route",
            vec![shaped("p", "period")],
            vec![InputRoute {
                id: "r".to_owned(),
                from: "p".to_owned(),
                to: "q".to_owned(),
                orthogonal: true,
                marker_start: String::new(),
                marker_end: String::new(),
                line: "dotted".to_owned(),
                min_length: 1,
                from_side: None,
                to_side: None,
            }],
        ),
    ];
    for (name, boxes, routes) in cases {
        let mut malformed = base();
        malformed.boxes = boxes;
        malformed.routes = routes;
        assert!(
            matches!(layout(&malformed), Err(LayoutError::Domain)),
            "{name}"
        );
    }
}

#[test]
fn cell_scene_draws_sections_and_events_as_rects_and_periods_as_round_rects()
-> Result<(), &'static str> {
    let (scene, _) = layout(&input(SAMPLE, Profile::Cell)?).map_err(|_| "layout failed")?;
    let mut rects = 0;
    let mut rounds = 0;
    for group in scene.items().iter().filter(|g| g.role == GroupRole::Node) {
        for item in &group.items {
            match item {
                Item::Rect(_) => rects += 1,
                Item::RoundRect(_) => rounds += 1,
                _ => {}
            }
        }
    }
    assert!(rects > 0);
    assert!(rounds > 0);
    Ok(())
}
