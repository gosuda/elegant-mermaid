use super::*;
use crate::diag::Severity;
use crate::layout::modeldump::model_dump;
use crate::model::Resolved;
use crate::syntax::preprocess::preprocess;

const SAMPLE: &str = "eventmodeling\n\
    tf 01 ui Cart.Screen\n\
    tf 02 cmd AddItem { id: 7 }\n\
    tf 03 evt ItemAdded [[ItemData]]\n\
    rf 04 evt External.Changed\n\
    tf 05 pcr Sync ->> 04\n\
    data ItemData {\n  item: 7\n  count: 1\n}\n";

fn input(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let removed = preprocess(source).removed;
    let (model, diagnostics) = Resolved::parse(crate::DiagramKind::Eventmodeling, source, &removed);
    if diagnostics.iter().any(|d| d.severity == Severity::Error) {
        return Err("source has errors");
    }
    model
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|_| "input failed")
}

#[test]
fn input_identifies_lanes_frames_and_relations() -> Result<(), &'static str> {
    let input = input(SAMPLE, Profile::Vector)?;
    assert_eq!(input.kind, "eventmodeling");
    assert_eq!(input.direction, Direction::Lr);
    let ids: Vec<&str> = input.boxes.iter().map(|b| b.id.as_str()).collect();
    assert_eq!(
        ids,
        [
            "lane0", "lane1", "lane100", "lane200", "lane201", "01", "02", "03", "04", "05"
        ]
    );
    let parents: Vec<&str> = input.boxes.iter().map(|b| b.parent.as_str()).collect();
    assert_eq!(
        parents,
        [
            "", "", "", "", "", "lane1", "lane100", "lane200", "lane201", "lane0"
        ]
    );
    let shapes: Vec<&str> = input.boxes.iter().map(|b| b.shape.as_str()).collect();
    assert_eq!(
        shapes,
        [
            "lane:0",
            "lane:1",
            "lane:100",
            "lane:200",
            "lane:201",
            "ui",
            "command",
            "event",
            "event",
            "processor"
        ]
    );
    for item in &input.boxes {
        assert_eq!(item.role == BoxRole::Node, item.exclusive, "{}", item.id);
    }
    let routes: Vec<String> = input
        .routes
        .iter()
        .map(|r| format!("{}:{}>{}", r.id, r.from, r.to))
        .collect();
    assert_eq!(routes, ["e0:01>02", "e1:02>03", "e2:04>05"]);
    for route in &input.routes {
        assert_eq!(route.marker_end, "point");
        assert!(!route.orthogonal);
    }
    let labels: Vec<String> = input
        .labels
        .iter()
        .map(|l| format!("{}={}", l.owner, l.text))
        .collect();
    assert_eq!(
        labels,
        [
            "lane0=UI/Automation",
            "lane1=UI/A: Cart",
            "lane100=Command/Read Model",
            "lane200=Events",
            "lane201=Stream: External"
        ]
    );
    Ok(())
}

#[test]
fn frame_text_carries_the_data_block() -> Result<(), &'static str> {
    let input = input(SAMPLE, Profile::Vector)?;
    let text = |id: &str| {
        input
            .boxes
            .iter()
            .find(|b| b.id == id)
            .map(|b| b.text.clone())
    };
    assert_eq!(text("01").as_deref(), Some("Screen"));
    assert_eq!(text("02").as_deref(), Some("AddItem\n\n id: 7"));
    assert_eq!(
        text("03").as_deref(),
        Some("ItemAdded\n\n  item: 7\n  count: 1")
    );
    Ok(())
}

#[test]
fn layout_measures_data_blocks_and_wraps_long_names() -> Result<(), &'static str> {
    let source = format!(
        "eventmodeling\ntf 01 cmd {} [[D]]\ntf 02 evt Plain\ndata D {{\n{}}}\n",
        "LongName".repeat(12),
        "  line\n".repeat(8)
    );
    for profile in [Profile::Vector, Profile::Cell] {
        let input = input(&source, profile)?;
        let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
        assert!(scene.check().map_err(|_| "validate failed")?, "{profile:?}");
        let height = |id: &str| scene.boxes().iter().find(|b| b.id == id).map(|b| b.rect.h);
        assert!(height("01") > height("02"));
    }
    Ok(())
}

#[test]
fn dumps_keep_model_identities() -> Result<(), &'static str> {
    for profile in [Profile::Vector, Profile::Cell] {
        let input = input(SAMPLE, profile)?;
        let model = model_dump(&input);
        let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
        assert_eq!(scene.boxes().len(), input.boxes.len());
        assert_eq!(scene.routes().len(), input.routes.len());
        assert_eq!(scene.labels().len(), input.labels.len());
        for (item, placed) in input.boxes.iter().zip(scene.boxes()) {
            assert_eq!(item.id, placed.id);
            assert!(model.contains(&format!("\"id\":\"{}\"", item.id)));
        }
        assert!(scene.labels().iter().all(|label| !label.lines.is_empty()));
    }
    Ok(())
}

#[test]
fn routes_between_unknown_frames_are_rejected() -> Result<(), &'static str> {
    let mut broken = input(SAMPLE, Profile::Cell)?;
    broken.routes.push(InputRoute {
        id: "bad".to_owned(),
        from: "01".to_owned(),
        to: "zz".to_owned(),
        orthogonal: false,
        marker_start: String::new(),
        marker_end: String::new(),
        line: String::new(),
        min_length: 1,
        from_side: None,
        to_side: None,
    });
    assert_eq!(layout(&broken).unwrap_err(), LayoutError::Domain);
    let mut stray = input(SAMPLE, Profile::Cell)?;
    stray.labels.push(InputLabel {
        id: "bad.label".to_owned(),
        owner: "01".to_owned(),
        role: TextRole::Label,
        text: "x".to_owned(),
    });
    assert_eq!(layout(&stray).unwrap_err(), LayoutError::Domain);
    Ok(())
}

fn random_source(seed: u32) -> String {
    let mut state = seed;
    let mut draw = |lo: u32, hi: u32| {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        lo + state % (hi - lo + 1)
    };
    let types = [
        "ui",
        "cmd",
        "command",
        "evt",
        "event",
        "pcr",
        "processor",
        "rmo",
        "readmodel",
    ];
    let mut out = String::from("eventmodeling\n");
    let count = draw(2, 12);
    for i in 0..count {
        let keyword = if draw(0, 3) == 0 { "rf" } else { "tf" };
        let mut name = format!("Name{i}");
        if draw(0, 2) == 0 {
            name = format!("ns{}.{name}", draw(0, 2));
        }
        if draw(0, 6) == 0 {
            name = "W".repeat(draw(10, 60) as usize);
        }
        let kind = types[draw(0, 8) as usize];
        out.push_str(&format!("{keyword} {:03} {kind} {name}", i + 1));
        if draw(0, 2) == 0 {
            for _ in 0..draw(1, 2) {
                out.push_str(&format!(" ->> {:03}", draw(1, count + 1)));
            }
        }
        if draw(0, 3) == 0 {
            out.push_str(&format!(" {{ k: v{i} }}"));
        }
        out.push('\n');
    }
    out
}

#[test]
fn random_layouts_satisfy_the_hard_constraints() -> Result<(), &'static str> {
    for seed in 1..=300 {
        let source = random_source(seed);
        for profile in [Profile::Vector, Profile::Cell] {
            let input = input(&source, profile)?;
            let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
            assert!(
                scene.check().map_err(|_| "validate failed")?,
                "seed {seed} {profile:?}\n{source}"
            );
        }
    }
    Ok(())
}
