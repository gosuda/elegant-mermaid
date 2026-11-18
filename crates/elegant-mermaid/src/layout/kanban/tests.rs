use crate::DiagramKind;
use crate::error::RenderError;
use crate::geom::{GeomError, Rect, Size};
use crate::layout::families::layout;
use crate::layout::input::{Box as InputBox, Input, Route as InputRoute, Spacing};
use crate::layout::modeldump::model_dump;
use crate::model::Resolved;
use crate::scene::{
    Align, BoxRole, Direction, DumpOptions, DumpValue, GroupRole, Item, Limits, Profile, Scene,
    ShapeStyle, TextItem,
};

const DEMO: &str = "kanban\n  todo[To Do]\n    a[Task A]@{ ticket: T1, assigned: me, priority: High }\n    b[Task B]\n  done[Done]\n";

fn input_of(src: &str, profile: Profile, options: DumpOptions) -> Result<Input, &'static str> {
    let pre = crate::syntax::preprocess::preprocess(src);
    let (model, diagnostics) = Resolved::parse(DiagramKind::Kanban, src, &pre.removed);
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

fn r(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn texts(scene: &Scene) -> Vec<&TextItem> {
    scene
        .items()
        .iter()
        .flat_map(|group| &group.items)
        .filter_map(|item| match item {
            Item::Text(text) => Some(text),
            _ => None,
        })
        .collect()
}

fn joined(text: &TextItem) -> Vec<String> {
    text.lines
        .iter()
        .map(|line| line.iter().map(|run| run.text.as_str()).collect())
        .collect()
}

#[test]
fn cell_geometry() -> Result<(), &'static str> {
    let scene = scene_of(DEMO, Profile::Cell)?;
    assert_eq!(scene.canvas(), Size { w: 53, h: 16 });
    assert_eq!(
        rects(&scene),
        [
            r(1, 1, 25, 14),
            r(1, 3, 24, 6),
            r(1, 10, 24, 3),
            r(27, 1, 25, 5)
        ]
    );
    let ids: Vec<&str> = scene.boxes().iter().map(|b| b.id.as_str()).collect();
    assert_eq!(ids, ["s0", "s0.c0", "s0.c1", "s1"]);
    assert_eq!(scene.boxes()[1].parent, "s0");
    assert!(scene.boxes()[1].exclusive);
    assert!(!scene.boxes()[0].exclusive);
    assert_eq!(scene.boxes()[0].role, BoxRole::Group);
    Ok(())
}

#[test]
fn cell_scene() -> Result<(), &'static str> {
    let scene = scene_of(DEMO, Profile::Cell)?;
    let groups = scene.items();
    assert_eq!(groups.len(), 4);
    let roles: Vec<GroupRole> = groups.iter().map(|g| g.role).collect();
    assert_eq!(
        roles,
        [
            GroupRole::Group,
            GroupRole::Group,
            GroupRole::Node,
            GroupRole::Node
        ]
    );
    let owners: Vec<&str> = groups.iter().map(|g| g.owner.as_str()).collect();
    assert_eq!(owners, ["s0", "s1", "s0.c0", "s0.c1"]);
    let Some(Item::RoundRect(frame)) = groups[2].items.first() else {
        return Err("card frame");
    };
    assert_eq!(frame.shape.style, ShapeStyle::Node);
    let Some(Item::Text(text)) = groups[2].items.get(1) else {
        return Err("card text");
    };
    assert_eq!(text.align, Align::Start);
    assert_eq!(text.rect, r(4, 4, 18, 4));
    assert_eq!(
        joined(text),
        ["Task A", "ticket: T1", "assigned: me", "priority: High"]
    );
    let Some(Item::Text(title)) = groups[0].items.get(1) else {
        return Err("section title");
    };
    assert_eq!(title.align, Align::Middle);
    assert_eq!(title.rect, r(1, 2, 25, 1));
    assert_eq!(joined(title), ["To Do"]);
    Ok(())
}

#[test]
fn vector_geometry() -> Result<(), &'static str> {
    let scene = scene_of(
        "kanban\n  todo[To Do]\n    a[Task A]\n    b[Task B]\n",
        Profile::Vector,
    )?;
    assert_eq!(scene.canvas(), Size { w: 13824, h: 8704 });
    let boxes = rects(&scene);
    assert_eq!(boxes[0], r(512, 512, 12800, 7680));
    assert_eq!(boxes[1], r(992, 2112, 11840, 2560));
    assert_eq!(boxes[2], r(992, 2112 + 2560 + 320, 11840, 2560));
    let all = texts(&scene);
    assert_eq!(all[0].rect, r(512, 672, 12800, 1280));
    assert_eq!(all[1].rect, r(992 + 1280, 2112 + 640, 11840 - 2560, 1280));
    Ok(())
}

#[test]
fn header_band_follows_tallest_title() -> Result<(), &'static str> {
    let scene = scene_of(
        "kanban\n  a[One]\n  b[A title that must wrap onto several lines of the narrow column]\n    c[Card]\n",
        Profile::Cell,
    )?;
    let all = texts(&scene);
    let long = all[1];
    assert!(long.lines.len() > 2);
    assert_eq!(i32::try_from(long.lines.len()), Ok(long.rect.h));
    let band = scene.boxes()[2].rect.y - scene.boxes()[1].rect.y;
    assert_eq!(i32::try_from(long.lines.len() + 1), Ok(band));
    assert!(all[0].rect.y > long.rect.y);
    Ok(())
}

#[test]
fn repeated_section_ids_repeat_cards_with_distinct_box_ids() -> Result<(), &'static str> {
    let scene = scene_of(
        "kanban\n  s[One]\n    a[A]\n  s[Two]\n    b[B]\n",
        Profile::Cell,
    )?;
    let ids: Vec<&str> = scene.boxes().iter().map(|b| b.id.as_str()).collect();
    assert_eq!(ids, ["s0", "s0.c0", "s0.c1", "s1", "s1.c0", "s1.c1"]);
    Ok(())
}

#[test]
fn config_scales_section_and_margin() -> Result<(), &'static str> {
    let src = "%%{init: {\"kanban\": {\"sectionWidth\": 100, \"padding\": 4}}}%%\nkanban\n  a[One]\n    b[Task]\n";
    let vector = scene_of(src, Profile::Vector)?;
    assert_eq!(vector.boxes()[0].rect.w, 6400);
    assert_eq!(vector.boxes()[0].rect.x, 256);
    assert_eq!(vector.boxes()[1].rect.w, 6400 - 960);
    let cell = scene_of(src, Profile::Cell)?;
    assert_eq!(cell.boxes()[0].rect.w, 13);
    assert_eq!(cell.boxes()[1].rect.w, 12);
    assert_eq!(cell.boxes()[0].rect.x, 1);
    let dump = model_dump(&input_of(src, Profile::Vector, DumpOptions::default())?);
    assert!(dump.contains(r#""padding":4,"sectionWidth":100"#), "{dump}");
    Ok(())
}

#[test]
fn model_dump_names_sections_and_cards() -> Result<(), &'static str> {
    let dump = model_dump(&input_of(DEMO, Profile::Vector, DumpOptions::default())?);
    for needle in [
        r#"{"id":"s0","role":"group","parent":"","exclusive":false,"direction":"","shape":"kanbanSection","text":"To Do"}"#,
        r#"{"id":"s0.c0","role":"node","parent":"s0","exclusive":true,"shape":"kanbanItem","text":"Task A<br>ticket: T1<br>assigned: me<br>priority: High"}"#,
        r#""routes":[]"#,
    ] {
        assert!(dump.contains(needle), "{needle} missing from {dump}");
    }
    Ok(())
}

#[test]
fn labels_are_trimmed() -> Result<(), &'static str> {
    let scene = scene_of("kanban\n  s[  Todo  ]\n    c[ Card ]\n", Profile::Cell)?;
    let all = texts(&scene);
    assert_eq!(joined(all[0]), ["Todo"]);
    assert_eq!(joined(all[1]), ["Card"]);
    Ok(())
}

#[test]
fn empty_diagram_is_a_margin() -> Result<(), &'static str> {
    let vector = scene_of("kanban\n\n", Profile::Vector)?;
    assert_eq!(vector.canvas(), Size { w: 1024, h: 1024 });
    let cell = scene_of("kanban\n\n", Profile::Cell)?;
    assert_eq!(cell.canvas(), Size { w: 2, h: 2 });
    assert!(vector.boxes().is_empty() && cell.boxes().is_empty());
    Ok(())
}

#[test]
fn profiles_share_identities() -> Result<(), &'static str> {
    let vector = scene_of(DEMO, Profile::Vector)?;
    let cell = scene_of(DEMO, Profile::Cell)?;
    let ids = |s: &Scene| -> Vec<(String, String)> {
        s.boxes()
            .iter()
            .map(|b| (b.id.clone(), b.parent.clone()))
            .collect()
    };
    assert_eq!(ids(&vector), ids(&cell));
    Ok(())
}

#[test]
fn corpus_validates_in_both_profiles() -> Result<(), &'static str> {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../corpus/kanban");
    let mut checked = 0;
    for source in std::fs::read_dir(root).map_err(|_| "corpus directory")? {
        let source = source.map_err(|_| "entry")?.path();
        for file in std::fs::read_dir(&source).map_err(|_| "source directory")? {
            let path = file.map_err(|_| "entry")?.path();
            let src = std::fs::read_to_string(&path).map_err(|_| "corpus file")?;
            for profile in [Profile::Vector, Profile::Cell] {
                scene_of(&src, profile)?;
            }
            checked += 1;
        }
    }
    assert!(checked > 0);
    Ok(())
}

fn small_input() -> Input {
    let group = InputBox {
        icon: false,
        id: "s".into(),
        role: BoxRole::Group,
        shape: "kanbanSection".into(),
        parent: String::new(),
        exclusive: false,
        text: String::new(),
        direction: String::new(),
    };
    let card = InputBox {
        icon: false,
        id: "c".into(),
        role: BoxRole::Node,
        shape: String::new(),
        parent: "s".into(),
        exclusive: true,
        text: "card".into(),
        direction: String::new(),
    };
    Input {
        kind: "kanban",
        profile: Profile::Cell,
        direction: Direction::Tb,
        options: DumpOptions::default(),
        boxes: vec![group, card],
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    }
}

#[test]
fn rejects_inconsistent_boxes() {
    let mut missing = small_input();
    missing.boxes[1].parent = "nowhere".into();
    assert!(matches!(super::layout(&missing), Err(GeomError::Domain)));
    let mut nested = small_input();
    nested.boxes.push(InputBox {
        icon: false,
        id: "inner".into(),
        role: BoxRole::Group,
        shape: String::new(),
        parent: "s".into(),
        exclusive: false,
        text: String::new(),
        direction: String::new(),
    });
    assert!(matches!(super::layout(&nested), Err(GeomError::Domain)));
    let mut deep = small_input();
    deep.boxes.push(InputBox {
        icon: false,
        id: "deep".into(),
        role: BoxRole::Node,
        shape: String::new(),
        parent: "c".into(),
        exclusive: true,
        text: String::new(),
        direction: String::new(),
    });
    assert!(matches!(super::layout(&deep), Err(GeomError::Domain)));
}

#[test]
fn enforces_limits() {
    let edit: [fn(&mut Input); 3] = [
        |input| {
            input.options.limits = Limits {
                max_nodes: 1,
                ..Limits::default()
            }
        },
        |input| {
            input.options.limits = Limits {
                max_text_bytes: 3,
                ..Limits::default()
            }
        },
        |input| {
            input.options.limits = Limits {
                max_edges: 1,
                ..Limits::default()
            };
            input.routes = ["e", "f"]
                .iter()
                .map(|id| InputRoute {
                    id: (*id).into(),
                    from: String::new(),
                    to: String::new(),
                    orthogonal: true,
                    marker_start: String::new(),
                    marker_end: String::new(),
                    line: String::new(),
                    min_length: 0,
                    from_side: None,
                    to_side: None,
                })
                .collect();
        },
    ];
    for apply in edit {
        let mut input = small_input();
        apply(&mut input);
        assert!(matches!(layout(&input), Err(RenderError::TooLarge { .. })));
    }
}

#[test]
fn rejects_oversized_config() {
    let mut input = small_input();
    input.profile = Profile::Vector;
    input
        .options
        .config
        .insert("sectionWidth".into(), DumpValue::Integer(99_999_999));
    assert!(matches!(super::layout(&input), Err(GeomError::Overflow)));
}
