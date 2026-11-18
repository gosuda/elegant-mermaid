use crate::DiagramKind;
use crate::layout::families::layout;
use crate::layout::input::Input;
use crate::layout::modeldump::model_dump;
use crate::model::Resolved;
use crate::scene::{DumpOptions, Group, GroupRole, Item, Line, MarkerAxis, Profile, Scene, Width};

const PROFILES: [Profile; 2] = [Profile::Vector, Profile::Cell];

fn input_of(src: &str, profile: Profile) -> Result<Input, &'static str> {
    let pre = crate::syntax::preprocess::preprocess(src);
    let (model, diagnostics) = Resolved::parse(DiagramKind::Block, src, &pre.removed);
    if diagnostics
        .iter()
        .any(|d| d.severity == crate::diag::Severity::Error)
    {
        return Err("source has errors");
    }
    model
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|_| "input failed")
}

fn scene_of(src: &str, profile: Profile) -> Result<Scene, &'static str> {
    let input = input_of(src, profile)?;
    let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
    let violated = scene.validate().map_err(|_| "validate failed")?;
    assert!(violated.is_none(), "{violated:?}");
    Ok(scene)
}

fn node_group<'s>(scene: &'s Scene, owner: &str) -> Result<&'s Group, String> {
    scene
        .items()
        .iter()
        .find(|group| group.role == GroupRole::Node && group.owner == owner)
        .ok_or_else(|| format!("no node group for {owner}"))
}

fn first_item<'s>(scene: &'s Scene, owner: &str) -> Result<&'s Item, String> {
    node_group(scene, owner)?
        .items
        .first()
        .ok_or_else(|| format!("{owner} draws nothing"))
}

fn kind_of(item: &Item) -> &'static str {
    match item {
        Item::Rect(_) => "Rect",
        Item::RoundRect(_) => "RoundRect",
        Item::Ellipse(_) => "Ellipse",
        Item::Polygon(_) => "Polygon",
        Item::Polyline(_) => "Polyline",
        Item::Path(_) => "Path",
        _ => "other",
    }
}

#[test]
fn corpus_lays_out_validly() -> Result<(), String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/block");
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
    assert!(checked > 0, "corpus/block holds no file");
    Ok(())
}

#[test]
fn input_encodes_the_tree_in_declaration_order() -> Result<(), &'static str> {
    let src = "block-beta\ncolumns 3\ne0 b:2\nblock:g\ncolumns 2\nx y\nend\ne0 --> b\nb -- \"t\" --> g\nspace\n";
    let input = input_of(src, Profile::Vector)?;
    let ids: Vec<&str> = input.boxes.iter().map(|b| b.id.as_str()).collect();
    let shapes: Vec<&str> = input.boxes.iter().map(|b| b.shape.as_str()).collect();
    let parents: Vec<&str> = input.boxes.iter().map(|b| b.parent.as_str()).collect();
    assert_eq!(ids, ["root0", "e0", "b", "g", "x", "y", "space0-0"]);
    assert_eq!(
        shapes,
        [
            "composite;columns=3",
            "rect",
            "rect;span=2",
            "composite;columns=2",
            "rect",
            "rect",
            "space"
        ]
    );
    assert_eq!(parents, ["", "root0", "root0", "root0", "g", "g", "root0"]);
    assert_eq!(
        [input.routes[0].id.as_str(), input.routes[1].id.as_str()],
        ["e1", "e2"]
    );
    assert_eq!(input.labels[0].id, "e2.label");
    Ok(())
}

#[test]
fn input_maps_edge_styles() -> Result<(), &'static str> {
    let src = "block-beta\nA --> B\nB --x C\nC ==> D\nD -.-> E\nE --- F\nF <--> G\n";
    let input = input_of(src, Profile::Vector)?;
    let got: Vec<[&str; 3]> = input
        .routes
        .iter()
        .map(|r| {
            [
                r.marker_start.as_str(),
                r.marker_end.as_str(),
                r.line.as_str(),
            ]
        })
        .collect();
    assert_eq!(
        got,
        [
            ["", "point", "normal"],
            ["", "cross", "normal"],
            ["", "point", "thick"],
            ["", "point", "dotted"],
            ["", "", "normal"],
            ["point", "point", "normal"],
        ]
    );
    Ok(())
}

#[test]
fn vector_shape_primitives() -> Result<(), String> {
    let src = "block-beta\na[\"x\"] b(\"x\") c((\"x\")) d{\"x\"} e{{\"x\"}} f([\"x\"]) g[[\"x\"]] h[(\"x\")] i(((\"x\"))) j>\"x\"] k[/\"x\"/] l[\\\"x\"\\] m[/\"x\"\\] n[\\\"x\"/] o<[\"x\"]>(right)\n";
    let scene = scene_of(src, Profile::Vector).map_err(String::from)?;
    let expected = [
        ("a", "Rect"),
        ("b", "RoundRect"),
        ("c", "Ellipse"),
        ("d", "Polygon"),
        ("e", "Polygon"),
        ("f", "RoundRect"),
        ("g", "Rect"),
        ("i", "Ellipse"),
        ("j", "Polygon"),
        ("k", "Polygon"),
        ("l", "Polygon"),
        ("m", "Polygon"),
        ("n", "Polygon"),
        ("o", "Polygon"),
    ];
    for (id, want) in expected {
        assert_eq!(kind_of(first_item(&scene, id)?), want, "{id}");
    }
    assert_eq!(node_group(&scene, "g")?.items.len(), 4);
    assert_eq!(node_group(&scene, "i")?.items.len(), 3);
    Ok(())
}

#[test]
fn cell_shapes() -> Result<(), String> {
    let src = "block-beta\na[\"x\"] b(\"x\") c((\"x\")) i(((\"x\"))) o<[\"x\"]>(right, down)\n";
    let scene = scene_of(src, Profile::Cell).map_err(String::from)?;
    assert_eq!(kind_of(first_item(&scene, "a")?), "Rect");
    assert_eq!(kind_of(first_item(&scene, "b")?), "RoundRect");
    assert_eq!(kind_of(first_item(&scene, "c")?), "RoundRect");
    let Item::Rect(ring) = first_item(&scene, "i")? else {
        return Err("doublecircle is not a Rect".into());
    };
    assert_eq!(ring.shape.line, Line::Double);
    let axes: Vec<MarkerAxis> = node_group(&scene, "o")?
        .items
        .iter()
        .filter_map(|item| match item {
            Item::MarkerRef(marker) => Some(marker.axis),
            _ => None,
        })
        .collect();
    assert_eq!(axes, [MarkerAxis::PlusX, MarkerAxis::PlusY]);
    Ok(())
}

#[test]
fn arrow_heads_follow_directions() -> Result<(), String> {
    let src = "block-beta\na<[\"x\"]>(right) b<[\"x\"]>(x) c<[\"x\"]>(up, down, left, right) d<[\"x\"]>(y)\n";
    let scene = scene_of(src, Profile::Vector).map_err(String::from)?;
    let mut counts = Vec::new();
    for id in ["a", "b", "c", "d"] {
        let Item::Polygon(polygon) = first_item(&scene, id)? else {
            return Err(format!("{id} is not a polygon"));
        };
        counts.push(polygon.points.len());
    }
    assert_eq!(counts, [5, 6, 8, 6]);
    Ok(())
}

#[test]
fn edge_paint() -> Result<(), String> {
    let scene = scene_of("block-beta\nA --> B\nB ==> C\nC -.-x D\n", Profile::Vector)
        .map_err(String::from)?;
    let edges: Vec<&Group> = scene
        .items()
        .iter()
        .filter(|group| group.role == GroupRole::Edge)
        .collect();
    assert_eq!(edges.len(), 3);
    let lines: Vec<&crate::scene::PolylineItem> = edges
        .iter()
        .filter_map(|group| match group.items.first() {
            Some(Item::Polyline(line)) => Some(line),
            _ => None,
        })
        .collect();
    assert_eq!(lines.len(), 3);
    assert_eq!(lines[0].shape.width, Width::Normal);
    assert_eq!(lines[1].shape.width, Width::Emphasis);
    assert_eq!(lines[2].shape.line, Line::Dotted);
    let marker = |group: &Group| match group.items.get(1) {
        Some(Item::MarkerRef(marker)) => Some(marker.marker.as_str()),
        _ => None,
    };
    assert_eq!(marker(edges[0]), Some("point"));
    assert_eq!(marker(edges[2]), Some("cross"));
    Ok(())
}

#[test]
fn spaces_are_boxes_but_never_drawn() -> Result<(), String> {
    let scene =
        scene_of("block-beta\ncolumns 2\nspace A\n", Profile::Vector).map_err(String::from)?;
    let space = scene
        .boxes()
        .iter()
        .find(|b| b.id == "space0-0")
        .ok_or("no space box")?;
    assert!(!space.exclusive);
    assert!(scene.items().iter().all(|group| group.owner != "space0-0"));
    Ok(())
}

#[test]
fn padding_config_widens_the_grid() -> Result<(), &'static str> {
    let plain = scene_of("block-beta\nA B\n", Profile::Vector)?;
    let src = "---\nconfig:\n  block:\n    padding: 24\n---\nblock-beta\nA B\n";
    let wide = scene_of(src, Profile::Vector)?;
    assert_eq!(wide.canvas().w - plain.canvas().w, 7 * (24 * 64 - 512));
    let cell_src = "---\nconfig:\n  block:\n    padding: 0\n---\nblock-beta\nA B\n";
    let cell = scene_of(cell_src, Profile::Cell)?;
    assert_eq!(cell.boxes()[1].rect.x, 1);
    Ok(())
}

#[test]
fn zero_padding_routes_between_touching_blocks_draw_nothing() -> Result<(), String> {
    let src = "%%{init: {\"block\": {\"padding\": 0}}}%%\nblock-beta\ncolumns 2\nA B\nA --> B\n";
    let scene = scene_of(src, Profile::Vector).map_err(String::from)?;
    assert_eq!(scene.routes()[0].points.len(), 1);
    let edge = scene
        .items()
        .iter()
        .find(|group| group.role == GroupRole::Edge)
        .ok_or("no edge group")?;
    assert!(edge.items.is_empty());
    Ok(())
}

#[test]
fn model_dump_carries_columns_and_spans() -> Result<(), &'static str> {
    let input = input_of(
        "block-beta\ncolumns 2\nA:2 B\nA --> B\nB --- A\n",
        Profile::Vector,
    )?;
    let dump = model_dump(&input);
    for want in [
        "\"kind\":\"block\"",
        "\"shape\":\"composite;columns=2\"",
        "\"shape\":\"rect;span=2\"",
        "\"marker_end\":\"none\"",
    ] {
        assert!(dump.contains(want), "{want} missing from {dump}");
    }
    Ok(())
}

#[test]
fn empty_diagram_has_only_margins() -> Result<(), &'static str> {
    let scene = scene_of("block-beta\ncolumns 2\n", Profile::Vector)?;
    assert_eq!((scene.canvas().w, scene.canvas().h), (512, 512));
    assert_eq!(scene.boxes().len(), 1);
    Ok(())
}

#[test]
fn routes_never_cross_the_other_blocks() -> Result<(), &'static str> {
    for profile in PROFILES {
        let src = "block-beta\ncolumns 3\nA B C\nD E F\nA --> C\nA --> F\nD --> B\nE --> E\n";
        assert_eq!(scene_of(src, profile)?.routes().len(), 4);
    }
    Ok(())
}

#[test]
fn labels_stay_strictly_inside_the_frames() -> Result<(), &'static str> {
    for profile in PROFILES {
        scene_of(
            "block-beta\nA --> A\nB -- \"loop label\" --> B\nA --> B\nB --> A\n",
            profile,
        )?;
        scene_of(
            "block-beta\ncolumns 3\na b c\na --> c\na -- \"x\" --> c\na -- \"y\" --> c\nb --> b\n",
            profile,
        )?;
    }
    Ok(())
}
