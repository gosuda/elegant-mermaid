use super::{escape_shape, parse_shape, unescape_shape};
use crate::DiagramKind;
use crate::layout::families::layout;
use crate::layout::input::{Input, RouteSide};
use crate::layout::modeldump::model_dump;
use crate::model::Resolved;
use crate::scene::{DumpOptions, Group, GroupRole, Item, Profile, Scene};

const PROFILES: [Profile; 2] = [Profile::Vector, Profile::Cell];
const DEMO: &str = "architecture-beta\n  group api(cloud)[API]\n  service db(database)[Database] in api\n  service app(server)[App] in api\n  service raw[Raw]\n  junction j\n  db:R -[reads]- L:app\n  app:B --> T:j\n  j:R -- L:raw\n";

fn resolved(src: &str) -> Result<Resolved, &'static str> {
    let pre = crate::syntax::preprocess::preprocess(src);
    let (model, diagnostics) = Resolved::parse(DiagramKind::Architecture, src, &pre.removed);
    if diagnostics
        .iter()
        .any(|d| d.severity == crate::diag::Severity::Error)
    {
        return Err("source has errors");
    }
    model.ok_or("no model")
}

fn input_of(src: &str, profile: Profile) -> Result<Input, &'static str> {
    resolved(src)?
        .input(profile, DumpOptions::default())
        .map_err(|_| "input failed")
}

fn scene_of(src: &str, profile: Profile) -> Result<Scene, &'static str> {
    let (scene, _) = layout(&input_of(src, profile)?).map_err(|_| "layout failed")?;
    let violated = scene.validate().map_err(|_| "validate failed")?;
    assert!(violated.is_none(), "{violated:?}");
    Ok(scene)
}

fn group<'s>(scene: &'s Scene, role: GroupRole, owner: &str) -> Result<&'s Group, String> {
    scene
        .items()
        .iter()
        .find(|group| group.role == role && group.owner == owner)
        .ok_or_else(|| format!("no group for {owner}"))
}

#[test]
fn corpus_lays_out_validly() -> Result<(), String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/architecture");
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
    assert!(checked > 0, "corpus/architecture holds no file");
    Ok(())
}

#[test]
fn model_dump_names_shapes_and_sides() -> Result<(), &'static str> {
    let src = format!("{DEMO}  align row db app\n");
    let dump = model_dump(&input_of(&src, Profile::Vector)?);
    for want in [
        r#""id":"api","role":"group","parent":"","exclusive":false,"direction":"","shape":"group;icon=cloud","text":"API""#,
        r#""id":"db","role":"node","parent":"api","exclusive":true,"shape":"service;icon=database;align=0:r:0","text":"Database""#,
        r#""id":"app","role":"node","parent":"api","exclusive":true,"shape":"service;icon=server;align=0:r:1","text":"App""#,
        r#""id":"raw","role":"node","parent":"","exclusive":true,"shape":"service","text":"Raw""#,
        r#""id":"j","role":"node","parent":"","exclusive":true,"shape":"junction""#,
        r#""from_side":"R","to_side":"L""#,
        r#""id":"e1","from":"app","to":"j","orthogonal":true,"from_side":"B","to_side":"T""#,
    ] {
        assert!(dump.contains(want), "missing {want} in {dump}");
    }
    Ok(())
}

#[test]
fn edge_markers_follow_the_arrow_direction() -> Result<(), &'static str> {
    let src = "architecture-beta\nservice a(server)\nservice b(server)\nservice c(server)\na:R <--> L:b\nb:R -- L:c\n";
    let input = input_of(src, Profile::Vector)?;
    assert_eq!(input.routes[0].marker_start, "point");
    assert_eq!(input.routes[0].marker_end, "point");
    assert!(input.routes[1].marker_start.is_empty());
    assert!(input.routes[1].marker_end.is_empty());
    assert_eq!(input.routes[0].from_side, Some(RouteSide::Right));
    assert_eq!(input.routes[0].to_side, Some(RouteSide::Left));
    Ok(())
}

#[test]
fn icon_text_escapes_shape_separators() -> Result<(), &'static str> {
    let input = input_of("architecture-beta\nservice a \"x;y=z%\"\n", Profile::Vector)?;
    assert_eq!(input.boxes[0].shape, "service;icontext=x%3By%3Dz%25");
    let spec = parse_shape(&input.boxes[0].shape);
    assert_eq!(spec.kind, "service");
    assert_eq!(spec.icon_text, "x;y=z%");
    assert_eq!(escape_shape("x;y=z%"), "x%3By%3Dz%25");
    assert_eq!(unescape_shape("x%3By%3Dz%25"), "x;y=z%");
    Ok(())
}

#[test]
fn config_scales_padding_and_icons() -> Result<(), &'static str> {
    let base = "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\n";
    let cfg =
        format!("---\nconfig:\n  architecture:\n    padding: 80\n    iconSize: 40\n---\n{base}");
    for profile in PROFILES {
        let plain = scene_of(base, profile)?;
        let scaled = scene_of(&cfg, profile)?;
        assert_ne!(plain.boxes()[0].rect.w, scaled.boxes()[0].rect.w);
    }
    let vector = scene_of(&cfg, Profile::Vector)?;
    assert_eq!(vector.boxes()[0].rect.w, 40 * 64);
    Ok(())
}

#[test]
fn services_paint_an_outline_and_a_label() -> Result<(), String> {
    let scene = scene_of(DEMO, Profile::Vector)?;
    let db = group(&scene, GroupRole::Node, "db")?;
    assert!(matches!(db.items.first(), Some(Item::RoundRect(_))));
    assert!(db.items.iter().any(|item| matches!(item, Item::Text(_))));
    let frame = group(&scene, GroupRole::Group, "api")?;
    assert!(matches!(frame.items.first(), Some(Item::Rect(_))));
    let junction = group(&scene, GroupRole::Node, "j")?;
    assert!(matches!(junction.items.as_slice(), [Item::Ellipse(_)]));
    Ok(())
}

#[test]
fn cell_profile_draws_junctions_as_symbols() -> Result<(), String> {
    let scene = scene_of(DEMO, Profile::Cell)?;
    let junction = group(&scene, GroupRole::Node, "j")?;
    assert!(matches!(junction.items.as_slice(), [Item::SymbolRef(_)]));
    let db = group(&scene, GroupRole::Node, "db")?;
    assert!(matches!(db.items.first(), Some(Item::Rect(_))));
    Ok(())
}
