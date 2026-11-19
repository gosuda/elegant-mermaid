use std::path::{Path, PathBuf};

use super::wardley::{
    Wardley, WardleyAnnotation, WardleyFlow, WardleyForce, WardleyLink, WardleyNode, WardleyNote,
    WardleyPipeline, WardleyPoint, WardleyStrategy, WardleyTrend,
};
use super::{WardleyDump, decode_wardley, layout_wardley};
use crate::geom::{Rect, Size};
use crate::scene::{DumpOptions, DumpValue, Item, Profile, Scene, SceneBox, SceneLabel};

type Check = Result<(), String>;

fn rich() -> Wardley {
    let node = |label: &str, x: i64, y: i64| WardleyNode {
        label: label.to_owned(),
        x,
        y,
        ..WardleyNode::default()
    };
    Wardley {
        title: "Tea".to_owned(),
        stages: ["Genesis", "Custom", "Product", "Commodity"]
            .map(str::to_owned)
            .to_vec(),
        boundaries: vec![250, 500, 750, 1000],
        nodes: vec![
            WardleyNode {
                anchor: true,
                ..node("Customer", 50000, 90000)
            },
            WardleyNode {
                strategy: WardleyStrategy::Build,
                inertia: true,
                ..node("Cup", 40000, 70000)
            },
            WardleyNode {
                has_offset: true,
                offset_x: -16,
                offset_y: 32,
                strategy: WardleyStrategy::Market,
                ..node("Tea", 60000, 50000)
            },
            WardleyNode {
                pipeline_parent: true,
                ..node("Kettle", 45000, 30000)
            },
            node("Fire", 20000, 30000),
            node("Electric", 70000, 30000),
        ],
        pipelines: vec![WardleyPipeline {
            parent: 3,
            children: vec![4, 5],
        }],
        links: vec![
            WardleyLink {
                from: 0,
                to: 1,
                dashed: false,
                label: String::new(),
                flow: WardleyFlow::Forward,
            },
            WardleyLink {
                from: 1,
                to: 2,
                dashed: true,
                label: "uses".to_owned(),
                flow: WardleyFlow::Backward,
            },
            WardleyLink {
                from: 2,
                to: 4,
                dashed: false,
                label: String::new(),
                flow: WardleyFlow::Bidirectional,
            },
        ],
        trends: vec![WardleyTrend {
            node: 1,
            target_x: 85000,
            target_y: 70000,
        }],
        notes: vec![WardleyNote {
            text: "note".to_owned(),
            x: 10000,
            y: 10000,
        }],
        accelerators: vec![WardleyForce {
            name: "Cloud".to_owned(),
            x: 20000,
            y: 20000,
        }],
        deaccelerators: vec![WardleyForce {
            name: "Legacy".to_owned(),
            x: 60000,
            y: 20000,
        }],
        annotations: vec![
            WardleyAnnotation {
                number: 2,
                x: 40000,
                y: 60000,
                text: "second".to_owned(),
            },
            WardleyAnnotation {
                number: 1,
                x: 50000,
                y: 40000,
                text: "first".to_owned(),
            },
            WardleyAnnotation {
                number: 3,
                x: 70000,
                y: 40000,
                text: String::new(),
            },
        ],
        box_point: Some(WardleyPoint { x: 5000, y: 95000 }),
    }
}

fn options(profile: Profile) -> DumpOptions {
    DumpOptions {
        profile,
        ..DumpOptions::default()
    }
}

fn laid_out(w: &Wardley, options: &DumpOptions) -> Result<Scene, String> {
    let (scene, _) = layout_wardley(w, options).map_err(|e| format!("{e:?}"))?;
    let clause = scene.validate().map_err(|e| format!("{e:?}"))?;
    assert!(clause.is_none(), "{clause:?}");
    Ok(scene)
}

fn find_box<'a>(scene: &'a Scene, id: &str) -> Result<&'a SceneBox, String> {
    scene
        .boxes()
        .iter()
        .find(|b| b.id == id)
        .ok_or_else(|| format!("no box {id}"))
}

fn find_label<'a>(scene: &'a Scene, id: &str) -> Result<&'a SceneLabel, String> {
    scene
        .labels()
        .iter()
        .find(|l| l.id == id)
        .ok_or_else(|| format!("no label {id}"))
}

fn dump_of(w: &Wardley) -> WardleyDump {
    let skeleton = w.skeleton();
    WardleyDump {
        routes: skeleton.routes,
        labels: skeleton.labels,
        regions: w.regions(),
    }
}

#[test]
fn dump_round_trips_every_feature() -> Check {
    let want = rich();
    let got = decode_wardley(&dump_of(&want)).map_err(|e| format!("{e:?}"))?;
    assert_eq!(want, got);
    Ok(())
}

#[test]
fn decode_rejects_malformed_dumps() {
    let good = rich();
    let routes = good.skeleton().routes;
    let tail = routes[routes.len() - 3..].to_vec();
    let cases = [
        vec![vec![99]],
        vec![vec![1, 0, 0]],
        vec![vec![2, 0, 3, 1]],
        vec![vec![0, 1, 2, 1000]],
        vec![vec![1, 0, 9, 0, 0, 0, 0]],
    ];
    for regions in cases {
        let dump = WardleyDump {
            routes: Vec::new(),
            labels: Vec::new(),
            regions,
        };
        assert!(decode_wardley(&dump).is_err());
    }
    let dump = WardleyDump {
        routes: tail,
        labels: Vec::new(),
        regions: vec![good.regions()[0].clone()],
    };
    assert!(decode_wardley(&dump).is_err());
}

#[test]
fn projection_places_nodes_in_the_inset_plot() -> Check {
    let node = |label: &str, x: i64, y: i64| WardleyNode {
        label: label.to_owned(),
        x,
        y,
        ..WardleyNode::default()
    };
    let w = Wardley {
        stages: vec!["A".to_owned()],
        nodes: vec![
            node("N", 25000, 50000),
            node("Low", 0, 0),
            node("High", 100000, 100000),
            node("Far", 250000, 400000),
        ],
        ..Wardley::default()
    };
    let scene = laid_out(&w, &options(Profile::Vector))?;
    assert_eq!(scene.canvas(), Size { w: 57600, h: 38400 });
    let at = |id: &str| -> Result<(i32, i32), String> {
        let r = find_box(&scene, id)?.rect;
        Ok((r.x, r.y))
    };
    assert_eq!(at("n0")?, (3072 + 12864, 38400 - 3072 - 16128));
    assert_eq!(at("n1")?, (3072, 38400 - 3072));
    assert_eq!(at("n2")?, (57600 - 3072, 3072));
    assert_eq!(at("n3")?, (57600 - 3072, 3072));
    assert_eq!(
        find_box(&scene, "plot")?.rect,
        Rect {
            x: 3072,
            y: 3072,
            w: 57600 - 6144,
            h: 38400 - 6144
        }
    );
    Ok(())
}

#[test]
fn config_sizes_the_canvas_per_profile() -> Check {
    let w = Wardley {
        stages: vec!["A".to_owned()],
        ..Wardley::default()
    };
    let mut o = options(Profile::Vector);
    o.config
        .insert("height".to_owned(), DumpValue::Integer(300));
    o.config.insert("width".to_owned(), DumpValue::Integer(400));
    assert_eq!(
        laid_out(&w, &o)?.canvas(),
        Size {
            w: 400 * 64,
            h: 300 * 64
        }
    );
    o.profile = Profile::Cell;
    assert_eq!(laid_out(&w, &o)?.canvas(), Size { w: 50, h: 19 });
    let mut o = options(Profile::Vector);
    o.config
        .insert("padding".to_owned(), DumpValue::Integer(20));
    let plot = find_box(&laid_out(&w, &o)?, "plot")?.rect;
    assert_eq!(
        plot,
        Rect {
            x: 1280,
            y: 1280,
            w: 57600 - 2560,
            h: 38400 - 2560
        }
    );
    Ok(())
}

#[test]
fn tiny_canvas_still_holds_every_box() -> Check {
    let mut o = options(Profile::Vector);
    o.config.insert("height".to_owned(), DumpValue::Integer(1));
    o.config.insert("width".to_owned(), DumpValue::Integer(1));
    laid_out(&rich(), &o)?;
    Ok(())
}

#[test]
fn pipeline_frame_encloses_children_and_parent_sits_on_its_top_edge() -> Check {
    let scene = laid_out(&rich(), &options(Profile::Vector))?;
    let frame = find_box(&scene, "pl0")?.rect;
    for id in ["n4", "n5"] {
        let child = find_box(&scene, id)?;
        assert_eq!(child.parent, "pl0");
        assert!(frame.x <= child.rect.x && child.rect.x <= frame.x + frame.w);
        assert!(frame.y < child.rect.y && child.rect.y < frame.y + frame.h);
    }
    let parent = find_box(&scene, "n3")?;
    assert_eq!(parent.parent, "plot");
    assert!(parent.rect.y < frame.y + frame.h / 2);
    let (a, b) = (
        find_box(&scene, "n4")?.rect.x,
        find_box(&scene, "n5")?.rect.x,
    );
    assert_eq!(parent.rect.x, (a + b) / 2);
    let link = scene
        .routes()
        .iter()
        .find(|r| r.id == "pl0.l0")
        .ok_or("no pipeline link")?;
    assert_eq!((link.from.as_str(), link.to.as_str()), ("n4", "n5"));
    assert_eq!(link.stroke, "dotted");
    Ok(())
}

fn marker_count(scene: &Scene, owner: &str) -> usize {
    scene
        .items()
        .iter()
        .filter(|g| g.role == crate::scene::GroupRole::Edge && g.owner == owner)
        .flat_map(|g| &g.items)
        .filter(|item| matches!(item, Item::MarkerRef(_)))
        .count()
}

#[test]
fn markers_follow_flow_direction() -> Check {
    let scene = laid_out(&rich(), &options(Profile::Vector))?;
    assert_eq!(marker_count(&scene, "l0"), 1);
    assert_eq!(marker_count(&scene, "l1"), 1);
    assert_eq!(marker_count(&scene, "l2"), 2);
    assert_eq!(marker_count(&scene, "tr0"), 1);
    assert_eq!(marker_count(&scene, "pl0.l0"), 0);
    Ok(())
}

#[test]
fn annotation_box_stacks_texts_by_number() -> Check {
    let scene = laid_out(&rich(), &options(Profile::Vector))?;
    let ab = find_box(&scene, "ab")?.rect;
    let first = find_label(&scene, "an1.text")?;
    let second = find_label(&scene, "an0.text")?;
    assert_eq!(first.text, "1. first");
    assert_eq!(second.text, "2. second");
    assert!(first.rect.y < second.rect.y);
    assert_eq!(first.rect.x, second.rect.x);
    for l in [first, second] {
        assert!(l.rect.x >= ab.x && l.rect.x + l.rect.w <= ab.x + ab.w);
        assert!(l.rect.y >= ab.y && l.rect.y + l.rect.h <= ab.y + ab.h);
    }
    assert!(find_label(&scene, "an2.text")?.lines.is_empty());
    let mut bare = rich();
    bare.box_point = None;
    let scene = laid_out(&bare, &options(Profile::Vector))?;
    assert!(scene.boxes().iter().all(|b| b.id != "ab"));
    let text = find_label(&scene, "an0.text")?;
    assert_eq!(text.owner, "an0");
    assert!(text.rect.x > find_box(&scene, "an0")?.rect.x);
    Ok(())
}

#[test]
fn node_labels_follow_offsets_and_anchors() -> Check {
    let scene = laid_out(&rich(), &options(Profile::Vector))?;
    let (tea, at) = (
        find_label(&scene, "n2.label")?,
        find_box(&scene, "n2")?.rect,
    );
    assert_eq!(at.x - 16 * 64, tea.rect.x + tea.rect.w / 2);
    assert_eq!(at.y + 32 * 64, tea.rect.y + tea.rect.h / 2);
    let (customer, anchor) = (
        find_label(&scene, "n0.label")?,
        find_box(&scene, "n0")?.rect,
    );
    assert_eq!(anchor.x, customer.rect.x + customer.rect.w / 2);
    let (cup, cup_at) = (
        find_label(&scene, "n1.label")?,
        find_box(&scene, "n1")?.rect,
    );
    assert!(cup.rect.x > cup_at.x);
    assert_eq!(cup_at.y, cup.rect.y + cup.rect.h);
    Ok(())
}

#[test]
fn empty_map_still_lays_out() -> Check {
    for profile in [Profile::Vector, Profile::Cell] {
        let scene = laid_out(&Wardley::default(), &options(profile))?;
        assert_eq!(scene.boxes().len(), 1);
        assert_eq!(scene.boxes()[0].id, "plot");
    }
    Ok(())
}

fn corpus_files() -> Result<Vec<PathBuf>, std::io::Error> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/wardley");
    let mut paths = Vec::new();
    for source in std::fs::read_dir(root)? {
        for file in std::fs::read_dir(source?.path())? {
            let path = file?.path();
            if path.extension().is_some_and(|ext| ext == "mmd") {
                paths.push(path);
            }
        }
    }
    paths.sort();
    assert!(!paths.is_empty());
    Ok(paths)
}

fn refusals(name: &str) -> usize {
    match name {
        "wardley~0011.mmd" | "wardley~pr-check~1-should-render-tea-shop.mmd" => 1,
        "wardley~0019.mmd" => 12,
        "wardley~pr-check~6-should-render-gpt-tokeniser-architecture.mmd" => 7,
        _ => 0,
    }
}

fn corpus_scene(source: &str, profile: Profile) -> Result<Option<Scene>, String> {
    use crate::DiagramKind;
    use crate::model::Resolved;
    use crate::syntax::preprocess::preprocess;
    let removed = preprocess(source).removed;
    let (resolved, diagnostics) = Resolved::parse(DiagramKind::Wardley, source, &removed);
    let Some(resolved) = resolved.filter(|_| diagnostics.is_empty()) else {
        return Ok(None);
    };
    let input = resolved
        .input(profile, DumpOptions::default())
        .map_err(|e| format!("{e:?}"))?;
    let (scene, _) = crate::layout::families::layout(&input).map_err(|e| format!("{e:?}"))?;
    Ok(Some(scene))
}

#[test]
fn corpus_scenes_are_valid() -> Check {
    for path in corpus_files().map_err(|e| e.to_string())? {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        for profile in [Profile::Vector, Profile::Cell] {
            let Some(scene) = corpus_scene(&source, profile)? else {
                continue;
            };
            let clause = scene.validate().map_err(|e| format!("{e:?}"))?;
            assert!(clause.is_none(), "{path:?} {profile:?}: {clause:?}");
            if profile == Profile::Cell {
                let rendered =
                    crate::cells::render::render(&scene, &crate::cells::render::Options::default())
                        .map_err(|e| format!("{e:?}"))?;
                let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
                assert_eq!(rendered.refused_clusters, refusals(name), "{path:?}");
            }
        }
    }
    Ok(())
}
