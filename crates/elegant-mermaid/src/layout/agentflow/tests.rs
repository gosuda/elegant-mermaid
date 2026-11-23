use super::*;
fn input(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let parsed = crate::syntax::agentflow::parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 0);
    let (model, diagnostics) = crate::model::agentflow::resolve(source, &parsed.document);
    assert_eq!(diagnostics.len(), 0);
    from_agentflow(&model, profile, DumpOptions::default()).map_err(|_| "agentflow adapter failed")
}
#[test]
fn node_minimum_padding_and_wrap_are_profile_specific() -> Result<(), &'static str> {
    for profile in [Profile::Cell, Profile::Vector] {
        let input = input(
            "agentflow-beta\nA[abcdefghijklmnopabcdefghijklmnop]\n",
            profile,
        )?;
        let node = input.boxes.first().ok_or("missing node")?;
        assert_eq!(node.shape, "roundedRect");
        let SizeRule::Content(size) = input.sizes.first().ok_or("missing size")? else {
            return Err("expected content size");
        };
        assert!(
            size.w >= if profile == Profile::Cell { 15 } else { 7680 },
            "a 32-char label must be wrapped, so the content width must reach the kind wrap minimum ({:?} expects >= {}), got {} for node {:?}",
            profile,
            if profile == Profile::Cell { 15 } else { 7680 },
            size.w,
            node.id,
        );
        if profile == Profile::Cell {
            assert_eq!(
                size.h, 5,
                "the kind wrap target 15 cells must give lines 15/15/2 plus 2*1 pad; observed {size:?}"
            );
        }
        assert_eq!(input.spacing, Spacing::for_kind(profile, "agentflow"));
    }
    Ok(())
}
#[test]
fn relations_have_stable_ids_markers_lengths_and_owned_labels() -> Result<(), &'static str> {
    let input = input(
        "agentflow-beta\ne0 -->|next| B\nB --x C\nC -.- e0\n",
        Profile::Cell,
    )?;
    assert_eq!(
        input
            .routes
            .iter()
            .map(|r| (
                r.id.as_str(),
                r.marker_end.as_str(),
                r.line.as_str(),
                r.min_length
            ))
            .collect::<Vec<_>>(),
        [
            ("e1", "point", "normal", 2),
            ("e2", "cross", "normal", 1),
            ("e3", "none", "dotted", 1)
        ]
    );
    let label = input.labels.first().ok_or("missing route label")?;
    assert_eq!((&*label.id, &*label.owner), ("e1.label", "e1"));
    Ok(())
}
#[test]
fn flows_become_directional_nonexclusive_groups() -> Result<(), &'static str> {
    let input = input(
        "agentflow-beta\nflow Outer[Outer]\ndirection LR\nflow Inner[Inner]\nA --> B\nend\nend\n",
        Profile::Cell,
    )?;
    assert_eq!(
        input
            .groups
            .iter()
            .map(|g| (g.id.as_str(), g.parent.as_str(), g.direction.as_str()))
            .collect::<Vec<_>>(),
        [("Outer", "", "LR"), ("Inner", "Outer", "")]
    );
    assert_eq!(
        input
            .boxes
            .iter()
            .find(|b| b.id == "A")
            .ok_or("missing child")?
            .parent,
        "Inner"
    );
    Ok(())
}
#[test]
fn collapsed_flows_hide_descendants_and_redirect_routes() -> Result<(), &'static str> {
    let input = input(
        "agentflow-beta\nflow F[Fold] @{ view: collapsed }\nA --> B\nend\nB --> C\n",
        Profile::Cell,
    )?;
    assert_eq!(
        input
            .boxes
            .iter()
            .map(|b| b.id.as_str())
            .collect::<Vec<_>>(),
        ["F", "C"]
    );
    assert_eq!(
        input.boxes.first().ok_or("missing collapsed flow")?.shape,
        "collapsedGroup"
    );
    assert_eq!(
        input.routes.first().ok_or("missing redirected route")?.from,
        "F"
    );
    assert_eq!(input.routes.len(), 1);
    Ok(())
}
#[test]
fn short_nodes_use_exact_kind_minima_and_padding() -> Result<(), &'static str> {
    let cell = input("agentflow-beta\nA\n", Profile::Cell)?;
    let vector = input("agentflow-beta\nA\n", Profile::Vector)?;
    assert_eq!(
        content("A", None, &cell)
            .map_err(|_| "cell measurement failed")?
            .1,
        Size { w: 15, h: 3 }
    );
    assert_eq!(
        content("A", None, &vector)
            .map_err(|_| "vector measurement failed")?
            .1,
        Size { w: 7680, h: 2304 }
    );
    assert_eq!(
        padding_units(Some(0), Profile::Cell).map_err(|_| "zero padding failed")?,
        (1, 1)
    );
    assert_eq!(
        padding_units(Some(17), Profile::Cell).map_err(|_| "cell padding failed")?,
        (3, 2)
    );
    assert_eq!(
        padding_units(Some(17), Profile::Vector).map_err(|_| "vector padding failed")?,
        (1088, 1088)
    );
    Ok(())
}

#[test]
fn geometric_outlines_keep_the_normalized_shape_identity() -> Result<(), &'static str> {
    use crate::{
        geom::{Point, Rect},
        scene::Item,
    };
    let rect = Rect {
        x: 0,
        y: 0,
        w: 100,
        h: 40,
    };
    let diamond = outline("diamond", rect, Profile::Vector).map_err(|_| "diamond failed")?;
    let Item::Polygon(diamond) = diamond.first().ok_or("missing diamond")? else {
        return Err("diamond is not polygon");
    };
    assert_eq!(
        diamond.points,
        [
            Point { x: 50, y: 0 },
            Point { x: 100, y: 20 },
            Point { x: 50, y: 40 },
            Point { x: 0, y: 20 }
        ]
    );
    let tool = outline("subroutine", rect, Profile::Vector).map_err(|_| "tool failed")?;
    assert_eq!(
        tool.len(),
        3,
        "subroutine outline must draw the body plus two side ticks, got {} primitives",
        tool.len()
    );
    assert!(
        matches!(tool.first(), Some(Item::Rect(_))),
        "subroutine outline must start with the body Rect, got {:?} instead",
        tool.first(),
    );
    let document = outline("lin-doc", rect, Profile::Vector).map_err(|_| "document failed")?;
    assert_eq!(document.len(), 2);
    assert!(
        matches!(document.first(), Some(Item::Polygon(_))),
        "lin-doc outline must draw its frame as a Polygon, first primitive is {:?}",
        document.first(),
    );
    Ok(())
}

#[test]
fn layered_scene_is_replaced_with_agentflow_outlines() -> Result<(), &'static str> {
    for profile in [Profile::Vector, Profile::Cell] {
        let input = input("agentflow-beta\nA[Start]\n", profile)?;
        let (scene, _) = layout(&input).map_err(|_| "agentflow layout failed")?;
        let node = scene
            .items()
            .iter()
            .find(|group| group.owner == "A")
            .ok_or("missing node drawing")?;
        assert!(
            matches!(node.items.first(), Some(crate::scene::Item::RoundRect(_))),
            "agentflow layout must replace the layered scene with a RoundRect outline for node {:?}, first item is {:?}",
            node.owner,
            node.items.first(),
        );
        assert!(
            node.items
                .iter()
                .any(|item| matches!(item, crate::scene::Item::Text(_))),
            "agentflow node {:?} outline must carry its label as a Text item, none found among {} items",
            node.owner,
            node.items.len(),
        );
    }
    Ok(())
}

fn node_texts<'a>(scene: &'a crate::scene::Scene, owner: &str) -> Vec<&'a crate::scene::TextItem> {
    let groups = scene.items().iter().filter(|group| group.owner == owner);
    let mut texts = Vec::new();
    for item in groups.flat_map(|group| &group.items) {
        if let crate::scene::Item::Text(text) = item {
            texts.push(text);
        }
    }
    texts
}

fn node_runs(scene: &crate::scene::Scene, owner: &str) -> Vec<crate::scene::Run> {
    let mut runs = Vec::new();
    for text in node_texts(scene, owner) {
        for line in &text.lines {
            runs.extend(line.iter().cloned());
        }
    }
    runs
}

fn node_lines(scene: &crate::scene::Scene, owner: &str) -> Vec<String> {
    let mut lines = Vec::new();
    for text in node_texts(scene, owner) {
        for line in &text.lines {
            lines.push(line.iter().map(|run| run.text.as_str()).collect());
        }
    }
    lines
}

#[test]
fn emphasis_crossing_a_wrap_boundary_stays_bold_without_delimiters() -> Result<(), &'static str> {
    let label = "**abcdefghijklmnopqrstuvwxyz abcdefghijklmnopqrstuvwxyz**";
    let input = input(&format!("agentflow-beta\nA({label})\n"), Profile::Cell)?;
    let SizeRule::Content(size) = input.sizes.first().ok_or("missing size")? else {
        return Err("expected content size");
    };
    assert_eq!(
        (size.w, size.h),
        (17, 6),
        "cell widths ignore style, so the kind target 15 must wrap into lines 15/11/15/11 plus 2*1 pad on each axis; observed {size:?}"
    );
    let (scene, _) = layout(&input).map_err(|_| "agentflow layout failed")?;
    let runs = node_runs(&scene, "A");
    assert!(
        runs.iter().any(|run| run.bold),
        "the emphasized run must arrive bold even though the wrap falls inside it: {runs:?}"
    );
    assert!(
        runs.iter().all(|run| !run.text.contains("**")),
        "delimiters must never appear as scene text: {runs:?}"
    );
    assert_eq!(
        node_lines(&scene, "A"),
        [
            "abcdefghijklmno".to_string(),
            "pqrstuvwxyz".to_string(),
            "abcdefghijklmno".to_string(),
            "pqrstuvwxyz".to_string(),
        ],
        "both halves of the split emphasis must wrap at the kind target; observed {:?}",
        node_lines(&scene, "A")
    );
    Ok(())
}

#[test]
fn escape_unsupported_and_math_render_unstyled_in_scene() -> Result<(), &'static str> {
    let input = input(
        "agentflow-beta\nB(a\\*b \\_c)\nC(a * b _c_d)\nD($$x$$)\n",
        Profile::Cell,
    )?;
    let (scene, _) = layout(&input).map_err(|_| "agentflow layout failed")?;
    for (owner, expected) in [("B", "a*b _c"), ("C", "a * b _c_d"), ("D", "$$x$$")] {
        let runs = node_runs(&scene, owner);
        assert_eq!(
            runs.iter().map(|run| run.text.as_str()).collect::<String>(),
            expected,
            "{owner} must render {expected} unchanged: {runs:?}"
        );
        assert!(
            runs.iter().all(|run| !run.bold && !run.italic),
            "{owner} must stay unstyled: {runs:?}"
        );
    }
    Ok(())
}

#[test]
fn forced_breaks_keep_empty_rows_in_sizes_and_scene() -> Result<(), &'static str> {
    let input = input("agentflow-beta\nA(x<br/><br/>y)\n", Profile::Cell)?;
    let SizeRule::Content(size) = input.sizes.first().ok_or("missing size")? else {
        return Err("expected content size");
    };
    assert_eq!(
        (size.w, size.h),
        (15, 5),
        "three forced regions render rows x/empty/y: height 3 plus 2*1 pad, width 1 plus 2*1 pad against the 15 minimum; observed {size:?}"
    );
    let (scene, _) = layout(&input).map_err(|_| "agentflow layout failed")?;
    assert_eq!(
        node_lines(&scene, "A"),
        ["x".to_string(), String::new(), "y".to_string()],
        "the empty forced region must stay an empty row; observed {:?}",
        node_lines(&scene, "A")
    );
    Ok(())
}

#[test]
fn route_labels_render_styled_and_dump_the_source_text() -> Result<(), &'static str> {
    let input = input("agentflow-beta\nA -->|**go**| B\n", Profile::Cell)?;
    let (scene, _) = layout(&input).map_err(|_| "agentflow layout failed")?;
    let edge = scene
        .items()
        .iter()
        .find(|group| group.owner == "e0")
        .ok_or("missing edge group")?;
    assert!(
        edge.items
            .iter()
            .any(|item| matches!(item, crate::scene::Item::Text(_))),
        "the edge group must carry its label as a Text item: {:?}",
        edge.items
    );
    let runs = node_runs(&scene, "e0");
    assert!(
        runs.iter().any(|run| run.bold),
        "the route label emphasis must survive into the scene: {runs:?}"
    );
    assert_eq!(
        runs.iter().map(|run| run.text.as_str()).collect::<String>(),
        "go",
        "route label delimiters must not render: {runs:?}"
    );
    let dump = scene
        .labels()
        .iter()
        .find(|label| label.owner == "e0")
        .ok_or("missing dump label")?;
    assert_eq!(
        &*dump.text, "**go**",
        "the dump must keep the source label text verbatim while its lines render"
    );
    Ok(())
}
