use elegant_mermaid::{LayoutOptions, Profile, cells, layout, parse};

type TestResult = Result<(), Box<dyn std::error::Error>>;

fn render_cells(source: &str) -> Result<cells::RenderResult, Box<dyn std::error::Error>> {
    let document = parse(source);
    assert!(!document.has_errors(), "{:?}", document.diagnostics());
    let scene = layout(
        &document,
        &LayoutOptions {
            profile: Profile::Cell,
            ..LayoutOptions::default()
        },
    )?;
    assert!(scene.check()?, "{}", scene.dump());
    Ok(cells::render(&scene, &cells::Options::default())?)
}

#[test]
fn framed_tool_labels_clear_the_inner_rules() -> TestResult {
    let label = "abcdefghijklmno";
    for shape in [
        "tool",
        "subroutine",
        "subprocess",
        "subproc",
        "framed-rectangle",
    ] {
        for padding in [None, Some(0), Some(17)] {
            let config = padding.map_or_else(String::new, |padding| {
                format!("---\nconfig:\n  flowchart:\n    padding: {padding}\n---\n")
            });
            let source =
                format!("{config}agentflow-beta TB\nA[\"{label}\"]@{{ shape: {shape} }}\n");
            let rendered = render_cells(&source)?;
            assert_eq!(
                rendered.refused_clusters, 0,
                "{shape} {padding:?}: {}",
                rendered.text
            );
            assert_eq!(rendered.route_conflicts, 0, "{}", rendered.text);
            assert!(rendered.text.contains(label), "{}", rendered.text);
        }
    }
    Ok(())
}

#[test]
fn concurrent_region_dividers_preserve_the_composite_title() -> TestResult {
    for direction in ["TB", "LR"] {
        let source = format!(
            "stateDiagram-v2\ndirection {direction}\nstate Outer {{\ndirection {direction}\nA --> B\n--\nC --> D\n}}\n"
        );
        let rendered = render_cells(&source)?;
        assert_eq!(
            rendered.refused_clusters, 0,
            "{direction}: {}",
            rendered.text
        );
        assert_eq!(rendered.route_conflicts, 0, "{}", rendered.text);
        assert_eq!(
            rendered.text.matches("Outer").count(),
            1,
            "{}",
            rendered.text
        );
    }
    Ok(())
}

#[test]
fn note_routing_preserves_state_transition_labels() -> TestResult {
    for direction in ["TB", "BT", "LR", "RL"] {
        let source = format!(
            "stateDiagram-v2\ndirection {direction}\nstate Auth {{\n[*] --> Login\nLogin --> MFA : code\nMFA --> Success\n}}\n[*] --> Auth\nAuth --> [*]\nNote right of Auth: Handles user auth\nNote right of MFA: One-time code\n"
        );
        let rendered = render_cells(&source)?;
        assert_eq!(
            rendered.refused_clusters, 0,
            "{direction}: {}",
            rendered.text
        );
        assert_eq!(rendered.route_conflicts, 0, "{}", rendered.text);
        assert_eq!(
            rendered.text.matches("code").count(),
            2,
            "{}",
            rendered.text
        );
        assert!(
            rendered.text.contains("Handles user auth"),
            "{}",
            rendered.text
        );
        assert!(rendered.text.contains("One-time code"), "{}", rendered.text);
    }
    Ok(())
}

#[test]
fn swimlane_routes_and_relocated_captions_preserve_every_glyph() -> TestResult {
    let cases = [
        (
            "swimlanes~0013",
            include_str!("../../../corpus/swimlane/mermaid/swimlanes~0013.mmd"),
        ),
        (
            "disagree-exits-b-c",
            include_str!(
                "../../../corpus/swimlane/mermaid/swimlanes~pr-check~12-disagree-exits-b-c.mmd"
            ),
        ),
        (
            "query-process",
            include_str!("../../../corpus/swimlane/mermaid/swimlanes~pr-check~query-process.mmd"),
        ),
        (
            "sales-process",
            include_str!("../../../corpus/swimlane/mermaid/swimlanes~pr-check~sales-process.mmd"),
        ),
        (
            "mermaid-work",
            include_str!("../../../corpus/swimlane/mermaid/swimlanes~pr-check~mermaid-work.mmd"),
        ),
    ];
    for (name, source) in cases {
        let rendered = render_cells(source).map_err(|error| format!("{name}: {error}"))?;
        assert_eq!(rendered.refused_clusters, 0, "{name}: {}", rendered.text);
    }
    Ok(())
}

#[test]
fn c4_directional_ports_keep_their_existing_text_clearance() -> TestResult {
    for source in [
        include_str!("../../../corpus/c4/mermaid/c4~0006.mmd"),
        include_str!("../../../corpus/c4/mermaid/c4~pr-check~directional-relationships.mmd"),
    ] {
        let rendered = render_cells(source)?;
        assert_eq!(rendered.refused_clusters, 0, "{}", rendered.text);
        assert_eq!(rendered.route_conflicts, 0, "{}", rendered.text);
    }
    Ok(())
}

#[test]
fn swimlane_side_ports_preserve_centered_node_text() -> TestResult {
    for direction in ["LR", "RL"] {
        let source = format!(
            "swimlane-beta {direction}\nsubgraph Left[Left]\nA[Alpha]\nend\nsubgraph Right[Right]\nB[Beta]\nend\nA --> B\n"
        );
        let rendered = render_cells(&source)?;
        assert_eq!(rendered.refused_clusters, 0, "{}", rendered.text);
        assert_eq!(rendered.route_conflicts, 0, "{}", rendered.text);
        assert!(rendered.text.contains("Alpha"), "{}", rendered.text);
        assert!(rendered.text.contains("Beta"), "{}", rendered.text);
    }
    Ok(())
}
