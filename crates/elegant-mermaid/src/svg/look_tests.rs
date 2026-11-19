use crate::geom::Size;
use crate::{LayoutOptions, RenderError, SvgOptions, TextOptions, parse, render_svg, render_text};

type TestResult = Result<(), RenderError>;

const DIAGRAM: &str = "flowchart LR\n  A[Start] --> B[End]\n";

fn svg_with(source: &str, config: Option<&str>) -> Result<String, RenderError> {
    let options = SvgOptions {
        layout: LayoutOptions {
            config: config.map(str::to_owned),
            ..LayoutOptions::default()
        },
        ..SvgOptions::default()
    };
    render_svg(&parse(source), &options)
}

fn hand_drawn(seed: u32) -> String {
    format!("look: handDrawn\nhandDrawnSeed: {seed}\n")
}

#[test]
fn look_hand_drawn_seed() -> TestResult {
    let classic = svg_with(DIAGRAM, None)?;
    let first = svg_with(DIAGRAM, Some(&hand_drawn(7)))?;
    let second = svg_with(DIAGRAM, Some(&hand_drawn(7)))?;
    assert_eq!(first, second, "one seed must render identical bytes");
    assert_ne!(first, classic, "the look must change the output");
    assert!(first.contains("<path class='emd-h-edge'"), "{first}");
    assert!(first.contains("<path class='emd-h-node'"), "{first}");
    assert!(first.contains(".emd-f-node{fill:"), "{first}");
    assert!(!first.contains("<rect class='emd-s-node'"), "{first}");
    assert_ne!(first, svg_with(DIAGRAM, Some(&hand_drawn(8)))?);
    assert_eq!(
        svg_with(DIAGRAM, Some(&hand_drawn(0)))?,
        svg_with(DIAGRAM, Some("look: handDrawn\n"))?,
        "an absent seed is seed 0"
    );
    let node_passes = first.matches("<path class='emd-h-node'").count();
    assert_eq!(
        node_passes,
        2 * 4 * 2,
        "two passes for each of four sides, two nodes"
    );
    let edge_passes = first.matches("<path class='emd-h-edge'").count();
    assert_eq!(edge_passes, 2, "one straight edge segment, two passes");
    Ok(())
}

#[test]
fn look_hand_drawn_reads_every_config_source_alike() -> TestResult {
    let expected = svg_with(DIAGRAM, Some(&hand_drawn(7)))?;
    let frontmatter =
        format!("---\nconfig:\n  look: handDrawn\n  handDrawnSeed: 7\n---\n{DIAGRAM}");
    let directive =
        format!("%%{{init: {{\"look\": \"handDrawn\", \"handDrawnSeed\": 7}}}}%%\n{DIAGRAM}");
    assert_eq!(svg_with(&frontmatter, None)?, expected);
    assert_eq!(svg_with(&directive, None)?, expected);
    let overridden = svg_with(&frontmatter, Some("handDrawnSeed: 9\n"))?;
    assert_eq!(overridden, svg_with(DIAGRAM, Some(&hand_drawn(9)))?);
    Ok(())
}

#[test]
fn look_hand_drawn_leaves_the_cell_profile_alone() -> TestResult {
    let plain = render_text(&parse(DIAGRAM), &TextOptions::default())?;
    let options = TextOptions {
        layout: LayoutOptions {
            config: Some(hand_drawn(7)),
            ..LayoutOptions::default()
        },
        ..TextOptions::default()
    };
    assert_eq!(render_text(&parse(DIAGRAM), &options)?, plain);
    Ok(())
}

#[test]
fn look_hand_drawn_rejects_out_of_range_seeds() {
    for seed in ["-1", "4294967296", "1.5", "text", "true"] {
        let config = format!("look: handDrawn\nhandDrawnSeed: {seed}\n");
        assert!(
            matches!(
                svg_with(DIAGRAM, Some(&config)),
                Err(RenderError::InvalidConfig { errors: 1 })
            ),
            "{seed}"
        );
    }
    let document = parse("---\nconfig:\n  handDrawnSeed: 4294967296\n---\nflowchart LR\nA\n");
    let codes: Vec<_> = document.diagnostics().iter().map(|d| d.code).collect();
    assert_eq!(codes, ["config/malformed"]);
    assert!(matches!(
        render_svg(&document, &SvgOptions::default()),
        Err(RenderError::InvalidDocument { errors: 1 })
    ));
}

fn neo_scene() -> crate::Scene {
    use crate::geom::{Point, Rect};
    use crate::scene::{
        Dump, DumpOptions, Group, GroupRole, Item, PolylineItem, RectItem, RoundRectItem, Shape,
        ShapeStyle, Width,
    };
    let node = Shape::plain(ShapeStyle::Node);
    let rect = Rect {
        x: 640,
        y: 640,
        w: 3840,
        h: 2560,
    };
    crate::Scene::new(
        Size { w: 12800, h: 3840 },
        Dump::new("flowchart", DumpOptions::default()),
        vec![Group::new(GroupRole::Node, "").with_items(vec![
            Item::RoundRect(RoundRectItem {
                shape: node,
                rect,
                r: 512,
            }),
            Item::RoundRect(RoundRectItem {
                shape: node,
                rect,
                r: 256,
            }),
            Item::Rect(RectItem {
                shape: node.with_width(Width::Emphasis),
                rect,
            }),
            Item::Polyline(PolylineItem {
                shape: Shape::plain(ShapeStyle::Edge).with_width(Width::Units(192)),
                points: vec![Point { x: 0, y: 0 }, Point { x: 64, y: 0 }],
                corner: 0,
            }),
        ])],
    )
}

fn neo_output(look: crate::look::Look) -> Result<String, super::ConfigError> {
    let mut out = String::new();
    super::write(
        &mut out,
        &neo_scene(),
        &super::Options {
            look,
            ..super::Options::default()
        },
    )?;
    Ok(out)
}

#[test]
fn look_neo_widens_normal_strokes_and_the_radius_token_only() -> Result<(), super::ConfigError> {
    use crate::look::{Look, LookKind};
    let classic = neo_output(Look::default())?;
    let neo = neo_output(Look {
        kind: LookKind::Neo,
        seed: 0,
    })?;
    assert!(
        classic.contains("rx='8' ry='8' stroke-width='1'"),
        "{classic}"
    );
    assert!(neo.contains("rx='12' ry='12' stroke-width='2'"), "{neo}");
    assert!(neo.contains("rx='4' ry='4' stroke-width='2'"), "{neo}");
    assert!(
        neo.contains("stroke-width='3'"),
        "an explicit width stays: {neo}"
    );
    assert_eq!(
        classic.matches("stroke-width='2'").count(),
        1,
        "the emphasis rect is the only classic 2 px stroke"
    );
    let colours = |svg: &str| {
        svg.lines()
            .filter(|line| line.starts_with(".emd-"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    assert_eq!(colours(&classic), colours(&neo), "neo keeps every colour");
    Ok(())
}

#[test]
fn look_neo_reads_the_config_and_spares_the_cell_profile() -> TestResult {
    let classic = svg_with(DIAGRAM, None)?;
    let neo = svg_with(DIAGRAM, Some("look: neo\n"))?;
    assert_ne!(classic, neo);
    assert!(neo.contains("stroke-width='2'"));
    assert!(!neo.contains("emd-h-"));
    let plain = render_text(&parse(DIAGRAM), &TextOptions::default())?;
    let options = TextOptions {
        layout: LayoutOptions {
            config: Some("look: neo\n".into()),
            ..LayoutOptions::default()
        },
        ..TextOptions::default()
    };
    assert_eq!(render_text(&parse(DIAGRAM), &options)?, plain);
    Ok(())
}
