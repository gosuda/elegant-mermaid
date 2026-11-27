use super::super::{
    LayoutError,
    graph::{Node, Params, Proper, ProperNode},
    route::Routing,
};
use super::{StraightenContext, WorkBox, corridor_clear, is_real_node};
use crate::geom::{Point, Rect};

fn context_with(nodes: Vec<ProperNode>, border: Vec<bool>) -> StraightenContext {
    StraightenContext {
        proper: Proper {
            nodes,
            edges: Vec::new(),
            rank: Vec::new(),
            chains: Vec::new(),
            out: Vec::new(),
            r#in: Vec::new(),
            params: Params {
                slot: 0,
                pivot_factor: 0,
                node_gap: 0,
                rank_gap: 0,
                port_gap: 0,
                cluster_pad: 0,
            },
        },
        layers: Vec::new(),
        x: Vec::new(),
        y: Vec::new(),
        top: Vec::new(),
        routing: Routing {
            gaps: Vec::new(),
            source_x: Vec::new(),
            target_x: Vec::new(),
            segment: Vec::new(),
        },
        cluster_tops: Vec::new(),
        border,
    }
}

fn proper_node(id: &str, dummy: bool, label: bool) -> ProperNode {
    ProperNode {
        node: Node {
            id: id.to_string(),
            decl: 0,
            w: 10,
            h: 10,
        },
        dummy,
        label,
        edge: -1,
    }
}

#[test]
fn straighten_is_real_node_accepts_plain_node() {
    let context = context_with(vec![proper_node("g", false, false)], vec![false]);
    assert!(is_real_node(&context, 0));
}

#[test]
fn straighten_is_real_node_rejects_dummy_label_and_border() {
    let context = context_with(
        vec![
            proper_node("a", false, false),
            proper_node("d", true, false),
            proper_node("l", false, true),
            proper_node("b", false, false),
        ],
        vec![false, false, false, true],
    );
    assert!(is_real_node(&context, 0));
    assert!(!is_real_node(&context, 1));
    assert!(!is_real_node(&context, 2));
    assert!(!is_real_node(&context, 3));
}

#[test]
fn straighten_corridor_clear_declines_box_between_endpoints() -> Result<(), LayoutError> {
    let candidate = [Point { x: 100, y: 40 }, Point { x: 100, y: 200 }];
    let boxes = vec![WorkBox {
        id: "g".to_string(),
        rect: Rect {
            x: 80,
            y: 100,
            w: 40,
            h: 40,
        },
    }];
    assert!(!corridor_clear(&candidate, "a", "b", &boxes)?);
    Ok(())
}

#[test]
fn straighten_corridor_clear_accepts_miss_and_skips_endpoints() -> Result<(), LayoutError> {
    let candidate = [Point { x: 100, y: 40 }, Point { x: 100, y: 200 }];
    let far = vec![WorkBox {
        id: "n".to_string(),
        rect: Rect {
            x: 500,
            y: 100,
            w: 40,
            h: 40,
        },
    }];
    assert!(corridor_clear(&candidate, "a", "b", &far)?);
    let ends = vec![
        WorkBox {
            id: "a".to_string(),
            rect: Rect {
                x: 60,
                y: 0,
                w: 80,
                h: 40,
            },
        },
        WorkBox {
            id: "b".to_string(),
            rect: Rect {
                x: 60,
                y: 200,
                w: 80,
                h: 40,
            },
        },
    ];
    assert!(corridor_clear(&candidate, "a", "b", &ends)?);
    Ok(())
}
