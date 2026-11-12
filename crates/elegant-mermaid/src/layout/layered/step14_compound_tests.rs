use super::{Edge, Graph, Node, Params, Proper, ProperEdge, ProperNode};
use crate::{
    geom::{Point, Rect},
    layout::layered::{
        clusters::Cluster,
        gutters,
        route::{Routing, RoutingGap, RoutingSegment},
    },
};

fn boundary(point: Point, rect: Rect) -> bool {
    let right = i64::from(rect.x) + i64::from(rect.w);
    let bottom = i64::from(rect.y) + i64::from(rect.h);
    i64::from(point.x) >= i64::from(rect.x)
        && i64::from(point.x) <= right
        && i64::from(point.y) >= i64::from(rect.y)
        && i64::from(point.y) <= bottom
        && (point.x == rect.x
            || i64::from(point.x) == right
            || point.y == rect.y
            || i64::from(point.y) == bottom)
}

fn assert_frame_contains(frame: Rect, member: Rect) {
    assert!(member.x >= frame.x);
    assert!(member.y >= frame.y);
    assert!(i64::from(member.x) + i64::from(member.w) <= i64::from(frame.x) + i64::from(frame.w));
    assert!(i64::from(member.y) + i64::from(member.h) <= i64::from(frame.y) + i64::from(frame.h));
}

#[test]
fn compound_frame_contains_members_and_routes_use_ports() -> Result<(), Box<dyn std::error::Error>>
{
    let document = crate::parse("graph TB\nsubgraph one\nA --> B\nend\n");
    assert!(!document.has_errors());
    for profile in [crate::Profile::Vector, crate::Profile::Cell] {
        let scene = crate::layout(
            &document,
            &crate::LayoutOptions {
                profile,
                ..Default::default()
            },
        )?;
        let dump = scene.dump_part();
        assert_eq!(
            dump.boxes.iter().map(|b| b.id.as_str()).collect::<Vec<_>>(),
            ["one", "A", "B"]
        );
        assert!(dump.labels.is_empty());
        let frame = dump.boxes[0].rect;
        for member in &dump.boxes[1..] {
            assert_eq!(member.parent, "one");
            assert_frame_contains(frame, member.rect);
        }
        assert_eq!(dump.routes.len(), 1);
        let route = &dump.routes[0];
        assert_eq!((&*route.from, &*route.to), ("A", "B"));
        assert!(route.points.len() >= 2);
        assert!(
            route
                .points
                .first()
                .is_some_and(|&point| boundary(point, dump.boxes[1].rect))
        );
        assert!(
            route
                .points
                .last()
                .is_some_and(|&point| boundary(point, dump.boxes[2].rect))
        );
        assert!(
            route
                .points
                .windows(2)
                .all(|p| p[0].x == p[1].x || p[0].y == p[1].y)
        );
    }
    Ok(())
}

#[test]
fn compound_derived_nodes_keep_cluster_declaration() -> Result<(), Box<dyn std::error::Error>> {
    let graph = Graph {
        nodes: vec![
            Node {
                decl: 0,
                ..Default::default()
            },
            Node {
                decl: 1,
                ..Default::default()
            },
            Node {
                decl: 0,
                ..Default::default()
            },
        ],
        edges: vec![
            Edge {
                tail: 0,
                head: 1,
                min_len: 1,
                decl: i32::MAX,
                reversed: false,
            },
            Edge {
                tail: 1,
                head: 2,
                min_len: 1,
                decl: i32::MAX,
                reversed: false,
            },
        ],
        params: Params::for_profile("vector")?,
    };
    graph.validate()?;
    assert_eq!(
        crate::layout::layered::cycles::break_cycles(&graph)?,
        [false, false]
    );
    Ok(())
}

#[test]
fn compound_gutter_uses_frame_edge_not_border_centre() -> Result<(), Box<dyn std::error::Error>> {
    let node = |w| ProperNode {
        node: Node {
            w,
            ..Default::default()
        },
        dummy: false,
        label: false,
        edge: -1,
    };
    let proper = Proper {
        nodes: vec![node(0), node(8), node(0)],
        edges: vec![ProperEdge {
            tail: 0,
            head: 2,
            decl: 0,
            original: 0,
        }],
        rank: vec![0, 0, 1],
        chains: vec![vec![0, 2]],
        out: vec![vec![0], vec![], vec![]],
        r#in: vec![vec![], vec![], vec![0]],
        params: Params::for_profile("vector")?,
    };
    let mut routing = Routing {
        gaps: vec![RoutingGap {
            segments: vec![RoutingSegment {
                tail: 0,
                head: 2,
                decl: 0,
                slot: -1,
                source_x: 20,
                target_x: 30,
                edges: vec![0],
            }],
            slots: 0,
        }],
        source_x: vec![20],
        target_x: vec![30],
        segment: vec![0],
    };
    gutters::number(
        &[Cluster {
            node: 0,
            bottom: 2,
            title: 0,
            left: vec![1],
            right: vec![],
        }],
        &proper,
        &[20, 10, 30],
        &mut routing,
    )?;
    assert_eq!(routing.gaps[0].segments[0].source_x, 6);
    assert_eq!(routing.source_x, [20]);
    Ok(())
}
