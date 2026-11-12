use super::*;
use crate::{
    geom::Size,
    layout::{
        input,
        layered::{
            graph::{Node, Params},
            isolate::Fixed,
        },
    },
    scene::{self, DumpOptions, Profile},
};

#[test]
fn embedded_nodes_and_routes_change_the_parent_cost_denominator() -> Result<(), LayoutError> {
    let mut child_dump = scene::Dump::new(
        "flowchart",
        DumpOptions {
            profile: Profile::Cell,
            ..DumpOptions::default()
        },
    );
    child_dump.boxes = [("A", 0), ("B", 5)]
        .into_iter()
        .map(|(id, x)| scene::SceneBox {
            id: id.into(),
            role: BoxRole::Node,
            rect: Rect {
                x,
                y: 0,
                w: 3,
                h: 3,
            },
            parent: String::new(),
            exclusive: true,
        })
        .collect();
    child_dump.routes.push(scene::SceneRoute {
        id: "inner".into(),
        from: "A".into(),
        to: "B".into(),
        orthogonal: true,
        points: vec![Point { x: 3, y: 1 }, Point { x: 5, y: 1 }],
        marker_start: String::new(),
        marker_end: String::new(),
        stroke: String::new(),
    });
    let child = scene::Scene::new(Size { w: 8, h: 3 }, child_dump, Vec::new());
    let fixed = [Fixed {
        id: "S",
        scene: &child,
        direction: Direction::Tb,
    }];
    let measurements = Measurements {
        route_lines: Vec::new(),
        route_stacks: Vec::new(),
        titles: vec![Size { w: 3, h: 2 }],
        fixed: &fixed,
    };
    let input = Input {
        kind: "flowchart",
        profile: Profile::Cell,
        direction: Direction::Tb,
        options: DumpOptions::default(),
        boxes: vec![input::Box {
            id: "S".into(),
            role: BoxRole::Group,
            shape: String::new(),
            parent: String::new(),
            exclusive: false,
            text: "S".into(),
            direction: "LR".into(),
        }],
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
    };
    let graph = Graph {
        nodes: vec![Node {
            id: "S".into(),
            decl: 0,
            w: 10,
            h: 6,
        }],
        edges: Vec::new(),
        params: Params::for_profile("cell")?,
    };
    let part = Component {
        boxes: vec![Rect {
            x: 0,
            y: 0,
            w: 10,
            h: 6,
        }],
        routes: Vec::new(),
        labels: Vec::new(),
        titles: vec![(
            0,
            Rect {
                x: 1,
                y: 1,
                w: 1,
                h: 1,
            },
        )],
        loop_extents: Vec::new(),
        label_reservations: Vec::new(),
        budget: false,
    };
    assert_eq!(score(&graph, &input, &measurements, &part)?, 3);
    Ok(())
}
