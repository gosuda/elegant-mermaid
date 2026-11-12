use super::input::Input;
use crate::geom::Rect;
use crate::scene::{Dump, SceneBox, SceneLabel, SceneRoute};

pub fn model_dump(input: &Input) -> String {
    let mut options = input.options.clone();
    options.profile = input.profile;
    options.direction = input.direction;
    let mut dump = Dump::new(input.kind, options);
    dump.boxes = input
        .boxes
        .iter()
        .map(|b| SceneBox {
            id: b.id.clone(),
            role: b.role,
            rect: Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            },
            parent: b.parent.clone(),
            exclusive: b.exclusive,
        })
        .collect();
    dump.routes = input
        .routes
        .iter()
        .map(|r| SceneRoute {
            id: r.id.clone(),
            from: r.from.clone(),
            to: r.to.clone(),
            orthogonal: r.orthogonal,
            points: Vec::new(),
            marker_start: if r.marker_start == "none" {
                String::new()
            } else {
                r.marker_start.clone()
            },
            marker_end: r.marker_end.clone(),
            stroke: r.line.clone(),
        })
        .collect();
    dump.labels = input
        .labels
        .iter()
        .map(|l| SceneLabel {
            id: l.id.clone(),
            owner: l.owner.clone(),
            text: l.text.clone(),
            rect: Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            },
            lines: Vec::new(),
        })
        .collect();
    dump.dump_model()
}
