use super::{
    input::Input,
    layered::{LayoutError, pipeline},
};
use crate::scene::Scene;

pub struct Family {
    pub kind: &'static str,
    pub layout: fn(&Input) -> Result<(Scene, bool), LayoutError>,
}
pub const FAMILIES: &[Family] = &[
    Family {
        kind: "flowchart",
        layout: flowchart,
    },
    Family {
        kind: "class",
        layout: super::class::layout,
    },
];
pub fn layout(
    input: &Input,
) -> Result<(Scene, Vec<crate::diag::Diagnostic>), crate::error::RenderError> {
    check_limits(input)?;
    if input
        .boxes
        .iter()
        .any(|b| input.routes.iter().any(|r| r.id == b.id))
    {
        return Err(crate::error::RenderError::InvalidConfig { errors: 1 });
    }
    let family = FAMILIES
        .iter()
        .find(|f| f.kind == input.kind)
        .ok_or(crate::error::RenderError::InvalidConfig { errors: 1 })?;
    let (mut scene, budget) = (family.layout)(input).map_err(|error| match error {
        LayoutError::Overflow => crate::error::RenderError::Overflow,
        LayoutError::Domain => crate::error::RenderError::InvalidConfig { errors: 1 },
    })?;
    crate::scene::project_cell_attachments(&mut scene);
    let mut diagnostics = if budget {
        vec![crate::diag::Diagnostic {
            code: "layout/budget-exhausted",
            severity: crate::diag::Severity::Info,
            message: "layout stopped at its iteration cap".into(),
            span: crate::source::Span { start: 0, end: 0 },
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        }]
    } else {
        Vec::new()
    };
    for group in input
        .groups
        .iter()
        .filter(|group| !group.direction.is_empty())
    {
        let inside = |id: &str| {
            super::layered::clusters::ancestors(input, id)
                .iter()
                .any(|&i| input.boxes[i].id == group.id)
        };
        if !input
            .routes
            .iter()
            .any(|route| inside(&route.from) != inside(&route.to))
        {
            continue;
        }
        diagnostics.push(crate::diag::Diagnostic {
            code: "flowchart/subgraph-direction-ignored",
            severity: crate::diag::Severity::Warning,
            message: "subgraph direction is ignored because an edge crosses its boundary".into(),
            span: group.direction_span,
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        });
    }
    Ok((scene, diagnostics))
}

fn check_limits(input: &Input) -> Result<(), crate::error::RenderError> {
    let limits = &input.options.limits;
    if limits.max_nodes == 0
        || limits.max_edges == 0
        || limits.max_text_bytes == 0
        || !(1..=5).contains(&input.options.thoroughness)
    {
        return Err(crate::error::RenderError::InvalidConfig { errors: 1 });
    }
    let nodes = input.boxes.len();
    let mut bytes = 0usize;
    for b in &input.boxes {
        if !input.labels.iter().any(|label| label.owner == b.id) {
            bytes = bytes
                .checked_add(b.text.len())
                .ok_or(crate::error::RenderError::Overflow)?;
        }
    }
    for label in &input.labels {
        bytes = bytes
            .checked_add(label.text.len())
            .ok_or(crate::error::RenderError::Overflow)?;
    }
    for (actual, limit) in [
        (nodes, limits.max_nodes),
        (input.routes.len(), limits.max_edges),
        (bytes, limits.max_text_bytes),
    ] {
        if u64::try_from(actual).map_err(|_| crate::error::RenderError::Overflow)?
            > u64::from(limit)
        {
            return Err(crate::error::RenderError::TooLarge {
                limit,
                actual: u32::try_from(actual).unwrap_or(u32::MAX),
            });
        }
    }
    Ok(())
}

fn flowchart(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let edges = input
        .routes
        .iter()
        .map(|r| pipeline::EdgeOptions {
            marker_start: scene_marker(&r.marker_start),
            marker_end: scene_marker(&r.marker_end),
            stroke: &r.line,
            min_length: 1,
        })
        .collect::<Vec<_>>();
    pipeline::layout_family(input, &edges)
}

fn scene_marker(marker: &str) -> Option<crate::scene::MarkerName> {
    if marker == "none" {
        return None;
    }
    crate::r#gen::markers::MARKERS
        .iter()
        .find(|row| row.name == marker)
        .and_then(|row| crate::scene::MarkerName::new(row.name))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::{
        model,
        scene::{Direction, DumpOptions, Profile},
        syntax,
    };
    fn input(source: &str, profile: Profile) -> Input {
        let parsed = syntax::flowchart::parse(source, &[]);
        let (model, _) = model::flowchart::resolve(source, &parsed.document);
        super::super::flowchart::from_flowchart(&model, profile, DumpOptions::default())
    }
    #[test]
    fn pipeline_two_node_golden() {
        let (scene, _) = layout(&input("flowchart\nA -->|yes| B\n", Profile::Vector)).unwrap();
        assert_eq!(
            scene.dump(),
            include_str!("../../../../spec/golden/two-node.layout.json")
        );
    }
    #[test]
    fn one_family_per_kind() {
        let source = "flowchart\nA[x] -->|yes| B[y]\n";
        let a = layout(&input(source, Profile::Vector)).unwrap().0;
        let b = layout(&input(source, Profile::Cell)).unwrap().0;
        assert_eq!(
            a.boxes().iter().map(|b| &b.id).collect::<Vec<_>>(),
            b.boxes().iter().map(|b| &b.id).collect::<Vec<_>>()
        );
        assert_eq!(
            a.routes().iter().map(|r| &r.id).collect::<Vec<_>>(),
            b.routes().iter().map(|r| &r.id).collect::<Vec<_>>()
        );
        assert_eq!(
            a.labels().iter().map(|l| &l.id).collect::<Vec<_>>(),
            b.labels().iter().map(|l| &l.id).collect::<Vec<_>>()
        );
        for scene in [&a, &b] {
            assert_eq!(
                scene
                    .labels()
                    .iter()
                    .map(|l| (l.id.as_str(), l.owner.as_str(), l.text.as_str()))
                    .collect::<Vec<_>>(),
                [("e0.label", "e0", "yes")]
            );
            assert_eq!(
                scene_text(scene),
                [("e0", "yes".into()), ("A", "x".into()), ("B", "y".into())]
            );
        }
    }
    fn scene_text(scene: &crate::scene::Scene) -> Vec<(&str, String)> {
        scene
            .items()
            .iter()
            .flat_map(|group| {
                group.items.iter().filter_map(|item| match item {
                    crate::scene::Item::Text(text) => Some((
                        group.owner.as_str(),
                        text.lines
                            .iter()
                            .map(|line| {
                                line.iter().map(|run| run.text.as_str()).collect::<String>()
                            })
                            .collect::<Vec<_>>()
                            .join("\n"),
                    )),
                    _ => None,
                })
            })
            .collect()
    }
    #[test]
    fn pipeline_demo_and_directions() {
        let source =
            "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";
        for profile in [Profile::Vector, Profile::Cell] {
            let mut model = input(source, profile);
            let s = layout(&model).unwrap().0;
            let margin = if profile == Profile::Cell { 1 } else { 1024 };
            assert_eq!(s.boxes().iter().map(|b| b.rect.x).min(), Some(margin));
            assert_eq!(s.routes()[2].points.len(), 6);
            assert_eq!(s.routes()[2].points[0].x, s.boxes()[1].rect.x);
            assert_eq!(
                s.labels()
                    .iter()
                    .map(|l| (l.id.as_str(), l.owner.as_str(), l.text.as_str()))
                    .collect::<Vec<_>>(),
                [("e1.label", "e1", "yes"), ("e2.label", "e2", "no")]
            );
            assert_eq!(
                scene_text(&s),
                [
                    ("e1", "yes".into()),
                    ("e2", "no".into()),
                    ("A", "Start".into()),
                    ("B", "Choice".into()),
                    ("C", "Done".into())
                ]
            );
            assert!(s.canvas().w > s.boxes()[2].rect.x + s.boxes()[2].rect.w);
            assert!(s.canvas().h > s.boxes().iter().map(|b| b.rect.y + b.rect.h).max().unwrap());
            for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
                model.direction = direction;
                assert!(layout(&model).unwrap().0.check().unwrap());
            }
        }
    }
    #[test]
    fn pipeline_random_layered_validity() {
        for seed in 1..=200u32 {
            let mut state = seed;
            let mut draw = |lo: usize, hi: usize| {
                state ^= state << 13;
                state ^= state >> 17;
                state ^= state << 5;
                lo + usize::try_from(state).unwrap() % (hi - lo + 1)
            };
            let n = draw(2, 30);
            let mut source = String::from("flowchart TD\n");
            for i in 0..n {
                let word = draw(0, 15);
                let words = [
                    "amber", "birch", "cedar", "delta", "ember", "fjord", "garnet", "harbor",
                    "iris", "juniper", "kelp", "lumen", "maple", "nectar", "onyx", "pine",
                ];
                source.push_str(&format!("n{i}[{}{i}]\n", words[word]));
            }
            let count = draw(1, n);
            for _ in 0..count {
                let a = draw(0, n - 2);
                let b = draw(a + 1, n - 1);
                source.push_str(&format!("n{a} --> n{b}\n"));
            }
            for profile in [Profile::Vector, Profile::Cell] {
                let mut model = input(&source, profile);
                for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
                    model.direction = direction;
                    let scene = layout(&model).unwrap().0;
                    assert_eq!(
                        scene.validate().unwrap(),
                        None,
                        "seed {seed}: {profile:?} {direction:?}"
                    );
                }
            }
        }
    }
    #[test]
    fn pipeline_components_and_distinct_neighbours() {
        for profile in [Profile::Vector, Profile::Cell] {
            let model = input("flowchart\nA\nB\n", profile);
            let s = layout(&model).unwrap().0;
            let gap = if profile == Profile::Cell { 2 } else { 1536 };
            let a_rect = s.boxes()[0].rect;
            let b_rect = s.boxes()[1].rect;
            if a_rect.y == b_rect.y {
                assert_eq!(b_rect.x - a_rect.x - a_rect.w, gap);
            } else {
                assert_eq!(b_rect.x, a_rect.x);
                assert_eq!(b_rect.y - a_rect.y - a_rect.h, gap);
            }
            assert_eq!(s.boxes()[0].id, "A");
            let a = layout(&input("flowchart\nA --> B\n", profile)).unwrap().0;
            let b = layout(&input("flowchart\nA --> B\nA --> B\nA --> B\n", profile))
                .unwrap()
                .0;
            assert_eq!(a.boxes()[0].rect.w, b.boxes()[0].rect.w);
        }
    }
    #[test]
    fn pipeline_direction_transforms() {
        let mut model = input(
            "flowchart\nA[a<br>b<br>c] --> B[d<br>e<br>f]\n",
            Profile::Cell,
        );
        let views: Vec<_> = [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl]
            .into_iter()
            .map(|d| {
                model.direction = d;
                layout(&model).unwrap().0
            })
            .collect();
        for (i, b) in views[0].boxes().iter().enumerate() {
            let tb = b.rect;
            assert_eq!(tb.w, tb.h);
            assert_eq!(
                views[1].boxes()[i].rect.y,
                views[0].canvas().h - tb.y - tb.h
            );
            assert_eq!(
                views[2].boxes()[i].rect,
                crate::geom::Rect {
                    x: tb.y,
                    y: tb.x,
                    w: tb.h,
                    h: tb.w
                }
            );
            let lr = views[2].boxes()[i].rect;
            assert_eq!(
                views[3].boxes()[i].rect.x,
                views[2].canvas().w - lr.x - lr.w
            );
        }
        for (i, p) in views[0].routes()[0].points.iter().enumerate() {
            let lr = views[2].routes()[0].points[i];
            assert_eq!(lr, crate::geom::Point { x: p.y, y: p.x });
            assert_eq!(views[1].routes()[0].points[i].y, views[0].canvas().h - p.y);
            assert_eq!(views[3].routes()[0].points[i].x, views[2].canvas().w - lr.x);
        }
    }
}
