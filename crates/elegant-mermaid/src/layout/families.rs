use super::{
    input::Input,
    layered::{LayoutError, pipeline},
};
use crate::scene::Scene;

pub struct Family {
    pub kind: &'static str,
    pub layout: fn(&Input) -> Result<(Scene, bool), LayoutError>,
}
pub const FAMILIES: &[Family] = &[Family {
    kind: "flowchart",
    layout: flowchart,
}];
pub fn layout(input: &Input) -> Result<(Scene, Vec<crate::diag::Diagnostic>), LayoutError> {
    let family = FAMILIES
        .iter()
        .find(|f| f.kind == input.kind)
        .ok_or(LayoutError::Domain)?;
    let (scene, budget) = (family.layout)(input)?;
    let diagnostics = if budget {
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
    Ok((scene, diagnostics))
}

fn flowchart(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let edges = input
        .routes
        .iter()
        .map(|r| {
            Ok(pipeline::EdgeOptions {
                marker_start: scene_marker(&r.marker_start),
                marker_end: scene_marker(&r.marker_end),
                stroke: &r.line,
                min_length: i32::try_from(r.min_length).map_err(|_| LayoutError::Overflow)?,
            })
        })
        .collect::<Result<Vec<_>, LayoutError>>()?;
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
        super::super::flowchart::from_flowchart(
            &parsed.document,
            &model,
            profile,
            DumpOptions::default(),
        )
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
        assert_eq!(FAMILIES.len(), 1);
        let a = layout(&input("flowchart\nA[x] --> B[y]\n", Profile::Vector))
            .unwrap()
            .0;
        let b = layout(&input("flowchart\nA[x] --> B[y]\n", Profile::Cell))
            .unwrap()
            .0;
        assert_eq!(
            a.boxes().iter().map(|b| &b.id).collect::<Vec<_>>(),
            b.boxes().iter().map(|b| &b.id).collect::<Vec<_>>()
        );
        assert!(a.labels().is_empty());
        assert!(
            a.items()
                .iter()
                .flat_map(|g| &g.items)
                .any(|i| matches!(i, crate::scene::Item::Text(_)))
        );
    }
    #[test]
    fn pipeline_demo_and_directions() {
        let source =
            "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";
        for (profile, width, height) in [(Profile::Vector, 25830, 2304), (Profile::Cell, 41, 3)] {
            let mut model = input(source, profile);
            let s = layout(&model).unwrap().0;
            assert_eq!(
                s.canvas(),
                crate::geom::Size {
                    w: width,
                    h: height
                }
            );
            assert_eq!(s.boxes()[0].rect.x, 0);
            assert_eq!(s.routes()[2].points[0].x, s.boxes()[1].rect.x);
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
            assert_eq!(s.boxes()[1].rect.x - s.boxes()[0].rect.w, gap);
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
