use super::input::{Box, Group, Input, Label, Route};
use crate::model::flowchart::Model;
use crate::scene::{BoxRole, Direction, DumpOptions, Profile};

pub fn from_flowchart(model: &Model, profile: Profile, options: DumpOptions) -> Input {
    let direction = Direction::from_token(&model.direction).unwrap_or_default();
    let mut input = Input {
        kind: "flowchart",
        profile,
        direction,
        options,
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: super::input::Spacing::default(),
    };
    append_nodes(&mut input, model);
    append_groups(&mut input, model);
    input.boxes.sort_by_key(|b| declaration(model, &b.id));
    input.labels = input
        .boxes
        .iter()
        .filter(|b| b.text != b.id)
        .map(|b| Label {
            id: format!("{}.label", b.id),
            owner: b.id.clone(),
            role: crate::scene::TextRole::Label,
            text: b.text.clone(),
        })
        .collect();
    append_routes(&mut input, model);
    input
}

fn append_nodes(input: &mut Input, model: &Model) {
    for node in &model.nodes {
        if model.groups.iter().any(|g| g.id == node.id) {
            continue;
        }
        let parent = model
            .groups
            .iter()
            .rev()
            .find(|g| g.members.contains(&node.id))
            .map_or_else(String::new, |g| g.id.clone());
        let text = if node.label_kind.is_some() {
            node.label.clone()
        } else {
            node.id.clone()
        };
        input.boxes.push(Box {
            id: node.id.clone(),
            role: BoxRole::Node,
            shape: node.shape.clone(),
            icon: node.attrs.get("icon").is_some_and(|icon| !icon.is_empty()),
            parent,
            exclusive: true,
            text,
            direction: String::new(),
        });
    }
}

fn append_groups(input: &mut Input, model: &Model) {
    for group in &model.groups {
        input.boxes.push(Box {
            id: group.id.clone(),
            role: BoxRole::Group,
            shape: String::new(),
            icon: false,
            parent: group.parent.clone(),
            exclusive: false,
            text: group.title.clone(),
            direction: Direction::from_token(&group.direction)
                .map_or_else(String::new, |d| d.as_str().into()),
        });
        input.groups.push(Group {
            id: group.id.clone(),
            parent: group.parent.clone(),
            direction: Direction::from_token(&group.direction)
                .map_or_else(String::new, |d| d.as_str().into()),
            direction_span: group.direction_span,
        });
    }
}

fn append_routes(input: &mut Input, model: &Model) {
    let mut blocked: Vec<_> = input
        .boxes
        .iter()
        .filter_map(|b| route_number(&b.id))
        .collect();
    blocked.sort();
    blocked.dedup();
    let mut next = 0usize;
    for edge in &model.edges {
        while blocked.binary_search(&next).is_ok() {
            next += 1;
        }
        let id = format!("e{next}");
        next += 1;
        input.routes.push(Route {
            id: id.clone(),
            from: edge.from.clone(),
            to: edge.to.clone(),
            orthogonal: true,
            marker_start: edge.start.clone(),
            marker_end: edge.marker.clone(),
            line: edge.stroke.clone(),
            min_length: if edge.label.is_some() { 2 } else { 1 },
            from_side: None,
            to_side: None,
        });
        if let Some(text) = &edge.label {
            input.labels.push(Label {
                id: format!("{id}.label"),
                owner: id,
                role: crate::scene::TextRole::Label,
                text: text.clone(),
            });
        }
    }
}

fn route_number(id: &str) -> Option<usize> {
    let suffix = id.strip_prefix('e')?;
    if suffix.is_empty()
        || (suffix.len() > 1 && suffix.starts_with('0'))
        || !suffix.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    suffix.parse().ok()
}

fn declaration(model: &Model, id: &str) -> usize {
    model
        .groups
        .iter()
        .find(|g| g.id == id)
        .map(|g| g.span.start)
        .or_else(|| {
            model
                .nodes
                .iter()
                .find(|n| n.id == id)
                .map(|n| n.first.start)
        })
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::modeldump::model_dump;

    fn build(source: &str) -> Input {
        let parsed = crate::syntax::flowchart::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, diagnostics) = crate::model::flowchart::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        from_flowchart(&model, Profile::Vector, DumpOptions::default())
    }

    #[test]
    fn indented_group_direction_is_explicit_not_inherited() {
        for direction in ["TB", "BT", "LR", "RL"] {
            let input = build(&format!(
                "flowchart RL\nsubgraph G\n    direction {direction}\n A --> B\nend\n"
            ));
            let directions: Vec<&str> = input
                .boxes
                .iter()
                .filter(|b| b.id == "G")
                .map(|b| b.direction.as_str())
                .collect();
            assert_eq!(directions, [direction]);
            assert!(
                model_dump(&input).contains(&format!("\"direction\":\"{direction}\"")),
                "indented_group_direction_is_explicit_not_inherited: input violates model_dump(&input).contains(&format!(\"\\\"direction\\\":\\\"{{direction}}\\\"\")); observed {:?}",
                input
            );
        }
        let input = build("flowchart LR\nsubgraph G\n A --> B\nend\n");
        let directions: Vec<&str> = input
            .boxes
            .iter()
            .filter(|b| b.id == "G")
            .map(|b| b.direction.as_str())
            .collect();
        assert_eq!(directions, [""]);
    }

    #[test]
    fn reversed_label_centres_before_subtracting_half_extent()
    -> Result<(), std::boxed::Box<dyn std::error::Error>> {
        let input = build("flowchart LR\n A -->|workload exits| B\n B -->|run| A\n");
        let scene = crate::layout::families::layout(&input)?.0;
        let route = scene
            .routes()
            .iter()
            .find(|r| r.id == "e1")
            .ok_or("route")?;
        let label = scene
            .labels()
            .iter()
            .find(|l| l.owner == "e1")
            .ok_or("label")?;
        assert_eq!(
            label.rect.x + label.rect.w / 2,
            (route.points[1].x + route.points[4].x) / 2
        );
        Ok(())
    }

    #[test]
    fn independent_frame_uses_child_direction_and_one_padding_band()
    -> Result<(), std::boxed::Box<dyn std::error::Error>> {
        let child = crate::layout::families::layout(&build("flowchart LR\n A --> B\n"))?.0;
        let input = build("flowchart TB\nsubgraph G\n direction LR\n A --> B\nend\n");
        let scene = crate::layout::families::layout(&input)?.0;
        let frame = scene
            .boxes()
            .iter()
            .find(|b| b.id == "G")
            .ok_or("frame")?
            .rect;
        let title = scene
            .items()
            .iter()
            .find(|g| g.owner == "G")
            .and_then(|g| {
                g.items.iter().find_map(|item| match item {
                    crate::scene::Item::Text(text) => Some(text.rect),
                    _ => None,
                })
            })
            .ok_or("title")?;
        assert_eq!(frame.w, child.canvas().w + title.w);
        assert_eq!(frame.h, child.canvas().h);
        assert_eq!(title.x, frame.x + 1024);
        Ok(())
    }
    #[test]
    fn model_dump_label_defaults() {
        for (source, labels, text) in [
            ("flowchart\nA --> B\n", 0, ""),
            ("flowchart\nA[A]\n", 0, ""),
            ("flowchart\nA@{label: \"\"}\n", 1, ""),
        ] {
            let input = build(source);
            assert_eq!(input.labels.len(), labels);
            if let Some(label) = input.labels.first() {
                assert_eq!(label.text, text);
            }
        }
    }

    #[test]
    fn stroke_length_does_not_change_minimum_rank_span() {
        for source in [
            "flowchart\nA --> B\n",
            "flowchart\nA ----> B\n",
            "flowchart\nA ====> B\n",
        ] {
            let input = build(source);
            assert_eq!(input.routes[0].min_length, 1);
        }
        let input = build("flowchart\nA ---->|label| B\n");
        assert_eq!(input.routes[0].min_length, 2);
    }

    #[test]
    fn group_title_fallback_is_not_a_canonical_label() {
        for (source, count, text) in [
            ("flowchart\nsubgraph G\nA\nend\n", 0, ""),
            ("flowchart\nsubgraph G[G]\nA\nend\n", 0, ""),
            ("flowchart\nsubgraph G[Title]\nA\nend\n", 1, "Title"),
            ("flowchart\nsubgraph G[\"\"]\nA\nend\n", 1, ""),
        ] {
            let input = build(source);
            assert_eq!(input.labels.len(), count, "{source}");
            if let Some(label) = input.labels.first() {
                assert_eq!((&*label.owner, &*label.text), ("G", text));
            }
        }
    }

    #[test]
    fn fallback_title_measurement_matches_id() -> Result<(), std::boxed::Box<dyn std::error::Error>>
    {
        for direction in ["LR", "TD"] {
            let mut input = build(&format!(
                "flowchart {direction}\nsubgraph one\nA --> B\nend\n"
            ));
            input.profile = crate::scene::Profile::Cell;
            let scene = crate::layout::families::layout(&input)?.0;
            let title = scene
                .items()
                .iter()
                .find(|group| group.owner == "one")
                .and_then(|group| {
                    group.items.iter().find_map(|item| match item {
                        crate::scene::Item::Text(text) => Some(text),
                        _ => None,
                    })
                })
                .ok_or("missing group title")?;
            assert_eq!((title.rect.w, title.rect.h), (3, 1));
            assert_eq!(title.lines[0][0].text, "one");
        }
        Ok(())
    }

    #[test]
    fn fallback_group_title_keeps_independent_content_geometry()
    -> Result<(), std::boxed::Box<dyn std::error::Error>> {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let mut input = build("flowchart\nsubgraph G\n direction LR\n A --> B\nend\n");
            input.direction = direction;
            let scene = crate::layout::families::layout(&input)?.0;
            assert!(
                !scene.labels().iter().any(|label| label.owner == "G"),
                "fallback_group_title_keeps_independent_content_geometry: input violates !scene.labels().iter().any(|label| label.owner == \"G\"); observed {:?}",
                scene.dump()
            );
            let group = scene
                .items()
                .iter()
                .find(|group| group.owner == "G")
                .ok_or("missing group G scene items")?;
            let title = group
                .items
                .iter()
                .find_map(|item| match item {
                    crate::scene::Item::Text(text) => Some(text),
                    _ => None,
                })
                .ok_or("missing fallback title for group G")?;
            assert_eq!(title.lines[0][0].text, "G");
            let frame = scene
                .boxes()
                .iter()
                .find(|b| b.id == "G")
                .ok_or("missing group G frame")?
                .rect;
            assert!(
                crate::geom::contains(frame, title.rect)?,
                "fallback_group_title_keeps_independent_content_geometry: input violates crate::geom::contains(frame, title.rect)?; observed {:?}",
                (frame, title.rect)
            );
            for child in scene.boxes().iter().filter(|b| b.parent == "G") {
                assert!(
                    crate::geom::contains(frame, child.rect)?,
                    "fallback_group_title_keeps_independent_content_geometry: input violates crate::geom::contains(frame, child.rect)?; observed {:?}",
                    (frame, child.rect, title.rect)
                );
                assert!(
                    !crate::geom::intersects(title.rect, child.rect)?,
                    "fallback_group_title_keeps_independent_content_geometry: input violates !crate::geom::intersects(title.rect, child.rect)?; observed {:?}",
                    (frame, child.rect, title.rect)
                );
            }
        }
        Ok(())
    }

    #[test]
    fn model_dump_explicit_empty_bracket_label() {
        let source = "flowchart\nA[x]\nA --> B\n";
        let parsed = crate::syntax::flowchart::parse(source, &[]);
        let (mut model, _) = crate::model::flowchart::resolve(source, &parsed.document);
        model.nodes[0].label.clear();
        let input = from_flowchart(&model, Profile::Vector, DumpOptions::default());
        assert_eq!(input.labels.len(), 1);
        assert_eq!(input.labels[0].text, "");
        assert_eq!(input.labels[0].owner, "A");
    }

    #[test]
    fn model_dump_golden() {
        let output = model_dump(&build("flowchart\nA -->|yes| B\n"));
        assert_eq!(
            output,
            concat!(
                "{\"version\":1,\"stage\":\"model\",\"kind\":\"flowchart\",\"profile\":\"vector\",\"options\":{\"profile\":\"vector\",\"thoroughness\":3,\"max_width\":0,\"direction\":\"TB\",\"limits\":{\"max_nodes\":2000,\"max_edges\":5000,\"max_text_bytes\":1048576}},\n",
                "\"boxes\":[{\"id\":\"A\",\"role\":\"node\",\"parent\":\"\",\"exclusive\":true},\n{\"id\":\"B\",\"role\":\"node\",\"parent\":\"\",\"exclusive\":true}],\n",
                "\"routes\":[{\"id\":\"e0\",\"from\":\"A\",\"to\":\"B\",\"orthogonal\":true}],\n\"labels\":[{\"id\":\"e0.label\",\"owner\":\"e0\",\"text\":\"yes\",\"lines\":[]}]}\n"
            )
        );
    }

    #[test]
    fn model_dump_shapes_keep_declared_owners() {
        let input =
            build("flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n");
        assert_eq!(
            input
                .boxes
                .iter()
                .map(|b| b.id.as_str())
                .collect::<Vec<_>>(),
            ["A", "B", "C"]
        );
        assert_eq!(
            input
                .labels
                .iter()
                .map(|l| (l.owner.as_str(), l.text.as_str()))
                .collect::<Vec<_>>(),
            [
                ("A", "Start"),
                ("B", "Choice"),
                ("C", "Done"),
                ("e1", "yes"),
                ("e2", "no")
            ]
        );
        assert_eq!(input.direction, Direction::Lr);
        let output = model_dump(&input);
        let boxes = output
            .split("\"boxes\":[")
            .nth(1)
            .and_then(|section| section.split("],\n\"routes\":").next())
            .unwrap_or("");
        for (id, shape) in [("A", None), ("B", Some("diamond")), ("C", None)] {
            let prefix = format!("{{\"id\":\"{id}\",\"role\":\"node\",");
            let record = boxes.lines().find(|line| line.starts_with(&prefix));
            assert!(record.is_some(), "missing source node {id}: {output}");
            let record = record.unwrap_or("");
            if let Some(shape) = shape {
                assert!(
                    record.contains(&format!("\"shape\":\"{shape}\"")),
                    "node {id} must retain its declared shape: {record}"
                );
            } else {
                assert!(
                    !record.contains("\"shape\":"),
                    "default rectangle {id} must omit shape: {record}"
                );
            }
        }
    }

    #[test]
    fn model_dump_corpus_relations() -> Result<(), std::boxed::Box<dyn std::error::Error>> {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/flowchart");
        let mut paths = Vec::new();
        corpus_paths(&root, &mut paths)?;
        paths.sort();
        assert!(
            !paths.is_empty(),
            "model_dump_corpus_relations: input violates !paths.is_empty(); observed {:?}",
            paths
        );
        for path in paths {
            let source = std::fs::read_to_string(path)?;
            let prep = crate::syntax::preprocess::preprocess(&source);
            let parsed = crate::syntax::flowchart::parse(&source, &prep.removed);
            let (model, resolved) = crate::model::flowchart::resolve(&source, &parsed.document);
            if prep
                .diagnostics
                .iter()
                .chain(&parsed.diagnostics)
                .chain(&resolved)
                .any(|d| d.severity == crate::diag::Severity::Error)
            {
                continue;
            }
            let input = from_flowchart(&model, Profile::Vector, DumpOptions::default());
            check_relations(&input);
        }
        Ok(())
    }

    fn corpus_paths(
        root: &std::path::Path,
        paths: &mut Vec<std::path::PathBuf>,
    ) -> std::io::Result<()> {
        for entry in std::fs::read_dir(root)? {
            let path = entry?.path();
            if path.is_dir() {
                corpus_paths(&path, paths)?;
            } else if path.extension().is_some_and(|e| e == "mmd") {
                paths.push(path);
            }
        }
        Ok(())
    }

    fn check_relations(input: &Input) {
        let boxes: std::collections::BTreeSet<_> = input.boxes.iter().map(|b| &b.id).collect();
        let routes: std::collections::BTreeSet<_> = input.routes.iter().map(|r| &r.id).collect();
        let labels: std::collections::BTreeSet<_> = input.labels.iter().map(|l| &l.id).collect();
        assert_eq!(boxes.len(), input.boxes.len());
        assert_eq!(routes.len(), input.routes.len());
        assert_eq!(labels.len(), input.labels.len());
        assert!(
            input
                .routes
                .iter()
                .all(|r| boxes.contains(&r.from) && boxes.contains(&r.to)),
            "check_relations: input violates input .routes .iter() .all(|r| boxes.contains(&r.from) && boxes.contains(&r.to)); observed {:?}",
            input
        );
        assert!(
            input
                .labels
                .iter()
                .all(|l| boxes.contains(&l.owner) || routes.contains(&l.owner)),
            "check_relations: input violates input .labels .iter() .all(|l| boxes.contains(&l.owner) || routes.contains(&l.owner)); observed {:?}",
            input
        );
        let first = model_dump(input);
        assert_eq!(first, model_dump(input));
        for key in ["canvas", "x", "y", "w", "h", "points"] {
            assert!(
                !first.contains(&format!("\"{key}\":")),
                "check_relations: input violates !first.contains(&format!(\"\\\"{{key}}\\\":\")); observed {:?}",
                first
            );
        }
    }
}
