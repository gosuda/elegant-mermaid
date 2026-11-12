use super::input::{Box, Group, Input, Label, Route};
use crate::model::flowchart::Model;
use crate::scene::{BoxRole, Direction, DumpOptions, Profile};
use crate::syntax::flowchart::ast::{Document, Line, Statement};

pub fn from_flowchart(
    document: &Document,
    model: &Model,
    profile: Profile,
    options: DumpOptions,
) -> Input {
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
    };
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
        let text = effective_text(document, node);
        input.boxes.push(Box {
            id: node.id.clone(),
            role: BoxRole::Node,
            shape: node.shape.clone(),
            parent,
            exclusive: true,
            text,
        });
    }
    for group in &model.groups {
        input.boxes.push(Box {
            id: group.id.clone(),
            role: BoxRole::Group,
            shape: String::new(),
            parent: group.parent.clone(),
            exclusive: false,
            text: String::new(),
        });
        input.groups.push(Group {
            id: group.id.clone(),
            parent: group.parent.clone(),
            direction: group.direction.clone(),
            text: group.title.clone(),
        });
    }
    input.boxes.sort_by_key(|b| declaration(model, &b.id));
    input.labels = input
        .boxes
        .iter()
        .filter(|b| b.role == BoxRole::Node && b.text != b.id)
        .map(|b| Label {
            id: format!("{}.label", b.id),
            owner: b.id.clone(),
            role: crate::scene::TextRole::Label,
            text: b.text.clone(),
        })
        .collect();
    for (index, edge) in model.edges.iter().enumerate() {
        let id = format!("e{index}");
        input.routes.push(Route {
            id: id.clone(),
            from: edge.from.clone(),
            to: edge.to.clone(),
            orthogonal: true,
            marker_start: edge.start.clone(),
            marker_end: edge.marker.clone(),
            line: edge.stroke.clone(),
            min_length: edge.length.max(if edge.label.is_some() { 2 } else { 1 }),
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
    input
}

fn effective_text(document: &Document, node: &crate::model::flowchart::Node) -> String {
    if node.attrs.contains_key("label")
        || !node.label.is_empty()
        || has_label(&document.lines, &node.id)
    {
        node.label.clone()
    } else {
        node.id.clone()
    }
}

fn has_label(lines: &[Line], id: &str) -> bool {
    lines.iter().any(|line| match &line.kind {
        Statement::Subgraph(group) => has_label(&group.body, id),
        Statement::Vertex(statement) => std::iter::once(&statement.first)
            .chain(statement.rest.iter().map(|(_, group)| group))
            .flat_map(|group| &group.nodes)
            .any(|node| node.vertex.id.text == id && node.vertex.label.is_some()),
        _ => false,
    })
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
        from_flowchart(
            &parsed.document,
            &model,
            Profile::Vector,
            DumpOptions::default(),
        )
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
    fn model_dump_explicit_empty_bracket_label() {
        let source = "flowchart\nA[x]\nA --> B\n";
        let parsed = crate::syntax::flowchart::parse(source, &[]);
        let (mut model, _) = crate::model::flowchart::resolve(source, &parsed.document);
        model.nodes[0].label.clear();
        let input = from_flowchart(
            &parsed.document,
            &model,
            Profile::Vector,
            DumpOptions::default(),
        );
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
    fn model_dump_demo() {
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
        assert_eq!(
            model_dump(&input),
            concat!(
                "{\"version\":1,\"stage\":\"model\",\"kind\":\"flowchart\",\"profile\":\"vector\",\"options\":{\"profile\":\"vector\",\"thoroughness\":3,\"max_width\":0,\"direction\":\"LR\",\"limits\":{\"max_nodes\":2000,\"max_edges\":5000,\"max_text_bytes\":1048576}},\n",
                "\"boxes\":[{\"id\":\"A\",\"role\":\"node\",\"parent\":\"\",\"exclusive\":true},\n",
                "{\"id\":\"B\",\"role\":\"node\",\"parent\":\"\",\"exclusive\":true},\n",
                "{\"id\":\"C\",\"role\":\"node\",\"parent\":\"\",\"exclusive\":true}],\n",
                "\"routes\":[{\"id\":\"e0\",\"from\":\"A\",\"to\":\"B\",\"orthogonal\":true},\n",
                "{\"id\":\"e1\",\"from\":\"B\",\"to\":\"C\",\"orthogonal\":true},\n",
                "{\"id\":\"e2\",\"from\":\"B\",\"to\":\"A\",\"orthogonal\":true}],\n",
                "\"labels\":[{\"id\":\"A.label\",\"owner\":\"A\",\"text\":\"Start\",\"lines\":[]},\n",
                "{\"id\":\"B.label\",\"owner\":\"B\",\"text\":\"Choice\",\"lines\":[]},\n",
                "{\"id\":\"C.label\",\"owner\":\"C\",\"text\":\"Done\",\"lines\":[]},\n",
                "{\"id\":\"e1.label\",\"owner\":\"e1\",\"text\":\"yes\",\"lines\":[]},\n",
                "{\"id\":\"e2.label\",\"owner\":\"e2\",\"text\":\"no\",\"lines\":[]}]}\n"
            )
        );
    }

    #[test]
    fn model_dump_corpus_relations() -> Result<(), std::boxed::Box<dyn std::error::Error>> {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/flowchart");
        let mut paths = Vec::new();
        corpus_paths(&root, &mut paths)?;
        paths.sort();
        assert!(!paths.is_empty());
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
            let input = from_flowchart(
                &parsed.document,
                &model,
                Profile::Vector,
                DumpOptions::default(),
            );
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
                .all(|r| boxes.contains(&r.from) && boxes.contains(&r.to))
        );
        assert!(
            input
                .labels
                .iter()
                .all(|l| boxes.contains(&l.owner) || routes.contains(&l.owner))
        );
        let first = model_dump(input);
        assert_eq!(first, model_dump(input));
        for key in ["canvas", "x", "y", "w", "h", "points"] {
            assert!(!first.contains(&format!("\"{key}\":")));
        }
    }
}
