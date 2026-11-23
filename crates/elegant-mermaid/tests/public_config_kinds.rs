use elegant_mermaid::{LayoutOptions, Profile, Severity, Span, layout, parse, scene};

type TestResult = Result<(), Box<dyn std::error::Error>>;

// Kind, source, first over-limit statement, semantic edge count, configured limit.
const EDGE_CASES: &[(&str, &str, &str, usize, usize)] = &[
    ("flowchart", "flowchart LR\nA --> B\n", "A --> B", 1, 0),
    ("swimlane", "swimlane-beta LR\nA --> B\n", "A --> B", 1, 0),
    ("agentflow", "agentflow-beta TB\nA --> B\n", "A --> B", 1, 0),
    (
        "architecture",
        "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\n",
        "a:R -- L:b",
        1,
        0,
    ),
    ("block", "block-beta\nA --> B\n", "A --> B", 1, 0),
    (
        "c4",
        "C4Context\nPerson(a, \"A\")\nPerson(b, \"B\")\nRel(a, b, \"link\")\n",
        "Rel(a, b, \"link\")",
        1,
        0,
    ),
    ("class", "classDiagram\nA --> B\n", "A --> B", 1, 0),
    (
        "cynefin",
        "cynefin-beta\ncomplex --> clear\n",
        "complex --> clear",
        1,
        0,
    ),
    (
        "er",
        "erDiagram\nA ||--o{ B : owns\n",
        "A ||--o{ B : owns",
        1,
        0,
    ),
    (
        "requirement",
        "requirementDiagram\nrequirement A {\n}\nelement B {\n}\nA - satisfies -> B\n",
        "A - satisfies -> B",
        1,
        0,
    ),
    ("sankey", "sankey\nA,B,1\n", "A,B,1", 1, 0),
    ("state", "stateDiagram-v2\nA --> B\n", "A --> B", 1, 0),
    (
        "usecase",
        "usecase-beta\nactor A\nU(Task)\nA --> U\n",
        "A --> U",
        1,
        0,
    ),
    (
        "wardley",
        "wardley-beta\ncomponent A [0.1, 0.2]\ncomponent B [0.3, 0.4]\nA -> B\n",
        "A -> B",
        1,
        0,
    ),
    (
        "eventmodeling",
        "eventmodeling\ntf 01 cmd Add\ntf 02 evt Added\n",
        "tf 02 evt Added",
        1,
        0,
    ),
    (
        "gitgraph",
        "gitGraph\ncommit id: \"A\"\nbranch develop\ncommit id: \"B\"\ncheckout main\ncommit id: \"C\"\nmerge develop\ncherry-pick id: \"B\"\n",
        "cherry-pick id: \"B\"",
        6,
        5,
    ),
    ("ishikawa", "ishikawa-beta\nRoot\n  Child\n", "Child", 1, 0),
    ("mindmap", "mindmap\nRoot\n  Child\n", "Child", 1, 0),
    (
        "treeview",
        "treeView-beta\nRoot\n  Child\n",
        "  Child",
        2,
        1,
    ),
    (
        "sequence",
        "sequenceDiagram\nA->>B: hello\n",
        "A->>B: hello",
        1,
        0,
    ),
];

const OTHER_CASES: &[(&str, &str)] = &[
    ("xychart", "xychart\nx-axis [Alpha, Beta]\nbar [1, 2]\n"),
    ("timeline", "timeline\ntitle History\n1 : First\n"),
    ("railroad", "railroad-beta\nr = terminal(\"Alpha\") ;\n"),
    (
        "radar",
        "radar-beta\naxis Alpha, Beta, Gamma\ncurve c{1, 2, 3}\n",
    ),
    ("info", "info showInfo\n"),
    ("packet", "packet\ntitle Packet\n0-7: \"Alpha\"\n"),
    ("kanban", "kanban\n  todo[To Do]\n    a[Task Alpha]\n"),
    ("pie", "pie\ntitle Portions\n\"Alpha\" : 1\n\"Beta\" : 2\n"),
    (
        "quadrant",
        "quadrantChart\ntitle Priorities\nAlpha: [0.25, 0.75]\n",
    ),
    (
        "journey",
        "journey\ntitle My day\nsection Go\n  Make tea: 5: Me\n",
    ),
    (
        "gantt",
        "gantt\ndateFormat YYYY-MM-DD\nFirst :a, 2024-01-01, 1d\nSecond :b, after a, 1d\n",
    ),
    (
        "venn",
        "venn-beta\ntitle Skills\nset A[\"Alpha\"]:10\nset B[\"Beta\"]:6\nunion A,B[\"Shared\"]:3\n",
    ),
    ("treemap", "treemap-beta\n\"Root\"\n  \"Leaf\": 10\n"),
];

#[test]
fn semantic_edge_limits_keep_statement_spans_in_every_edge_bearing_kind() -> TestResult {
    for &(kind, body, statement, count, limit) in EDGE_CASES {
        let source = format!("---\nconfig:\n  maxEdges: {limit}\n---\n{body}");
        let document = parse(&source);
        assert_eq!(document.kind().map(|kind| kind.id()), Some(kind));
        let errors = document
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{kind}: {errors:?}");
        let diagnostic = errors.first().ok_or("missing edge-limit diagnostic")?;
        assert_eq!(diagnostic.code, "limit/max-edges", "{kind}");
        let start = source.find(statement).ok_or("missing source statement")?;
        assert_eq!(
            diagnostic.span,
            Span {
                start,
                end: start + statement.len(),
            },
            "{kind}",
        );
        assert_eq!(
            diagnostic.message,
            format!("diagram has {count} edges; the limit is {limit}"),
            "{kind}",
        );
    }
    Ok(())
}

#[test]
fn zero_edge_limit_allows_kinds_without_semantic_edge_records() {
    for &(kind, body) in OTHER_CASES {
        let source = format!("---\nconfig:\n  maxEdges: 0\n---\n{body}");
        let document = parse(&source);
        assert_eq!(document.kind().map(|kind| kind.id()), Some(kind));
        assert!(
            !document.has_errors(),
            "{kind}: {:?}",
            document.diagnostics()
        );
    }
}

#[test]
fn font_config_survives_every_kind_adapter_and_keeps_cell_geometry() -> TestResult {
    let cases = EDGE_CASES
        .iter()
        .map(|&(kind, source, _, _, _)| (kind, source))
        .chain(OTHER_CASES.iter().copied());
    let mut kinds = std::collections::BTreeSet::new();
    for (kind, source) in cases {
        assert!(kinds.insert(kind), "duplicate kind {kind}");
        let document = parse(source);
        assert!(
            !document.has_errors(),
            "{kind}: {:?}",
            document.diagnostics()
        );
        for profile in [Profile::Vector, Profile::Cell] {
            let base = LayoutOptions {
                profile,
                ..LayoutOptions::default()
            };
            let before = layout(&document, &base)?;
            let options = LayoutOptions {
                config: Some("fontFamily: Example\n".into()),
                ..base
            };
            let after = layout(&document, &options)?;
            assert!(
                matches!(
                    after.dump_part().options.config.get("fontFamily"),
                    Some(scene::DumpValue::String(value)) if value == "Example",
                ),
                "{kind}: {}",
                after.dump(),
            );
            assert_eq!(before.profile(), after.profile(), "{kind}");
            if after.profile() == scene::Profile::Cell {
                assert_eq!(before.canvas(), after.canvas(), "{kind}");
                assert_eq!(before.boxes(), after.boxes(), "{kind}");
                assert_eq!(before.routes(), after.routes(), "{kind}");
                assert_eq!(before.labels(), after.labels(), "{kind}");
            } else if profile == Profile::Cell {
                // These chart kinds use vector geometry for the braille backend.
                assert!(matches!(kind, "pie" | "radar" | "sankey" | "venn"));
            }
        }
    }
    assert_eq!(kinds.len(), 33);
    Ok(())
}
