use elegant_mermaid::{LayoutOptions, Limits, Profile, RenderError, Span, layout, model, parse};

#[test]
fn public_options_reject_values_outside_shared_integer_range() {
    let document = parse("flowchart\nA --> B");
    for value in [i32::MAX.unsigned_abs() + 1, u32::MAX] {
        let invalid = [
            LayoutOptions {
                max_width: value,
                ..LayoutOptions::default()
            },
            LayoutOptions {
                limits: Limits {
                    max_nodes: value,
                    ..Limits::default()
                },
                ..LayoutOptions::default()
            },
            LayoutOptions {
                limits: Limits {
                    max_edges: value,
                    ..Limits::default()
                },
                ..LayoutOptions::default()
            },
            LayoutOptions {
                limits: Limits {
                    max_text_bytes: value,
                    ..Limits::default()
                },
                ..LayoutOptions::default()
            },
        ];
        for options in invalid {
            for profile in [Profile::Vector, Profile::Cell] {
                let options = LayoutOptions {
                    profile,
                    ..options.clone()
                };
                assert!(
                    matches!(
                        layout(&document, &options),
                        Err(RenderError::InvalidConfig { errors: 1 })
                    ),
                    "out-of-range options must fail before layout: {options:?}"
                );
            }
        }
    }
}

#[test]
fn public_zero_limits_remain_invalid() {
    let document = parse("flowchart\nA --> B");
    for limits in [
        Limits {
            max_nodes: 0,
            ..Limits::default()
        },
        Limits {
            max_edges: 0,
            ..Limits::default()
        },
        Limits {
            max_text_bytes: 0,
            ..Limits::default()
        },
    ] {
        for profile in [Profile::Vector, Profile::Cell] {
            let options = LayoutOptions {
                limits,
                profile,
                ..LayoutOptions::default()
            };
            assert!(matches!(
                layout(&document, &options),
                Err(RenderError::InvalidConfig { errors: 1 })
            ));
        }
    }
}

#[test]
fn public_options_accept_largest_shared_integer() -> Result<(), RenderError> {
    let document = parse("flowchart\nA --> B");
    let max = i32::MAX.unsigned_abs();
    for profile in [Profile::Vector, Profile::Cell] {
        let options = LayoutOptions {
            profile,
            max_width: max,
            limits: Limits {
                max_nodes: max,
                max_edges: max,
                max_text_bytes: max,
            },
            ..LayoutOptions::default()
        };
        layout(&document, &options)?;
    }
    Ok(())
}

#[test]
fn public_flowchart_nesting_is_bounded_and_recovers() -> Result<(), &'static str> {
    for depth in [64, 65, 1024] {
        let mut source = String::from("flowchart\n");
        for index in 0..depth {
            source.push_str(&format!("subgraph group{index}\n"));
        }
        source.push_str("Inside\n");
        source.push_str(&"end\n".repeat(depth));
        source.push_str("After --> Done\n");
        let document = parse(&source);
        if depth == 64 {
            assert!(!document.has_errors(), "{:#?}", document.diagnostics());
        } else {
            let start = source
                .find("subgraph group64")
                .ok_or("missing boundary group")?;
            let diagnostics = document.diagnostics();
            assert_eq!(diagnostics.len(), 1, "depth {depth}: {diagnostics:#?}");
            assert_eq!(diagnostics[0].code, "limit/nesting-depth");
            assert_eq!(diagnostics[0].message, "nesting depth exceeds 64");
            assert_eq!(
                diagnostics[0].help,
                "Reduce the nesting to 64 levels or fewer."
            );
            assert_eq!(
                diagnostics[0].span,
                Span {
                    start,
                    end: start + "subgraph".len()
                }
            );
        }
        let Some(model::Resolved::Flowchart(model)) = document.resolved() else {
            return Err("flowchart must retain its model after parsing");
        };
        assert!(model.nodes.iter().any(|node| node.id == "After"));
        assert!(model.nodes.iter().any(|node| node.id == "Done"));
        assert!(
            !model
                .groups
                .iter()
                .any(|group| group.members.iter().any(|id| id == "After" || id == "Done")),
            "nodes after the subtree must remain outside every subgraph"
        );
    }
    Ok(())
}

#[test]
fn public_flowchart_nesting_recovery_respects_subgraph_headings() -> Result<(), &'static str> {
    let bodies = [
        (
            "opening keyword in heading",
            r#"subgraph hidden subgraph
Hidden["subgraph end"]
Hidden -->|end subgraph| Other
end
"#,
        ),
        (
            "closing keyword in heading",
            "subgraph other end\nOtherNode\nend\n",
        ),
        (
            "adjacent bracketed headings",
            "subgraph bracketed[Title] subgraph child[Title]\nSkipped\nend\nend\n",
        ),
    ];
    for (name, body) in bodies {
        let mut source = String::from("flowchart\n");
        for index in 0..64 {
            source.push_str(&format!("subgraph group{index}\n"));
        }
        source.push_str("subgraph overflow\n");
        source.push_str(body);
        source.push_str("end\nVisible\n");
        source.push_str(&"end\n".repeat(64));
        source.push_str("After\n");
        let document = parse(&source);
        let diagnostics = document.diagnostics();
        assert_eq!(diagnostics.len(), 1, "{name}: {diagnostics:#?}");
        assert_eq!(diagnostics[0].code, "limit/nesting-depth", "{name}");
        let Some(model::Resolved::Flowchart(model)) = document.resolved() else {
            return Err("flowchart must retain its model after parsing");
        };
        assert_eq!(model.groups.len(), 65, "{name}");
        let overflow = model
            .groups
            .iter()
            .find(|group| group.id == "overflow")
            .ok_or("overflow group must be retained")?;
        assert!(overflow.members.is_empty(), "{name}");
        let parent = model
            .groups
            .iter()
            .find(|group| group.id == "group63")
            .ok_or("innermost parent must be retained")?;
        assert_eq!(parent.members, ["Visible"], "{name}");
        assert_eq!(model.nodes.len(), 2, "{name}");
        assert!(
            model.nodes.iter().any(|node| node.id == "Visible"),
            "{name}"
        );
        assert!(model.nodes.iter().any(|node| node.id == "After"), "{name}");
        assert!(
            !model
                .groups
                .iter()
                .any(|group| group.members.iter().any(|id| id == "After")),
            "{name}: the node after the subtree must remain outside every subgraph"
        );
    }
    Ok(())
}
