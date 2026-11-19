use crate::*;

#[test]
fn public_source_ownership_and_positions() {
    let source = "flowchart\r\nA[é]\rB";
    let document = parse(source);
    assert_eq!(document.source().as_ptr(), source.as_ptr());
    assert_eq!(document.position(14), Position { line: 2, column: 3 });
    assert_eq!(
        document.position(usize::MAX),
        Position { line: 3, column: 2 }
    );
    let repaired = parse_bytes(b"flowchart\nA[\xff]");
    assert_eq!(repaired.source(), "flowchart\nA[�]");
    assert!(
        repaired.has_errors(),
        "{}; observed: {:?}",
        "Invariant failed: repaired.has_errors()",
        repaired.diagnostics()
    );
    let diagnostic = repaired
        .diagnostics()
        .iter()
        .find(|d| d.code == "source/invalid-utf8");
    assert_eq!(
        diagnostic.map(|d| d.span),
        Some(Span { start: 12, end: 15 })
    );
}

#[test]
fn public_render_errors_and_cancellation() {
    let document = parse("flowchart\nA[unfinished");
    let count = document
        .diagnostics()
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .count();
    {
        let observed = layout(&document, &LayoutOptions::default());
        assert!(
            matches!(&observed, Err(RenderError::InvalidDocument { errors }) if *errors == count),
            "invalid document must report {count} errors; observed: {:?}",
            observed
        );
    };
    let document = parse("flowchart\nA --> B");
    let mut options = LayoutOptions::default();
    options.limits.max_text_bytes = 1;
    {
        let observed = layout(&document, &options);
        assert!(
            matches!(
                &observed,
                Err(RenderError::TooLarge {
                    limit: 1,
                    actual: 2
                })
            ),
            "{}; observed: {:?}",
            "Invariant failed: matches!( layout(&document, &options), Err(RenderError::TooLarge { limit: 1, actual: 2 }) )",
            observed
        );
    };
    options.cancel = Cancel::new();
    options.cancel.cancel();
    {
        let observed = layout(&document, &options);
        assert!(
            matches!(&observed, Err(RenderError::Cancelled)),
            "{}; observed: {:?}",
            "Invariant failed: matches!( layout(&document, &options), Err(RenderError::Cancelled) )",
            observed
        );
    };
}

#[test]
fn public_render_preserves_document_and_metadata() -> Result<(), RenderError> {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<Document<'static>>();
    send_sync::<Scene>();
    let source = "flowchart LR\naccTitle: Example\naccDescr: Two nodes\nA[Alpha] --> B[Beta]\n";
    let document = parse(source);
    let before = document.diagnostics().to_vec();
    let svg = render_svg(&document, &SvgOptions::default())?;
    assert!(
        svg.contains(">Example</title>"),
        "{}; observed: {:?}",
        "Invariant failed: svg.contains(\">Example</title>\")",
        svg
    );
    assert!(
        svg.contains(">Two nodes</desc>"),
        "{}; observed: {:?}",
        "Invariant failed: svg.contains(\">Two nodes</desc>\")",
        svg
    );
    let mut options = TextOptions::default();
    options.layout.profile = Profile::Vector;
    let text = render_text(&document, &options)?;
    assert!(
        text.contains("Alpha"),
        "{}; observed: {:?}",
        "Invariant failed: text.contains(\"Alpha\")",
        text
    );
    assert!(
        text.contains("Beta"),
        "{}; observed: {:?}",
        "Invariant failed: text.contains(\"Beta\")",
        text
    );
    assert_eq!(document.source(), source);
    assert_eq!(document.diagnostics(), before);
    {
        let observed = layout(&document, &LayoutOptions::default())?.dump();
        assert!(
            observed.contains("\"stage\":\"layout\""),
            "{}; observed: {:?}",
            "Invariant failed: layout(&document, &LayoutOptions::default())? .dump() .contains(\"\\\"stage\\\":\\\"layout\\\"\")",
            observed
        );
    };
    Ok(())
}

#[test]
fn public_invalid_options_are_typed() {
    let document = parse("flowchart\nA --> B");
    for config in [
        "[one, two]",
        "plain",
        "null",
        "theme: [",
        "a: 1\na: 2\nbroken: [",
    ] {
        let options = LayoutOptions {
            config: Some(config.into()),
            ..LayoutOptions::default()
        };
        {
            let observed = layout(&document, &options);
            assert!(
                matches!(&observed, Err(RenderError::InvalidConfig { errors: 1 })),
                "{}; observed: {:?}",
                "Invariant failed: matches!( layout(&document, &options), Err(RenderError::InvalidConfig { errors: 1 }) )",
                observed
            );
        };
    }
    let mut options = SvgOptions {
        id_prefix: "1-invalid".into(),
        ..SvgOptions::default()
    };
    {
        let observed = render_svg(&document, &options);
        assert!(
            matches!(&observed, Err(RenderError::InvalidConfig { errors: 1 })),
            "{}; observed: {:?}",
            "Invariant failed: matches!( render_svg(&document, &options), Err(RenderError::InvalidConfig { errors: 1 }) )",
            observed
        );
    };
    options.id_prefix.clear();
    options.text = TextMode::Paths;
    {
        let observed = render_svg(&document, &options);
        assert!(
            matches!(&observed, Err(RenderError::InvalidConfig { errors: 1 })),
            "{}; observed: {:?}",
            "Invariant failed: matches!( render_svg(&document, &options), Err(RenderError::InvalidConfig { errors: 1 }) )",
            observed
        );
    };
}

#[test]
fn public_text_budget_counts_resolved_labels_not_source() -> Result<(), RenderError> {
    for profile in [Profile::Vector, Profile::Cell] {
        let options = LayoutOptions {
            profile,
            limits: Limits {
                max_text_bytes: 2,
                ..Limits::default()
            },
            ..LayoutOptions::default()
        };
        let plain = layout(&parse("flowchart\nA[é]"), &options)?.dump();
        let metadata = "metadata".repeat(128);
        let source = format!(
            "flowchart\n%% {metadata}\naccTitle: {metadata}\naccDescr: {metadata}\nA[#233;]\n"
        );
        let document = parse(&source);
        assert_eq!(layout(&document, &options)?.dump(), plain);
        let svg = SvgOptions {
            layout: options.clone(),
            ..SvgOptions::default()
        };
        {
            let observed = render_svg(&document, &svg)?;
            assert!(
                observed.contains(&metadata),
                "{}; observed: {:?}",
                "Invariant failed: render_svg(&document, &svg)?.contains(&metadata)",
                observed
            );
        };
        let text = TextOptions {
            layout: options.clone(),
            ..TextOptions::default()
        };
        {
            let observed = render_text(&document, &text)?;
            assert!(
                observed.contains('é'),
                "resolved label must retain é; observed: {:?}",
                observed
            );
        };
        let options = LayoutOptions {
            limits: Limits {
                max_text_bytes: 1,
                ..options.limits
            },
            ..options
        };
        {
            let observed = layout(&document, &options);
            assert!(
                matches!(
                    &observed,
                    Err(RenderError::TooLarge {
                        limit: 1,
                        actual: 2
                    })
                ),
                "{}; observed: {:?}",
                "Invariant failed: matches!( layout(&document, &options), Err(RenderError::TooLarge { limit: 1, actual: 2 }) )",
                observed
            );
        };
        let svg = SvgOptions {
            layout: options.clone(),
            ..SvgOptions::default()
        };
        {
            let observed = render_svg(&document, &svg);
            assert!(
                matches!(
                    &observed,
                    Err(RenderError::TooLarge {
                        limit: 1,
                        actual: 2
                    })
                ),
                "{}; observed: {:?}",
                "Invariant failed: matches!( render_svg(&document, &svg), Err(RenderError::TooLarge { limit: 1, actual: 2 }) )",
                observed
            );
        };
        let text = TextOptions {
            layout: options.clone(),
            ..TextOptions::default()
        };
        {
            let observed = render_text(&document, &text);
            assert!(
                matches!(
                    &observed,
                    Err(RenderError::TooLarge {
                        limit: 1,
                        actual: 2
                    })
                ),
                "{}; observed: {:?}",
                "Invariant failed: matches!( render_text(&document, &text), Err(RenderError::TooLarge { limit: 1, actual: 2 }) )",
                observed
            );
        };
    }
    Ok(())
}

#[test]
fn public_text_budget_counts_displayed_fallback_ids() -> Result<(), RenderError> {
    let document = parse("flowchart\nFallback");
    let mut options = LayoutOptions::default();
    options.limits.max_text_bytes = 8;
    {
        let observed = layout(&document, &options)?.dump();
        assert!(
            observed.contains("\"Fallback\""),
            "{}; observed: {:?}",
            "Invariant failed: layout(&document, &options)?.dump().contains(\"\\\"Fallback\\\"\")",
            observed
        );
    };
    options.limits.max_text_bytes = 7;
    {
        let observed = layout(&document, &options);
        assert!(
            matches!(
                &observed,
                Err(RenderError::TooLarge {
                    limit: 7,
                    actual: 8
                })
            ),
            "{}; observed: {:?}",
            "Invariant failed: matches!( layout(&document, &options), Err(RenderError::TooLarge { limit: 7, actual: 8 }) )",
            observed
        );
    };
    Ok(())
}

#[test]
fn public_config_accepts_empty_and_valid_mappings() -> Result<(), RenderError> {
    let document = parse("flowchart\nA");
    let default = layout(&document, &LayoutOptions::default())?.dump();
    for config in ["", " \n  \r\n", "# comment\n", "{}", "layout: elk\n"] {
        let options = LayoutOptions {
            config: Some(config.into()),
            ..LayoutOptions::default()
        };
        assert_eq!(layout(&document, &options)?.dump(), default);
    }
    Ok(())
}

#[test]
fn public_config_counts_duplicate_entries() {
    let document = parse("flowchart\nA");
    let options = LayoutOptions {
        config: Some("a: 1\na: 2\nb: 1\nb: 2\n".into()),
        ..LayoutOptions::default()
    };
    {
        let observed = layout(&document, &options);
        assert!(
            matches!(&observed, Err(RenderError::InvalidConfig { errors: 2 })),
            "{}; observed: {:?}",
            "Invariant failed: matches!( layout(&document, &options), Err(RenderError::InvalidConfig { errors: 2 }) )",
            observed
        );
    };
}

#[test]
fn public_source_renderers_observe_preexisting_cancellation() {
    let cancel = Cancel::new();
    cancel.cancel();
    let mut svg = SvgOptions::default();
    svg.layout.cancel = cancel.clone();
    let mut text = TextOptions::default();
    text.layout.cancel = cancel;
    for source in ["flowchart\nA[unfinished", "flowchart\nA[é]", ""] {
        {
            let observed = render_svg_str(source, &svg);
            assert!(
                matches!(&observed, Err(RenderError::Cancelled)),
                "{}; observed: {:?}",
                "Invariant failed: matches!( render_svg_str(source, &svg), Err(RenderError::Cancelled) )",
                observed
            );
        };
        {
            let observed = render_text_str(source, &text);
            assert!(
                matches!(&observed, Err(RenderError::Cancelled)),
                "{}; observed: {:?}",
                "Invariant failed: matches!( render_text_str(source, &text), Err(RenderError::Cancelled) )",
                observed
            );
        };
    }
}

#[test]
fn public_renderers_force_their_output_profile() -> Result<(), RenderError> {
    let document = parse("flowchart\nA[Alpha] --> B[Beta]");
    let mut svg = SvgOptions::default();
    let vector = render_svg(&document, &svg)?;
    svg.layout.profile = Profile::Cell;
    svg.layout.max_width = 1;
    assert_eq!(render_svg(&document, &svg)?, vector);
    let mut text = TextOptions::default();
    let cell = render_text(&document, &text)?;
    text.layout.profile = Profile::Cell;
    assert_eq!(render_text(&document, &text)?, cell);
    Ok(())
}
