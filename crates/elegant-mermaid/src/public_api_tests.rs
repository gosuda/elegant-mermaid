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
    assert!(repaired.has_errors());
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
    assert!(
        matches!(layout(&document, &LayoutOptions::default()), Err(RenderError::InvalidDocument { errors }) if errors == count)
    );
    let document = parse("flowchart\nA --> B");
    let mut options = LayoutOptions::default();
    options.limits.max_text_bytes = 1;
    assert!(matches!(
        layout(&document, &options),
        Err(RenderError::TooLarge {
            limit: 1,
            actual: 2
        })
    ));
    options.cancel = Cancel::new();
    options.cancel.cancel();
    assert!(matches!(
        layout(&document, &options),
        Err(RenderError::Cancelled)
    ));
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
    assert!(svg.contains(">Example</title>"));
    assert!(svg.contains(">Two nodes</desc>"));
    let mut options = TextOptions::default();
    options.layout.profile = Profile::Vector;
    let text = render_text(&document, &options)?;
    assert!(text.contains("Alpha"));
    assert!(text.contains("Beta"));
    assert_eq!(document.source(), source);
    assert_eq!(document.diagnostics(), before);
    assert!(
        layout(&document, &LayoutOptions::default())?
            .dump()
            .contains("\"stage\":\"layout\"")
    );
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
        assert!(matches!(
            layout(&document, &options),
            Err(RenderError::InvalidConfig { errors: 1 })
        ));
    }
    let mut options = SvgOptions {
        id_prefix: "1-invalid".into(),
        ..SvgOptions::default()
    };
    assert!(matches!(
        render_svg(&document, &options),
        Err(RenderError::InvalidConfig { errors: 1 })
    ));
    options.id_prefix.clear();
    options.text = TextMode::Paths;
    assert!(matches!(
        render_svg(&document, &options),
        Err(RenderError::InvalidConfig { errors: 1 })
    ));
}

#[test]
fn public_text_budget_counts_resolved_labels_not_source() -> Result<(), RenderError> {
    let mut options = LayoutOptions::default();
    options.limits.max_text_bytes = 2;
    for profile in [Profile::Vector, Profile::Cell] {
        options.profile = profile;
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
        assert!(render_svg(&document, &svg)?.contains(&metadata));
        let text = TextOptions {
            layout: options.clone(),
            ..TextOptions::default()
        };
        assert!(render_text(&document, &text)?.contains('é'));
        options.limits.max_text_bytes = 1;
        assert!(matches!(
            layout(&document, &options),
            Err(RenderError::TooLarge {
                limit: 1,
                actual: 2
            })
        ));
        let svg = SvgOptions {
            layout: options.clone(),
            ..SvgOptions::default()
        };
        assert!(matches!(
            render_svg(&document, &svg),
            Err(RenderError::TooLarge {
                limit: 1,
                actual: 2
            })
        ));
        let text = TextOptions {
            layout: options.clone(),
            ..TextOptions::default()
        };
        assert!(matches!(
            render_text(&document, &text),
            Err(RenderError::TooLarge {
                limit: 1,
                actual: 2
            })
        ));
        options.limits.max_text_bytes = 2;
    }
    Ok(())
}

#[test]
fn public_text_budget_counts_displayed_fallback_ids() -> Result<(), RenderError> {
    let document = parse("flowchart\nFallback");
    let mut options = LayoutOptions::default();
    options.limits.max_text_bytes = 8;
    assert!(layout(&document, &options)?.dump().contains("\"Fallback\""));
    options.limits.max_text_bytes = 7;
    assert!(matches!(
        layout(&document, &options),
        Err(RenderError::TooLarge {
            limit: 7,
            actual: 8
        })
    ));
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
    assert!(matches!(
        layout(&document, &options),
        Err(RenderError::InvalidConfig { errors: 2 })
    ));
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
        assert!(matches!(
            render_svg_str(source, &svg),
            Err(RenderError::Cancelled)
        ));
        assert!(matches!(
            render_text_str(source, &text),
            Err(RenderError::Cancelled)
        ));
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
