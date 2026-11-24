use elegant_mermaid::{
    Diagnostic, LayoutOptions, Limits, Profile, RenderError, Severity, Span, SvgOptions, layout,
    measure, parse, parse_bytes, render_svg,
};

type TestResult = Result<(), Box<dyn std::error::Error>>;

fn one_diagnostic<'a>(
    diagnostics: &'a [Diagnostic],
    code: &str,
) -> Result<&'a Diagnostic, &'static str> {
    let mut matching = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == code);
    let diagnostic = matching.next().ok_or("missing diagnostic")?;
    assert!(
        matching.next().is_none(),
        "duplicate {code}: {diagnostics:?}"
    );
    Ok(diagnostic)
}

#[test]
fn default_text_limit_counts_repaired_source_bytes_and_is_inclusive() -> TestResult {
    let mut source = String::from("flowchart\nA\n%% ");
    source.push_str(&"x".repeat(50_000 - source.len()));
    assert!(!parse(&source).has_errors());
    source.push('x');
    let document = parse(&source);
    let diagnostic = one_diagnostic(document.diagnostics(), "limit/max-text-size")?;
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(
        diagnostic.span,
        Span {
            start: 50_000,
            end: 50_001
        }
    );
    assert_eq!(
        diagnostic.message,
        "source has 50001 bytes; the limit is 50000 bytes"
    );
    assert_eq!(diagnostic.help, "Shorten the source, or raise maxTextSize.");

    let mut bytes = source.into_bytes();
    bytes.truncate(49_999);
    bytes.push(0xff);
    let document = parse_bytes(&bytes);
    assert_eq!(document.source().len(), 50_002);
    let diagnostic = one_diagnostic(document.diagnostics(), "limit/max-text-size")?;
    assert_eq!(
        diagnostic.span,
        Span {
            start: 50_000,
            end: 50_002
        }
    );
    assert_eq!(
        diagnostic.message,
        "source has 50002 bytes; the limit is 50000 bytes"
    );
    one_diagnostic(document.diagnostics(), "source/invalid-utf8")?;
    Ok(())
}

#[test]
fn source_edge_limit_counts_resolved_records_and_marks_the_whole_statement() -> TestResult {
    let source = "---\nconfig:\n  maxEdges: 1\n---\nflowchart\nA --> A\nA --> B --> A\n";
    let document = parse(source);
    let diagnostic = one_diagnostic(document.diagnostics(), "limit/max-edges")?;
    let start = source.find("A --> B").ok_or("missing second statement")?;
    assert_eq!(
        diagnostic.span,
        Span {
            start,
            end: source.len() - 1
        }
    );
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(diagnostic.message, "diagram has 3 edges; the limit is 1");
    assert_eq!(
        diagnostic.help,
        "Reduce the number of edges, or raise maxEdges."
    );

    let source = format!("flowchart\n{}", "A --> A\n".repeat(501));
    let document = parse(&source);
    let diagnostic = one_diagnostic(document.diagnostics(), "limit/max-edges")?;
    assert_eq!(
        diagnostic.span,
        Span {
            start: source.len() - 8,
            end: source.len() - 1
        }
    );
    assert_eq!(
        diagnostic.message,
        "diagram has 501 edges; the limit is 500"
    );
    Ok(())
}

#[test]
fn higher_options_caps_recover_without_mutating_the_document() -> TestResult {
    let mut source = String::from("flowchart\nA[Alphabet]\n%% ");
    source.push_str(&"x".repeat(50_001 - source.len()));
    let document = parse(&source);
    let original = document.diagnostics().to_vec();
    assert!(matches!(
        layout(&document, &LayoutOptions::default()),
        Err(RenderError::InvalidDocument { errors: 1 })
    ));
    for profile in [Profile::Vector, Profile::Cell] {
        let options = LayoutOptions {
            profile,
            config: Some("maxTextSize: 50001\n".into()),
            ..LayoutOptions::default()
        };
        layout(&document, &options)?;
        assert_eq!(document.diagnostics(), original);
    }
    assert!(document.has_errors());
    assert!(matches!(
        layout(&document, &LayoutOptions::default()),
        Err(RenderError::InvalidDocument { errors: 1 })
    ));

    let document = parse("---\nconfig:\n  maxEdges: 0\n---\nflowchart\nA --> B\n");
    let original = document.diagnostics().to_vec();
    let options = LayoutOptions {
        config: Some("maxEdges: 1\n".into()),
        ..LayoutOptions::default()
    };
    layout(&document, &options)?;
    assert_eq!(document.diagnostics(), original);
    Ok(())
}

#[test]
fn cap_precedence_and_model_limits_remain_distinct() -> TestResult {
    let source = "---\nconfig:\n  maxEdges: 0\n---\n%%{init: {'maxEdges': 1}}%%\n%%{init: {'maxEdges': 2}}%%\nflowchart\nA --> B --> A\n";
    let document = parse(source);
    assert!(!document.has_errors(), "{:?}", document.diagnostics());
    layout(&document, &LayoutOptions::default())?;
    let too_small = LayoutOptions {
        config: Some("maxEdges: 1\n".into()),
        ..LayoutOptions::default()
    };
    assert!(matches!(
        layout(&document, &too_small),
        Err(RenderError::InvalidDocument { errors: 1 })
    ));
    let model_limit = LayoutOptions {
        config: Some("maxEdges: 2\n".into()),
        limits: Limits {
            max_edges: 1,
            ..Limits::default()
        },
        ..LayoutOptions::default()
    };
    assert!(matches!(
        layout(&document, &model_limit),
        Err(RenderError::TooLarge {
            limit: 1,
            actual: 2
        })
    ));
    let zero = parse("---\nconfig:\n  maxEdges: 0\n---\nflowchart\nA\n");
    assert!(!zero.has_errors(), "{:?}", zero.diagnostics());
    Ok(())
}

#[test]
fn config_values_are_checked_at_source_and_option_boundaries() -> TestResult {
    for key in ["maxTextSize", "maxEdges"] {
        for value in ["-1", "2147483648", "1.5", "'1'", "true", "null", "[]", "{}"] {
            let text = format!("{key}: {value}\n");
            let source = format!("---\nconfig:\n  {text}---\nflowchart\nA\n");
            let document = parse(&source);
            let diagnostic = one_diagnostic(document.diagnostics(), "config/malformed")?;
            let start = source.find(key).ok_or("missing config key")?;
            assert_eq!(
                diagnostic.span,
                Span {
                    start,
                    end: start + key.len()
                }
            );
            let options = LayoutOptions {
                config: Some(format!("{key}: 2147483647\n")),
                ..LayoutOptions::default()
            };
            assert!(matches!(
                layout(&document, &options),
                Err(RenderError::InvalidDocument { errors: 1 })
            ));

            let document = parse("flowchart\nA\n");
            let options = LayoutOptions {
                config: Some(text),
                ..LayoutOptions::default()
            };
            assert!(
                matches!(
                    layout(&document, &options),
                    Err(RenderError::InvalidConfig { errors: 1 })
                ),
                "{key}: {value}"
            );
        }
    }
    let document = parse("flowchart\nA\n");
    let options = LayoutOptions {
        config: Some("maxEdges: -1\nmaxTextSize: false\nfontFamily: 5\n".into()),
        ..LayoutOptions::default()
    };
    assert!(matches!(
        layout(&document, &options),
        Err(RenderError::InvalidConfig { errors: 3 })
    ));
    Ok(())
}

#[test]
fn font_family_is_escaped_announced_and_changes_only_vector_measurements() -> TestResult {
    let source = "---\nconfig:\n  fontFamily: 'Custom & <Font>'\n---\nflowchart\nA[Alphabet]\n";
    let document = parse(source);
    let diagnostic = one_diagnostic(document.diagnostics(), "config/font-metrics-approximate")?;
    assert_eq!(diagnostic.severity, Severity::Info);
    assert_eq!(
        diagnostic.message,
        "text width is measured with Inter; fontFamily is Custom & <Font>"
    );
    assert_eq!(
        diagnostic.help,
        "Text widths may differ from the font named in fontFamily."
    );
    let start = source.find("fontFamily").ok_or("missing font key")?;
    assert_eq!(
        diagnostic.span,
        Span {
            start,
            end: start + "fontFamily".len()
        }
    );
    let svg = render_svg(&document, &SvgOptions::default())?;
    assert!(
        svg.contains("font-family='Custom &amp; &lt;Font&gt;'"),
        "{svg}"
    );

    let plain = parse("flowchart\nA -->|Alphabet| B\n");
    for profile in [Profile::Vector, Profile::Cell] {
        let base = LayoutOptions {
            profile,
            ..LayoutOptions::default()
        };
        let configured = LayoutOptions {
            config: Some("fontFamily: Custom\n".into()),
            ..base.clone()
        };
        let before = layout(&plain, &base)?;
        let after = layout(&plain, &configured)?;
        let old = before.labels().first().ok_or("missing plain label")?;
        let new = after.labels().first().ok_or("missing configured label")?;
        if profile == Profile::Vector {
            let metric = measure::Metric::for_role(measure::Role::Label);
            assert_eq!(old.rect.w, metric.width("Alphabet")?);
            assert_eq!(new.rect.w, metric.with_font_family().width("Alphabet")?);
        } else {
            assert_eq!(before.canvas(), after.canvas());
            assert_eq!(before.labels(), after.labels());
        }
    }
    Ok(())
}

#[test]
fn site_font_family_overrides_source_and_empty_clears_it() -> TestResult {
    let source = "---\nconfig:\n  fontFamily: Front\n---\n%%{init: {'fontFamily': 'Init'}}%%\nflowchart\nA\n";
    let document = parse(source);
    assert!(render_svg(&document, &SvgOptions::default())?.contains("font-family='Init'"));
    let options = SvgOptions {
        layout: LayoutOptions {
            config: Some("fontFamily: Site\n".into()),
            ..LayoutOptions::default()
        },
        ..SvgOptions::default()
    };
    assert!(render_svg(&document, &options)?.contains("font-family='Site'"));
    let options = SvgOptions {
        layout: LayoutOptions {
            config: Some("fontFamily: ''\n".into()),
            ..LayoutOptions::default()
        },
        ..SvgOptions::default()
    };
    assert!(!render_svg(&document, &options)?.contains("font-family='Init'"));
    assert_eq!(
        one_diagnostic(document.diagnostics(), "config/font-metrics-approximate")?.message,
        "text width is measured with Inter; fontFamily is Init"
    );
    Ok(())
}

#[test]
fn unknown_keys_preserve_authored_paths_and_leave_opaque_mappings_alone() -> TestResult {
    let source = "---\nconfig:\n  typo: {nested: true}\n  xyChart:\n    xAxis:\n      typo: true\n    yAxis:\n      showLabel: true\n  themeVariables: {arbitrary: value}\n---\nflowchart\nA\n";
    let document = parse(source);
    let original = document.diagnostics().to_vec();
    let warnings = document
        .diagnostics()
        .iter()
        .filter(|diagnostic| diagnostic.code == "config/unknown-key")
        .collect::<Vec<_>>();
    assert_eq!(warnings.len(), 2, "{warnings:?}");
    for (diagnostic, message) in warnings.iter().zip([
        "unknown config key typo",
        "unknown config key xyChart.xAxis.typo",
    ]) {
        assert_eq!(diagnostic.severity, Severity::Warning);
        assert_eq!(diagnostic.message, message);
        assert_eq!(&source[diagnostic.span.start..diagnostic.span.end], "typo");
        assert_eq!(
            diagnostic.help,
            "Check the spelling of the key, or remove it."
        );
    }
    let config_text = "fontFamily: Site\nxyChart:\n  xAxis:\n    misspelled: true\n";
    let effective = document.effective_config(Some(config_text))?;
    let diagnostics = document.diagnostics_for(&effective);
    let site_warning = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.message == "unknown config key xyChart.xAxis.misspelled")
        .ok_or("missing site warning")?;
    assert_eq!(site_warning.severity, Severity::Warning);
    assert_eq!(site_warning.span, Span { start: 0, end: 0 });
    let font = one_diagnostic(&diagnostics, "config/font-metrics-approximate")?;
    assert_eq!(font.span, Span { start: 0, end: 0 });
    assert_eq!(
        font.message,
        "text width is measured with Inter; fontFamily is Site"
    );
    layout(
        &document,
        &LayoutOptions {
            config: Some(config_text.into()),
            ..LayoutOptions::default()
        },
    )?;
    assert_eq!(document.diagnostics(), original);
    Ok(())
}

#[test]
fn aliased_config_blocks_validate_nested_keys_with_authored_paths() -> TestResult {
    for block in ["quadrantChart", "wardley-beta"] {
        let source = format!("---\nconfig:\n  {block}: {{typo: true}}\n---\nflowchart\nA\n");
        let document = parse(&source);
        let diagnostic = one_diagnostic(document.diagnostics(), "config/unknown-key")?;
        assert_eq!(diagnostic.severity, Severity::Warning);
        assert_eq!(diagnostic.message, format!("unknown config key {block}.typo"));
        assert_eq!(&source[diagnostic.span.start..diagnostic.span.end], "typo");

        let document = parse("flowchart\nA\n");
        let effective = document.effective_config(Some(&format!("{block}: {{typo: true}}\n")))?;
        let diagnostics = document.diagnostics_for(&effective);
        let diagnostic = one_diagnostic(&diagnostics, "config/unknown-key")?;
        assert_eq!(diagnostic.message, format!("unknown config key {block}.typo"));
        assert_eq!(diagnostic.span, Span { start: 0, end: 0 });
    }
    Ok(())
}

#[test]
fn configured_font_reaches_pre_measured_table_bodies() -> TestResult {
    for source in [
        "classDiagram\nclass A {\n+longAlphabeticalMemberNameUsedForMeasurement\n}\n",
        "erDiagram\nA {\nstring longAlphabeticalAttributeNameUsedForMeasurement\n}\n",
        "requirementDiagram\nrequirement R {\ntext: long alphabetical field text used for measurement\n}\n",
    ] {
        let document = parse(source);
        assert!(
            !document.has_errors(),
            "{source}: {:?}",
            document.diagnostics()
        );
        for profile in [Profile::Vector, Profile::Cell] {
            let options = LayoutOptions {
                profile,
                ..LayoutOptions::default()
            };
            let before = layout(&document, &options)?;
            let configured = LayoutOptions {
                config: Some("fontFamily: Other\n".into()),
                ..options
            };
            let after = layout(&document, &configured)?;
            let old = before.boxes().first().ok_or("missing table box")?;
            let new = after
                .boxes()
                .first()
                .ok_or("missing configured table box")?;
            if profile == Profile::Vector {
                assert!(new.rect.w > old.rect.w, "{source}: {old:?} -> {new:?}");
                assert_eq!(new.rect.h, old.rect.h, "{source}");
            } else {
                assert_eq!(before.canvas(), after.canvas(), "{source}");
                assert_eq!(before.boxes(), after.boxes(), "{source}");
                assert_eq!(before.labels(), after.labels(), "{source}");
                assert_eq!(before.routes(), after.routes(), "{source}");
            }
        }
    }
    Ok(())
}

#[test]
fn effective_error_counts_keep_source_failures_and_recompute_caps() -> TestResult {
    let source = "---\nconfig:\n  maxTextSize: 0\n  maxEdges: -1\n---\nflowchart\nA\n";
    let document = parse(source);
    assert!(matches!(
        layout(&document, &LayoutOptions::default()),
        Err(RenderError::InvalidDocument { errors: 2 })
    ));
    let raised = LayoutOptions {
        config: Some("maxTextSize: 2147483647\nmaxEdges: 2147483647\n".into()),
        ..LayoutOptions::default()
    };
    assert!(matches!(
        layout(&document, &raised),
        Err(RenderError::InvalidDocument { errors: 1 })
    ));
    let malformed = LayoutOptions {
        config: Some("maxTextSize: -1\n".into()),
        ..LayoutOptions::default()
    };
    assert!(matches!(
        layout(&document, &malformed),
        Err(RenderError::InvalidDocument { errors: 2 })
    ));
    let valid = parse("flowchart\nA\n");
    layout(&valid, &raised)?;
    let zero = LayoutOptions {
        config: Some("maxTextSize: -0\nmaxEdges: +0\n".into()),
        ..LayoutOptions::default()
    };
    assert!(matches!(
        layout(&valid, &zero),
        Err(RenderError::InvalidDocument { errors: 1 })
    ));
    Ok(())
}
