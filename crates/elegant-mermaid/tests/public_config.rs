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

    let plain = parse("flowchart\nA[Alphabet]\n");
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
