use elegant_mermaid::{geom, layout, parse, scene};
use scene::Profile;

type TestResult = Result<(), Box<dyn std::error::Error>>;

fn input(
    source: &str,
    profile: Profile,
) -> Result<layout::input::Input, Box<dyn std::error::Error>> {
    let document = parse(source);
    assert!(!document.has_errors(), "{:?}", document.diagnostics());
    let mut options = scene::DumpOptions {
        profile,
        ..scene::DumpOptions::default()
    };
    document.config().apply_to(&mut options);
    Ok(document
        .resolved()
        .ok_or("missing model")?
        .input(profile, options)?)
}

#[test]
fn authored_padding_is_losslessly_carried_by_model_options() -> TestResult {
    for profile in [Profile::Vector, Profile::Cell] {
        for (padding, height, width) in [
            (None, 3, 15),
            (Some(0), 3, 15),
            (Some(17), 5, 15),
            (Some(64), 9, 17),
        ] {
            let config = padding.map_or_else(String::new, |padding| {
                format!("---\nconfig:\n  flowchart:\n    padding: {padding}\n---\n")
            });
            let source = format!("{config}agentflow-beta\nA\n");
            let input = input(&source, profile)?;
            assert_eq!(
                input.options.config.get("flowchart.padding"),
                padding
                    .map(|value| scene::DumpValue::Integer(i64::from(value)))
                    .as_ref()
            );
            let dump = layout::modeldump::model_dump(&input);
            assert_eq!(dump.contains("\"flowchart.padding\":"), padding.is_some());
            if profile == Profile::Cell {
                let [layout::input::SizeRule::Content(size)] = input.sizes.as_slice() else {
                    return Err("expected one content-sized node".into());
                };
                assert_eq!(
                    *size,
                    geom::Size {
                        w: width,
                        h: height
                    }
                );
            }
        }
    }
    Ok(())
}

#[test]
fn padding_transport_keeps_init_precedence_and_shared_font_configuration() -> TestResult {
    let source = "---\nconfig:\n  fontFamily: Courier\n  flowchart:\n    padding: 64\n---\n%%{init: {\"flowchart\": {\"padding\": 0}}}%%\nagentflow-beta\nA\n";
    for profile in [Profile::Vector, Profile::Cell] {
        let input = input(source, profile)?;
        assert_eq!(
            input.options.config.get("flowchart.padding"),
            Some(&scene::DumpValue::Integer(0))
        );
        assert_eq!(
            input.options.config.get("fontFamily"),
            Some(&scene::DumpValue::String("Courier".into()))
        );
        let dump = layout::modeldump::model_dump(&input);
        assert!(
            dump.contains("\"flowchart.padding\":0,\"fontFamily\":\"Courier\""),
            "{dump}"
        );
    }
    Ok(())
}

#[test]
fn out_of_range_source_padding_keeps_the_existing_absent_value() -> TestResult {
    for padding in ["2147483648", "-2147483649"] {
        let source =
            format!("---\nconfig:\n  flowchart:\n    padding: {padding}\n---\nagentflow-beta\nA\n");
        let input = input(&source, Profile::Cell)?;
        assert!(!input.options.config.contains_key("flowchart.padding"));
    }
    Ok(())
}

#[test]
fn negative_padding_is_rejected_even_without_nodes() -> TestResult {
    let document = parse("---\nconfig:\n  flowchart:\n    padding: -1\n---\nagentflow-beta\n");
    let model = document.resolved().ok_or("missing model")?;
    assert!(matches!(
        model.input(Profile::Cell, scene::DumpOptions::default()),
        Err(geom::GeomError::Domain)
    ));
    Ok(())
}

#[test]
fn collapsed_group_height_rejects_authored_padding_overflow() -> TestResult {
    let source = "---\nconfig:\n  flowchart:\n    padding: 16000000\n---\nagentflow-beta\nflow A[A]\nend\nA@{ view: \"collapsed\" }\n";
    let document = parse(source);
    assert!(!document.has_errors(), "{:?}", document.diagnostics());
    let model = document.resolved().ok_or("missing model")?;
    assert!(matches!(
        model.input(Profile::Vector, scene::DumpOptions::default()),
        Err(geom::GeomError::Overflow)
    ));
    Ok(())
}
