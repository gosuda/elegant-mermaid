use crate::emd_call;
use crate::options::{Op, OptionError, parse};

const DEMO: &str = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";

fn rejected(key: &str) -> String {
    format!(
        "{{\"ok\":false,\"output\":\"invalid option: {key}\",\"diagnostics\":[],\"applied\":0}}"
    )
}

#[test]
fn version_matches_the_cli() {
    assert_eq!(
        emd_call("version", "", ""),
        "{\"ok\":true,\"output\":\"emd 0.1.0\\n\",\"diagnostics\":[],\"applied\":0}"
    );
}

#[test]
fn unknown_op_is_rejected_as_op() {
    assert_eq!(emd_call("explain", DEMO, ""), rejected("op"));
}

#[test]
fn unknown_key_wrong_type_and_bad_json_are_rejected() {
    assert_eq!(emd_call("check", DEMO, "{\"bogus\":1}"), rejected("bogus"));
    assert_eq!(
        emd_call("render_svg", DEMO, "{\"theme\":5}"),
        rejected("theme")
    );
    assert_eq!(
        emd_call("render_text", DEMO, "{\"charset\":\"latin\"}"),
        rejected("charset")
    );
    assert_eq!(
        emd_call("layout", DEMO, "{\"stage\":\"model\",\"profile\":null}"),
        rejected("profile")
    );
    assert_eq!(
        emd_call("render_text", DEMO, "{\"max_width\":-1}"),
        rejected("max_width")
    );
    assert_eq!(
        emd_call("render_text", DEMO, "{\"max_width\":1.5}"),
        rejected("max_width")
    );
    for text in [
        "[]",
        "{",
        "{\"theme\"}",
        "{} {}",
        "{\"theme\":\"x\",}",
        "nul",
    ] {
        assert_eq!(emd_call("check", DEMO, text), rejected("options"), "{text}");
    }
}

#[test]
fn keys_the_op_does_not_read_are_ignored() {
    let text = "{\"theme\":\"nord\",\"max_width\":null,\"charset\":\"ascii\"}";
    assert!(parse(Op::Check, text).is_ok());
    assert!(parse(Op::Layout, text).is_ok());
    assert_eq!(
        parse(Op::Layout, "{\"theme\":5,\"profile\":\"cell\"}").map(|o| o.cell),
        Ok(true)
    );
    assert_eq!(
        parse(Op::RenderSvg, "{\"profile\":3}").map(|o| o.cell),
        Ok(false)
    );
}

#[test]
fn unknown_key_wins_before_a_later_syntax_error() {
    assert_eq!(
        parse(Op::Check, "{\"bogus\":1,\"theme\":}").err(),
        Some(OptionError::Rejected("bogus".to_owned()))
    );
}

#[test]
fn width_accepts_null_and_non_negative_integers() {
    assert_eq!(
        parse(Op::RenderText, "{\"max_width\":null}").map(|o| o.width),
        Ok(0)
    );
    assert_eq!(
        parse(Op::RenderText, "{\"max_width\":80}").map(|o| o.width),
        Ok(80)
    );
    assert_eq!(
        parse(Op::RenderText, "{\"max_width\":-0}").map(|o| o.width),
        Ok(0)
    );
    assert!(parse(Op::RenderText, "{\"max_width\":2147483648}").is_err());
}

#[test]
fn background_null_and_empty_mean_the_theme_bg() {
    assert_eq!(
        parse(Op::RenderSvg, "{\"background\":null}").map(|o| o.background),
        Ok(String::new())
    );
    assert_eq!(
        parse(Op::RenderSvg, "{\"background\":\"\\u0023fff\"}").map(|o| o.background),
        Ok("#fff".to_owned())
    );
}

#[test]
fn lint_object_follows_the_emd_json_shape() {
    let text = "{\"lint\":{\"select\":[\"common/acc-title-missing\"],\"ignore\":[\"flowchart/duplicate-ids\"],\"severity\":{\"common/no-experimental\":\"info\",\"common/acc-descr-missing\":\"off\"}}}";
    let config = parse(Op::Lint, text).map(|o| o.lint).unwrap_or_default();
    assert_eq!(config.select, ["common/acc-title-missing"]);
    assert_eq!(config.ignore, ["flowchart/duplicate-ids"]);
    assert_eq!(config.off, ["common/acc-descr-missing"]);
    assert_eq!(config.severity.len(), 1);
    for bad in [
        "{\"lint\":[]}",
        "{\"lint\":{\"other\":[]}}",
        "{\"lint\":{\"select\":[1]}}",
        "{\"lint\":{\"severity\":{\"common/no-experimental\":\"fatal\"}}}",
        "{\"lint\":{\"severity\":{\"common/no-experimental\":null}}}",
    ] {
        assert_eq!(
            parse(Op::Fix, bad).err(),
            Some(OptionError::Rejected("lint".to_owned())),
            "{bad}"
        );
    }
}

#[test]
fn check_reports_the_stdin_document() {
    let response = emd_call("check", DEMO, "");
    assert!(response.starts_with("{\"ok\":true,\"output\":\"{\\\"version\\\":1,"));
    assert!(response.contains("\\\"path\\\":\\\"<stdin>\\\",\\\"kind\\\":\\\"flowchart\\\""));
    assert!(response.ends_with(",\"diagnostics\":[],\"applied\":0}"));
}

#[test]
fn check_and_render_report_errors_with_spans() {
    let source = "flowchart LR\n  A[Start --> B\n";
    for op in ["check", "render_svg", "render_text", "layout"] {
        let response = emd_call(op, source, "");
        assert!(response.starts_with("{\"ok\":false,\"output\":"), "{op}");
        assert!(
            response.contains("\"code\":\"flowchart/unclosed-node-bracket\""),
            "{op}"
        );
    }
    for op in ["render_svg", "render_text", "layout"] {
        assert!(emd_call(op, source, "").starts_with("{\"ok\":false,\"output\":\"\","));
    }
}

#[test]
fn render_text_draws_boxes_and_an_unknown_theme_fails() {
    let response = emd_call("render_text", DEMO, "");
    assert!(response.starts_with("{\"ok\":true,\"output\":\""));
    assert!(response.contains("Choice"));
    let failed = emd_call("render_text", DEMO, "{\"theme\":\"no-such-theme\"}");
    assert!(failed.starts_with("{\"ok\":false,\"output\":\"\","));
    assert!(failed.contains("\"diagnostics\":[],"));
}

#[test]
fn render_svg_rejects_a_bad_background() {
    let svg = emd_call("render_svg", DEMO, "{\"background\":\"#ffffff\"}");
    assert!(svg.starts_with("{\"ok\":true,\"output\":\"<svg"));
    let bad = emd_call("render_svg", DEMO, "{\"background\":\"white\"}");
    assert!(bad.starts_with("{\"ok\":false,\"output\":\"\","));
}

#[test]
fn layout_stages_and_profiles_print_the_dump() {
    let model = emd_call("layout", DEMO, "{\"stage\":\"model\"}");
    assert!(model.contains("\\\"stage\\\":\\\"model\\\""));
    let cell = emd_call("layout", DEMO, "{\"profile\":\"cell\"}");
    assert!(cell.contains("\\\"profile\\\":\\\"cell\\\""));
    assert!(cell.contains("\\\"stage\\\":\\\"layout\\\""));
}

#[test]
fn fix_returns_the_source_and_its_remaining_diagnostics() {
    let response = emd_call("fix", DEMO, "");
    assert!(response.starts_with("{\"ok\":true,\"output\":\"flowchart LR\\n"));
    assert!(response.ends_with(",\"applied\":0}"));
}

#[test]
fn lint_reports_the_stdin_document() {
    let response = emd_call("lint", DEMO, "{\"lint\":{}}");
    assert!(response.starts_with("{\"ok\":true,\"output\":\"{\\\"version\\\":1,"));
}

#[test]
fn control_characters_and_line_separators_are_escaped_like_go() {
    let response = emd_call("fix", "\u{1}\u{2028}x", "");
    assert!(response.starts_with("{\"ok\":true,\"output\":\"\\u0001\\u2028x\""));
}

const DUPLICATE: &str = "flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n";
const SUPPRESSED: &str = "flowchart LR\n  A[Start] --> B[End]\n  %% emd-disable-next-line flowchart/duplicate-ids: ids collide upstream\n  A[Begin] --> C[End]\n";

#[test]
fn lint_reports_an_error_and_a_next_line_suppression_removes_it() {
    let failed = emd_call("lint", DUPLICATE, "");
    assert!(failed.starts_with("{\"ok\":false,\"output\":\""));
    assert!(failed.contains("\"code\":\"flowchart/duplicate-ids\""));
    assert!(failed.ends_with(",\"applied\":0}"));
    let kept = emd_call("lint", SUPPRESSED, "");
    assert!(kept.starts_with("{\"ok\":true,\"output\":\""));
    assert!(
        kept.ends_with(",\"diagnostics\":[],\"applied\":0}"),
        "{kept}"
    );
}

#[test]
fn fix_keeps_the_text_and_drops_the_suppressed_diagnostic() {
    let response = emd_call("fix", SUPPRESSED, "");
    assert!(response.starts_with("{\"ok\":true,\"output\":\"flowchart LR\\n"));
    assert!(
        response.ends_with(",\"diagnostics\":[],\"applied\":0}"),
        "{response}"
    );
    let remaining = emd_call("fix", DUPLICATE, "");
    assert!(remaining.contains("\"code\":\"flowchart/duplicate-ids\""));
    assert!(remaining.ends_with(",\"applied\":0}"));
}

#[test]
fn lint_severity_and_ignore_options_change_the_report() {
    let info = emd_call(
        "lint",
        DUPLICATE,
        "{\"lint\":{\"severity\":{\"flowchart/duplicate-ids\":\"info\"}}}",
    );
    assert!(info.starts_with("{\"ok\":true,"));
    assert!(info.contains("\"severity\":\"info\""));
    let ignored = emd_call(
        "lint",
        DUPLICATE,
        "{\"lint\":{\"ignore\":[\"flowchart/duplicate-ids\"]},\"max\":\"unsafe\"}",
    );
    assert!(
        ignored.ends_with(",\"diagnostics\":[],\"applied\":0}"),
        "{ignored}"
    );
}

#[test]
fn unknown_lint_codes_and_shapes_are_rejected_as_lint() {
    for options in [
        "{\"lint\":{\"select\":[\"nope\"]}}",
        "{\"lint\":{\"ignore\":[\"flowchart/duplicate-ids\",\"bogus\"]}}",
        "{\"lint\":{\"severity\":{\"nope/x\":\"info\"}}}",
        "{\"lint\":{\"severity\":{\"flowchart/duplicate-ids\":\"fatal\"}}}",
        "{\"lint\":{\"Select\":[]}}",
        "{\"lint\":{\"extra\":1}}",
        "{\"lint\":null}",
        "{\"lint\":[]}",
    ] {
        for op in ["lint", "fix"] {
            assert_eq!(
                emd_call(op, DUPLICATE, options),
                rejected("lint"),
                "{op} {options}"
            );
        }
    }
    let plain = emd_call("check", DUPLICATE, "");
    let keyed = emd_call("check", DUPLICATE, "{\"lint\":{\"select\":[\"nope\"]}}");
    assert_eq!(keyed, plain, "an option the op does not read is ignored");
}
