#![expect(
    clippy::unwrap_used,
    reason = "each test asserts its preconditions first, so an unwrap is a proven invariant"
)]

use crate::diag::{Diagnostic, FixSafety, Severity};
use crate::lint::config::find_config;
use crate::lint::config::parse_config;
use crate::lint::{apply_fixes as apply, lint, lint_document};
use crate::options::LintConfig;
use crate::source::Span;

use support::{GOLDEN, checked, codes};

mod support {
    use super::*;

    pub const GOLDEN: &str = include_str!("../../../../spec/golden/lint/error-duplicate-ids.mmd");

    pub fn checked(source: &str) -> crate::Document<'_> {
        let document = crate::parse(source);
        assert!(
            !document
                .diagnostics()
                .iter()
                .any(|d| d.code == "common/unknown-diagram-kind"),
            "test source must parse: {:?}",
            document.diagnostics()
        );
        document
    }

    pub fn codes(ds: &[Diagnostic]) -> Vec<&'static str> {
        ds.iter().map(|d| d.code).collect()
    }

    pub fn tmp_dir(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("emd-lint-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }
}

#[test]
fn suppression() {
    let config = LintConfig::default();
    suppress_next_line(&config);
    suppress_range(&config);
    report_unused(&config);
    report_unknown_rule(&config);
    report_malformed(&config);
    report_duplicate_disable(&config);
    report_stray_enable(&config);
    keep_parser_errors(&config);
    guard_meta_codes(&config);
    suppress_firing_warning(&config);
    suppress_file_form(&config);
}

fn suppress_next_line(config: &LintConfig) {
    let next_line = "flowchart LR\n  A[Start] --> B[End]\n  %% emd-disable-next-line flowchart/duplicate-ids: ids collide\n  A[Begin] --> C[End]\n";
    let out = lint(&checked(next_line), config);
    assert_eq!(codes(&out), Vec::<&'static str>::new());
}

fn suppress_range(config: &LintConfig) {
    let range = "flowchart LR\n  %% emd-disable flowchart/duplicate-ids: ids\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n  %% emd-enable flowchart/duplicate-ids\n  A[X] --> C\n";
    let out = lint(&checked(range), config);
    assert_eq!(out.len(), 1, "got {:?}", codes(&out));
    assert_eq!(out[0].code, "flowchart/duplicate-ids");
    assert_eq!(
        out[0].span,
        Span {
            start: 145,
            end: 146
        }
    );
}

fn report_unused(config: &LintConfig) {
    let unused =
        "flowchart LR\n  %% emd-disable-next-line common/acc-title-missing: none\n  A --> B\n";
    let out = lint(&checked(unused), config);
    assert_eq!(codes(&out), ["meta/unused-suppression"]);
}

fn report_unknown_rule(config: &LintConfig) {
    let unknown = "flowchart LR\n  %% emd-disable-diagram no-such/rule, flowchart/duplicate-ids: ids\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n";
    let out = lint(&checked(unknown), config);
    assert_eq!(codes(&out), ["meta/unknown-rule"]);
    assert_eq!(out[0].message, "unknown rule no-such/rule");
}

fn report_malformed(config: &LintConfig) {
    let malformed = "flowchart LR\n  %% emd-disable-diagram flowchart/duplicate-ids\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n";
    let out = lint(&checked(malformed), config);
    assert_eq!(
        codes(&out),
        ["meta/malformed-suppression", "flowchart/duplicate-ids"]
    );
    let empty_codes = "flowchart LR\n  %% emd-disable-diagram : ids\n  A --> B\n";
    let out = lint(&checked(empty_codes), config);
    assert_eq!(codes(&out), ["meta/malformed-suppression"]);
}

fn report_duplicate_disable(config: &LintConfig) {
    let duplicate_disable = "flowchart LR\n  %% emd-disable flowchart/duplicate-ids: first\n  A[Start] --> B[End]\n  %% emd-disable flowchart/duplicate-ids: second\n  A[Begin] --> C[End]\n";
    let out = lint(&checked(duplicate_disable), config);
    assert_eq!(codes(&out), ["meta/malformed-suppression"]);
    let twice = "flowchart LR\n  %% emd-disable-diagram flowchart/duplicate-ids: first\n  A[Start] --> B[End]\n  %% emd-disable-diagram flowchart/duplicate-ids: second\n  A[Begin] --> C[End]\n";
    assert_eq!(
        codes(&lint(&checked(twice), config)),
        Vec::<&'static str>::new()
    );
}

fn report_stray_enable(config: &LintConfig) {
    let stray_enable = "flowchart LR\n  %% emd-enable flowchart/duplicate-ids\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n";
    let out = lint(&checked(stray_enable), config);
    assert_eq!(
        codes(&out),
        ["meta/malformed-suppression", "flowchart/duplicate-ids"]
    );
}

fn keep_parser_errors(config: &LintConfig) {
    let maid_error =
        "flowchart LR\n  %% emd-disable-diagram flowchart/arrow-invalid: kept\n  A -> B\n";
    let out = lint_document(&checked(maid_error), config);
    assert_eq!(
        codes(&out),
        ["meta/malformed-suppression", "flowchart/arrow-invalid"]
    );
    assert!(
        out.iter()
            .any(|d| d.code == "flowchart/arrow-invalid" && d.severity == Severity::Error)
    );
}

fn guard_meta_codes(config: &LintConfig) {
    let meta_named = "flowchart LR\n  %% emd-disable-diagram meta/unknown-rule: never\n  A --> B\n";
    let out = lint(&checked(meta_named), config);
    assert_eq!(codes(&out), ["meta/malformed-suppression"]);
}

fn suppress_firing_warning(config: &LintConfig) {
    let beta = "block-beta\n  %% emd-disable-diagram common/no-experimental: beta\n  a --> b\n";
    let out = lint(&checked(beta), config);
    assert_eq!(codes(&out), Vec::<&'static str>::new());
    let bare = lint(&checked("block-beta\n  a --> b\n"), config);
    assert_eq!(codes(&bare), ["common/no-experimental"]);
}

fn suppress_file_form(config: &LintConfig) {
    let file_form = "<!-- emd-disable-file flowchart/duplicate-ids: ids -->\n```mermaid\nflowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n```\n";
    let document = crate::parse("flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n");
    let mut file = crate::lint::suppression::file_suppressions(
        file_form,
        &[Span {
            start: 55,
            end: file_form.len(),
        }],
    );
    let pass = crate::lint::engine::host_pass(&document, config, &mut file);
    assert!(pass.lint.is_empty());
    assert!(file.meta().is_empty());
    let bare = crate::lint::engine::pass(&document, config);
    assert_eq!(codes(&bare.lint), ["flowchart/duplicate-ids"]);
    let mut idle = crate::lint::suppression::file_suppressions(
        "<!-- emd-disable-file common/acc-title-missing: none -->\n",
        &[],
    );
    let idle_pass = crate::lint::engine::host_pass(&document, config, &mut idle);
    assert_eq!(codes(&idle_pass.lint), ["flowchart/duplicate-ids"]);
    assert_eq!(codes(&idle.meta()), ["meta/unused-suppression"]);
}

#[test]
fn emd_json() {
    parse_valid_config();
    reject_invalid_configs();
    reject_unknown_codes();
    locate_config_files();
    apply_effective_set(GOLDEN);
}

fn parse_valid_config() {
    let parsed = parse_config(
        "emd.json",
        "{\"lint\":{\"select\":[\"common/acc-title-missing\"],\"ignore\":[\"common/no-experimental\"],\"severity\":{\"flowchart/duplicate-ids\":\"info\"}}}",
    )
    .unwrap();
    assert_eq!(parsed.select, ["common/acc-title-missing"]);
    assert_eq!(parsed.ignore, ["common/no-experimental"]);
    assert_eq!(
        parsed.severity.get("flowchart/duplicate-ids"),
        Some(&Severity::Info)
    );
    assert!(parsed.off.is_empty());

    let off = parse_config(
        "emd.json",
        "{\"lint\":{\"severity\":{\"common/acc-title-missing\":\"off\"}}}",
    )
    .unwrap();
    assert_eq!(off.off, ["common/acc-title-missing"]);
    assert!(off.severity.is_empty());

    let empty_select = parse_config("emd.json", "{\"lint\":{\"select\":[]}}").unwrap();
    assert!(empty_select.select.is_empty());
}

fn reject_invalid_configs() {
    let errors = [
        (
            "{\"other\":1}",
            "invalid emd.json emd.json: unknown key \"other\"",
        ),
        ("{", "invalid emd.json emd.json: not valid JSON"),
        (
            "3",
            "invalid emd.json emd.json: top level must be a JSON object",
        ),
        (
            "{\"lint\":3}",
            "invalid emd.json emd.json: lint must be a JSON object",
        ),
        (
            "{\"mermaid\":3}",
            "invalid emd.json emd.json: mermaid must be a JSON object",
        ),
        (
            "{\"lint\":{\"select\":[3]}}",
            "invalid emd.json emd.json: lint.select must be an array of strings",
        ),
        (
            "{\"lint\":{\"severity\":{\"common/no-experimental\":\"loud\"}}}",
            "invalid emd.json emd.json: lint.severity \"common/no-experimental\" must be error, warning, info, or off",
        ),
        (
            "{\"lint\":{\"spelling\":1}}",
            "invalid emd.json emd.json: unknown key \"lint.spelling\"",
        ),
    ];
    for (text, message) in errors {
        let error = parse_config("emd.json", text).unwrap_err().to_string();
        assert_eq!(error, message);
    }
}

fn reject_unknown_codes() {
    let unknown =
        parse_config("emd.json", "{\"lint\":{\"select\":[\"flowchart/nope\"]}}").unwrap_err();
    assert_eq!(
        unknown.to_string(),
        "unknown diagnostic code: flowchart/nope; use a code printed by emd check or emd lint"
    );
    let known = parse_config(
        "emd.json",
        "{\"lint\":{\"ignore\":[\"source/invalid-utf8\"]}}",
    );
    assert!(known.is_ok());
}

fn locate_config_files() {
    use support::tmp_dir;

    let root = tmp_dir("json");
    std::fs::write(
        root.join("emd.json"),
        "{\"lint\":{\"select\":[\"common/acc-title-missing\"]}}",
    )
    .unwrap();
    let nested = root.join("a").join("b");
    std::fs::create_dir_all(&nested).unwrap();
    assert_eq!(find_config(&nested), Some(root.join("emd.json")));
    let empty = tmp_dir("empty");
    assert_eq!(find_config(&empty), None);
    let loaded = crate::lint::load_config(&root.join("emd.json")).unwrap();
    assert_eq!(loaded.select, ["common/acc-title-missing"]);
}

fn apply_effective_set(golden: &str) {
    let selected = LintConfig {
        select: vec!["common/acc-title-missing".into()],
        ..LintConfig::default()
    };
    let out = lint(&checked(golden), &selected);
    assert!(codes(&out).contains(&"common/acc-title-missing"));
    assert_eq!(
        out.iter()
            .find(|d| d.code == "common/acc-title-missing")
            .unwrap()
            .severity,
        Severity::Warning
    );

    let over = LintConfig {
        severity: [("common/acc-title-missing".to_owned(), Severity::Error)]
            .into_iter()
            .collect(),
        ..LintConfig::default()
    };
    let out = lint(&checked(golden), &over);
    assert_eq!(
        out.iter()
            .find(|d| d.code == "common/acc-title-missing")
            .unwrap()
            .severity,
        Severity::Error
    );

    let ignored = LintConfig {
        ignore: vec!["flowchart/duplicate-ids".into()],
        ..LintConfig::default()
    };
    assert!(!codes(&lint(&checked(golden), &ignored)).contains(&"flowchart/duplicate-ids"));

    let offed = LintConfig {
        select: vec!["common/acc-title-missing".into()],
        off: vec!["common/acc-title-missing".into()],
        ..LintConfig::default()
    };
    assert!(!codes(&lint(&checked(golden), &offed)).contains(&"common/acc-title-missing"));
}

#[test]
fn alias_codes_name_their_current_rule_in_the_configuration() {
    let alias = "flowchart/node-unclosed-bracket";
    let current = "flowchart/unclosed-node-bracket";
    assert!(crate::lint::describe(alias).is_some_and(|row| row.code == current));
    let text = format!(
        "{{\"lint\":{{\"select\":[\"{alias}\"],\"ignore\":[\"{alias}\"],\"severity\":{{\"{alias}\":\"info\"}}}}}}"
    );
    let config = parse_config("emd.json", &text).unwrap();
    assert_eq!(config.select, [alias]);
    let err = parse_config(
        "emd.json",
        "{\"lint\":{\"ignore\":[\"flowchart/node-nope\"]}}",
    )
    .unwrap_err();
    assert!(
        err.to_string()
            .starts_with("unknown diagnostic code: flowchart/node-nope")
    );
    let dup = "flowchart LR\n  A[S] --> B[E]\n  A[T] --> C[E]\n";
    let by_alias = LintConfig {
        ignore: vec!["flowchart/duplicate-ids".into()],
        ..LintConfig::default()
    };
    assert!(lint(&checked(dup), &by_alias).is_empty());
}

#[test]
fn the_unknown_code_error_follows_go_order_select_ignore_off_severity() {
    let text = "{\"lint\":{\"select\":[],\"ignore\":[\"nope/b\"],\"severity\":{\"nope/a\":\"off\",\"nope/c\":\"info\"}}}";
    let err = parse_config("emd.json", text).unwrap_err().to_string();
    assert!(err.starts_with("unknown diagnostic code: nope/b;"), "{err}");
    let text = "{\"lint\":{\"severity\":{\"nope/z\":\"off\",\"nope/a\":\"info\"}}}";
    let err = parse_config("emd.json", text).unwrap_err().to_string();
    assert!(err.starts_with("unknown diagnostic code: nope/z;"), "{err}");
}

#[test]
fn emd_json_follows_the_go_json_decoder() {
    let ok = [
        "{\"lint\":{\"select\":null}}",
        "{\"lint\":{\"ignore\":null,\"severity\":{}}}",
        "{\"mermaid\":{\"theme\":\"dark\",\"n\":[1.5e3,-0,true,null]}}",
        "{\"lint\":{\"ignore\":[\"flowchart/duplicate-ids\"],\"ignore\":[]}}",
    ];
    for text in ok {
        assert!(parse_config("emd.json", text).is_ok(), "{text}");
    }
    let invalid_json = [
        "{\"lint\":{\"select\":tru}}",
        "{\"mermaid\":{\"n\":01}}",
        "{\"mermaid\":{\"n\":1.}}",
        "{\"mermaid\":\"a\tb\"}",
        "{\"mermaid\":{\"n\":-}}",
    ];
    for text in invalid_json {
        let err = parse_config("emd.json", text).unwrap_err().to_string();
        assert_eq!(err, "invalid emd.json emd.json: not valid JSON", "{text}");
    }
    let wrong_type = parse_config("emd.json", "{\"lint\":{\"severity\":{\"a\":1}}}").unwrap_err();
    assert_eq!(
        wrong_type.to_string(),
        "invalid emd.json emd.json: lint.severity must be a JSON object"
    );
    let first_unknown = parse_config("emd.json", "{\"zzz\":1,\"aaa\":2}").unwrap_err();
    assert_eq!(
        first_unknown.to_string(),
        "invalid emd.json emd.json: unknown key \"aaa\""
    );
    let null_element = parse_config("emd.json", "{\"lint\":{\"select\":[null]}}").unwrap_err();
    assert!(
        null_element
            .to_string()
            .starts_with("unknown diagnostic code: ;")
    );
}

#[test]
fn no_experimental_names_the_header_token_and_needs_the_beta_suffix() {
    let config = LintConfig {
        select: vec!["common/no-experimental".into()],
        ..LintConfig::default()
    };
    let beta = crate::parse("block-beta\n  columns 1\n");
    let out = lint(&beta, &config);
    assert_eq!(codes(&out), ["common/no-experimental"]);
    assert_eq!(out[0].message, "block-beta is a beta diagram type");
    let plain = crate::parse("block\n  columns 1\n");
    assert!(lint(&plain, &config).is_empty());
    let upper = crate::parse("BLOCK-BETA\n");
    assert_eq!(
        lint(&upper, &config)[0].message,
        "BLOCK-BETA is a beta diagram type"
    );
}

#[test]
fn meta_diagnostics_obey_select_ignore_and_severity() {
    let unused = "flowchart LR\n  %% emd-disable-next-line flowchart/duplicate-ids: r\n  A --> B\n";
    let document = checked(unused);
    assert_eq!(
        codes(&lint(&document, &LintConfig::default())),
        ["meta/unused-suppression"]
    );
    let ignored = LintConfig {
        ignore: vec!["meta/unused-suppression".into()],
        ..LintConfig::default()
    };
    assert!(lint(&document, &ignored).is_empty());
    let selected = LintConfig {
        select: vec!["flowchart/duplicate-ids".into()],
        ..LintConfig::default()
    };
    assert!(lint(&document, &selected).is_empty());
    let info = LintConfig {
        severity: [("meta/unused-suppression".to_owned(), Severity::Info)]
            .into_iter()
            .collect(),
        ..LintConfig::default()
    };
    assert_eq!(lint(&document, &info)[0].severity, Severity::Info);
}

#[test]
fn apply_fixes() {
    let config = LintConfig::default();
    fix_safe_arrow(&config);
    fix_unsafe_stray_end(&config);
    fix_past_shifted_error(&config);
    fix_shifted_open_bracket(&config);
    fix_two_arrows(&config);
    skip_suppressed_fix(&config);
    repair_invalid_utf8(&config);
}

fn fix_safe_arrow(config: &LintConfig) {
    let arrows = "flowchart LR\n  A -> B\n";
    let out = apply(arrows.as_bytes(), config, FixSafety::Safe);
    assert_eq!(out.text, "flowchart LR\n  A --> B\n");
    assert_eq!(out.applied, 1);
}

fn fix_unsafe_stray_end(config: &LintConfig) {
    let stray = "flowchart TD\n  A --> B\n  end\n";
    let out = apply(stray.as_bytes(), config, FixSafety::Safe);
    assert_eq!(out.text, stray);
    assert_eq!(out.applied, 0);
    let out = apply(stray.as_bytes(), config, FixSafety::Unsafe);
    assert_eq!(out.text, "flowchart TD\n  A --> B\n");
    assert_eq!(out.applied, 1);
}

fn fix_past_shifted_error(config: &LintConfig) {
    let shifted = "flowchart TD\n  A -> B\n  end\n";
    let out = apply(shifted.as_bytes(), config, FixSafety::Safe);
    assert_eq!(out.text, "flowchart TD\n  A --> B\n  end\n");
    assert_eq!(out.applied, 1);
    let out = apply(shifted.as_bytes(), config, FixSafety::Unsafe);
    assert_eq!(out.text, "flowchart TD\n  A --> B\n");
    assert_eq!(out.applied, 2);
}

fn fix_shifted_open_bracket(config: &LintConfig) {
    let open_bracket = "flowchart LR\n  A -> B\n  C[unclosed\n";
    let out = apply(open_bracket.as_bytes(), config, FixSafety::Safe);
    assert_eq!(out.text, "flowchart LR\n  A --> B\n  C[unclosed\n");
    assert_eq!(out.applied, 1);
}

fn fix_two_arrows(config: &LintConfig) {
    let twice = "flowchart LR\n  A -> B\n  B -> C\n";
    let out = apply(twice.as_bytes(), config, FixSafety::Safe);
    assert_eq!(out.text, "flowchart LR\n  A --> B\n  B --> C\n");
    assert_eq!(out.applied, 2);
}

fn skip_suppressed_fix(config: &LintConfig) {
    let quoted = "sequenceDiagram\n  %% emd-disable-diagram sequence/quote-unclosed: quoted\n  participant \"Bob\n  A->>Bob: hi\n";
    let out = apply(quoted.as_bytes(), config, FixSafety::Unsafe);
    assert_eq!(out.text, quoted);
    assert_eq!(out.applied, 0);
}

fn repair_invalid_utf8(config: &LintConfig) {
    let repaired: &[u8] = b"flowchart LR\n  A -> B\n\xFF";
    let out = apply(repaired, config, FixSafety::Safe);
    assert_eq!(out.text, "flowchart LR\n  A --> B\n\u{fffd}");
    assert_eq!(out.applied, 1);
}

#[test]
fn lint_format() {
    let document = checked(GOLDEN);
    let config = LintConfig::default();
    let ds = lint(&document, &config);
    golden_diagnostic(&ds);
    text_format(GOLDEN, &ds);
    json_format(&document, GOLDEN, &ds);
    sarif_format(GOLDEN, &ds);
    github_format(GOLDEN, &ds);
    sarif_utf16_columns();
    github_escapes();
}

fn golden_diagnostic(ds: &[Diagnostic]) {
    assert_eq!(ds.len(), 1, "got {:?}", codes(ds));
    let only = &ds[0];
    assert_eq!(only.code, "flowchart/duplicate-ids");
    assert_eq!(only.severity, Severity::Error);
    assert_eq!(only.message, "Node id declared twice with different labels");
    assert_eq!(only.span, Span { start: 37, end: 38 });
    assert_eq!(
        only.help,
        "Give each node one label, or use a new id for the second node."
    );
    assert!(only.fixes.is_empty());
    assert_eq!(only.related.len(), 1);
    assert_eq!(only.related[0].span, Span { start: 15, end: 16 });
    assert_eq!(only.related[0].message, "first declared here");
}

fn text_format(golden: &str, ds: &[Diagnostic]) {
    let mut out = String::new();
    crate::lint::format::text(&mut out, "error-duplicate-ids.mmd", golden, ds, false);
    assert!(out.contains("error-duplicate-ids.mmd:3:3: error[flowchart/duplicate-ids]: Node id declared twice with different labels"));
    assert!(
        out.contains("  = help: Give each node one label, or use a new id for the second node.")
    );
    assert!(out.contains("  = note: first declared here at error-duplicate-ids.mmd:2:3"));
    assert!(out.contains("3 |   A[Begin] --> C[End]"));
    assert!(out.contains("  |   ^"));
}

fn json_format(document: &crate::Document<'_>, golden: &str, ds: &[Diagnostic]) {
    let mut out = String::new();
    crate::lint::format::json(
        &mut out,
        "error-duplicate-ids.mmd",
        document.kind().map(|kind| kind.id()),
        golden,
        ds,
    );
    assert!(out.starts_with("{\"version\":1,\"files\":[{\"path\":\"error-duplicate-ids.mmd\",\"kind\":\"flowchart\",\"diagnostics\":[{\"code\":\"flowchart/duplicate-ids\",\"severity\":\"error\",\"message\":\"Node id declared twice with different labels\",\"span\":{\"start\":37,\"end\":38}"));
    assert!(out.contains("\"related\":[{\"span\":{\"start\":15,\"end\":16},\"line\":2,\"column\":3,\"message\":\"first declared here\"}]"));
    assert!(out.ends_with("],\"summary\":{\"files\":1,\"errors\":1,\"warnings\":0,\"info\":0}}\n"));
}

fn sarif_format(golden: &str, ds: &[Diagnostic]) {
    let mut out = String::new();
    crate::lint::format::sarif(&mut out, "error-duplicate-ids.mmd", golden, ds);
    assert!(out.contains("\"version\":\"0.1.0\""));
    assert!(out.contains("\"rules\":[{\"id\":\"flowchart/duplicate-ids\""));
    assert!(out.contains("\"ruleId\":\"flowchart/duplicate-ids\",\"level\":\"error\",\"message\":{\"text\":\"Node id declared twice with different labels\"}"));
    assert!(out.contains("\"startLine\":3,\"startColumn\":3,\"endLine\":3,\"endColumn\":4"));
    assert!(out.contains("\"relatedLocations\":[{\"physicalLocation\""));
}

fn github_format(golden: &str, ds: &[Diagnostic]) {
    let mut out = String::new();
    crate::lint::format::github(&mut out, "error-duplicate-ids.mmd", golden, ds);
    assert_eq!(
        out,
        "::error file=error-duplicate-ids.mmd,line=3,col=3,endLine=3,endColumn=4,title=flowchart/duplicate-ids::Node id declared twice with different labels\n"
    );
}

fn sarif_utf16_columns() {
    let wide = "\u{1f600} ab\n";
    let index = crate::source::LineIndex::new(wide);
    assert_eq!(index.utf16_column(4), 3);
    let synthetic = [Diagnostic {
        code: "common/empty-source",
        severity: Severity::Error,
        message: String::new(),
        span: Span { start: 4, end: 5 },
        related: Vec::new(),
        help: String::new(),
        fixes: Vec::new(),
    }];
    let mut out = String::new();
    crate::lint::format::sarif(&mut out, "wide.mmd", wide, &synthetic);
    assert!(out.contains("\"startLine\":1,\"startColumn\":3,\"endLine\":1,\"endColumn\":4"));
}

fn github_escapes() {
    let escaped = [Diagnostic {
        code: "common/empty-source",
        severity: Severity::Warning,
        message: "50%\r\nok".to_owned(),
        span: Span { start: 0, end: 1 },
        related: Vec::new(),
        help: String::new(),
        fixes: Vec::new(),
    }];
    let mut out = String::new();
    crate::lint::format::github(&mut out, "a:b,c.mmd", "x\n", &escaped);
    assert_eq!(
        out,
        "::warning file=a%3Ab%2Cc.mmd,line=1,col=1,endLine=1,endColumn=2,title=common/empty-source::50%25%0D%0Aok\n"
    );
}
