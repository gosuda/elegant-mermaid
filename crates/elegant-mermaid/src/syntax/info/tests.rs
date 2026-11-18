use crate::diag::Diagnostic;
use crate::syntax::preprocess::preprocess;

use super::ast::Info;
use super::parse;

fn run(src: &str) -> (Info, Vec<Diagnostic>) {
    let removed = preprocess(src).removed;
    let parsed = parse(src, &removed);
    (parsed.document, parsed.diagnostics)
}

fn messages(ds: &[Diagnostic]) -> Vec<String> {
    ds.iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

#[test]
fn accepted_forms() {
    for src in [
        "info",
        "info\n",
        "\n\ninfo showInfo",
        "info\nshowInfo\n",
        "info %% note\nshowInfo %% note",
        "info showInfo title x",
        "info title x\naccTitle: t\naccDescr: d",
        "info\n\n\nshowInfo\n\ntitle t\n",
    ] {
        let (doc, ds) = run(src);
        assert!(ds.is_empty(), "{src}");
        assert_eq!(doc.header.kind, "info");
    }
}

#[test]
fn show_info_is_recorded_once() {
    assert!(run("info\nshowInfo\n").0.show_info.is_some());
    assert!(run("info\n").0.show_info.is_none());
}

#[test]
fn metadata_keeps_last_value() {
    let (doc, ds) =
        run("info\ntitle one\ntitle  two  words\naccTitle: a\naccDescr {\n x\n  y\n}\n");
    assert!(ds.is_empty());
    assert_eq!(doc.title.unwrap().text, "two words");
    assert_eq!(doc.acc_title.unwrap().text, "a");
    assert_eq!(doc.acc_descr.unwrap().text, "x\ny");
}

#[test]
fn diagnostics() {
    let after = "unexpected showInfo, expected one of: ACC_DESCR, ACC_TITLE, EOF, TITLE";
    let cases: [(&str, String); 8] = [
        (
            "info\nshowInfo\nshowInfo\n",
            format!("info/unexpected-token: {after}"),
        ),
        (
            "info\ntitle t\nshowInfo\n",
            format!("info/unexpected-token: {after}"),
        ),
        (
            "info\nfoo bar\nshowInfo\n",
            "info/unknown-statement: unknown statement foo".into(),
        ),
        (
            "info foo\n",
            "info/unknown-statement: unknown statement foo".into(),
        ),
        (
            "info\n\"quoted\"\n",
            "info/unknown-statement: unknown statement \"quoted\"".into(),
        ),
        (
            "info\naccDescr {\nnever closed",
            "info/unterminated: unterminated {".into(),
        ),
        (
            "infox\n",
            "info/unexpected-token: unexpected infox, expected one of: info".into(),
        ),
        (
            "info{\n",
            "info/unexpected-token: unexpected info, expected one of: info".into(),
        ),
    ];
    for (src, want) in cases {
        let (_, ds) = run(src);
        assert_eq!(messages(&ds), [want], "{src}");
    }
}

#[test]
fn unknown_statement_span_runs_to_line_end() {
    let src = "info\nfoo bar baz\nshowInfo";
    let (_, ds) = run(src);
    assert_eq!(ds.len(), 1);
    assert_eq!(&src[ds[0].span.start..ds[0].span.end], "foo bar baz");
}

#[test]
fn line_endings_are_uniform() {
    for eol in ["\n", "\r\n", "\r"] {
        let (_, ds) = run(&format!("info{eol}showInfo{eol}title t{eol}"));
        assert!(ds.is_empty(), "{eol:?}");
    }
}
