use crate::diag::Diagnostic;
use crate::syntax::preprocess::preprocess;

use super::ast::Cynefin;
use super::parse;

fn run(src: &str) -> (Cynefin, Vec<Diagnostic>) {
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
fn header_forms() {
    for src in [
        "cynefin-beta",
        "cynefin-beta:",
        "\n\ncynefin-beta\n",
        "cynefin-beta %% note\ncomplex",
        "cynefin-beta:complex",
    ] {
        let (doc, ds) = run(src);
        assert!(ds.is_empty(), "{src}");
        assert!(["cynefin-beta", "cynefin-beta:"].contains(&doc.header.kind));
    }
}

#[test]
fn header_guard_rejects_glued_text() {
    let (_, ds) = run("cynefin-betax");
    assert_eq!(
        messages(&ds),
        [
            "cynefin/unexpected-token: unexpected cynefin-betax, expected one of: cynefin-beta, cynefin-beta:"
        ]
    );
}

#[test]
fn domain_blocks_and_transitions() {
    let src = "cynefin-beta\n  title T\n  complex \"a\" 'b'\n\n  \"c\"\n  clear\n  complicated --> clear : \"x\"\n  chaotic --> complex\n";
    let (doc, ds) = run(src);
    assert!(ds.is_empty());
    assert_eq!(doc.title.unwrap().text, "T");
    assert_eq!(doc.domains.len(), 2);
    assert_eq!(doc.domains[0].domain.text, "complex");
    assert_eq!(doc.domains[0].items.len(), 3);
    assert_eq!(doc.domains[0].items[1].label.text, "b");
    assert!(doc.domains[1].items.is_empty());
    assert_eq!(doc.transitions.len(), 2);
    assert_eq!(doc.transitions[0].label.as_ref().unwrap().text, "x");
    assert!(doc.transitions[1].label.is_none());
}

#[test]
fn domain_spans_cover_items_only() {
    let src = "cynefin-beta\ncomplex\n\"one\"\n\n\"two\"\n\n%% c\nclear\n";
    let (doc, ds) = run(src);
    assert!(ds.is_empty());
    let first = doc.domains[0].span;
    assert_eq!((first.start, first.end), (13, 33));
    assert_eq!(&src[first.start..first.end], "complex\n\"one\"\n\n\"two\"");
    let second = doc.domains[1].span;
    assert_eq!(&src[second.start..second.end], "clear");
}

#[test]
fn transition_span_excludes_line_end() {
    let src = "cynefin-beta\ncomplex --> clear : \"go\" %% note\n";
    let (doc, ds) = run(src);
    assert!(ds.is_empty());
    let span = doc.transitions[0].span;
    assert_eq!(&src[span.start..span.end], "complex --> clear : \"go\"");
}

#[test]
fn metadata_last_value_wins() {
    let src = "cynefin-beta\ntitle  a   b\naccTitle: t1\naccDescr: d1\ntitle second\naccTitle: t2 %% c\naccDescr {\n  multi\n    line\n}\n";
    let (doc, ds) = run(src);
    assert!(ds.is_empty());
    assert_eq!(doc.title.unwrap().text, "second");
    assert_eq!(doc.acc_title.unwrap().text, "t2");
    assert_eq!(doc.acc_descr.unwrap().text, "multi\nline");
}

#[test]
fn diagnostics() {
    let cases: [(&str, &[&str]); 10] = [
        (
            "cynefin-beta\ncomplex -->",
            &["cynefin/unexpected-token: unexpected end of input, expected one of: DOMAIN_NAME"],
        ),
        (
            "cynefin-beta\nfoo\ncomplex\n",
            &["cynefin/unknown-statement: unknown statement foo"],
        ),
        (
            "cynefin-beta\n--> clear\n",
            &["cynefin/unknown-statement: unknown statement -->"],
        ),
        (
            "cynefin-beta\ncomplex --> \"x\"\n",
            &["cynefin/unexpected-token: unexpected \"x\", expected one of: DOMAIN_NAME"],
        ),
        (
            "cynefin-beta\ncomplex --> clear :\n",
            &["cynefin/unexpected-token: unexpected \n, expected one of: STRING"],
        ),
        (
            "cynefin-beta\ncomplex --> clear extra\n",
            &["cynefin/unexpected-token: unexpected extra, expected one of: :, EOF, NEWLINE"],
        ),
        (
            "cynefin-beta\ncomplex --> clear : \"x\" extra\n",
            &["cynefin/unexpected-token: unexpected extra, expected one of: EOF, NEWLINE"],
        ),
        (
            "cynefin-beta\ncomplex \"never closed\n",
            &["cynefin/unterminated: unterminated \""],
        ),
        (
            "cynefin-beta\naccDescr {\nnever closed",
            &["cynefin/unterminated: unterminated {"],
        ),
        (
            "cynefin-beta\n5 6\n",
            &["cynefin/unknown-statement: unknown statement 5"],
        ),
    ];
    for (src, want) in cases {
        let (_, ds) = run(src);
        assert_eq!(messages(&ds), want, "{src}");
    }
}

#[test]
fn rejected_statements_produce_nothing() {
    let (doc, ds) = run("cynefin-beta\ncomplex --> clear extra\nchaotic --> complex\n");
    assert_eq!(ds.len(), 1);
    assert_eq!(doc.transitions.len(), 1);
    assert_eq!(doc.transitions[0].from.text, "chaotic");
}

#[test]
fn domain_names_are_case_sensitive_prefixes() {
    let (doc, ds) = run("cynefin-beta\nComplex\ncomplexity\n");
    assert_eq!(
        messages(&ds),
        [
            "cynefin/unknown-statement: unknown statement Complex",
            "cynefin/unknown-statement: unknown statement ity"
        ]
    );
    assert_eq!(doc.domains.len(), 1);
    assert_eq!(doc.domains[0].domain.text, "complex");
}

#[test]
fn string_escapes() {
    let (doc, ds) = run("cynefin-beta\nclear \"a\\\"b\\n\\x\"\n");
    assert!(ds.is_empty());
    assert_eq!(doc.domains[0].items[0].label.text, "a\"b\nx");
}

#[test]
fn line_endings_are_uniform() {
    for eol in ["\n", "\r\n", "\r"] {
        let src = format!("cynefin-beta{eol}complex{eol}\"a\"{eol}complex --> clear{eol}");
        let (doc, ds) = run(&src);
        assert!(ds.is_empty(), "{eol:?}");
        assert_eq!(doc.domains[0].items.len(), 1);
        assert_eq!(doc.transitions.len(), 1);
    }
}
