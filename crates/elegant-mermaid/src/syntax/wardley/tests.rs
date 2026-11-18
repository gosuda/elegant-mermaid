use super::lexer::lex;
use super::parse;
use super::parser::Parsed;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;

fn parsed(source: &str) -> Parsed {
    let removed = preprocess(source).removed;
    parse(source, &removed)
}

fn messages(parsed: &Parsed) -> Vec<String> {
    parsed
        .diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

fn kinds(source: &str) -> Vec<&'static str> {
    lex(source, &[]).iter().map(|t| t.kind).collect()
}

fn slice(source: &str, span: Span) -> &str {
    source.get(span.start..span.end).unwrap_or("")
}

const FAMILIES: &str = "wardley-beta\ntitle Tea\nsize [1100, 800]\nevolution Genesis@0.25 -> Custom / Concept -> Product@0.75\nanchor Business [0.95, 0.63]\ncomponent Cup of Tea [0.79, 0.61] label [-60, 35] (build) (inertia)\ncomponent \"Web App\" [0.7, 0.8] (inertia)\nBusiness -> Cup of Tea\n\"Web App\" +<> Cup of Tea; note\nCup of Tea +'a b'> Business\nevolve Cup of Tea 0.9\npipeline Cup of Tea {\n  component Fire [0.3] label [1, -2]\n  component Gas [0.5]\n}\nnote \"n\" [0.1, 0.2]\nannotations [0.1, 2]\nannotation 3,[0.5, 7] \"text\"\naccelerator A [0.1, 0.2]\ndeaccelerator D [0.3, 0.4]\n";

fn families() -> Parsed {
    let p = parsed(FAMILIES);
    assert!(p.diagnostics.is_empty(), "{:?}", messages(&p));
    p
}

#[test]
fn statement_header_and_metadata() {
    let p = families();
    let ast = &p.document;
    assert_eq!(ast.header.as_ref().map(|t| t.kind), Some("KW_WARDLEY"));
    assert_eq!(ast.metadata.len(), 1);
    assert_eq!(ast.metadata[0].field, "title");
    assert_eq!(ast.metadata[0].value, "Tea");
    assert_eq!(ast.metadata[0].span, Span { start: 13, end: 22 });
    assert_eq!(
        ast.size.as_ref().map(|s| s.width.text.as_str()),
        Some("1100")
    );
}

#[test]
fn statement_evolution_stages() {
    let p = families();
    let stages = &p
        .document
        .evolution
        .as_ref()
        .map(|e| e.stages.clone())
        .unwrap_or_default();
    assert_eq!(stages.len(), 3);
    assert_eq!(
        stages[0].boundary.as_ref().map(|b| b.text.as_str()),
        Some("0.25")
    );
    assert_eq!(
        stages[1].second_name.as_ref().map(|b| b.text.as_str()),
        Some("Concept")
    );
}

#[test]
fn statement_components() {
    let p = families();
    let ast = &p.document;
    assert_eq!(ast.anchors.len(), 1);
    assert_eq!(ast.components.len(), 2);
    let cup = &ast.components[0];
    assert_eq!(cup.name.text, "Cup of Tea");
    let label = cup.label.as_ref();
    assert_eq!(
        label.map(|l| (l.neg_x, l.offset_x.text.as_str(), l.neg_y)),
        Some((true, "60", false))
    );
    assert_eq!(
        cup.decorator.as_ref().map(|d| d.strategy.text.as_str()),
        Some("build")
    );
    assert!(cup.inertia);
    assert!(ast.components[1].inertia);
    assert!(ast.components[1].decorator.is_none());
}

#[test]
fn statement_links() {
    let p = families();
    let links = &p.document.links;
    assert_eq!(links.len(), 3);
    assert_eq!(
        links[1].from_port.as_ref().map(|v| v.text.as_str()),
        Some("+<>")
    );
    assert_eq!(
        links[1].link_label.as_ref().map(|v| v.text.as_str()),
        Some("note")
    );
    assert_eq!(
        links[2].arrow.as_ref().map(|v| v.text.as_str()),
        Some("+'a b'>")
    );
}

#[test]
fn statement_pipelines_and_the_rest() {
    let p = families();
    let ast = &p.document;
    assert_eq!(ast.evolves.len(), 1);
    assert_eq!(ast.pipelines.len(), 1);
    assert_eq!(ast.pipelines[0].components.len(), 2);
    let fire = ast.pipelines[0].components[0].label.as_ref();
    assert_eq!(
        fire.map(|l| (l.neg_y, l.offset_y.text.as_str())),
        Some((true, "2"))
    );
    assert_eq!(ast.notes.len(), 1);
    assert_eq!(ast.annotations.len(), 1);
    assert_eq!(ast.annotation.len(), 1);
    assert_eq!(ast.accelerators.len(), 1);
    assert_eq!(ast.deaccelerators.len(), 1);
}

#[test]
fn spans_cover_statement_without_line_end() {
    let source = "wardley-beta\nanchor A [0.5, 0.5]\n\n\ncomponent B [0.1, 0.2]\n";
    let p = parsed(source);
    assert!(p.diagnostics.is_empty());
    assert_eq!(
        slice(source, p.document.anchors[0].span),
        "anchor A [0.5, 0.5]"
    );
    assert_eq!(
        slice(source, p.document.components[0].span),
        "component B [0.1, 0.2]"
    );
    assert_eq!(slice(source, p.document.anchors[0].name.span), "A");
}

#[test]
fn hyphen_and_arrow_tokenisation() {
    let p = parsed(
        "wardley-beta\nA->B\nfoo-bar->baz\nreal-time processing -> end-user\nfoo--bar -> x\nfoo- -> y\n",
    );
    assert!(p.diagnostics.is_empty(), "{:?}", messages(&p));
    let links = &p.document.links;
    assert_eq!(links.len(), 5);
    let names: Vec<(&str, &str)> = links
        .iter()
        .map(|l| (l.from.text.as_str(), l.to.text.as_str()))
        .collect();
    assert_eq!(names[0], ("A", "B"));
    assert_eq!(names[1], ("foo-bar", "baz"));
    assert_eq!(names[2].0, "real-time processing");
    assert_eq!(names[3].0, "foo--bar");
    assert_eq!(names[4].0, "foo-");
}

#[test]
fn token_priority_follows_authority() {
    assert_eq!(
        kinds("wardley-beta buyer"),
        ["KW_WARDLEY", "STRATEGY", "NAME_WITH_SPACES", "EOF"]
    );
    assert_eq!(
        kinds("component Foo"),
        ["KW_COMPONENT", "NAME_WITH_SPACES", "EOF"]
    );
    assert_eq!(kinds("component _foo"), ["KW_COMPONENT", "ID", "EOF"]);
    assert_eq!(kinds("\"label\""), ["STRING", "EOF"]);
    assert_eq!(kinds("sizes"), ["KW_SIZE", "NAME_WITH_SPACES", "EOF"]);
    assert_eq!(
        kinds("wardley-beta\ntitleX"),
        ["KW_WARDLEY", "NEWLINE", "NAME_WITH_SPACES", "EOF"]
    );
    assert_eq!(
        kinds("wardley-beta\ntitle"),
        ["KW_WARDLEY", "NEWLINE", "NAME_WITH_SPACES", "EOF"]
    );
    assert_eq!(
        kinds("wardley-beta\ntitle\n"),
        ["KW_WARDLEY", "NEWLINE", "TITLE", "NEWLINE", "EOF"]
    );
    assert_eq!(
        kinds("wardley-beta\naccTitleX"),
        ["KW_WARDLEY", "NEWLINE", "ID", "EOF"]
    );
    assert_eq!(kinds("12."), ["INT", "ID", "INVALID", "EOF"]);
    assert_eq!(kinds("0abc"), ["INT", "NAME_WITH_SPACES", "EOF"]);
}

#[test]
fn header_folds_case_only_at_document_start() {
    let p = parsed("Wardley-Beta\ncomponent A [0.1, 0.1]\n");
    assert!(p.diagnostics.is_empty());
    assert_eq!(
        p.document.header.as_ref().map(|t| t.text.as_str()),
        Some("Wardley-Beta")
    );
    assert_eq!(
        kinds("wardley-beta\nWardley-Beta"),
        ["KW_WARDLEY", "NEWLINE", "NAME_WITH_SPACES", "EOF"]
    );
    assert!(
        !parsed("wardley-beta\nWardley-Beta\n")
            .diagnostics
            .is_empty()
    );
}

#[test]
fn keywords_are_case_sensitive() {
    let p = parsed("wardley-beta\nComponent A [0.1, 0.1]\n");
    assert_eq!(
        messages(&p),
        [
            "wardley/unexpected-token: unexpected [, expected one of: ARROW, ID, LINK_ARROW, LINK_PORT, NAME_WITH_SPACES, STRING"
        ]
    );
}

#[test]
fn decimal_coordinates_reject_integers() {
    let p = parsed("wardley-beta\ncomponent A [1, 0.5]\n");
    assert_eq!(
        messages(&p),
        ["wardley/unexpected-token: unexpected 1, expected one of: WARDLEY_NUMBER"]
    );
    let p = parsed("wardley-beta\nannotations [1, 2]\nannotation 1,[1, 0.5] \"a\"\n");
    assert!(p.diagnostics.is_empty(), "{:?}", messages(&p));
}

#[test]
fn unknown_statement_spans_line() {
    let source = "wardley-beta\n[x] y z\ncomponent A [0.1, 0.1]\n";
    let p = parsed(source);
    assert_eq!(
        messages(&p),
        ["wardley/unknown-statement: unknown statement ["]
    );
    assert_eq!(slice(source, p.diagnostics[0].span), "[x] y z");
    assert_eq!(p.document.components.len(), 1);
}

#[test]
fn unterminated_delimiters() {
    let cases = [
        (
            "wardley-beta\ncomponent A [0.1, ",
            "wardley/unterminated: unterminated [",
        ),
        (
            "wardley-beta\ncomponent A [0.1, 0.2] (",
            "wardley/unterminated: unterminated (",
        ),
        (
            "wardley-beta\ncomponent A [0.1, 0.2] label [",
            "wardley/unterminated: unterminated [",
        ),
        (
            "wardley-beta\npipeline P {\n",
            "wardley/unterminated: unterminated {",
        ),
        (
            "wardley-beta\npipeline P {\ncomponent A [0.1",
            "wardley/unterminated: unterminated [",
        ),
        (
            "wardley-beta\nnote \"never closed",
            "wardley/unterminated: unterminated \"",
        ),
        (
            "wardley-beta\naccDescr {\nnever closed",
            "wardley/unterminated: unterminated {",
        ),
    ];
    for (source, message) in cases {
        let p = parsed(source);
        assert_eq!(messages(&p), [message], "{source}");
        assert_eq!(p.diagnostics[0].span.end, source.len(), "{source}");
    }
}

#[test]
fn pipeline_recovery() {
    let p = parsed(
        "wardley-beta\npipeline P {\n  note x\n  component A [0.1]\n  component B [x]\n  component C [0.3] }\ncomponent D [0.1, 0.2]\n",
    );
    assert_eq!(p.diagnostics.len(), 3);
    assert_eq!(p.diagnostics[0].code, "wardley/unexpected-token");
    assert_eq!(p.document.pipelines.len(), 1);
    assert_eq!(p.document.pipelines[0].components.len(), 1);
    assert_eq!(p.document.components.len(), 1);
}

#[test]
fn pipeline_needs_components_and_newline() {
    let p = parsed("wardley-beta\npipeline P {\n}\n");
    assert_eq!(
        messages(&p),
        ["wardley/unexpected-token: unexpected }, expected one of: KW_COMPONENT"]
    );
    let p = parsed("wardley-beta\npipeline P { component A [0.1]\n}\n");
    assert_eq!(
        messages(&p),
        [
            "wardley/unexpected-token: unexpected component, expected one of: NEWLINE",
            "wardley/unknown-statement: unknown statement }"
        ]
    );
}

#[test]
fn metadata() {
    let p = parsed(
        "wardley-beta\ntitle  A   B  %% c\naccTitle: t\naccDescr: d\naccDescr {\n  x\n\n  y\n}\n",
    );
    assert!(p.diagnostics.is_empty(), "{:?}", messages(&p));
    let values: Vec<String> = p
        .document
        .metadata
        .iter()
        .map(|m| format!("{}={}", m.field, m.value))
        .collect();
    assert_eq!(
        values,
        ["title=A B", "accTitle=t", "accDescr=d", "accDescr=x\ny"]
    );
}

#[test]
fn string_escapes() {
    let p = parsed("wardley-beta\nnote \"a\\\"b\\n\" [0.1, 0.2]\ncomponent 'x\\'y' [0.1, 0.2]\n");
    assert!(p.diagnostics.is_empty(), "{:?}", messages(&p));
    assert_eq!(p.document.notes[0].text.text, "a\"b\n");
    assert_eq!(p.document.components[0].name.text, "x'y");
}

#[test]
fn evolution_needs_two_stages() {
    let p = parsed("wardley-beta\nevolution A\n");
    assert_eq!(
        messages(&p),
        ["wardley/unexpected-token: unexpected \n, expected one of: /, @, ARROW"]
    );
}

#[test]
fn link_ports_and_arrows() {
    let p = parsed("wardley-beta\nA +> B\nA -.-> B\nA --> B +<\nA > B\n");
    assert!(p.diagnostics.is_empty(), "{:?}", messages(&p));
    let links = &p.document.links;
    assert_eq!(links.len(), 4);
    assert_eq!(
        links[0].from_port.as_ref().map(|v| v.text.as_str()),
        Some("+>")
    );
    assert_eq!(
        links[1].arrow.as_ref().map(|v| v.text.as_str()),
        Some("-.->")
    );
    assert_eq!(
        links[2].to_port.as_ref().map(|v| v.text.as_str()),
        Some("+<")
    );
    assert_eq!(links[3].arrow.as_ref().map(|v| v.text.as_str()), Some(">"));
}

#[test]
fn invalid_byte_is_rejected() {
    let p = parsed("wardley-beta\ncomponent A [0.1, 0.1] .\n");
    assert_eq!(
        messages(&p),
        [
            "wardley/unexpected-token: unexpected ., expected one of: (, EOF, KW_INERTIA, KW_LABEL, NEWLINE"
        ]
    );
}
