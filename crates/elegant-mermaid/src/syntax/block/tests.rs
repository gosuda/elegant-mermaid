use super::ast::StatementKind;
use super::lexer::lex;
use super::parse;
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;

fn diagnostics_of(source: &str) -> Vec<Diagnostic> {
    let removed = preprocess(source).removed;
    parse(source, &removed).diagnostics
}

fn first_code(source: &str) -> Option<&'static str> {
    diagnostics_of(source).first().map(|d| d.code)
}

#[test]
fn corpus_files_parse_without_diagnostics() -> Result<(), String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/block");
    let mut checked = 0usize;
    let sources = std::fs::read_dir(&root).map_err(|e| e.to_string())?;
    for source in sources {
        let dir = source.map_err(|e| e.to_string())?.path();
        for entry in std::fs::read_dir(&dir).map_err(|e| e.to_string())? {
            let path = entry.map_err(|e| e.to_string())?.path();
            let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
            if let Some(d) = diagnostics_of(&text).first() {
                return Err(format!("{}: {}: {}", path.display(), d.code, d.message));
            }
            checked += 1;
        }
    }
    assert!(checked > 0, "corpus/block holds no file");
    Ok(())
}

#[test]
fn accepted_forms_raise_no_diagnostic() {
    let forms = [
        ("size on first node", "block\n  A:2 --> B\n"),
        ("chain", "block\n  A-->B-->C\n"),
        (
            "keyword prefixed ids",
            "block\n  blockchain\n  block1\n  endpoint\n  default1\n",
        ),
        (
            "composite with size",
            "block\n  columns 3\n  block:g:2\n    A\n  end\n",
        ),
        (
            "labelled composite",
            "block\n  block:g[\"T\"]:2\n    A\n  end\n",
        ),
        (
            "nested anonymous",
            "block\n  block\n    block\n      A\n    end\n  end\n",
        ),
        (
            "all arrow spellings",
            "block\n  A --- B\n  C --x D\n  G <--> H\n  I ===> J\n  K -.-> L\n",
        ),
        ("marker letters as ids", "block\n  E o--o F\n"),
        ("tilde as identifier", "block\n  M ~~~ N\n"),
        (
            "labelled edges",
            "block\n  A -- \"hello\" --> B\n  C == \"x\" ==> D\n  E -. \"y\" .-> F\n",
        ),
        ("empty multiline desc", "block\n  accDescr {}\n  A\n"),
        (
            "class statements",
            "block\n  A B\n  classDef foo fill:#f96,color:#fff;\n  class A,B foo\n  style A fill:#00f\n",
        ),
        (
            "lowercase default",
            "block\n  A\n  classDef default fill:#f96\n",
        ),
        ("mismatched pair", "block\n  a(\"1\"] b[\"2\")\n"),
        ("stray bracket in id", "block\n  a]\n"),
        ("huge size", "block\n  a:99999999999\n"),
        (
            "arrow directions",
            "block\n  A<[\"x\"]>(x)\n  B<[\"y\"]>(y, up)\n  C<[\"z\"]>(right,left,down)\n",
        ),
        ("block-beta header", "block-beta\n  A\n"),
        ("style at end of input", "block\n  A\n  style A"),
    ];
    for (name, source) in forms {
        let found: Vec<String> = diagnostics_of(source)
            .iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect();
        assert!(found.is_empty(), "{name}: {found:?}");
    }
}

#[test]
fn rejected_forms_raise_their_first_code() {
    let forms = [
        (
            "empty label",
            "block\n  A[\"\"]\n",
            "block/unexpected-token",
        ),
        (
            "unquoted label",
            "block\n  A[foo]\n",
            "block/unexpected-token",
        ),
        (
            "space inside shape",
            "block\n  A[ \"x\" ]\n",
            "block/unexpected-token",
        ),
        (
            "size on link target",
            "block\n  A --> B:2\n",
            "block/unexpected-token",
        ),
        ("double size", "block\n  A:2:3\n", "block/unexpected-token"),
        (
            "upper case default",
            "block\n  A\n  classDef DEFAULT fill:#f96\n",
            "block/unexpected-token",
        ),
        (
            "stray end",
            "block\n  A\n  end\n",
            "block/unknown-statement",
        ),
        (
            "unknown direction",
            "block\n  A<[\"x\"]>(sideways)\n",
            "block/unexpected-token",
        ),
        (
            "empty direction list",
            "block\n  A<[\"x\"]>()\n",
            "block/unexpected-token",
        ),
        (
            "markdown label",
            "block\n  A[\"`x`\"]\n",
            "block/unexpected-token",
        ),
        (
            "colon identifier",
            "block\n  a:b\n",
            "block/unknown-statement",
        ),
        ("empty document", "block\n", "block/unexpected-token"),
        (
            "empty composite",
            "block\n  block\n  end\n",
            "block/unexpected-token",
        ),
        (
            "accessibility title",
            "block\n  accTitle: x\n  A\n",
            "block/unknown-statement",
        ),
        (
            "unterminated composite",
            "block\n  block\n    A\n",
            "block/unterminated",
        ),
        (
            "unterminated string",
            "block\n  A[\"x\n",
            "block/unterminated",
        ),
        ("unterminated shape", "block\n  A[", "block/unterminated"),
        (
            "unterminated arrow",
            "block\n  A<[\"x\"]>(right\n",
            "block/unterminated",
        ),
        (
            "unterminated link",
            "block\n  A -- \"x\n",
            "block/unterminated",
        ),
    ];
    for (name, source, code) in forms {
        assert_eq!(first_code(source), Some(code), "{name}");
    }
}

#[test]
fn unexpected_token_names_the_token_and_the_accepted_kinds() {
    let found = diagnostics_of("block\n  A[foo]\n");
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].message, "unexpected f, expected one of: STR");
    assert_eq!(found[0].span.start, 10);
}

#[test]
fn recovery_keeps_later_statements() {
    let source = "block\n  A[foo]\n  B\n  C\n";
    let parsed = parse(source, &[]);
    assert!(!parsed.diagnostics.is_empty());
    assert_eq!(parsed.document.document.statements.len(), 2);
}

#[test]
fn recovery_stops_before_the_composite_end() {
    let parsed = parse("block\n  block\n    A[foo] end\n  B\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1, "{:?}", parsed.diagnostics);
    assert_eq!(parsed.document.document.statements.len(), 2);
}

#[test]
fn nesting_beyond_sixty_four_raises_one_diagnostic() {
    let source = format!("block\n{}A\n{}", "block\n".repeat(70), "end\n".repeat(70));
    let found = diagnostics_of(&source);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].code, "limit/nesting-depth");
}

#[test]
fn spans_stay_on_tokens() -> Result<(), &'static str> {
    let parsed = parse("block\n  A[\"x\"]:2 --> B\n", &[]);
    assert!(parsed.diagnostics.is_empty());
    let statement = parsed
        .document
        .document
        .statements
        .first()
        .ok_or("no statement")?;
    let StatementKind::Node(node) = &statement.kind else {
        return Err("not a node statement");
    };
    let size = node.size.ok_or("no size")?;
    assert_eq!(size.span, Span { start: 14, end: 16 });
    assert_eq!(node.links[0].link.end.span, Span { start: 17, end: 20 });
    Ok(())
}

#[test]
fn padded_tokens_drop_surrounding_space() {
    let tokens = lex("block\n  A --> B\n  end  \n", &[]);
    let link = tokens.iter().find(|t| t.kind == "LINK");
    assert_eq!(link.map(|t| t.span), Some(Span { start: 10, end: 13 }));
}

#[test]
fn removed_spans_are_skipped() {
    let source = "block\n  A\n  %% note\n  B\n";
    let removed = preprocess(source).removed;
    let kinds: Vec<&str> = lex(source, &removed).iter().map(|t| t.kind).collect();
    assert_eq!(kinds, ["BLOCK_DIAGRAM_KEY", "NODE_ID", "NODE_ID", "EOF"]);
}
