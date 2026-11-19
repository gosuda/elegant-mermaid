use super::ast::{Token, TreeView};
use super::parse;
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;

fn parsed(src: &str) -> (TreeView, Vec<Diagnostic>) {
    let result = parse(src, &preprocess(src).removed);
    (result.document, result.diagnostics)
}

fn codes(ds: &[Diagnostic]) -> Vec<&'static str> {
    ds.iter().map(|d| d.code).collect()
}

fn text(src: &str, span: Span) -> &str {
    src.get(span.start..span.end).unwrap_or("")
}

fn slice<'a>(src: &'a str, token: Option<&Token>) -> &'a str {
    token.map_or("<nil>", |t| text(src, t.span))
}

fn names(tv: &TreeView) -> Vec<&str> {
    tv.nodes.iter().map(|n| n.name.value.as_str()).collect()
}

fn levels(tv: &TreeView) -> Vec<usize> {
    tv.nodes
        .iter()
        .map(|n| n.indent.as_ref().map_or(0, |t| t.text.len()))
        .collect()
}

fn value(token: Option<&Token>) -> &str {
    token.map_or("<nil>", |t| t.value.as_str())
}

fn node_field(
    tv: &TreeView,
    at: usize,
    pick: fn(&crate::syntax::treeview::ast::TreeNode) -> Option<&Token>,
) -> &str {
    tv.nodes.get(at).map_or("<none>", |n| value(pick(n)))
}

fn class_of(tv: &TreeView, at: usize) -> &str {
    node_field(tv, at, |n| n.class.as_ref())
}

fn icon_of(tv: &TreeView, at: usize) -> &str {
    node_field(tv, at, |n| n.icon.as_ref())
}

fn desc_of(tv: &TreeView, at: usize) -> &str {
    node_field(tv, at, |n| n.desc.as_ref())
}

#[test]
fn node_line_splits_name_and_annotations() {
    let src = "treeView-beta\n  App.tsx :::highlight icon(logos:react) ## main component\n";
    let (tv, ds) = parsed(src);
    assert!(ds.is_empty());
    assert_eq!(tv.nodes.len(), 1);
    assert_eq!(
        slice(src, tv.nodes.first().and_then(|n| n.indent.as_ref())),
        "  "
    );
    assert_eq!(names(&tv), ["App.tsx"]);
    assert_eq!(class_of(&tv, 0), "highlight");
    assert_eq!(icon_of(&tv, 0), "logos:react");
    assert_eq!(desc_of(&tv, 0), "main component");
    let span = tv
        .nodes
        .first()
        .map(|n| n.span)
        .unwrap_or(Span { start: 0, end: 0 });
    assert_eq!(
        src.get(span.start + 2..span.end),
        Some("App.tsx :::highlight icon(logos:react) ## main component")
    );
}

#[test]
fn bare_name_keeps_inner_blanks_and_quotes() {
    let src = "treeView-beta\na b  c \"d\" 'e  \n";
    let (tv, ds) = parsed(src);
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["a b  c \"d\" 'e"]);
    assert_eq!(
        slice(src, tv.nodes.first().map(|n| &n.name)),
        "a b  c \"d\" 'e  "
    );
}

#[test]
fn description_consumes_apparent_annotations() {
    let (tv, ds) = parsed("treeView-beta\n a ## d :::x icon(y)\n");
    assert!(ds.is_empty());
    assert_eq!(desc_of(&tv, 0), "d :::x icon(y)");
    assert_eq!(class_of(&tv, 0), "<nil>");
    assert_eq!(icon_of(&tv, 0), "<nil>");
}

#[test]
fn repeated_annotation_keeps_last() {
    let (tv, ds) = parsed("treeView-beta\n a :::x :::y icon(p) icon(q) ## 1 \n");
    assert!(ds.is_empty());
    assert_eq!(class_of(&tv, 0), "y");
    assert_eq!(icon_of(&tv, 0), "q");
    assert_eq!(desc_of(&tv, 0), "1");
}

#[test]
fn annotation_without_leading_blank_is_name_part() {
    for (src, name) in [("a:::x", "a:::x"), ("a## d", "a## d"), ("a :::9", "a :::9")] {
        let (tv, ds) = parsed(&format!("treeView-beta\n {src}\n"));
        assert!(ds.is_empty(), "{src}");
        assert_eq!(names(&tv), [name], "{src}");
        assert_eq!(class_of(&tv, 0), "<nil>", "{src}");
    }
}

#[test]
fn broken_icon_opener_is_rejected() {
    for src in ["a icon(", "a icon(p", "a icon(p:)", "a icon(a b)"] {
        let (tv, ds) = parsed(&format!("treeView-beta\n {src}\n"));
        assert!(!ds.is_empty(), "{src}");
        assert!(codes(&ds).contains(&super::C_UNKNOWN), "{src}");
        assert_eq!(icon_of(&tv, 0), "<nil>", "{src}");
    }
}

#[test]
fn icon_value_forms() {
    for (src, want) in [
        ("icon()", ""),
        ("icon(a-b)", "a-b"),
        ("icon(p:q)", "p:q"),
        ("icon(:q)", ":q"),
    ] {
        let (tv, ds) = parsed(&format!("treeView-beta\n a {src}\n"));
        assert!(ds.is_empty(), "{src}");
        assert_eq!(icon_of(&tv, 0), want, "{src}");
    }
}

#[test]
fn quoted_name_strips_quotes_and_may_span_lines() {
    let (tv, ds) = parsed("treeView-beta\n \"a\n b\" 'c'\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["a\n b", "c"]);
}

#[test]
fn backslash_does_not_escape_the_quote() {
    let (tv, ds) = parsed("treeView-beta\n \"a\\\" b\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["a\\", "b"]);
}

#[test]
fn metadata_before_nodes() {
    let (tv, ds) = parsed(
        "treeView-beta\n title  Hello   there \n accTitle : T\n accDescr: D\n accDescr {\n x\n\n  y \n }\n a\n",
    );
    assert!(ds.is_empty());
    assert_eq!(value(tv.title.as_ref()), "Hello there");
    assert_eq!(value(tv.acc_title.as_ref()), "T");
    assert_eq!(value(tv.acc_descr.as_ref()), "x\ny");
    assert_eq!(tv.nodes.len(), 1);
}

#[test]
fn title_without_blank_suffix_is_empty_title_then_name() {
    let (tv, ds) = parsed("treeView-beta\n title.md\n");
    assert!(ds.is_empty());
    assert_eq!(value(tv.title.as_ref()), "");
    assert_eq!(names(&tv), [".md"]);
    assert_eq!(levels(&tv), [0]);
}

#[test]
fn metadata_after_node_is_rejected() {
    let src = "treeView-beta\n a\n title t\n b\n";
    let (tv, ds) = parsed(src);
    assert_eq!(codes(&ds), [super::C_UNEXPECTED]);
    let first = ds.first();
    assert_eq!(first.map_or("", |d| text(src, d.span)), " title t");
    assert_eq!(
        first.map_or("", |d| d.message.as_str()),
        "unexpected  title t, expected one of: BARE_NAME, CLASS_ANNOTATION, DESC_ANNOTATION, EOF, ICON_ANNOTATION, INDENTATION, QUOTED_NAME"
    );
    assert_eq!(tv.nodes.len(), 2);
}

#[test]
fn indentation_without_name_is_rejected() {
    let (tv, ds) = parsed("treeView-beta\n a\n  \n b\n");
    assert_eq!(codes(&ds), [super::C_UNEXPECTED]);
    assert!(ds.first().is_some_and(|d| {
        d.message
            .contains(", expected one of: BARE_NAME, QUOTED_NAME")
    }));
    assert_eq!(tv.nodes.len(), 1);
}

#[test]
fn annotation_line_attaches_to_the_preceding_node() {
    let (tv, ds) = parsed("treeView-beta\n a\n :::x\n ## d\n");
    assert!(ds.is_empty());
    assert_eq!(class_of(&tv, 0), "x");
    assert_eq!(desc_of(&tv, 0), "d");
}

#[test]
fn annotation_before_any_node_is_rejected() {
    let (_, ds) = parsed("treeView-beta\n ## d\n");
    assert_eq!(codes(&ds), [super::C_UNEXPECTED]);
}

#[test]
fn header_must_be_alone() {
    for src in [
        "treeView-beta x\n a",
        "treeView-betax\n a",
        "treeView-beta  \n a",
    ] {
        let (tv, ds) = parsed(src);
        assert_eq!(codes(&ds), [super::C_UNEXPECTED], "{src}");
        assert!(tv.nodes.is_empty(), "{src}");
    }
}

#[test]
fn unterminated_quote_spans_to_end() {
    let src = "treeView-beta\n a\n \"never\n closed";
    let (tv, ds) = parsed(src);
    assert_eq!(codes(&ds), [super::C_UNTERMINATED]);
    let first = ds.first();
    assert_eq!(first.map_or("", |d| text(src, d.span)), "\"never\n closed");
    assert_eq!(first.map_or("", |d| d.message.as_str()), "unterminated \"");
    assert_eq!(tv.nodes.len(), 1);
}

#[test]
fn unclosed_accessibility_block_is_a_name() {
    let (tv, ds) = parsed("treeView-beta\naccDescr {\nopen\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["accDescr {", "open"]);
}

#[test]
fn text_after_quoted_name_without_blank_is_unknown_statement() {
    let src = "treeView-beta\n \"a\":::x\n b\n";
    let (tv, ds) = parsed(src);
    assert_eq!(codes(&ds), [super::C_UNKNOWN]);
    let first = ds.first();
    assert_eq!(first.map_or("", |d| text(src, d.span)), ":::x");
    assert_eq!(
        first.map_or("", |d| d.message.as_str()),
        "unknown statement :"
    );
    assert_eq!(names(&tv).last().copied(), Some("b"));
}

#[test]
fn hidden_comments_and_blank_lines_create_no_nodes() {
    let (tv, ds) = parsed("%% top\ntreeView-beta\n\n  %% inner\n a %% not a comment\n\n b\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["a %% not a comment", "b"]);
}

#[test]
fn bare_comment_indentation_preserves_nodes_hierarchy_and_source_spans() -> Result<(), &'static str>
{
    for eol in ["\n", "\r\n", "\r"] {
        for indent in ["", " ", "\t", " \t"] {
            for comment in ["%%", "%% text"] {
                let src = format!(
                    "treeView-beta{eol}{indent}{comment}{eol}    \"packages\"{eol}        \"mermaid\"{eol}{indent}{comment}{eol}            \"src\"{eol}        \"parser\"{eol}{indent}{comment}"
                );
                assert_bare_comment_treeview(&src)?;
            }
        }
    }
    Ok(())
}

fn assert_bare_comment_treeview(src: &str) -> Result<(), &'static str> {
    let (tv, ds) = parsed(src);
    assert!(ds.is_empty(), "{src:?}: {ds:?}");
    assert_eq!(names(&tv), ["packages", "mermaid", "src", "parser"]);
    assert_eq!(levels(&tv), [4, 8, 12, 8]);
    let (model, ds) = crate::model::treeview::resolve(src, &tv);
    assert!(ds.is_empty(), "{src:?}: {ds:?}");
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|n| n.name.as_str())
            .collect::<Vec<_>>(),
        ["/", "packages", "mermaid", "src", "parser"]
    );
    assert_eq!(
        model.nodes.iter().map(|n| n.parent).collect::<Vec<_>>(),
        [None, Some(0), Some(1), Some(2), Some(1)]
    );
    assert_eq!(model.nodes[0].children, [1]);
    assert_eq!(model.nodes[1].children, [2, 4]);
    assert_eq!(model.nodes[2].children, [3]);
    for (i, (name, width)) in [("packages", 4), ("mermaid", 8), ("src", 12), ("parser", 8)]
        .into_iter()
        .enumerate()
    {
        let quoted = format!("\"{name}\"");
        let start = src.find(&quoted).ok_or("source node name")?;
        let span = Span {
            start,
            end: start + quoted.len(),
        };
        assert_eq!(tv.nodes[i].name.span, span);
        assert_eq!(text(src, span), quoted);
        let indent_span = Span {
            start: start - width,
            end: start,
        };
        assert_eq!(
            tv.nodes[i].indent.as_ref().map(|t| t.span),
            Some(indent_span)
        );
        assert_eq!(
            model.nodes[i + 1].span,
            Span {
                start: indent_span.start,
                end: span.end
            }
        );
    }
    Ok(())
}

#[test]
fn header_before_comment_text_is_rejected() {
    let (_, ds) = parsed("treeView-beta %% tail\n a\n");
    assert_eq!(codes(&ds), [super::C_UNEXPECTED]);
}

#[test]
fn line_endings_are_all_breaks() {
    let (tv, ds) = parsed("treeView-beta\r\n a\r\n\tb\r c\n");
    assert!(ds.is_empty());
    assert_eq!(tv.nodes.len(), 3);
    assert_eq!(
        tv.nodes
            .get(1)
            .and_then(|n| n.indent.as_ref())
            .map(|t| t.text.as_str()),
        Some("\t")
    );
}

#[test]
fn spans_use_original_source_after_frontmatter() {
    let src = "---\nconfig:\n  treeView:\n    rowIndent: 3\n---\ntreeView-beta\n  a ## d\n";
    let (tv, ds) = parsed(src);
    assert!(ds.is_empty());
    assert_eq!(slice(src, tv.header.as_ref()), "treeView-beta");
    assert_eq!(slice(src, tv.nodes.first().map(|n| &n.name)), "a");
    assert_eq!(
        slice(src, tv.nodes.first().and_then(|n| n.desc.as_ref())),
        " ## d"
    );
}

#[test]
fn empty_body_is_accepted() {
    for src in [
        "treeView-beta",
        "treeView-beta\n",
        "treeView-beta\n\n%% c\n",
    ] {
        let (tv, ds) = parsed(src);
        assert!(ds.is_empty(), "{src}");
        assert!(tv.nodes.is_empty(), "{src}");
    }
}

#[test]
fn name_bytes_are_not_split_mid_rune() {
    let (tv, ds) = parsed("treeView-beta\n 🚀 rocket/ ## ünï\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["🚀 rocket/"]);
    assert_eq!(desc_of(&tv, 0), "ünï");
}

#[test]
fn box_input_becomes_four_space_per_depth() {
    let (tv, ds) = parsed("treeView-beta\n├── a\n│   ├── b\n│   │   └── c\n│   └── d\n└── e\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["a", "b", "c", "d", "e"]);
    assert_eq!(levels(&tv), [4, 8, 12, 8, 4]);
}

#[test]
fn box_segment_width_comes_from_first_branch_after_column_zero() {
    let (tv, ds) = parsed("treeView-beta\n  ├── a\n  │   └── b\n");
    assert!(ds.is_empty());
    assert_eq!(levels(&tv), [8, 16]);
    let (tv, ds) = parsed("treeView-beta\n├────── a\n│      └── b\n");
    assert!(ds.is_empty());
    assert_eq!(levels(&tv), [4, 8]);
}

#[test]
fn box_heavy_variants_and_tabs() {
    let (tv, ds) = parsed("treeView-beta\n┣━━ a\n┃   ┗━━ b\n\t├── c\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["a", "b", "c"]);
    assert_eq!(levels(&tv), [4, 8, 8]);
}

#[test]
fn box_removes_dashes_and_spaces_not_inner_text() {
    let (tv, ds) = parsed("treeView-beta\n└─ a  b  \n├──c\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["a  b", "c"]);
}

#[test]
fn box_passes_annotations_and_metadata() {
    let (tv, ds) = parsed("treeView-beta\n title T\n├── a ## d\n└── \"q\" icon(x)\n");
    assert!(ds.is_empty());
    assert_eq!(value(tv.title.as_ref()), "T");
    assert_eq!(desc_of(&tv, 0), "d");
    assert_eq!(names(&tv), ["a", "q"]);
    assert_eq!(icon_of(&tv, 1), "x");
}

#[test]
fn box_decoration_only_lines_are_omitted() {
    let (tv, ds) = parsed("treeView-beta\n│\n├── a\n│   \n ─ │ \n└── b\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["a", "b"]);
}

#[test]
fn box_line_with_box_chars_but_no_branch_is_a_root() {
    let (tv, ds) = parsed("treeView-beta\nSection ─ A.txt\n├── b\n");
    assert!(ds.is_empty());
    assert_eq!(names(&tv), ["Section ─ A.txt", "b"]);
    assert_eq!(levels(&tv), [0, 4]);
}

#[test]
fn box_empty_node_spans_prefix_to_line_end() {
    let src = "treeView-beta\n├── a\n└──\n";
    let (tv, ds) = parsed(src);
    assert_eq!(codes(&ds), [super::C_EMPTY_BOX]);
    let first = ds.first();
    assert_eq!(first.map_or("", |d| text(src, d.span)), "└──");
    assert_eq!(
        first.map_or("", |d| d.message.as_str()),
        "expected a filename or directory name after the box-drawing prefix"
    );
    assert_eq!(names(&tv), ["a"]);
}

#[test]
fn box_mixed_indentation_spans_leading_blanks() {
    let src = "treeView-beta\n├── a\n   b\n";
    let (tv, ds) = parsed(src);
    assert_eq!(codes(&ds), [super::C_MIXED]);
    let first = ds.first();
    assert_eq!(first.map_or("", |d| text(src, d.span)), "   ");
    assert_eq!(
        first.map_or("", |d| d.message.as_str()),
        "unexpected indentation without box-drawing characters"
    );
    assert_eq!(names(&tv), ["a"]);
}

#[test]
fn box_mixed_indentation_expands_tabs() {
    let src = "treeView-beta\n├── a\n\tb\n";
    let (_, ds) = parsed(src);
    assert_eq!(codes(&ds), [super::C_MIXED]);
    assert_eq!(ds.first().map_or("", |d| text(src, d.span)), "\t");
}

#[test]
fn box_indented_line_before_first_branch_is_mixed() {
    let (_, ds) = parsed("treeView-beta\n  a\n├── b\n");
    assert_eq!(codes(&ds), [super::C_MIXED]);
}

#[test]
fn box_mode_needs_header_line_alone() {
    let (tv, _) = parsed("treeView-beta  \n├── a\n");
    assert!(tv.nodes.is_empty());
}

#[test]
fn box_spans_point_into_original_lines() {
    let src = "treeView-beta\n├── a\n│   └── bb\n";
    let (tv, ds) = parsed(src);
    assert!(ds.is_empty());
    assert_eq!(slice(src, tv.nodes.get(1).map(|n| &n.name)), "bb");
    assert_eq!(slice(src, tv.nodes.first().map(|n| &n.name)), "a");
    let end = tv.nodes.first().map_or(0, |n| n.span.end);
    assert_eq!(src.get(end - 1..end), Some("a"));
}

#[test]
fn plain_input_without_box_characters_is_unchanged() {
    let (tv, ds) = parsed("treeView-beta\n  src/\n      a\n");
    assert!(ds.is_empty());
    assert_eq!(levels(&tv), [2, 6]);
}
