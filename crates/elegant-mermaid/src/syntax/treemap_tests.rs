use super::{convert_number, parse};
use crate::model::treemap::{format_value, resolve, thousandths};

#[test]
fn treemap_indent_tree_and_late_classes() {
    let source = "treemap-beta\n\"Root\"\n  \"Branch\":::aa\n    \"Leaf\": 1,234.5678\n  \"Sibling\": 2\nclassDef aa fill:red;\n";
    let (ast, diagnostics) = parse(source, &[]);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let (model, diagnostics) = resolve(source, &ast);
    assert!(diagnostics.is_empty());
    assert_eq!(model.roots, vec![0]);
    assert_eq!(model.nodes[0].children, vec![1, 3]);
    assert_eq!(model.nodes[1].children, vec![2]);
    assert_eq!(model.nodes[1].styles, vec!["fill:red"]);
    assert_eq!(model.nodes[2].value, 1_234_568);
}
#[test]
fn treemap_parse_float_prefix_and_value_text() {
    for (raw, expected) in [
        ("12_500", "12"),
        ("1,234.5", "1234.5"),
        (".25", ".25"),
        ("12.3.4", "12.3"),
    ] {
        assert_eq!(convert_number(raw), (expected.to_owned(), true));
    }
    assert_eq!(convert_number(".."), (String::new(), false));
    assert_eq!(format_value(thousandths("1234.5678")), "1,234.568");
}
#[test]
fn treemap_recovery_never_creates_unknown_nodes() {
    let source = "treemap\nunknown row\n \"A\": 1\n \"B\": 2\n";
    let (ast, diagnostics) = parse(source, &[]);
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "treemap/unknown-statement");
    let (model, _) = resolve(source, &ast);
    assert_eq!(model.nodes.len(), 2);
    assert_eq!(model.roots, vec![0, 1]);
}
#[test]
fn treemap_unterminated_span_and_multiple_roots() {
    let source = "treemap\n\"A\"\n\"B\"\n\"unterminated";
    let (ast, diagnostics) = parse(source, &[]);
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].span.end, source.len());
    assert_eq!(diagnostics[0].code, "treemap/unterminated");
    let (model, diagnostics) = resolve(source, &ast);
    assert!(diagnostics.is_empty());
    assert_eq!(model.roots, vec![0, 1]);
}
#[test]
fn treemap_lone_cr_and_depth_limit() {
    let source = "treemap\r\"Root\"\r \"A\": 1\r";
    let (ast, diagnostics) = parse(source, &[]);
    assert!(diagnostics.is_empty());
    let (model, _) = resolve(source, &ast);
    assert_eq!(model.nodes[0].children, vec![1]);
    let mut source = "treemap\n".to_owned();
    for i in 0..65 {
        source.push_str(&" ".repeat(i));
        source.push_str("\"N\"\n");
    }
    let (ast, _) = parse(&source, &[]);
    let (_, diagnostics) = resolve(&source, &ast);
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "limit/nesting-depth");
}
