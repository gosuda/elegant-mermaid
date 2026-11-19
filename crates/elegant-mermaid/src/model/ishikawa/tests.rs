use super::{Model, resolve};
use crate::diag::Diagnostic;
use crate::source::Span;

fn resolved(src: &str) -> (Model, Vec<Diagnostic>) {
    let pre = crate::syntax::preprocess::preprocess(src);
    let parsed = crate::syntax::ishikawa::parse(src, &pre.removed);
    let (model, mut diagnostics) = resolve(&parsed.document);
    diagnostics.splice(0..0, parsed.diagnostics);
    (model, diagnostics)
}

fn shape(model: &Model) -> Vec<String> {
    model
        .nodes
        .iter()
        .map(|node| match node.parent {
            Some(parent) => format!(
                "{}<{}",
                node.label,
                model.nodes.get(parent).map_or("", |p| p.label.as_str())
            ),
            None => node.label.clone(),
        })
        .collect()
}

fn labels(model: &Model) -> Vec<&str> {
    model.nodes.iter().map(|n| n.label.as_str()).collect()
}

fn shaped(src: &str) -> Vec<String> {
    let (model, ds) = resolved(src);
    assert!(ds.is_empty(), "{src}: {ds:?}");
    shape(&model)
}

#[test]
fn effect_causes_and_sub_causes() {
    let (m, ds) = resolved("ishikawa-beta\n  Effect\n    A\n      a1\n      a2\n    B\n      b1\n");
    assert!(ds.is_empty());
    assert_eq!(
        shape(&m),
        ["Effect", "A<Effect", "a1<A", "a2<A", "B<Effect", "b1<B"]
    );
    assert_eq!(m.nodes[0].children, [1, 4]);
    assert_eq!(m.nodes[1].children, [2, 3]);
    let depths: Vec<usize> = m.nodes.iter().map(|n| n.depth).collect();
    assert_eq!(depths, [0, 1, 2, 2, 1, 2]);
}

#[test]
fn effect_indentation_never_sets_the_base() {
    assert_eq!(
        shaped("ishikawa-beta\n      Effect\n  A\n    a1\n  B\n"),
        ["Effect", "A<Effect", "a1<A", "B<Effect"]
    );
}

#[test]
fn equal_indentation_makes_flat_causes() {
    assert_eq!(
        shaped("ishikawa-beta\n  Problem\n  Cause A\n  Subcause A1\n  Cause B\n"),
        [
            "Problem",
            "Cause A<Problem",
            "Subcause A1<Problem",
            "Cause B<Problem"
        ]
    );
}

#[test]
fn skipped_levels_attach_to_the_previous_cause() {
    assert_eq!(
        shaped("ishikawa-beta\n  E\n  A\n          deep\n    mid\n"),
        ["E", "A<E", "deep<A", "mid<A"]
    );
}

#[test]
fn decrease_uses_the_stack_not_seen_indentation() {
    assert_eq!(
        shaped("ishikawa-beta\n  E\n   A\n      x\n    y\n  z\n"),
        ["E", "A<E", "x<A", "y<A", "z<E"]
    );
}

#[test]
fn indentation_below_the_first_cause_is_level_one() {
    assert_eq!(
        shaped("ishikawa-beta\n  E\n      A\n  B\n    C\n"),
        ["E", "A<E", "B<E", "C<E"]
    );
}

#[test]
fn tab_counts_as_one_code_unit() {
    assert_eq!(
        shaped("ishikawa-beta\n\tE\n\t\tA\n\t\t\tB\n \t\tC\n"),
        ["E", "A<E", "B<A", "C<A"]
    );
}

#[test]
fn whitespace_statements_create_no_node_and_keep_the_stack() {
    assert_eq!(
        shaped("ishikawa-beta\n  E\n    A\n%% note\n\n   \n      a\n"),
        ["E", "A<E", "a<A"]
    );
}

#[test]
fn header_only_is_an_empty_model() {
    let (m, ds) = resolved("ishikawa-beta\n");
    assert!(ds.is_empty());
    assert!(m.nodes.is_empty());
}

#[test]
fn labels_are_trimmed_and_decoded_and_never_merged() {
    let (m, ds) = resolved(
        "ishikawa-beta\n  Tea #9829; time   \n    x\n    x\n    #amp; &#38; #nope; #0;\n    accTitle: name\n",
    );
    assert!(ds.is_empty());
    assert_eq!(
        labels(&m),
        [
            "Tea \u{2665} time",
            "x",
            "x",
            "& && #nope; #0;",
            "accTitle: name"
        ]
    );
}

#[test]
fn non_breaking_spaces_trim_like_javascript() {
    let (m, ds) = resolved("ishikawa-beta\n  \u{a0}E\u{3000}\n");
    assert!(ds.is_empty());
    assert_eq!(labels(&m), ["E"]);
}

fn chain(depth: usize) -> String {
    let mut out = String::from("ishikawa-beta\n");
    for i in 0..=depth {
        out.push_str(&" ".repeat(i + 1));
        out.push_str("n\n");
    }
    out
}

#[test]
fn depth_limit_is_sixty_four() {
    let (m, ds) = resolved(&chain(64));
    assert!(ds.is_empty());
    assert_eq!(m.nodes.len(), 65);
    assert_eq!(m.nodes[64].depth, 64);

    let src = chain(65);
    let (m, ds) = resolved(&src);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].code, "limit/nesting-depth");
    assert_eq!(ds[0].message, "nesting depth exceeds 64");
    assert_eq!(ds[0].help, "Reduce the nesting to 64 levels or fewer.");
    assert_eq!(m.nodes.len(), 65);
    let last = src.len() - 2;
    assert_eq!(
        ds[0].span,
        Span {
            start: last,
            end: last + 1
        }
    );
}

#[test]
fn siblings_after_a_dropped_node_still_attach() {
    let src = format!("{}   after\n", chain(65));
    let (m, ds) = resolved(&src);
    assert_eq!(ds.len(), 1);
    let last = m.nodes.last();
    assert_eq!(last.map(|n| n.label.as_str()), Some("after"));
    assert_eq!(last.map(|n| n.depth), Some(2));
}
