#![expect(
    clippy::unwrap_used,
    reason = "tests assert on fixtures whose absence is a failing test"
)]

use super::{Model, NodeType, resolve};
use crate::diag::Diagnostic;
use crate::syntax::kanban::parse;
use crate::syntax::preprocess::preprocess;

fn resolved(src: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(src).removed;
    let parsed = parse(src, &removed);
    let (model, mut diagnostics) = resolve(src, &parsed.document);
    let mut all = parsed.diagnostics;
    all.append(&mut diagnostics);
    (model, all)
}
fn codes(ds: &[Diagnostic]) -> Vec<&'static str> {
    ds.iter().map(|d| d.code).collect()
}

fn ids(model: &Model, indexes: &[usize]) -> Vec<String> {
    indexes
        .iter()
        .map(|index| model.nodes.get(*index).unwrap().id.clone())
        .collect()
}

fn slice(src: &str, d: &Diagnostic) -> String {
    src.get(d.span.start..d.span.end).unwrap_or("").to_owned()
}

#[test]
fn sections_and_cards() {
    let (model, ds) = resolved(
        "kanban\n  todo[To Do]\n    a[Task A]\n    b[Task B]\n  done[Done]\n    c[Task C]\n",
    );
    assert!(ds.is_empty());
    assert_eq!(ids(&model, &model.sections), ["todo", "done"]);
    let columns = model.columns();
    assert_eq!(columns.len(), 2);
    assert_eq!(ids(&model, &columns[0].cards), ["a", "b"]);
    assert_eq!(ids(&model, &columns[1].cards), ["c"]);
    let card = &model.nodes[columns[0].cards[0]];
    assert_eq!(card.label, "Task A");
    assert_eq!(card.level, 4);
    assert_eq!(model.nodes[0].node_type, NodeType::Rect);
}

#[test]
fn same_indentation_makes_every_node_a_section() {
    let (model, ds) = resolved("kanban\n  a[A]\n  b[B]\n  c[C]\n");
    assert!(ds.is_empty());
    assert_eq!(ids(&model, &model.sections), ["a", "b", "c"]);
    assert!(model.columns().iter().all(|column| column.cards.is_empty()));
}

#[test]
fn deeper_indentation_attaches_to_latest_section() {
    let (model, ds) = resolved("kanban\n  s[S]\n      a[A]\n    b[B]\n          c[C]\n");
    assert!(ds.is_empty());
    assert_eq!(ids(&model, &model.columns()[0].cards), ["a", "b", "c"]);
}

#[test]
fn repeated_section_ids_share_cards() {
    let (model, ds) = resolved("kanban\n  s[One]\n    a[A]\n  s[Two]\n    b[B]\n");
    assert!(ds.is_empty());
    let columns = model.columns();
    assert_eq!(ids(&model, &columns[0].cards), ["a", "b"]);
    assert_eq!(ids(&model, &columns[1].cards), ["a", "b"]);
}

#[test]
fn first_level_is_the_section_level() {
    let (model, ds) = resolved("kanban\n      s[S]\n      t[T]\n        a[A]\n");
    assert!(ds.is_empty());
    assert_eq!(ids(&model, &model.sections), ["s", "t"]);
    assert_eq!(model.nodes[0].level, 6);
}

#[test]
fn items_without_section_rejects_on_next_insertion() {
    let src = "kanban\n    s[S]\n  a[A]\n    t[T]\n";
    let (model, ds) = resolved(src);
    assert_eq!(codes(&ds), ["kanban/items-without-section"]);
    assert_eq!(ds[0].message, "items without section detected at A");
    assert_eq!(slice(src, &ds[0]), "  ");
    assert_eq!(model.nodes.len(), 2);
}

#[test]
fn items_without_section_uses_first_token_at_level_zero() {
    let src = "kanban\n  s[S]\nzero[Z]\n  t[T]\n";
    let (_, ds) = resolved(src);
    assert_eq!(codes(&ds), ["kanban/items-without-section"]);
    assert_eq!(slice(src, &ds[0]), "zero");
}

#[test]
fn below_section_level_card_is_retained_at_end_of_input() {
    let (model, ds) = resolved("kanban\n    s[S]\n  a[A]\n");
    assert!(ds.is_empty());
    assert_eq!(ids(&model, &model.columns()[0].cards), ["a"]);
}

#[test]
fn lower_level_error_is_reported_once_per_offender() {
    let (_, ds) = resolved("kanban\n    s[S]\n  a[A]\n    t[T]\n    u[U]\n");
    assert_eq!(codes(&ds), ["kanban/items-without-section"]);
}

#[test]
fn tabs_count_as_one_character() {
    let (model, ds) = resolved("kanban\n\ts[S]\n\t\ta[A]\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes[0].level, 1);
    assert_eq!(model.nodes[1].level, 2);
}

#[test]
fn node_types_and_stored_fields() {
    let (model, ds) =
        resolved("kanban\n  a\n  b[x]\n  c(x)\n  d((x))\n  e))x((\n  f{{x}}\n  g)x(\n");
    assert!(ds.is_empty());
    let want = [
        NodeType::Default,
        NodeType::Rect,
        NodeType::RoundedRect,
        NodeType::Circle,
        NodeType::Bang,
        NodeType::Hexagon,
        NodeType::Cloud,
    ];
    for (node, expected) in model.nodes.iter().zip(want) {
        assert_eq!(node.node_type, expected, "{}", node.id);
    }
    assert_eq!(model.nodes[0].padding, 10);
    assert_eq!(model.nodes[1].padding, 20);
    assert_eq!(model.nodes[2].padding, 20);
    assert_eq!(model.nodes[3].padding, 10);
    assert_eq!(model.nodes[5].padding, 20);
    assert_eq!(model.nodes[0].width, 200);
}

#[test]
fn id_falls_back_to_description_and_keeps_trailing_space() {
    let (model, ds) = resolved("kanban\n  [Only]\n  id  [x]\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes[0].id, "Only");
    assert_eq!(model.nodes[0].label, "Only");
    assert_eq!(model.nodes[1].id, "id  ");
}

#[test]
fn entities_decode_in_id_and_label() {
    let (model, ds) = resolved("kanban\n  a#35;b[x #quot; y #9731;]\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes[0].id, "a#b");
    assert_eq!(model.nodes[0].label, "x \" y \u{2603}");
}

#[test]
fn line_ends_in_text_normalise_before_decoding() {
    let (model, ds) =
        resolved("kanban\r\n  a[x\r\ny]\r\n    c[p\rq]\r\n    ::icon(i\rj)\r\n    :::k\r\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes[0].label, "x\ny");
    assert_eq!(model.nodes[1].label, "p\nq");
    assert_eq!(model.nodes[1].icon, "i\nj");
}

#[test]
fn metadata_fields() {
    let src = "kanban\n  s[S]\n    a[A]@{ ticket: MC-2036, assigned: 'knsv', priority: 'Very High', icon: 7, label: \"New\", extra: 1 }\n";
    let (model, ds) = resolved(src);
    assert!(ds.is_empty());
    let card = &model.nodes[1];
    assert_eq!(card.ticket, "MC-2036");
    assert_eq!(card.assigned, "knsv");
    assert_eq!(card.priority, "Very High");
    assert!(card.has_priority);
    assert_eq!(card.icon, "7");
    assert_eq!(card.label, "New");
}

#[test]
fn metadata_falsy_values_leave_fields_unset() {
    let (model, ds) = resolved(
        "kanban\n  a[A]@{ ticket: 0, assigned: false, priority: null, icon: '', label: 0.0 }\n",
    );
    assert!(ds.is_empty());
    let node = &model.nodes[0];
    assert!(node.ticket.is_empty() && node.assigned.is_empty() && node.icon.is_empty());
    assert!(!node.has_priority);
    assert_eq!(node.label, "A");
}

#[test]
fn metadata_javascript_conversions() {
    let (model, ds) = resolved(
        "kanban\n  a[A]@{ ticket: 007, assigned: 1.50, icon: [x, y], label: true }\n  b[B]@{\n    priority:\n      k: v\n}\n",
    );
    assert!(ds.is_empty());
    let node = &model.nodes[0];
    assert_eq!(node.ticket, "7");
    assert_eq!(node.assigned, "1.5");
    assert_eq!(node.icon, "x,y");
    assert_eq!(node.label, "true");
    assert_eq!(model.nodes[1].priority, "[object Object]");
    assert!(model.nodes[1].has_priority);
}

#[test]
fn metadata_conversion_failure_rejects() {
    let src = "kanban\n  a[A]@{\n    ticket:\n      toString: 1\n}\n";
    let (model, ds) = resolved(src);
    assert_eq!(codes(&ds), ["kanban/malformed-metadata"]);
    assert_eq!(ds[0].message, "invalid node metadata");
    assert_eq!(slice(src, &ds[0]), "@{\n    ticket:\n      toString: 1\n}");
    assert!(model.nodes.is_empty());
}

#[test]
fn metadata_block_form() {
    let (model, ds) = resolved("kanban\n  a[A]@{\n    ticket: T1\n    assigned: me\n  }\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes[0].ticket, "T1");
    assert_eq!(model.nodes[0].assigned, "me");
}

#[test]
fn metadata_quoted_line_break_becomes_br() {
    let (model, ds) = resolved("kanban\n  a[A]@{ label: \"x\n   y\" }\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes[0].label, "x<br/>y");
}

#[test]
fn malformed_metadata_rejects_without_insertion() {
    for src in [
        "kanban\n  a[A]@{ ticket: [ }\n",
        "kanban\n  a[A]@{ ticket: 1, ticket: 2 }\n",
        "kanban\n  a[A]@{\n}\n",
        "kanban\n  a[A]@{\n  # only a comment\n}\n",
        "kanban\n  a[A]@{ null }\n  b@{ ~ }\n",
    ] {
        let (model, ds) = resolved(src);
        assert!(codes(&ds).contains(&"kanban/malformed-metadata"), "{src}");
        assert!(model.nodes.is_empty(), "{src}");
    }
}

#[test]
fn scalar_metadata_document_is_ignored() {
    let (model, ds) = resolved("kanban\n  a[A]@{\n  just text\n}\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes.len(), 1);
}

#[test]
fn invalid_shape_rejects_with_value_span() {
    for (src, want) in [
        ("kanban\n  a[A]@{ shape: kanbanItem }\n", "kanbanItem"),
        (
            "kanban\n  a[A]@{ shape: 'two_words', x: 1 }\n",
            "'two_words'",
        ),
        ("kanban\n  a[A]@{ x: 1, shape: 5 }\n", "5"),
        ("kanban\n  a[A]@{\n    shape: Upper # note\n}\n", "Upper"),
    ] {
        let (model, ds) = resolved(src);
        assert_eq!(codes(&ds), ["kanban/invalid-shape"], "{src}");
        assert_eq!(slice(src, &ds[0]), want, "{src}");
        assert!(model.nodes.is_empty(), "{src}");
    }
    let (_, ds) = resolved("kanban\n  a[A]@{ shape: 5 }\n");
    assert_eq!(
        ds[0].message,
        "invalid shape 5; shape names must be lowercase without underscores"
    );
}

#[test]
fn lowercase_and_falsy_shapes_are_ignored() {
    let (model, ds) =
        resolved("kanban\n  a[A]@{ shape: rect }\n  b[B]@{ shape: '' }\n  c[C]@{ shape: false }\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes.len(), 3);
}

#[test]
fn decorations_modify_last_node() {
    let (model, ds) =
        resolved("kanban\n  s[S]\n    ::icon(fa fa-x)\n  :::big #35;\n        ::icon(fa fa-y)\n");
    assert!(ds.is_empty());
    assert_eq!(model.nodes[0].icon, "fa fa-y");
    assert_eq!(model.nodes[0].class, "big #");
}

#[test]
fn decoration_without_node_rejects() {
    let src = "kanban\n  ::icon(x)\n  s[S]\n";
    let (model, ds) = resolved(src);
    assert_eq!(codes(&ds), ["kanban/decoration-without-node"]);
    assert_eq!(ds[0].message, "decoration requires a preceding node");
    assert_eq!(slice(src, &ds[0]), "::icon(x)");
    assert_eq!(model.nodes.len(), 1);
}

#[test]
fn config_keys() {
    let (model, ds) = resolved(
        "---\nconfig:\n  kanban:\n    sectionWidth: 250\n    padding: 4\n  mindmap:\n    padding: 6\n    maxNodeWidth: 300\n---\nkanban\n  a[A]\n",
    );
    assert!(ds.is_empty());
    assert_eq!(model.config.section_width, Some(250));
    assert_eq!(model.config.padding, Some(4));
    assert_eq!(model.nodes[0].padding, 12);
    assert_eq!(model.nodes[0].width, 300);
}

#[test]
fn config_ignores_zero_width_decimals_and_negatives() {
    let (model, _) = resolved(
        "%%{init: {\"kanban\": {\"sectionWidth\": 0, \"padding\": 1.5}}}%%\nkanban\n  a\n",
    );
    assert_eq!(model.config.section_width, None);
    assert_eq!(model.config.padding, None);
    let (model, _) = resolved("%%{init: {\"kanban\": {\"padding\": -2}}}%%\nkanban\n  a\n");
    assert_eq!(model.config.padding, None);
}

#[test]
fn empty_document_has_no_sections() {
    let (model, ds) = resolved("kanban\n\n");
    assert!(ds.is_empty());
    assert!(model.sections.is_empty());
    assert!(model.columns().is_empty());
}
