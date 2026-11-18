use super::{Event, Model, Placement, box_color_label, preprocess, resolve};
use crate::diag::Diagnostic;
use crate::syntax::sequence::parse;

fn model_of(source: &str) -> (Model, Vec<Diagnostic>) {
    let parsed = parse(source, &[]);
    resolve(source, &parsed.document)
}

fn pairs(fields: &[(String, String)]) -> Vec<(&str, &str)> {
    fields
        .iter()
        .map(|(key, value)| (key.as_str(), value.as_str()))
        .collect()
}

fn split(raw: &str) -> (Option<String>, String) {
    box_color_label(raw)
}

#[test]
fn colour_function_runs_to_the_last_parenthesis() {
    assert_eq!(
        split("rgb(23, 124, 207) Profiles"),
        (
            Some("rgb(23, 124, 207)".to_string()),
            "Profiles".to_string()
        )
    );
    assert_eq!(
        split("rgb (1, 2, 3) T"),
        (Some("rgb (1, 2, 3)".to_string()), "T".to_string())
    );
}

#[test]
fn named_colour_is_the_leading_word() {
    assert_eq!(
        split("Green New serwis"),
        (Some("Green".to_string()), "New serwis".to_string())
    );
    assert_eq!(split("Aqua"), (Some("Aqua".to_string()), String::new()));
}

#[test]
fn other_text_is_the_whole_title() {
    assert_eq!(split("Group 1"), (None, "Group 1".to_string()));
    assert_eq!(split("\"Group\""), (None, "\"Group\"".to_string()));
    assert_eq!(split("rgb(1,2"), (None, "rgb(1,2".to_string()));
    assert_eq!(split("#fff Title"), (None, "#fff Title".to_string()));
}

#[test]
fn note_placement_folds_ascii_case_of_the_keyword() {
    let source = "sequenceDiagram\nNote RIGHT OF A: x\nnote right of A: y\nnote over A,B: z\nNOTE Left Of A: w\nNote OVER A: v\n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let placements: Vec<Placement> = model
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Note(note) => Some(note.placement),
            _ => None,
        })
        .collect();
    assert_eq!(
        placements,
        [
            Placement::RightOf,
            Placement::RightOf,
            Placement::Over,
            Placement::LeftOf,
            Placement::Over
        ]
    );
}

#[test]
fn metadata_alias_and_properties_come_from_a_yaml_mapping() {
    let source = "sequenceDiagram\nparticipant R@{ alias: Jobs }\nparticipant S@{ x: 1 }\nparticipant L@{ label: Kept }\n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.actors[0].label, "Jobs");
    assert_eq!(pairs(&model.actors[1].properties), [("x", "1")]);
    assert_eq!(model.actors[2].label, "L", "only the alias key renames");
    assert_eq!(pairs(&model.actors[2].properties), [("label", "Kept")]);
}

#[test]
fn metadata_on_one_line_holds_several_comma_separated_keys() {
    let source = "sequenceDiagram\nparticipant API@{ \"type\": \"boundary\", \"alias\": \"Public API\", \"x\": 1 }\nparticipant Q@{ type: queue, alias: Jobs }\n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.actors[0].kind, "boundary");
    assert_eq!(model.actors[0].label, "Public API");
    assert_eq!(pairs(&model.actors[0].properties), [("x", "1")]);
    assert_eq!(model.actors[1].kind, "queue");
    assert_eq!(model.actors[1].label, "Jobs");
}

#[test]
fn explicit_alias_beats_metadata_alias_unless_it_equals_the_id() {
    let source = "sequenceDiagram\nparticipant API@{ \"alias\": \"Internal\" } as External\nparticipant DB@{ \"alias\": \"Store\" } as DB\n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.actors[0].label, "External");
    assert_eq!(pairs(&model.actors[0].properties), [("alias", "Internal")]);
    assert_eq!(model.actors[1].label, "Store");
}

#[test]
fn metadata_on_several_lines_reads_a_block_mapping() {
    let source = "sequenceDiagram\nparticipant O@{\ntype: database\nalias: Oh\n}\n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.actors[0].kind, "database");
    assert_eq!(model.actors[0].label, "Oh");
}

#[test]
fn indented_metadata_on_several_lines_is_rejected_like_upstream() {
    for (source, span) in [
        (
            "sequenceDiagram\nparticipant A@{\n  type: database\n  alias: Disk\n}\n",
            (51, 57),
        ),
        (
            "sequenceDiagram\nparticipant A@{\n  type: database\n  type: queue\n}\n",
            (51, 56),
        ),
    ] {
        let (model, diagnostics) = model_of(source);
        assert_eq!(diagnostics.len(), 1, "{source:?}: {diagnostics:?}");
        assert_eq!(diagnostics[0].code, "config/malformed");
        assert_eq!(diagnostics[0].message, "malformed config value");
        assert_eq!(
            (diagnostics[0].span.start, diagnostics[0].span.end),
            span,
            "{source:?}"
        );
        assert_eq!(
            model.actors[0].kind, "participant",
            "a rejected body has no model effect"
        );
    }
}

#[test]
fn metadata_reader_diagnostics_reach_the_source_spans() {
    for (source, message, span) in [
        (
            "sequenceDiagram\nparticipant A@{ type: database, type: queue }\n",
            "duplicate key",
            (48, 52),
        ),
        (
            "sequenceDiagram\nparticipant A@{\ntype: database\ntype: queue\n}\n",
            "duplicate key",
            (47, 51),
        ),
        (
            "sequenceDiagram\nparticipant A@{ type: x, }\n",
            "malformed config value",
            (41, 42),
        ),
        (
            "sequenceDiagram\nparticipant A@{ type: x,\n}\n",
            "malformed config value",
            (41, 42),
        ),
        (
            "sequenceDiagram\nparticipant A@{ \"type: \"entity\" }\n",
            "malformed config value",
            (40, 49),
        ),
    ] {
        let (_, diagnostics) = model_of(source);
        assert_eq!(diagnostics.len(), 1, "{source:?}: {diagnostics:?}");
        assert_eq!(diagnostics[0].code, "config/malformed", "{source:?}");
        assert_eq!(diagnostics[0].message, message, "{source:?}");
        assert_eq!(
            (diagnostics[0].span.start, diagnostics[0].span.end),
            span,
            "{source:?}"
        );
    }
}

#[test]
fn link_without_at_sign_keeps_the_whole_text_as_the_url() {
    let source = "sequenceDiagram\nlink A: foo\nlink B: @url\nlink C: éé@ u\nlink D: abc  \n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(pairs(&model.actors[0].links), [("f", "foo")]);
    assert_eq!(pairs(&model.actors[1].links), [("@ur", "url")]);
    assert_eq!(pairs(&model.actors[2].links), [("é", "u")]);
    assert_eq!(pairs(&model.actors[3].links), [("a", "abc")]);
}

#[test]
fn repeated_link_label_replaces_the_earlier_url() {
    let source = "sequenceDiagram\nlink A: Docs @ https://one.dev\nlink A: Wiki @ https://wiki.dev\nlink A: Docs @ https://two.dev\nlinks A: {\"Wiki\": \"https://three.dev\"}\n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(
        pairs(&model.actors[0].links),
        [("Docs", "https://two.dev"), ("Wiki", "https://three.dev")]
    );
}

#[test]
fn properties_and_details_json_forms_map_onto_properties_and_links() {
    let source = "sequenceDiagram\nproperties A: {\"p\": \"v\", \"q\": true, \"n\": null, \"o\": {\"x\": 1}, \"a\": [1], \"d\": 1.5}\ndetails B: {\"properties\": {\"k\": \"v\"}, \"links\": {\"L\": \"https://l.dev\"}, \"other\": 1}\ndetails B: {\"properties\": {\"k\": \"w\"}}\ndetails C: {\"k\": \"v\"}\ndetails D: element-id\nproperties E: [1]\n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(
        pairs(&model.actors[0].properties),
        [("p", "v"), ("q", "true"), ("d", "1.5")]
    );
    assert_eq!(pairs(&model.actors[1].properties), [("k", "w")]);
    assert_eq!(pairs(&model.actors[1].links), [("L", "https://l.dev")]);
    assert!(
        model.actors[2].properties.is_empty(),
        "flat details has no properties member"
    );
    assert!(
        model.actors[3].properties.is_empty(),
        "a reference that is not JSON has no effect"
    );
    assert!(
        model.actors[4].properties.is_empty(),
        "a JSON array has no effect"
    );
}

#[test]
fn link_statements_drop_the_colon_before_their_text() {
    let source = "sequenceDiagram\nlink A: Dash @ https://x.dev\nlink B: wrap: Wrapped @ https://w.dev\nlinks C: {\"k\": \"https://k.dev\", \"n\": 2}\nproperties D: {\"p\": \"v\", \"q\": true}\nproperties D: {\"p\": \"w\"}\ndetails E: {\"properties\": {\"d\": \"v\"}}\nlinks F: not json\n";
    let (model, diagnostics) = model_of(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(pairs(&model.actors[0].links), [("Dash", "https://x.dev")]);
    assert_eq!(
        pairs(&model.actors[1].links),
        [("Wrapped", "https://w.dev")]
    );
    assert_eq!(
        pairs(&model.actors[2].links),
        [("k", "https://k.dev"), ("n", "2")]
    );
    assert_eq!(
        pairs(&model.actors[3].properties),
        [("p", "w"), ("q", "true")]
    );
    assert_eq!(pairs(&model.actors[4].properties), [("d", "v")]);
    assert!(
        model.actors[5].links.is_empty(),
        "malformed JSON has no model effect"
    );
}

#[test]
fn accessibility_block_drops_removed_comment_lines() {
    let with_comment = "sequenceDiagram\naccDescr {\nfirst\n%% c\nsecond\n}\nA->>B: x\n";
    let removed = preprocess(with_comment).removed;
    let parsed = parse(with_comment, &removed);
    let (model, diagnostics) = resolve(with_comment, &parsed.document);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.acc_descr, "first\nsecond");
}
