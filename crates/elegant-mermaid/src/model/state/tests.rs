use super::*;

fn resolved(source: &str) -> (Model, Vec<Diagnostic>) {
    let parsed = crate::syntax::state::parse(source, &[]);
    assert_eq!(parsed.diagnostics, Vec::<Diagnostic>::new());
    resolve(source, &parsed.document)
}

#[test]
fn repeated_definitions_keep_identity_type_and_first_body() {
    let (model, diagnostics) = resolved(
        "stateDiagram-v2\nA: first\nstate A <<fork>>\nstate A {\n B\n}\nstate A {\n C\n}\nA: second\n",
    );
    assert_eq!(
        model
            .states
            .iter()
            .map(|s| s.id.as_str())
            .collect::<Vec<_>>(),
        ["A", "B"]
    );
    assert_eq!(model.states[0].kind, StateKind::Default);
    assert_eq!(
        model.states[0]
            .descriptions
            .iter()
            .map(|s| s.value.as_str())
            .collect::<Vec<_>>(),
        ["first", "second"]
    );
    assert_eq!(model.states[1].parent, Some(Parent::State(0)));
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].span, model.states[0].descriptions[1].span);
}

#[test]
fn generated_ids_reuse_raw_identity_and_keep_endpoint_roles() {
    let (model, diagnostics) =
        resolved("stateDiagram-v2\nstate root_start <<fork>>\n[*] --> A\nA --> [*]\n[*] --> A\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.states.len(), 3);
    assert_eq!(model.states[0].kind, StateKind::Fork);
    assert_eq!(model.transitions[0].from.state, 0);
    assert_eq!(model.transitions[0].from.role, EndpointRole::Start);
    assert_eq!(model.transitions[1].to.role, EndpointRole::End);
    assert_eq!(model.transitions.len(), 3);
    assert_eq!(model.transitions[0].to.state, model.transitions[2].to.state);
}

#[test]
fn concurrent_regions_keep_empty_segments_and_delimiters() {
    let source = "stateDiagram-v2\nstate Box {\n--\nA\n--\n--\n}\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.regions.len(), 4);
    assert_eq!(
        model
            .regions
            .iter()
            .map(|r| r.children.len())
            .collect::<Vec<_>>(),
        [0, 1, 0, 0]
    );
    assert_eq!(model.states.len(), 2);
    assert_eq!(model.states[1].parent, Some(Parent::Region(1)));
    for region in &model.regions[1..] {
        assert!(
            region.separator.is_some(),
            "nonleading region {} must retain its divider span; observed {:?}",
            region.id,
            region.separator
        );
        if let Some(span) = region.separator {
            assert_eq!(&source[span.start..span.end], "--");
        }
    }
}

#[test]
fn ordinary_ids_are_global_and_direction_is_local_last_wins() {
    let (model, diagnostics) = resolved(
        "stateDiagram-v2\ndirection LR\nstate X {\n direction BT\n A\n direction RL\n}\nA: outside\ndirection TB\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.states.len(), 2);
    assert_eq!(model.scopes[0].direction, "TB");
    assert_eq!(model.scopes[1].direction, "RL");
    assert_eq!(model.states[1].descriptions[0].value, "outside");
}

#[test]
fn styles_remain_literal_and_classes_append() {
    let (model, diagnostics) = resolved(
        "stateDiagram-v2\nclassDef hot fill:#abc,color:red;\nclassDef hot stroke:#123;\nclass A,B hot\nA:::hot\nstyle A fill:#name;,color:blue;\nstyle A stroke:#456;\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.states[0].classes.len(), 2);
    assert_eq!(model.states[0].styles[0].value, "stroke:#456");
    assert_eq!(model.class_definitions[0].styles.len(), 3);
    assert_eq!(model.class_definitions[0].text_styles[0].value, "fill:red");
}

#[test]
fn notes_replace_and_links_do_not_create_targets() {
    let source = "stateDiagram-v2\nnote left of A: old\nnote right of A: new\nclick absent href \"https://example.test\"\naccTitle: first\naccTitle: last\naccDescr: detail\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.states.len(), 1);
    assert_eq!(model.states[0].note, Some(1));
    assert_eq!(model.notes[1].text.value, "new");
    assert_eq!(model.notes[1].position, "right of");
    assert_eq!(model.links[0].target, "absent");
    assert_eq!(
        model.acc_title.as_ref().map(|v| v.value.as_str()),
        Some("last")
    );
    assert_eq!(
        model.acc_descr.as_ref().map(|v| v.value.as_str()),
        Some("detail")
    );
    for directive in &model.directives {
        assert!(
            source.is_char_boundary(directive.span.start),
            "directive start {} must be a UTF-8 boundary in source of {} bytes",
            directive.span.start,
            source.len()
        );
        assert!(
            directive.span.end <= source.len(),
            "directive end {} must not exceed source length {}",
            directive.span.end,
            source.len()
        );
    }
}

#[test]
fn alias_colon_rules_and_transition_spans_are_retained() {
    let source = "stateDiagram-v2\nstate \"Label\" as A: body: ignored\nstate \"Group\" as B:full {\n [*] --> C: go\n C --> [*]\n}\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.states[0].id, "A");
    assert_eq!(model.states[0].descriptions[1].value, "body");
    assert_eq!(model.states[1].id, "B:full");
    assert_eq!(model.states[2].id, "B:full_start");
    assert_eq!(
        model.transitions[0]
            .label
            .as_ref()
            .map(|t| t.value.as_str()),
        Some("go")
    );
    let transition = &model.transitions[0];
    assert_eq!(
        &source[transition.from.id_span.start..transition.from.id_span.end],
        "[*]"
    );
    assert_eq!(
        &source[transition.arrow_span.start..transition.arrow_span.end],
        "-->"
    );
}

#[test]
fn accepted_no_effect_forms_do_not_create_states() {
    let (model, diagnostics) = resolved(
        "stateDiagram-v2\nstate Unused\nhide empty description\nscale 2 width\nnote \"floating\" as Ghost\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.states.len(), 0);
    assert_eq!(model.notes.len(), 0);
    assert_eq!(model.directives.len(), 4);
}

#[test]
fn last_click_replaces_link_without_implicitly_creating_state() {
    let (model, diagnostics) = resolved(
        "stateDiagram-v2\nclick Missing \"https://first.test\" \"first\"\nclick Missing href \"mailto:last@example.test\"\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.states.len(), 0);
    assert_eq!(model.links.len(), 1);
    assert_eq!(model.links[0].url.value, "mailto:last@example.test");
    assert_eq!(model.links[0].tooltip, None);
}

#[test]
fn unsafe_clicks_warn_even_when_superseded_and_keep_literal_links() {
    let source = "stateDiagram-v2\nclick Missing \"javascript:first\" \" first tooltip \"\nclick Missing \" data:second \" \" final tooltip \"\nclick Other href \" HtTpS://example.test \"\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(model.states.len(), 0);
    assert_eq!(model.links.len(), 2);
    assert_eq!(model.links[0].url.value, " data:second ");
    assert_eq!(
        model.links[0]
            .tooltip
            .as_ref()
            .map(|value| value.value.as_str()),
        Some(" final tooltip ")
    );
    assert_eq!(model.links[1].url.value, " HtTpS://example.test ");
    assert_eq!(diagnostics.len(), 2);
    for (diagnostic, rejected) in diagnostics
        .iter()
        .zip(["\"javascript:first\"", "\" data:second \""])
    {
        assert_eq!(diagnostic.code, "interaction/unsafe-url");
        assert_eq!(diagnostic.severity, Severity::Warning);
        assert_eq!(diagnostic.message, "link URL is not allowed");
        assert_eq!(diagnostic.help, "Use an http, https, or mailto link.");
        assert_eq!(
            &source[diagnostic.span.start..diagnostic.span.end],
            rejected
        );
        assert_eq!(diagnostic.fixes.len(), 0);
    }
}
