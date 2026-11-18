#![no_main]
use elegant_mermaid::scene::{DumpOptions, Profile};
use elegant_mermaid::{DiagramKind, layout, model};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|bytes: &[u8]| {
    let (source, _) = elegant_mermaid::source::repair_utf8(bytes);
    let prep = elegant_mermaid::syntax::preprocess::preprocess(&source);
    let parsed = elegant_mermaid::syntax::quadrant::parse(&source, &prep.removed);
    let (_, semantic_diagnostics) =
        elegant_mermaid::model::quadrant::resolve(&source, &parsed.document);
    for (stage, diagnostics) in [
        ("preprocess", prep.diagnostics.as_slice()),
        ("parser", parsed.diagnostics.as_slice()),
        ("resolver", semantic_diagnostics.as_slice()),
    ] {
        for diagnostic in diagnostics {
            let span = diagnostic.span;
            assert!(
                span.start <= span.end,
                "{stage} diagnostic {} has reversed span {span:?}; source: {source:?}",
                diagnostic.code
            );
            assert!(
                span.end <= source.len(),
                "{stage} diagnostic {} has out-of-bounds span {span:?} for {} bytes; source: {source:?}",
                diagnostic.code,
                source.len()
            );
            assert!(
                source.is_char_boundary(span.start),
                "{stage} diagnostic {} starts inside UTF-8 at {span:?}; source: {source:?}",
                diagnostic.code
            );
            assert!(
                source.is_char_boundary(span.end),
                "{stage} diagnostic {} ends inside UTF-8 at {span:?}; source: {source:?}",
                diagnostic.code
            );
        }
    }
    let clean = prep.diagnostics.is_empty()
        && parsed.diagnostics.is_empty()
        && semantic_diagnostics.is_empty();
    let (resolved, _) = model::Resolved::parse(DiagramKind::Quadrant, &source, &prep.removed);
    let Some(resolved) = resolved.filter(|_| clean) else {
        return;
    };
    for profile in [Profile::Vector, Profile::Cell] {
        let Ok(input) = resolved.input(profile, DumpOptions::default()) else {
            continue;
        };
        let Ok((scene, _)) = layout::families::layout(&input) else {
            continue;
        };
        let verdict = scene.validate();
        assert!(
            matches!(verdict, Ok(None)),
            "{profile:?} layout violates a clause: {verdict:?}; source: {source:?}"
        );
    }
});
