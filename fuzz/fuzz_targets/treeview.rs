#![no_main]
use elegant_mermaid::scene::{DumpOptions, Profile};
use elegant_mermaid::{DiagramKind, layout, model};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|bytes: &[u8]| {
    let (source, _) = elegant_mermaid::source::repair_utf8(bytes);
    let prep = elegant_mermaid::syntax::preprocess::preprocess(&source);
    let (resolved, diagnostics) =
        model::Resolved::parse(DiagramKind::Treeview, &source, &prep.removed);
    for diagnostic in prep.diagnostics.iter().chain(diagnostics.iter()) {
        let span = diagnostic.span;
        assert!(span.start <= span.end && span.end <= source.len());
        assert!(source.is_char_boundary(span.start));
        assert!(source.is_char_boundary(span.end));
        for related in &diagnostic.related {
            let span = related.span;
            assert!(span.start <= span.end && span.end <= source.len());
            assert!(source.is_char_boundary(span.start));
            assert!(source.is_char_boundary(span.end));
        }
    }
    let clean = prep.diagnostics.is_empty() && diagnostics.is_empty();
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
            "profile:{profile:?} layout violates a clause: {verdict:?}; source:{source:?}"
        );
    }
});
