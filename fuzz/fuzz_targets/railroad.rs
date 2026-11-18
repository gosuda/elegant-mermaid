#![no_main]
use elegant_mermaid::{
    Diagnostic, DiagramKind, RenderError,
    layout::families,
    model::{self, Resolved},
    scene::{DumpOptions, Profile},
    syntax,
};
use libfuzzer_sys::fuzz_target;

fn check_spans(stage: &str, source: &str, diagnostics: &[Diagnostic]) {
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
            source.is_char_boundary(span.start) && source.is_char_boundary(span.end),
            "{stage} diagnostic {} splits UTF-8 at {span:?}; source: {source:?}",
            diagnostic.code
        );
    }
}

fn check_layout(source: &str, removed: &[elegant_mermaid::Span]) {
    if elegant_mermaid::parse(source).kind() != Some(DiagramKind::Railroad) {
        return;
    }
    for profile in [Profile::Vector, Profile::Cell] {
        let (resolved, _) = Resolved::parse(DiagramKind::Railroad, source, removed);
        let Some(resolved) = resolved else {
            panic!("no railroad model for {source:?}");
        };
        let input = resolved
            .input(profile, DumpOptions::default())
            .unwrap_or_else(|error| panic!("{profile:?} input: {error}; source: {source:?}"));
        match families::layout(&input) {
            Err(RenderError::Overflow | RenderError::TooLarge { .. }) => {}
            Err(error) => panic!("{profile:?} layout: {error}; source: {source:?}"),
            Ok((scene, _)) => {
                let verdict = scene.validate();
                assert!(
                    matches!(verdict, Ok(None)),
                    "{profile:?} layout violates {verdict:?}; source: {source:?}"
                );
            }
        }
    }
}

fuzz_target!(|bytes: &[u8]| {
    let (source, _) = elegant_mermaid::source::repair_utf8(bytes);
    let prep = syntax::preprocess::preprocess(&source);
    let parsed = syntax::railroad::parse(&source, &prep.removed);
    let (_, resolved) = model::railroad::resolve(&parsed.document);
    check_spans("preprocess", &source, &prep.diagnostics);
    check_spans("parser", &source, &parsed.diagnostics);
    check_spans("resolver", &source, &resolved);
    check_layout(&source, &prep.removed);
});
