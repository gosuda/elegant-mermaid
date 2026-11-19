#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|bytes: &[u8]| {
    let (source, _) = elegant_mermaid::source::repair_utf8(bytes);
    let prep = elegant_mermaid::syntax::preprocess::preprocess(&source);
    let parsed = elegant_mermaid::syntax::eventmodeling::parse(&source, &prep.removed);
    let (_, semantic_diagnostics) =
        elegant_mermaid::model::eventmodeling::resolve(&parsed.document);
    for (stage, diagnostics) in [
        ("preprocess", prep.diagnostics.as_slice()),
        ("parser", parsed.diagnostics.as_slice()),
        ("resolver", semantic_diagnostics.as_slice()),
    ] {
        for diagnostic in diagnostics {
            let spans = std::iter::once(diagnostic.span)
                .chain(diagnostic.related.iter().map(|related| related.span));
            for span in spans {
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
    }
});
