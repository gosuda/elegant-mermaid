#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|bytes: &[u8]| {
    let (source, _) = elegant_mermaid::source::repair_utf8(bytes);
    let prep = elegant_mermaid::syntax::preprocess::preprocess(&source);
    let parsed = elegant_mermaid::syntax::cynefin::parse(&source, &prep.removed);
    let (_, semantic_diagnostics) =
        elegant_mermaid::model::cynefin::resolve(&source, &parsed.document);
    for (stage, diagnostics) in [
        ("preprocess", prep.diagnostics.as_slice()),
        ("parser", parsed.diagnostics.as_slice()),
        ("resolver", semantic_diagnostics.as_slice()),
    ] {
        for diagnostic in diagnostics {
            let span = diagnostic.span;
            assert!(
                span.start <= span.end && span.end <= source.len(),
                "{stage} diagnostic {} has span {span:?} for {} bytes; source: {source:?}",
                diagnostic.code,
                source.len()
            );
            assert!(
                source.is_char_boundary(span.start) && source.is_char_boundary(span.end),
                "{stage} diagnostic {} span {span:?} splits UTF-8; source: {source:?}",
                diagnostic.code
            );
        }
    }
});
