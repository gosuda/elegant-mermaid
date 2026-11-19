#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|source: &str| {
    let parsed = elegant_mermaid::syntax::class::parse(source, &[]);
    for diagnostic in &parsed.diagnostics {
        assert!(diagnostic.span.start <= diagnostic.span.end);
        assert!(diagnostic.span.end <= source.len());
        assert!(source.is_char_boundary(diagnostic.span.start));
        assert!(source.is_char_boundary(diagnostic.span.end));
    }
    let _ = elegant_mermaid::model::class::resolve(source, &parsed.document);
});
