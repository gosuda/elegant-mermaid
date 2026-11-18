#![no_main]
use elegant_mermaid::cells::Charset;
use elegant_mermaid::label::Segment;
use elegant_mermaid::math::syntax::{self, Parsed};
use elegant_mermaid::math::vector::{self, FormulaBox, Leaf};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };
    for line in &elegant_mermaid::label::parse(source).lines {
        for segment in &line.segments {
            check_segment(segment);
        }
    }
});

fn check_segment(segment: &Segment<'_>) {
    let Segment::Math(math) = segment else {
        return;
    };
    let parsed = syntax::parse(math.source);
    if !parsed.diagnostics.is_empty() {
        return;
    }
    check_linear(&parsed);
    for size_px in [14, 16] {
        check_boxes(&parsed, size_px);
    }
}

fn check_linear(parsed: &Parsed<'_>) {
    let _ = elegant_mermaid::math::cell::linear(&parsed.expression, Charset::Unicode);
    let _ = elegant_mermaid::math::cell::linear(&parsed.expression, Charset::Ascii);
}

fn check_boxes(parsed: &Parsed<'_>, size_px: i32) {
    let Ok(formula) = vector::layout(&parsed.expression, size_px) else {
        return;
    };
    for leaf in &formula.leaves {
        check_leaf(&formula, leaf);
    }
}

fn check_leaf(formula: &FormulaBox, leaf: &Leaf) {
    let Ok(rect) = leaf.box_rect() else {
        return;
    };
    let height = i64::from(formula.a) + i64::from(formula.d);
    assert!(rect.x >= 0);
    assert!(rect.y >= 0);
    assert!(rect.w >= 0);
    assert!(rect.h >= 0);
    assert!(i64::from(rect.x) + i64::from(rect.w) <= i64::from(formula.w));
    assert!(i64::from(rect.y) + i64::from(rect.h) <= height);
}
