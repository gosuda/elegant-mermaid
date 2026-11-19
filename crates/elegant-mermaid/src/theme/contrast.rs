use super::Colour;
fn linear_sum(c: Colour) -> i64 {
    let table = &crate::r#gen::lin16::LIN16;
    2126 * i64::from(table[usize::from(c.r)])
        + 7152 * i64::from(table[usize::from(c.g)])
        + 722 * i64::from(table[usize::from(c.b)])
}
pub fn luminance(c: Colour) -> i64 {
    linear_sum(c) / 10000
}
pub fn is_dark(c: Colour) -> bool {
    linear_sum(c) < 327675000
}
pub fn contrast(a: Colour, b: Colour, threshold10: i32) -> bool {
    let a = luminance(a);
    let b = luminance(b);
    10 * (a.max(b) + 3277) >= i64::from(threshold10) * (a.min(b) + 3277)
}
