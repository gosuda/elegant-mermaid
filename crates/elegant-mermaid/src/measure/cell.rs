use super::{Cluster, segment};
use crate::r#gen::{graphemes::GRAPHEMES, unicodewidth::UNICODE_WIDTH};
use crate::geom::GeomError;

pub(crate) const UNICODE_WIDTH_WIDE: u8 = 2;
pub(crate) fn unicode_width_value(cp: u32) -> u8 {
    let index = UNICODE_WIDTH.partition_point(|row| row.hi < cp);
    UNICODE_WIDTH
        .get(index)
        .filter(|row| row.lo <= cp)
        .map_or(1, |row| row.value)
}
fn property(cp: u32) -> u8 {
    let index = GRAPHEMES.partition_point(|row| row.hi < cp);
    GRAPHEMES
        .get(index)
        .filter(|row| row.lo <= cp)
        .map_or(0, |row| row.prop)
}
pub fn cluster_width(cluster: Cluster<'_>) -> i32 {
    let Some(first) = cluster.first_scalar() else {
        return 0;
    };
    if matches!(property(u32::from(first)), 4 | 5) {
        return 0;
    }
    if unicode_width_value(u32::from(first)) == 2 {
        return 2;
    }
    let mut pictographic = false;
    for cp in cluster.text.chars().map(u32::from) {
        if cp == 0x20e3 || (cp == 0xfe0f && pictographic) {
            return 2;
        }
        pictographic |= property(cp) == 14;
    }
    1
}
pub fn cell_width(text: &str) -> Result<i32, GeomError> {
    segment(text).into_iter().try_fold(0i32, |sum, cluster| {
        sum.checked_add(cluster_width(cluster))
            .ok_or(GeomError::Overflow)
    })
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn measure_cell_width_cases() {
        for (text, width) in [
            ("abc", 3),
            ("日本", 4),
            ("☹️", 2),
            ("1️⃣", 2),
            ("\u{301}", 0),
            ("a\u{301}", 1),
            ("alpha beta-gamma 日本語テキスト", 31),
        ] {
            assert_eq!(cell_width(text), Ok(width));
        }
    }
}
