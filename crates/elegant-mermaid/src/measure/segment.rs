//! Extended grapheme clusters at Unicode 18.0.0, from the generated tables.
//!
//! One left-to-right pass keeps the little state that GB9c, GB11, GB12, and
//! GB13 need: the Indic conjunct suffix, the `Extended_Pictographic Extend*
//! ZWJ` suffix, and the regional indicator run length.

use crate::r#gen::graphemes::GRAPHEMES;
use crate::r#gen::incb::INCB;

const CR: u8 = 1;
const LF: u8 = 2;
const CONTROL: u8 = 3;
const EXTEND: u8 = 4;
const ZWJ: u8 = 5;
const REGIONAL_INDICATOR: u8 = 6;
const PREPEND: u8 = 7;
const SPACING_MARK: u8 = 8;
const L: u8 = 9;
const V: u8 = 10;
const T: u8 = 11;
const LV: u8 = 12;
const LVT: u8 = 13;
const EXTENDED_PICTOGRAPHIC: u8 = 14;

const INCB_LINKER: u8 = 1;
const INCB_CONSONANT: u8 = 2;
const INCB_EXTEND: u8 = 3;

/// One extended grapheme cluster: a slice of the segmented text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cluster<'a> {
    pub text: &'a str,
}

impl<'a> Cluster<'a> {
    /// The text of the cluster.
    pub fn as_str(self) -> &'a str {
        self.text
    }

    /// The first scalar of the cluster.
    pub fn first_scalar(self) -> Option<char> {
        self.text.chars().next()
    }

    /// The last scalar of the cluster.
    pub fn last_scalar(self) -> Option<char> {
        self.text.chars().next_back()
    }

    /// Whether this cluster is one space, U+0020.
    pub fn is_space(self) -> bool {
        self.text == " "
    }
}

/// The `Grapheme_Cluster_Break` value of a scalar; 0 for `Other`.
fn grapheme_prop(cp: u32) -> u8 {
    lookup(GRAPHEMES, cp, |row| (row.lo, row.hi, row.prop))
}

/// The `InCB` value of a scalar; 0 for none.
fn incb_prop(cp: u32) -> u8 {
    lookup(INCB, cp, |row| (row.lo, row.hi, row.prop))
}

fn lookup<T>(ranges: &[T], cp: u32, fields: impl Fn(&T) -> (u32, u32, u8)) -> u8 {
    let index = ranges.partition_point(|row| fields(row).1 < cp);
    match ranges.get(index) {
        Some(row) => {
            let (lo, _, value) = fields(row);
            if lo <= cp { value } else { 0 }
        }
        None => 0,
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct State {
    prev: u8,
    ri_run: u32,
    pictographic_extend_run: bool,
    pictographic_zwj: bool,
    linker_run: bool,
}

impl State {
    fn advance(&mut self, cp: u32) {
        let prop = grapheme_prop(cp);
        let incb = incb_prop(cp);
        let pictographic_zwj = prop == ZWJ && self.pictographic_extend_run;
        let pictographic_extend_run = match prop {
            EXTENDED_PICTOGRAPHIC => true,
            EXTEND => self.pictographic_extend_run,
            _ => false,
        };
        let ri_run = if prop == REGIONAL_INDICATOR {
            self.ri_run.saturating_add(1)
        } else {
            0
        };
        let linker_run = match incb {
            INCB_LINKER => true,
            INCB_EXTEND => self.linker_run,
            _ => false,
        };
        *self = State {
            prev: prop,
            ri_run,
            pictographic_extend_run,
            pictographic_zwj,
            linker_run,
        };
    }

    fn allows_break_before(&self, cp: u32) -> bool {
        let prop = grapheme_prop(cp);
        if self.prev == CR && prop == LF {
            return false;
        }
        if matches!(self.prev, CONTROL | CR | LF) {
            return true;
        }
        if matches!(prop, CONTROL | CR | LF) {
            return true;
        }
        if self.prev == L && matches!(prop, L | V | LV | LVT) {
            return false;
        }
        if matches!(self.prev, LV | V) && matches!(prop, V | T) {
            return false;
        }
        if matches!(self.prev, LVT | T) && prop == T {
            return false;
        }
        if matches!(prop, EXTEND | ZWJ) {
            return false;
        }
        if prop == SPACING_MARK {
            return false;
        }
        if self.prev == PREPEND {
            return false;
        }
        if self.linker_run && incb_prop(cp) == INCB_CONSONANT {
            return false;
        }
        if self.pictographic_zwj && prop == EXTENDED_PICTOGRAPHIC {
            return false;
        }
        if self.prev == REGIONAL_INDICATOR && prop == REGIONAL_INDICATOR {
            return self.ri_run.is_multiple_of(2);
        }
        true
    }
}

/// Splits `text` into extended grapheme clusters.
pub fn segment(text: &str) -> Vec<Cluster<'_>> {
    let mut clusters = Vec::new();
    let mut state = State::default();
    let mut start = 0usize;
    for (offset, ch) in text.char_indices() {
        let cp = u32::from(ch);
        if offset > 0 && state.allows_break_before(cp) {
            clusters.push(Cluster {
                text: &text[start..offset],
            });
            start = offset;
        }
        state.advance(cp);
    }
    if start < text.len() {
        clusters.push(Cluster {
            text: &text[start..],
        });
    }
    clusters
}

#[cfg(test)]
mod tests {
    use crate::geom::testing::Xorshift32;

    use super::{EXTENDED_PICTOGRAPHIC, grapheme_prop, incb_prop, segment};

    fn texts(input: &str) -> Vec<&str> {
        segment(input).into_iter().map(|c| c.text).collect()
    }

    fn prop(cp: u32) -> u8 {
        grapheme_prop(cp)
    }

    #[test]
    fn table_properties_are_the_ones_under_test() {
        assert_eq!(prop(0x0D), super::CR);
        assert_eq!(prop(0x0A), super::LF);
        assert_eq!(prop(0x01), super::CONTROL);
        assert_eq!(prop(0x0300), super::EXTEND);
        assert_eq!(prop(0x200D), super::ZWJ);
        assert_eq!(prop(0x1F1E6), super::REGIONAL_INDICATOR);
        assert_eq!(prop(0x0600), super::PREPEND);
        assert_eq!(prop(0x0903), super::SPACING_MARK);
    }

    #[test]
    fn table_hangul_and_context_properties() {
        assert_eq!(prop(0x1100), super::L);
        assert_eq!(prop(0x1161), super::V);
        assert_eq!(prop(0x11A8), super::T);
        assert_eq!(prop(0xAC00), super::LV);
        assert_eq!(prop(0xAC01), super::LVT);
        assert_eq!(prop(0x1F468), EXTENDED_PICTOGRAPHIC);
        assert_eq!(incb_prop(0x094D), super::INCB_LINKER);
        assert_eq!(incb_prop(0x0915), super::INCB_CONSONANT);
        assert_eq!(incb_prop(0x200D), super::INCB_EXTEND);
    }

    #[test]
    fn gb3_crlf_is_one_cluster() {
        assert_eq!(texts("\r\n"), vec!["\r\n"]);
        assert_eq!(texts("a\r\nb"), vec!["a", "\r\n", "b"]);
        assert_eq!(texts("\r\n\r\n"), vec!["\r\n", "\r\n"]);
    }

    #[test]
    fn gb4_control_breaks_after() {
        assert_eq!(texts("\u{0001}a"), vec!["\u{0001}", "a"]);
        assert_eq!(texts("a\u{0001}b"), vec!["a", "\u{0001}", "b"]);
        assert_eq!(texts("\u{000D}a"), vec!["\u{000D}", "a"]);
    }

    #[test]
    fn gb5_control_breaks_before() {
        assert_eq!(texts("a\u{0002}"), vec!["a", "\u{0002}"]);
        assert_eq!(texts("ab\u{007F}cd"), vec!["a", "b", "\u{007F}", "c", "d"]);
        assert_eq!(texts("\u{0001}\u{0002}"), vec!["\u{0001}", "\u{0002}"]);
    }

    #[test]
    fn gb6_hangul_l_joins_l_v_lv_lvt() {
        assert_eq!(texts("\u{1100}\u{1100}"), vec!["\u{1100}\u{1100}"]);
        assert_eq!(texts("\u{1100}\u{1161}"), vec!["\u{1100}\u{1161}"]);
        assert_eq!(texts("\u{1100}\u{AC00}"), vec!["\u{1100}\u{AC00}"]);
        assert_eq!(texts("\u{1100}A"), vec!["\u{1100}", "A"]);
    }

    #[test]
    fn gb7_hangul_lv_and_v_join_v_and_t() {
        assert_eq!(texts("\u{AC00}\u{1161}"), vec!["\u{AC00}\u{1161}"]);
        assert_eq!(texts("\u{1161}\u{11A8}"), vec!["\u{1161}\u{11A8}"]);
        assert_eq!(texts("\u{AC00}T"), vec!["\u{AC00}", "T"]);
    }

    #[test]
    fn gb8_hangul_lvt_and_t_join_t() {
        assert_eq!(texts("\u{AC01}\u{11A8}"), vec!["\u{AC01}\u{11A8}"]);
        assert_eq!(texts("\u{11A8}\u{11A8}"), vec!["\u{11A8}\u{11A8}"]);
        assert_eq!(texts("\u{AC01}\u{1161}"), vec!["\u{AC01}", "\u{1161}"]);
    }

    #[test]
    fn gb9_extend_and_zwj_join_the_previous_cluster() {
        assert_eq!(texts("a\u{0301}"), vec!["a\u{0301}"]);
        assert_eq!(texts("a\u{200D}"), vec!["a\u{200D}"]);
        assert_eq!(texts("a\u{0301}\u{0302}b"), vec!["a\u{0301}\u{0302}", "b"]);
    }

    #[test]
    fn gb9a_spacing_mark_joins_the_previous_cluster() {
        assert_eq!(texts("\u{0915}\u{0903}"), vec!["\u{0915}\u{0903}"]);
        assert_eq!(texts("a\u{0903}\u{0903}"), vec!["a\u{0903}\u{0903}"]);
        assert_eq!(texts("\u{0903}a"), vec!["\u{0903}", "a"]);
    }

    #[test]
    fn gb9b_prepend_joins_the_next_cluster() {
        assert_eq!(texts("\u{0600}a"), vec!["\u{0600}a"]);
        assert_eq!(texts("\u{0600}\u{0915}"), vec!["\u{0600}\u{0915}"]);
        assert_eq!(texts("\u{0600}\u{1100}"), vec!["\u{0600}\u{1100}"]);
    }

    #[test]
    fn gb9c_indic_conjunct_keeps_the_consonant() {
        assert_eq!(
            texts("\u{0915}\u{094D}\u{0937}"),
            vec!["\u{0915}\u{094D}\u{0937}"]
        );
        assert_eq!(
            texts("\u{0915}\u{094D}\u{200D}\u{0937}"),
            vec!["\u{0915}\u{094D}\u{200D}\u{0937}"]
        );
        assert_eq!(texts("\u{0915}\u{0937}"), vec!["\u{0915}", "\u{0937}"]);
        assert_eq!(texts("\u{0915}\u{094D}a"), vec!["\u{0915}\u{094D}", "a"]);
    }

    #[test]
    fn gb11_emoji_zwj_sequence_stays_together() {
        assert_eq!(
            texts("\u{1F468}\u{200D}\u{1F469}"),
            vec!["\u{1F468}\u{200D}\u{1F469}"]
        );
        assert_eq!(
            texts("\u{1F468}\u{1F3FB}\u{200D}\u{1F469}"),
            vec!["\u{1F468}\u{1F3FB}\u{200D}\u{1F469}"]
        );
        assert_eq!(
            texts("\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}"),
            vec!["\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}"]
        );
        assert_eq!(
            texts("\u{2764}\u{FE0F}\u{200D}\u{1F525}"),
            vec!["\u{2764}\u{FE0F}\u{200D}\u{1F525}"]
        );
    }

    #[test]
    fn gb12_and_gb13_pair_regional_indicators() {
        assert_eq!(texts("\u{1F1F0}\u{1F1F7}"), vec!["\u{1F1F0}\u{1F1F7}"]);
        assert_eq!(
            texts("\u{1F1F0}\u{1F1F7}\u{1F1EF}\u{1F1F5}"),
            vec!["\u{1F1F0}\u{1F1F7}", "\u{1F1EF}\u{1F1F5}"]
        );
        assert_eq!(
            texts("\u{1F1F0}\u{1F1F7}\u{1F1EF}"),
            vec!["\u{1F1F0}\u{1F1F7}", "\u{1F1EF}"]
        );
        assert_eq!(
            texts("a\u{1F1F0}\u{1F1F7}"),
            vec!["a", "\u{1F1F0}\u{1F1F7}"]
        );
    }

    #[test]
    fn gb999_other_scalars_break_apart() {
        assert_eq!(texts("abc"), vec!["a", "b", "c"]);
        assert_eq!(texts("ab"), vec!["a", "b"]);
        assert_eq!(texts("a b"), vec!["a", " ", "b"]);
    }

    #[test]
    fn segment_covers_the_input() {
        assert_eq!(segment(""), Vec::new());
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let length = (rng.next_u32() % 24) as usize;
            let mut text = String::new();
            for _ in 0..length {
                let cp = rng.next_u32() % 0x11_0000;
                match char::from_u32(cp) {
                    Some(ch) => text.push(ch),
                    None => continue,
                }
            }
            let joined: String = segment(&text).iter().map(|c| c.text).collect();
            assert_eq!(joined, text, "case={case}");
        }
    }

    #[test]
    fn segment_clusters_are_contiguous_and_non_empty() {
        for case in 0..200usize {
            let mut rng = Xorshift32::new(case);
            let length = (rng.next_u32() % 16) as usize;
            let mut text = String::new();
            for _ in 0..length {
                match char::from_u32(rng.next_u32() % 0x3000) {
                    Some(ch) => text.push(ch),
                    None => continue,
                }
            }
            let clusters = segment(&text);
            let mut offset = 0usize;
            for cluster in &clusters {
                assert!(!cluster.text.is_empty());
                assert!(text[offset..].starts_with(cluster.text));
                offset += cluster.text.len();
            }
            assert_eq!(offset, text.len());
            assert_eq!(clusters.iter().map(|c| c.text).collect::<String>(), text);
        }
    }
}
