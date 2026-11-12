//! Vector widths from the generated Inter advance tables.
//!
//! A width is `ceil_div(sum * size_px * 64, upem)` in units of 1/64 px, where
//! `sum` is the sum of the advances of the codepoints of the string in font
//! units. A codepoint without a table row falls back to one em when it is
//! wide or emoji-presentation, and to 0.6 em otherwise.

use crate::r#gen::advances::ADVANCES;
use crate::r#gen::advancesupem::ADVANCES_UPEM;
use crate::geom::{GeomError, floor_div};

use super::ceil_div;
use super::cell::{UNICODE_WIDTH_WIDE, cell_width, unicode_width_value};
use super::narrow_i32;
use super::segment::Cluster;

const DEFAULT_UPEM: i64 = 2048;
const FONT_FAMILY_NUMERATOR: i64 = 108;
const FONT_FAMILY_DENOMINATOR: i64 = 100;
const UNITS_PER_PX: i64 = 64;

/// A text role, which fixes the size, line height, and weight of its text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Body,
    Label,
    Title,
}

impl Role {
    /// The size of the role in px.
    pub fn size_px(self) -> i32 {
        match self {
            Role::Body | Role::Label => 14,
            Role::Title => 16,
        }
    }

    /// The line height of the role in px.
    pub fn line_height_px(self) -> i32 {
        match self {
            Role::Body | Role::Label => 20,
            Role::Title => 24,
        }
    }

    /// The font weight of the role.
    pub fn weight(self) -> Weight {
        match self {
            Role::Body => Weight::Regular,
            Role::Label | Role::Title => Weight::Semibold,
        }
    }
}

/// A font weight that the advance tables hold.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Weight {
    Regular,
    Semibold,
}

impl Weight {
    pub(crate) fn index(self) -> u8 {
        match self {
            Weight::Regular => 0,
            Weight::Semibold => 1,
        }
    }
}

/// The units per em of the font that holds one weight.
pub fn upem(weight: Weight) -> i64 {
    let index = usize::from(weight.index());
    ADVANCES_UPEM
        .get(index)
        .map_or(DEFAULT_UPEM, |value| i64::from(*value))
}

/// The advance of one codepoint in font units.
pub fn advance_units(weight: Weight, cp: u32) -> i64 {
    match lookup_advance(weight, cp) {
        Some(units) => i64::from(units),
        None => fallback_advance(weight, cp),
    }
}

fn lookup_advance(weight: Weight, cp: u32) -> Option<u16> {
    let key = (weight.index(), cp);
    let index = ADVANCES.partition_point(|row| (row.weight, row.cp) < key);
    match ADVANCES.get(index) {
        Some(row) if (row.weight, row.cp) == key => Some(row.units),
        _ => None,
    }
}

fn fallback_advance(weight: Weight, cp: u32) -> i64 {
    let em = upem(weight);
    if unicode_width_value(cp) == UNICODE_WIDTH_WIDE {
        em
    } else {
        floor_div(6 * em + 5, 10)
    }
}

/// The sum of the advances of the codepoints of `text`, in font units.
pub fn advance_sum(text: &str, weight: Weight) -> Result<i64, GeomError> {
    let mut total = 0i64;
    for ch in text.chars() {
        let advance = advance_units(weight, u32::from(ch));
        total = total.checked_add(advance).ok_or(GeomError::Overflow)?;
    }
    Ok(total)
}

/// The vector width of `text` at `size_px`, in units of 1/64 px.
pub fn vector_width(text: &str, size_px: i32, weight: Weight) -> Result<i32, GeomError> {
    let units = advance_sum(text, weight)?;
    narrow_i32(scaled_width(units, size_px, weight)?)
}

pub(crate) fn scaled_width(units: i64, size_px: i32, weight: Weight) -> Result<i64, GeomError> {
    if size_px < 0 {
        return Err(GeomError::Domain);
    }
    let numerator = units
        .checked_mul(i64::from(size_px))
        .and_then(|value| value.checked_mul(UNITS_PER_PX))
        .ok_or(GeomError::Overflow)?;
    Ok(ceil_div(numerator, upem(weight)))
}

/// The `fontFamily` factor: `floor_div(width * 108, 100)`.
pub fn apply_font_family_factor(width: i32) -> Result<i32, GeomError> {
    narrow_i32(floor_div(
        i64::from(width) * FONT_FAMILY_NUMERATOR,
        FONT_FAMILY_DENOMINATOR,
    ))
}

/// The profile and the text settings that a measurement uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Metric {
    Vector {
        size_px: i32,
        weight: Weight,
        font_family: bool,
    },
    Cell,
}

impl Metric {
    /// The metric of one role in the vector profile.
    pub fn for_role(role: Role) -> Self {
        Metric::Vector {
            size_px: role.size_px(),
            weight: role.weight(),
            font_family: false,
        }
    }

    /// The cell profile.
    pub fn cell() -> Self {
        Metric::Cell
    }

    /// The same metric with the `fontFamily` factor applied to vector widths.
    pub fn with_font_family(self) -> Self {
        match self {
            Metric::Vector {
                size_px, weight, ..
            } => Metric::Vector {
                size_px,
                weight,
                font_family: true,
            },
            Metric::Cell => Metric::Cell,
        }
    }

    /// Whether the metric measures character cells.
    pub fn is_cell(self) -> bool {
        matches!(self, Metric::Cell)
    }

    /// The width of `text` in the units of the metric.
    pub fn width(self, text: &str) -> Result<i32, GeomError> {
        let units = self.text_units(text)?;
        self.width_from_units(units)
    }

    /// The number of profile units that the codepoints of `text` accumulate
    /// before the size scaling: advances in font units for the vector
    /// profile, cell widths for the cell profile.
    pub(crate) fn text_units(self, text: &str) -> Result<i64, GeomError> {
        match self {
            Metric::Cell => Ok(i64::from(cell_width(text)?)),
            Metric::Vector { weight, .. } => advance_sum(text, weight),
        }
    }

    /// The units that one grapheme cluster accumulates.
    pub(crate) fn unit_width(self, cluster: &Cluster<'_>) -> Result<i64, GeomError> {
        self.text_units(cluster.text)
    }

    /// The width in profile units of an accumulated unit count.
    pub(crate) fn width_from_units(self, units: i64) -> Result<i32, GeomError> {
        match self {
            Metric::Cell => narrow_i32(units),
            Metric::Vector {
                size_px,
                weight,
                font_family,
            } => {
                let width = narrow_i32(scaled_width(units, size_px, weight)?)?;
                if font_family {
                    apply_font_family_factor(width)
                } else {
                    Ok(width)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::r#gen::advances::ADVANCES;
    use crate::geom::GeomError;
    use crate::geom::testing::Xorshift32;

    use super::{
        Metric, Role, Weight, advance_sum, advance_units, apply_font_family_factor, upem,
        vector_width,
    };

    fn width_of(result: Result<i32, GeomError>, failures: &mut usize) -> i32 {
        match result {
            Ok(width) => width,
            Err(_) => {
                *failures += 1;
                0
            }
        }
    }

    fn naive_width(text: &str, size_px: i32, weight: Weight) -> i32 {
        let index = weight.index();
        let upem = i64::from(ADVANCES_UPEM_ORACLE[usize::from(index)]);
        let mut sum = 0i64;
        for ch in text.chars() {
            let cp = u32::from(ch);
            let mut advance = None;
            for row in ADVANCES {
                if row.weight == index && row.cp == cp {
                    advance = Some(i64::from(row.units));
                    break;
                }
            }
            sum += advance.unwrap_or(0);
        }
        let numerator = sum * i64::from(size_px) * 64;
        let quotient = if numerator % upem == 0 {
            numerator / upem
        } else if numerator < 0 {
            numerator / upem - 1
        } else {
            numerator / upem + 1
        };
        i32::try_from(quotient).unwrap_or(0)
    }

    const ADVANCES_UPEM_ORACLE: [i32; 2] = [2048, 2048];

    #[test]
    fn roles_fix_size_line_height_and_weight() {
        assert_eq!(Role::Body.size_px(), 14);
        assert_eq!(Role::Body.line_height_px(), 20);
        assert_eq!(Role::Body.weight(), Weight::Regular);
        assert_eq!(Role::Label.size_px(), 14);
        assert_eq!(Role::Label.line_height_px(), 20);
        assert_eq!(Role::Label.weight(), Weight::Semibold);
        assert_eq!(Role::Title.size_px(), 16);
        assert_eq!(Role::Title.line_height_px(), 24);
        assert_eq!(Role::Title.weight(), Weight::Semibold);
    }

    #[test]
    fn upem_reads_both_weights() {
        assert_eq!(upem(Weight::Regular), 2048);
        assert_eq!(upem(Weight::Semibold), 2048);
    }

    #[test]
    fn advances_match_hand_values() {
        assert_eq!(advance_units(Weight::Regular, u32::from('A')), 1413);
        assert_eq!(advance_units(Weight::Semibold, u32::from('A')), 1490);
        assert_eq!(advance_units(Weight::Regular, u32::from(' ')), 576);
        assert_eq!(advance_units(Weight::Regular, 0), 1200);
    }

    #[test]
    fn fallback_advance_is_one_em_for_wide_and_zero_point_six_em_otherwise() {
        assert_eq!(advance_units(Weight::Regular, 0x65E5), 2048);
        assert_eq!(advance_units(Weight::Regular, 0x1F600), 2048);
        assert_eq!(advance_units(Weight::Regular, 0x0378), 1229);
        assert_eq!(advance_units(Weight::Semibold, 0x0378), 1229);
    }

    #[test]
    fn vector_width_matches_hand_values() {
        let mut failures = 0usize;
        assert_eq!(
            width_of(vector_width("A", 14, Weight::Regular), &mut failures),
            619
        );
        assert_eq!(
            width_of(vector_width("A", 16, Weight::Semibold), &mut failures),
            745
        );
        assert_eq!(
            width_of(vector_width("AB", 14, Weight::Regular), &mut failures),
            1205
        );
        assert_eq!(
            width_of(vector_width("", 14, Weight::Regular), &mut failures),
            0
        );
        assert_eq!(
            width_of(vector_width("\u{65E5}", 14, Weight::Regular), &mut failures),
            896
        );
        assert_eq!(
            width_of(vector_width("\u{0378}", 14, Weight::Regular), &mut failures),
            538
        );
        assert_eq!(failures, 0);
    }

    #[test]
    fn vector_width_equals_naive_sum_for_ascii() {
        let mut failures = 0usize;
        for case in 0..50usize {
            let mut rng = Xorshift32::new(case);
            let length = 1 + (rng.next_u32() % 12) as usize;
            let mut text = String::new();
            for _ in 0..length {
                let code = 32 + (rng.next_u32() % 95);
                match char::from_u32(code) {
                    Some(ch) => text.push(ch),
                    None => failures += 1,
                }
            }
            let weight = if case % 2 == 0 {
                Weight::Regular
            } else {
                Weight::Semibold
            };
            let size_px = match case % 3 {
                0 => 14,
                1 => 16,
                _ => 20,
            };
            let got = width_of(vector_width(&text, size_px, weight), &mut failures);
            assert_eq!(got, naive_width(&text, size_px, weight), "text={text:?}");
        }
        assert_eq!(failures, 0);
    }

    #[test]
    fn advance_sum_adds_in_string_order() {
        let mut failures = 0usize;
        match advance_sum("AB", Weight::Regular) {
            Ok(total) => assert_eq!(total, 2753),
            Err(_) => failures += 1,
        }
        match advance_sum("", Weight::Regular) {
            Ok(total) => assert_eq!(total, 0),
            Err(_) => failures += 1,
        }
        assert_eq!(failures, 0);
    }

    #[test]
    fn font_family_factor_widens_by_eight_percent() {
        let mut failures = 0usize;
        assert_eq!(width_of(apply_font_family_factor(619), &mut failures), 668);
        assert_eq!(width_of(apply_font_family_factor(0), &mut failures), 0);
        assert_eq!(width_of(apply_font_family_factor(100), &mut failures), 108);
        assert_eq!(failures, 0);
        let plain = Metric::for_role(Role::Label);
        let widened = plain.with_font_family();
        assert_eq!(
            width_of(widened.width("A"), &mut failures),
            width_of(plain.width("A"), &mut failures) * 108 / 100
        );
        assert_eq!(failures, 0);
    }

    #[test]
    fn metric_width_agrees_with_its_unit_prefix() {
        let mut failures = 0usize;
        let metric = Metric::for_role(Role::Label);
        let text = "abc";
        let units = match metric.text_units(text) {
            Ok(value) => value,
            Err(_) => {
                failures += 1;
                0
            }
        };
        assert_eq!(
            width_of(metric.width(text), &mut failures),
            width_of(metric.width_from_units(units), &mut failures)
        );
        assert!(!metric.is_cell());
        assert!(Metric::cell().is_cell());
        assert_eq!(failures, 0);
    }
}
