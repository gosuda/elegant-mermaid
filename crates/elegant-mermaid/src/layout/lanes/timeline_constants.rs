//! Constants of the timeline planner, read per profile from `spec/data/layout-constants.json`.

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::layout::layered::LayoutError;
use crate::scene::Profile;

#[derive(Debug, Clone, Copy)]
pub(super) struct TimelineConstants {
    pub card_width: i64,
    pub column_gap: i64,
    pub event_gap: i64,
    pub section_gap: i64,
    pub card_padding: i64,
    pub left_margin: i64,
    pub corner_radius: i64,
    pub canvas_margin: i64,
}

fn constant(profile: Profile, name: &str) -> Result<i64, LayoutError> {
    let key = format!("{}.{name}", profile.as_str());
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| i64::from(row.value))
        .ok_or(LayoutError::Domain)
}

pub(super) fn load_timeline(profile: Profile) -> Result<TimelineConstants, LayoutError> {
    Ok(TimelineConstants {
        card_width: constant(profile, "timeline.card_width")?,
        column_gap: constant(profile, "timeline.column_gap")?,
        event_gap: constant(profile, "timeline.event_gap")?,
        section_gap: constant(profile, "timeline.section_gap")?,
        card_padding: constant(profile, "timeline.card_padding")?,
        left_margin: constant(profile, "timeline.left_margin")?,
        corner_radius: constant(profile, "corner_radius")?,
        canvas_margin: constant(profile, "canvas_margin")?,
    })
}
