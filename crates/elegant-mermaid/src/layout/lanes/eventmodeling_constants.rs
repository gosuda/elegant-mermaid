//! Constants of the eventmodeling planner (`spec/layout/lanes.md`, Event modeling), read
//! per profile from `spec/data/layout-constants.json`.

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::layout::layered::LayoutError;
use crate::scene::Profile;

#[derive(Debug, Clone, Copy)]
pub(super) struct EventConstants {
    pub lane_min_height: i64,
    pub lane_padding: i64,
    pub lane_gap: i64,
    pub box_padding: i64,
    pub box_overlap: i64,
    pub box_min_width: i64,
    pub box_max_width: i64,
    pub box_min_height: i64,
    pub box_max_height: i64,
    pub content_start_x: i64,
    pub line_height: i64,
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

pub(super) fn load_event_constants(profile: Profile) -> Result<EventConstants, LayoutError> {
    Ok(EventConstants {
        lane_min_height: constant(profile, "eventmodeling.swimlane_min_height")?,
        lane_padding: constant(profile, "eventmodeling.swimlane_padding")?,
        lane_gap: constant(profile, "eventmodeling.swimlane_gap")?,
        box_padding: constant(profile, "eventmodeling.box_padding")?,
        box_overlap: constant(profile, "eventmodeling.box_overlap")?,
        box_min_width: constant(profile, "eventmodeling.box_min_width")?,
        box_max_width: constant(profile, "eventmodeling.box_max_width")?,
        box_min_height: constant(profile, "eventmodeling.box_min_height")?,
        box_max_height: constant(profile, "eventmodeling.box_max_height")?,
        content_start_x: constant(profile, "eventmodeling.content_start_x")?,
        line_height: constant(profile, "line_h")?,
        corner_radius: constant(profile, "corner_radius")?,
        canvas_margin: constant(profile, "canvas_margin")?,
    })
}

impl EventConstants {
    pub(super) const fn label_inset(&self) -> i64 {
        2 * self.lane_padding
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct EventWraps {
    pub lane: i32,
    pub frame: i32,
}

pub(crate) fn event_modeling_wraps(profile: Profile) -> Result<EventWraps, LayoutError> {
    let c = load_event_constants(profile)?;
    let lane = c.content_start_x - 2 * c.label_inset();
    Ok(EventWraps {
        lane: i32::try_from(lane).map_err(|_| LayoutError::Overflow)?,
        frame: i32::try_from(c.box_max_width).map_err(|_| LayoutError::Overflow)?,
    })
}
