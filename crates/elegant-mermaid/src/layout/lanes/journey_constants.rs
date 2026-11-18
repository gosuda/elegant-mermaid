//! Constants of the journey planner, read per profile from `spec/data/layout-constants.json`.

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::layout::layered::LayoutError;
use crate::scene::Profile;

use super::journey::JourneyInput;

#[derive(Debug, Clone, Copy)]
pub(super) struct JourneyConstants {
    pub task_width: i64,
    pub task_height: i64,
    pub column_gap: i64,
    pub score_step: i64,
    pub score_min: i64,
    pub score_max: i64,
    pub band_height: i64,
    pub face_radius: i64,
    pub pad_x: i64,
    pub pad_y: i64,
    pub corner_radius: i64,
    pub canvas_margin: i64,
}

pub(super) fn constant(profile: Profile, name: &str) -> Result<i64, LayoutError> {
    let key = format!("{}.{name}", profile.as_str());
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| i64::from(row.value))
        .ok_or(LayoutError::Domain)
}

pub(super) fn load_journey(
    profile: Profile,
    input: &JourneyInput,
) -> Result<JourneyConstants, LayoutError> {
    let border = constant(profile, "node_border")?;
    let mut c = JourneyConstants {
        task_width: constant(profile, "journey.task_width")?,
        task_height: constant(profile, "journey.task_height")?,
        column_gap: constant(profile, "journey.column_gap")?,
        score_step: constant(profile, "journey.score_step")?,
        score_min: constant(profile, "journey.score_min")?,
        score_max: constant(profile, "journey.score_max")?,
        band_height: constant(profile, "journey.band_height")?,
        face_radius: constant(profile, "journey.face_radius")?,
        pad_x: constant(profile, "node_pad_x")? + border,
        pad_y: constant(profile, "node_pad_y")? + border,
        corner_radius: constant(profile, "corner_radius")?,
        canvas_margin: constant(profile, "canvas_margin")?,
    };
    for (value, into) in [
        (input.task_width, &mut c.task_width),
        (input.task_height, &mut c.task_height),
        (input.band_height, &mut c.band_height),
        (input.column_gap, &mut c.column_gap),
    ] {
        if value > 0 {
            *into = value;
        }
    }
    Ok(c)
}
