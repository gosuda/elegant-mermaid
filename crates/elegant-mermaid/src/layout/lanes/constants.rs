//! Constants of the lanes layout family (`spec/layout/lanes.md`), read per profile from
//! `spec/data/layout-constants.json`.

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::layout::layered::LayoutError;
use crate::scene::Profile;

#[derive(Debug, Clone, Copy)]
pub(super) struct GitgraphConstants {
    pub commit_step: i64,
    pub lane_pitch: i64,
    pub rotation_extra: i64,
    pub label_offset: i64,
    pub commit_radius: i64,
    pub tag_offset: i64,
    pub tag_pad: i64,
    pub label_gap: i64,
    pub branch_pad_x: i64,
    pub branch_pad_y: i64,
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

pub(super) fn load_gitgraph(profile: Profile) -> Result<GitgraphConstants, LayoutError> {
    Ok(GitgraphConstants {
        commit_step: constant(profile, "gitgraph.commit_step")?,
        lane_pitch: constant(profile, "gitgraph.lane_pitch")?,
        rotation_extra: constant(profile, "gitgraph.label_rotation_extra")?,
        label_offset: constant(profile, "gitgraph.label_offset")?,
        commit_radius: constant(profile, "gitgraph.commit_radius")?,
        tag_offset: constant(profile, "gitgraph.tag_offset")?,
        tag_pad: constant(profile, "gitgraph.tag_pad")?,
        label_gap: constant(profile, "gitgraph.label_gap")?,
        branch_pad_x: constant(profile, "gitgraph.branch_pad_x")?,
        branch_pad_y: constant(profile, "gitgraph.branch_pad_y")?,
        corner_radius: constant(profile, "corner_radius")?,
        canvas_margin: constant(profile, "canvas_margin")?,
    })
}
