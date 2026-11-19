//! The chart family (`spec/layout/charts.md`): scales, ticks, and the xychart layout.
//!
//! [`layout`] reads a [`Chart`] and returns the scene with its capped flag. The
//! integer scale rules live in [`scale`]; the xychart plan is split by phase.

mod cynefin;
mod cynefin_consts;
mod cynefin_route;
mod cynefin_scene;
mod cynefin_shape;
mod cynefin_spec;
mod cynefin_stack;
mod cynefin_text;
mod gantt;
mod gantt_place;
mod gantt_scene;
#[cfg(test)]
mod gantt_tests;
mod gantt_ticks;
mod info;
mod pie;
mod pie_scene;
mod quadrant;
mod quadrant_arrange;
mod quadrant_place;
mod quadrant_scene;
mod quadrant_spec;
mod radar;
mod radar_place;
mod radar_scene;
pub(crate) mod sankey;
pub mod scale;
mod treemap;
mod treemap_squarify;
mod treemap_text;
pub(crate) mod venn;
mod wardley;
mod wardley_codec;
mod wardley_items;
mod wardley_layout;
mod wardley_place;
mod wardley_plan;
mod wardley_scene;
mod xy;
mod xy_arrange;
mod xy_axis;
mod xy_place;
mod xy_scene;
mod xy_spec;

#[cfg(test)]
mod quadrant_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod wardley_tests;

use crate::geom::{GeomError, Rect};
use crate::model::chart::{Chart, Kind};
use crate::scene::{DumpOptions, Profile, Scene, SceneBox, SceneLabel};

use super::layered::LayoutError;

pub use cynefin::layout_cynefin;
pub use cynefin_spec::{Cynefin, CynefinDomain, CynefinTransition, Frame, cynefin_skeleton};
pub use info::{Info, InfoFrame, info_skeleton, layout_info};
pub(crate) use pie::{PiePayload, PieSection, layout_pie, pie_skeleton};
pub(crate) use quadrant::layout_quadrant;
pub(crate) use quadrant_spec::{
    NO_POINT_RADIUS, Quadrant, QuadrantPoint, skeleton as quadrant_skeleton,
};
pub use treemap::{Treemap, TreemapNode, layout_treemap, treemap_normalize, treemap_skeleton};
pub use wardley::{
    Wardley, WardleyAnnotation, WardleyFlow, WardleyForce, WardleyLink, WardleyNode, WardleyNote,
    WardleyPipeline, WardleyPoint, WardleySkeleton, WardleyStrategy, WardleyTrend,
};
pub use wardley_codec::{WardleyDump, decode_wardley};
pub use wardley_layout::layout_wardley;
pub use xy_spec::series_title;

pub(crate) const ZERO_RECT: Rect = Rect {
    x: 0,
    y: 0,
    w: 0,
    h: 0,
};

pub struct Skeleton {
    pub boxes: Vec<SceneBox>,
    pub labels: Vec<SceneLabel>,
}

pub fn layout(chart: &Chart, options: &DumpOptions) -> Result<(Scene, bool), LayoutError> {
    match chart.kind {
        Kind::XyChart => xy::layout_xy(chart, options),
        Kind::Radar => radar::layout_radar(chart, options),
        Kind::Gantt => gantt::layout_gantt(chart, options),
    }
}

pub fn model_skeleton(chart: &Chart) -> Result<Skeleton, LayoutError> {
    match chart.kind {
        Kind::XyChart => xy::skeleton(chart),
        Kind::Radar => radar::skeleton(chart),
        Kind::Gantt => gantt::skeleton(chart),
    }
}

pub(crate) fn constant(profile: Profile, name: &str) -> Result<i64, LayoutError> {
    let key = format!("{}.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| i64::from(row.value))
        .ok_or(GeomError::Domain)
}

pub(crate) fn to_i32(value: i64) -> Result<i32, LayoutError> {
    let limit = i64::from(i32::MAX);
    if (-limit..=limit).contains(&value) {
        i32::try_from(value).map_err(|_| GeomError::Overflow)
    } else {
        Err(GeomError::Overflow)
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Area {
    pub x: i64,
    pub y: i64,
    pub w: i64,
    pub h: i64,
}

impl Area {
    pub(crate) fn new(x: i64, y: i64, w: i64, h: i64) -> Area {
        Area { x, y, w, h }
    }

    pub(crate) fn to_rect(self) -> Result<Rect, LayoutError> {
        Ok(Rect {
            x: to_i32(self.x)?,
            y: to_i32(self.y)?,
            w: to_i32(self.w)?,
            h: to_i32(self.h)?,
        })
    }
}
