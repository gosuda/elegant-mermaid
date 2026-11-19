//! The constants of the cynefin plan: `layout-constants.json` rows plus the honoured
//! config keys `width`, `height`, `boundaryAmplitude`, and `seed`.

use crate::geom::floor_div;
use crate::measure;
use crate::scene::Profile;

use super::cynefin_spec::Cynefin;
use super::{LayoutError, constant};

const CELL_PX_WIDE: i64 = 8;
const CELL_PX_HIGH: i64 = 16;
const VECTOR_UNITS_PER_PX: i64 = 64;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Consts {
    pub width: i64,
    pub height: i64,
    pub confusion: i64,
    pub amplitude: i64,
    pub waves: i64,
    pub seed: u32,
    pub pad: i64,
    pub name_gap: i64,
    pub item_pad_x: i64,
    pub item_pad_y: i64,
    pub item_gap: i64,
    pub box_pad: i64,
    pub label_gap: i64,
    pub corner: i64,
    pub edge: i64,
}

pub(crate) fn canvas_side(profile: Profile, px: i64, cell_px: i64) -> i64 {
    if profile == Profile::Cell {
        measure::ceil_div(px, cell_px)
    } else {
        px * VECTOR_UNITS_PER_PX
    }
}

pub(crate) fn load_consts(profile: Profile, chart: &Cynefin) -> Result<Consts, LayoutError> {
    let get = |name: &str| constant(profile, name);
    let permille = get("cynefin.amplitude_permille")?;
    let mut consts = Consts {
        width: get("cynefin.width")?,
        height: get("cynefin.height")?,
        confusion: get("cynefin.confusion_permille")?,
        amplitude: 0,
        waves: get("cynefin.wave_segments")?,
        seed: 0,
        pad: get("cynefin.pad")?,
        name_gap: get("cynefin.name_gap")?,
        item_pad_x: get("cynefin.item_pad_x")?,
        item_pad_y: get("cynefin.item_pad_y")?,
        item_gap: get("cynefin.item_gap")?,
        box_pad: get("cynefin.box_pad")?,
        label_gap: get("cynefin.label_gap")?,
        corner: get("corner_radius")?,
        edge: i64::from(profile == Profile::Cell),
    };
    let mut seed = get("cynefin.default_seed")?;
    if let Some(n) = chart.integer("width") {
        consts.width = canvas_side(profile, n, CELL_PX_WIDE);
    }
    if let Some(n) = chart.integer("height") {
        consts.height = canvas_side(profile, n, CELL_PX_HIGH);
    }
    consts.amplitude = floor_div(consts.width * permille, 1000);
    if let Some(n) = chart.integer("boundaryAmplitude") {
        consts.amplitude = canvas_side(profile, n, CELL_PX_WIDE);
    }
    if let Some(n) = chart.integer("seed") {
        seed = n;
    }
    consts.seed = u32::try_from(seed).unwrap_or(0);
    Ok(consts)
}
