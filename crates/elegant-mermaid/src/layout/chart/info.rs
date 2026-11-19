//! The info plan: one box and the version text (`spec/layout/charts.md`).

use crate::geom::{Size, floor_div};
use crate::measure::Role;
use crate::scene::{
    Align, BoxRole, Direction, Dump, DumpOptions, Group, GroupRole, Profile, Scene, SceneBox,
    SceneLabel,
};

use super::cynefin_text::{TextSpec, bottom, right};
use super::{Area, LayoutError, ZERO_RECT, constant, to_i32};

const KIND: &str = "info";
const BOX_ID: &str = "info";
const LABEL_ID: &str = "version";
const VECTOR_UNITS_PER_PX: i64 = 64;

#[derive(Debug, Clone)]
pub struct Info {
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct InfoFrame {
    pub info_box: SceneBox,
    pub label: SceneLabel,
}

pub fn info_skeleton(info: &Info) -> InfoFrame {
    InfoFrame {
        info_box: SceneBox {
            id: BOX_ID.to_owned(),
            role: BoxRole::Node,
            rect: ZERO_RECT,
            parent: String::new(),
            exclusive: false,
        },
        label: SceneLabel {
            id: LABEL_ID.to_owned(),
            owner: BOX_ID.to_owned(),
            text: info.text.clone(),
            rect: ZERO_RECT,
            lines: Vec::new(),
        },
    }
}

struct Consts {
    width: i64,
    height: i64,
    text_x: i64,
    text_y: i64,
    font_size: i64,
}

fn load_consts(profile: Profile) -> Result<Consts, LayoutError> {
    Ok(Consts {
        width: constant(profile, "info.width")?,
        height: constant(profile, "info.height")?,
        text_x: constant(profile, "info.text_x")?,
        text_y: constant(profile, "info.text_y")?,
        font_size: constant(profile, "info.font_size")?,
    })
}

pub fn layout_info(info: &Info, options: &DumpOptions) -> Result<(Scene, bool), LayoutError> {
    let c = load_consts(options.profile)?;
    let size = i32::try_from(c.font_size / VECTOR_UNITS_PER_PX).unwrap_or(Role::Title.size_px());
    let spec = TextSpec {
        profile: options.profile,
        role: Role::Title,
        size,
    };
    let text = spec.measure(&info.text)?;
    let mut at = Area::new(
        c.text_x - floor_div(text.w, 2),
        c.text_y - floor_div(text.h, 2),
        text.w,
        text.h,
    );
    at.x = at.x.max(0);
    at.y = at.y.max(0);
    let canvas = Area::new(0, 0, c.width.max(right(at)), c.height.max(bottom(at)));
    let mut frame = info_skeleton(info);
    frame.info_box.rect = canvas.to_rect()?;
    frame.label.rect = at.to_rect()?;
    frame.label.lines.clone_from(&text.plain);
    let item = spec.item(&text, at, Align::Middle)?;
    let mut dump_options = options.clone();
    dump_options.direction = Direction::Tb;
    let mut dump = Dump::new(KIND, dump_options);
    dump.boxes = vec![frame.info_box];
    dump.labels = vec![frame.label];
    let size = Size {
        w: to_i32(canvas.w)?,
        h: to_i32(canvas.h)?,
    };
    let groups = vec![Group::new(GroupRole::Node, BOX_ID).with_items(vec![item])];
    Ok((Scene::new(size, dump, groups), false))
}
