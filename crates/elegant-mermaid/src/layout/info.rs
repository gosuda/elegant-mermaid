//! The info adapter and family entry (`spec/layout/charts.md`): one box and the version
//! label.

use crate::model::info as mi;
use crate::scene::{Direction, DumpOptions, Profile, Scene, TextRole};

use super::chart::{Info, info_skeleton, layout_info};
use super::input::{Box as InputBox, Input, Label as InputLabel, Spacing};
use super::layered::LayoutError;

const KIND: &str = "info";
const VERSION_LABEL: &str = "version";

pub(crate) fn from_info(
    model: &mi::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.config.clear();
    options.profile = profile;
    let frame = info_skeleton(&Info {
        text: format!("v{}", model.version),
    });
    Ok(Input {
        kind: KIND,
        profile,
        direction: Direction::Tb,
        options,
        boxes: vec![InputBox {
            icon: false,
            id: frame.info_box.id,
            role: frame.info_box.role,
            shape: String::new(),
            parent: frame.info_box.parent,
            exclusive: frame.info_box.exclusive,
            text: String::new(),
            direction: String::new(),
        }],
        routes: Vec::new(),
        labels: vec![InputLabel {
            id: frame.label.id,
            owner: frame.label.owner,
            role: TextRole::Label,
            text: frame.label.text,
        }],
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    })
}

fn info_of(input: &Input) -> Info {
    let text = input
        .labels
        .iter()
        .find(|l| l.id == VERSION_LABEL)
        .map_or_else(String::new, |l| l.text.clone());
    Info { text }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    layout_info(&info_of(input), &options)
}

#[cfg(test)]
mod tests;
