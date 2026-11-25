//! The pie adapter and family entry (`spec/layout/charts.md`).
//!
//! [`from_pie`] authors the model-stage input: the dump skeleton as boxes and labels, the
//! typed config entries as options, and the legend flag and section values as region
//! sets, because the closed [`Input`] has no chart payload. The pie is drawn from the
//! vector scene only, so every profile gives the vector input. [`layout`] decodes that
//! input again and runs the chart family.

use std::collections::BTreeMap;

use crate::model::pie as mp;
use crate::scene::{Direction, DumpOptions, DumpValue, Profile, Scene, TextRole};

use super::chart::{self, PiePayload, PieSection};
use super::input::{Box as InputBox, Input, Label as InputLabel, RegionSet, Spacing};
use super::layered::LayoutError;

const KIND: &str = "pie";
const TAG_META: usize = 0;
const TAG_SECTION: usize = 1;
const SECTION_LEN: usize = 3;
const SHOW_DATA: usize = 1;

pub(crate) fn from_pie(
    model: &mp::Model,
    _profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.set_kind_config(config_of(&model.config));
    options.profile = Profile::Vector;
    let payload = payload(model);
    let skeleton = chart::pie_skeleton(&payload)?;
    let boxes = skeleton
        .boxes
        .into_iter()
        .map(|b| InputBox {
            icon: false,
            id: b.id,
            role: b.role,
            shape: String::new(),
            parent: b.parent,
            exclusive: b.exclusive,
            text: String::new(),
            direction: String::new(),
        })
        .collect();
    let labels = skeleton
        .labels
        .into_iter()
        .map(|l| InputLabel {
            id: l.id,
            owner: l.owner,
            role: TextRole::Label,
            text: l.text,
        })
        .collect();
    Ok(Input {
        kind: KIND,
        profile: Profile::Vector,
        direction: Direction::Tb,
        options,
        boxes,
        routes: Vec::new(),
        labels,
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: regions(&payload),
        spacing: Spacing::default(),
    })
}

fn config_of(config: &BTreeMap<String, i64>) -> BTreeMap<String, DumpValue> {
    config
        .iter()
        .map(|(key, value)| (key.clone(), DumpValue::Integer(*value)))
        .collect()
}

fn payload(model: &mp::Model) -> PiePayload {
    PiePayload {
        title: model.title.clone(),
        config: config_of(&model.config),
        show_data: model.show_data,
        sections: model
            .sections
            .iter()
            .map(|s| PieSection {
                label: s.label.clone(),
                value: s.value,
                index: s.index,
            })
            .collect(),
    }
}

fn regions(payload: &PiePayload) -> Vec<RegionSet> {
    let show_data = if payload.show_data { SHOW_DATA } else { 0 };
    let mut sets = vec![RegionSet {
        parent: 0,
        regions: vec![TAG_META, show_data],
    }];
    for s in &payload.sections {
        sets.push(RegionSet {
            parent: sets.len(),
            regions: vec![TAG_SECTION, usize::try_from(s.value).unwrap_or(0), s.index],
        });
    }
    sets
}

fn payload_of(input: &Input) -> PiePayload {
    let mut payload = PiePayload {
        config: input.options.config.clone(),
        ..PiePayload::default()
    };
    for set in &input.region_sets {
        decode_region(&mut payload, &set.regions);
    }
    for label in &input.labels {
        decode_label(&mut payload, &label.id, &label.text);
    }
    payload
}

fn decode_region(payload: &mut PiePayload, r: &[usize]) {
    match r.first() {
        Some(&TAG_META) if r.len() >= 2 => payload.show_data = r[1] == SHOW_DATA,
        Some(&TAG_SECTION) if r.len() >= SECTION_LEN => payload.sections.push(PieSection {
            label: String::new(),
            value: i64::try_from(r[1]).unwrap_or(0),
            index: r[2],
        }),
        _ => {}
    }
}

fn decode_label(payload: &mut PiePayload, id: &str, text: &str) {
    if id == "title" {
        text.clone_into(&mut payload.title);
        return;
    }
    let Some(index) = id
        .strip_prefix("legend.")
        .and_then(|rest| rest.parse::<usize>().ok())
    else {
        return;
    };
    let show_data = payload.show_data;
    let Some(section) = payload.sections.get_mut(index) else {
        return;
    };
    let suffix = format!(" [{}]", chart::scale::format_number(section.value));
    section.label = if show_data {
        text.strip_suffix(&suffix).unwrap_or(text).to_owned()
    } else {
        text.to_owned()
    };
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = Profile::Vector;
    chart::layout_pie(&payload_of(input), &options)
}

#[cfg(test)]
mod tests;
