//! The venn adapter and family entry (`spec/layout/charts.md`).
//!
//! [`from_venn`] authors the model-stage input: the dump skeleton as boxes and labels, the
//! typed config entries as options, and the set sizes, overlaps, and region members as
//! region sets, because the closed [`Input`] has no chart payload. [`layout`] decodes that
//! input again and runs the venn plan. The kind has no cell profile: both profiles give the
//! vector scene, and the braille raster draws its text.

use crate::model::venn as mv;
use crate::scene::{Direction, DumpOptions, Profile, Scene, TextRole};

use super::chart::venn::{self as plan, Payload, VennOverlap, VennRegion, VennSet};
use super::input::{Box as InputBox, Input, Label as InputLabel, RegionSet, Spacing};
use super::layered::LayoutError;

const KIND: &str = "venn";
const TAG_SET: usize = 0;
const TAG_OVERLAP: usize = 1;
const TAG_REGION: usize = 2;

pub(crate) fn from_venn(
    model: &mv::Model,
    _profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.set_kind_config(model.config.clone());
    options.profile = Profile::Vector;
    let payload = payload(model);
    let skeleton = plan::skeleton(&payload)?;
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

fn texts_of(model: &mv::Model, key: &[String]) -> Vec<String> {
    model
        .texts
        .iter()
        .filter(|t| t.sets == key)
        .map(|t| t.display.clone())
        .collect()
}

fn payload(model: &mv::Model) -> Payload {
    let sets = model.sets();
    let ids: Vec<&str> = sets.iter().map(|s| s.id.as_str()).collect();
    let mut out = Payload {
        title: model.title.clone(),
        config: model.config.clone(),
        ..Payload::default()
    };
    for set in &sets {
        out.sets.push(VennSet {
            label: set.display.clone(),
            size: set.size,
            texts: texts_of(model, std::slice::from_ref(&set.id)),
        });
    }
    let mut keys: Vec<&[String]> = Vec::new();
    let mut labels: Vec<&str> = Vec::new();
    for subset in model.subsets.iter().filter(|s| s.sets.len() >= 2) {
        let at = keys.iter().position(|k| *k == subset.sets.as_slice());
        let at = at.unwrap_or_else(|| {
            keys.push(&subset.sets);
            labels.push("");
            keys.len() - 1
        });
        labels[at] = &subset.display;
        overlap_of(&mut out, &ids, subset);
    }
    for (key, label) in keys.iter().zip(labels) {
        let region = VennRegion {
            sets: members(&ids, key),
            label: label.to_owned(),
            texts: texts_of(model, key),
        };
        if !region.label.is_empty() || !region.texts.is_empty() {
            out.regions.push(region);
        }
    }
    out
}

fn members(ids: &[&str], key: &[String]) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    for id in key {
        if let Some(i) = ids.iter().position(|x| x == id)
            && !out.contains(&i)
        {
            out.push(i);
        }
    }
    out.sort_unstable();
    out
}

fn overlap_of(out: &mut Payload, ids: &[&str], subset: &mv::Subset) {
    let [first, second] = subset.sets.as_slice() else {
        return;
    };
    if first == second {
        return;
    }
    let [a, b] = members(ids, &subset.sets)[..] else {
        return;
    };
    match out.overlaps.iter_mut().find(|o| o.a == a && o.b == b) {
        Some(existing) => existing.value = subset.size,
        None => out.overlaps.push(VennOverlap {
            a,
            b,
            value: subset.size,
        }),
    }
}

fn zigzag(value: i64) -> usize {
    let magnitude = usize::try_from(value.unsigned_abs()).unwrap_or(usize::MAX / 2);
    if value < 0 {
        2 * magnitude - 1
    } else {
        2 * magnitude
    }
}

fn unzigzag(code: usize) -> i64 {
    let half = i64::try_from(code / 2).unwrap_or(i64::MAX);
    if code % 2 == 1 { -half - 1 } else { half }
}

fn regions(chart: &Payload) -> Vec<RegionSet> {
    let mut sets = Vec::new();
    let mut push = |regions: Vec<usize>| {
        sets.push(RegionSet { parent: 0, regions });
    };
    for set in &chart.sets {
        push(vec![TAG_SET, zigzag(set.size)]);
    }
    for o in &chart.overlaps {
        push(vec![TAG_OVERLAP, o.a, o.b, zigzag(o.value)]);
    }
    for region in &chart.regions {
        let mut row = vec![TAG_REGION];
        row.extend(&region.sets);
        push(row);
    }
    sets
}

fn chart_of(input: &Input) -> Payload {
    let mut chart = Payload {
        config: input.options.config.clone(),
        ..Payload::default()
    };
    for set in &input.region_sets {
        decode_region(&mut chart, &set.regions);
    }
    for label in &input.labels {
        decode_label(&mut chart, &label.id, &label.text);
    }
    chart
}

fn decode_region(chart: &mut Payload, r: &[usize]) {
    match r {
        [TAG_SET, size] => chart.sets.push(VennSet {
            size: unzigzag(*size),
            ..VennSet::default()
        }),
        [TAG_OVERLAP, a, b, value] => {
            chart.overlaps.push(VennOverlap {
                a: *a,
                b: *b,
                value: unzigzag(*value),
            });
        }
        [TAG_REGION, rest @ ..] => chart.regions.push(VennRegion {
            sets: rest.to_vec(),
            ..VennRegion::default()
        }),
        _ => {}
    }
}

fn decode_label(chart: &mut Payload, id: &str, text: &str) {
    if id == "title" {
        text.clone_into(&mut chart.title);
        return;
    }
    if let Some((index, rest)) = owner_of(id, "set")
        && let Some(set) = chart.sets.get_mut(index)
    {
        decode_text(&mut set.label, &mut set.texts, rest, text);
    }
    if let Some((index, rest)) = owner_of(id, "region")
        && let Some(region) = chart.regions.get_mut(index)
    {
        decode_text(&mut region.label, &mut region.texts, rest, text);
    }
}

fn decode_text(label: &mut String, texts: &mut Vec<String>, rest: &str, text: &str) {
    if rest == ".label" {
        text.clone_into(label);
    } else if rest.starts_with(".t") {
        texts.push(text.to_owned());
    }
}

fn owner_of<'a>(id: &'a str, prefix: &str) -> Option<(usize, &'a str)> {
    let tail = id.strip_prefix(prefix)?;
    let digits = tail.len() - tail.trim_start_matches(|c: char| c.is_ascii_digit()).len();
    let (number, rest) = tail.split_at(digits);
    Some((number.parse().ok()?, rest))
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = Profile::Vector;
    plan::layout_venn(&chart_of(input), &options)
}

#[cfg(test)]
mod tests;
