//! The radar adapter and family entry (`spec/layout/charts.md`).
//!
//! [`from_radar`] authors the model-stage input: the dump skeleton as boxes and labels,
//! the typed config entries as options, and the option set and curve values as region
//! sets, because the closed [`Input`] has no chart payload. The radar is drawn from the
//! vector scene only, so every profile gives the vector input. [`layout`] decodes that
//! input again and runs the chart family.

use crate::model::chart::{Chart, Graticule, Kind, Radar, RadarCurve};
use crate::model::radar as mr;
use crate::scene::{Direction, DumpOptions, Profile, Scene, TextRole};

use super::chart;
use super::input::{Box as InputBox, Input, Label as InputLabel, RegionSet, Spacing};
use super::layered::LayoutError;

const KIND: &str = "radar";
const TAG_OPTIONS: usize = 0;
const TAG_CURVE: usize = 1;
const OPTIONS_LEN: usize = 7;
const CURVE_HEAD: usize = 2;

pub(crate) fn from_radar(
    model: &mr::Model,
    _profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.set_kind_config(model.config.clone());
    options.profile = Profile::Vector;
    let payload = payload(model);
    let skeleton = chart::model_skeleton(&payload)?;
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

fn payload(model: &mr::Model) -> Chart {
    let o = &model.options;
    let radar = Radar {
        axes: model.axes.iter().map(|axis| axis.label.clone()).collect(),
        curves: model
            .curves
            .iter()
            .map(|curve| RadarCurve {
                label: curve.label.clone(),
                values: curve.values.clone(),
            })
            .collect(),
        show_legend: o.show_legend,
        ticks: o.ticks,
        has_max: o.has_max,
        max: o.max,
        min: o.min,
        graticule: o.graticule,
    };
    Chart {
        kind: Kind::Radar,
        title: model.title.clone(),
        config: model.config.clone(),
        xy: None,
        radar: Some(radar),
        gantt: None,
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

fn regions(chart: &Chart) -> Vec<RegionSet> {
    let Some(radar) = &chart.radar else {
        return Vec::new();
    };
    let options = vec![
        TAG_OPTIONS,
        usize::from(radar.graticule == Graticule::Polygon),
        usize::from(radar.show_legend),
        usize::try_from(radar.ticks).unwrap_or(0),
        usize::from(radar.has_max),
        zigzag(radar.max),
        zigzag(radar.min),
    ];
    let mut sets = vec![RegionSet {
        parent: 0,
        regions: options,
    }];
    for curve in &radar.curves {
        let mut regions = vec![TAG_CURVE, curve.values.len()];
        regions.extend(curve.values.iter().map(|&v| zigzag(v)));
        sets.push(RegionSet {
            parent: sets.len(),
            regions,
        });
    }
    sets
}

fn chart_of(input: &Input) -> Chart {
    let mut radar = Radar::default();
    let mut chart = Chart {
        kind: Kind::Radar,
        title: String::new(),
        config: input.options.config.clone(),
        xy: None,
        radar: None,
        gantt: None,
    };
    for set in &input.region_sets {
        decode_region(&mut radar, &set.regions);
    }
    for label in &input.labels {
        decode_label(&mut chart, &mut radar, &label.id, &label.text);
    }
    chart.radar = Some(radar);
    chart
}

fn decode_region(radar: &mut Radar, r: &[usize]) {
    match r.first() {
        Some(&TAG_OPTIONS) if r.len() >= OPTIONS_LEN => {
            radar.graticule = if r[1] == 1 {
                Graticule::Polygon
            } else {
                Graticule::Circle
            };
            radar.show_legend = r[2] == 1;
            radar.ticks = i64::try_from(r[3]).unwrap_or(0);
            radar.has_max = r[4] == 1;
            radar.max = unzigzag(r[5]);
            radar.min = unzigzag(r[6]);
        }
        Some(&TAG_CURVE) if r.len() >= CURVE_HEAD => radar.curves.push(decode_curve(r)),
        _ => {}
    }
}

fn decode_curve(r: &[usize]) -> RadarCurve {
    RadarCurve {
        label: String::new(),
        values: r[CURVE_HEAD..]
            .iter()
            .take(r[1])
            .map(|&code| unzigzag(code))
            .collect(),
    }
}

fn decode_label(chart: &mut Chart, radar: &mut Radar, id: &str, text: &str) {
    if let Some(rest) = id.strip_prefix("legend.") {
        if let Some(curve) = rest
            .parse::<usize>()
            .ok()
            .and_then(|i| radar.curves.get_mut(i))
        {
            curve.label = text.to_owned();
        }
        return;
    }
    if id.starts_with("axis.") {
        radar.axes.push(text.to_owned());
        return;
    }
    if id == "title" {
        chart.title = text.to_owned();
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = Profile::Vector;
    chart::layout(&chart_of(input), &options)
}

#[cfg(test)]
mod tests;
