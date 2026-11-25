//! The xychart adapter and family entry (`spec/layout/charts.md`).
//!
//! [`from_xychart`] authors the model-stage input: the dump skeleton as boxes and labels,
//! the typed config entries as options, and the axes and points as region sets, because
//! the closed [`Input`] has no chart payload. [`layout`] decodes that input again and
//! runs the chart family.

use crate::model::chart::{Chart, Kind, Orientation, Plot, PlotKind, Point, XAxis, Xy, YAxis};
use crate::model::xychart as mx;
use crate::scene::{Direction, DumpOptions, DumpValue, Profile, Scene, TextRole};

use super::chart;
use super::input::{Box as InputBox, Input, Label as InputLabel, RegionSet, Spacing};
use super::layered::LayoutError;

const KIND: &str = "xychart";
const ORIENTATION_KEY: &str = "chartOrientation";
const HORIZONTAL: &str = "horizontal";
const TAG_AXES: usize = 0;
const TAG_PLOT: usize = 1;
const AXES_FIELDS: usize = 7;
const PLOT_HEADER: usize = 3;
const PRESENT: usize = 1;
const HAS_X: usize = 2;
const PER_POINT: usize = 4;

pub(crate) fn from_xychart(
    model: &mx::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.set_kind_config(model.config.clone());
    if model.orientation == Orientation::Horizontal {
        options.config.insert(
            ORIENTATION_KEY.to_owned(),
            DumpValue::String(HORIZONTAL.to_owned()),
        );
    }
    options.profile = profile;
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
        profile,
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

fn payload(model: &mx::Model) -> Chart {
    let xy = Xy {
        orientation: model.orientation,
        x_title: model.x.title.clone(),
        y_title: model.y.title.clone(),
        x_axis: XAxis {
            band: model.x.band,
            categories: model.x.categories.clone(),
            min: model.x.min,
            max: model.x.max,
        },
        y_axis: YAxis {
            min: model.y.min,
            max: model.y.max,
        },
        plots: model.plots.iter().map(plot_of).collect(),
    };
    Chart {
        kind: Kind::XyChart,
        title: model.title.clone(),
        config: model.config.clone(),
        xy: Some(xy),
        radar: None,
        gantt: None,
    }
}

fn plot_of(plot: &mx::Plot) -> Plot {
    Plot {
        kind: if plot.line {
            PlotKind::Line
        } else {
            PlotKind::Bar
        },
        title: plot.title.clone(),
        points: plot
            .points
            .iter()
            .map(|p| Point {
                present: p.present,
                slot: p.slot,
                has_x: p.has_x,
                x: p.x,
                value: p.y,
                label: p.label.clone(),
            })
            .collect(),
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
    let Some(xy) = &chart.xy else {
        return Vec::new();
    };
    let axes = vec![
        TAG_AXES,
        usize::from(xy.orientation == Orientation::Horizontal),
        usize::from(xy.x_axis.band),
        zigzag(xy.x_axis.min),
        zigzag(xy.x_axis.max),
        zigzag(xy.y_axis.min),
        zigzag(xy.y_axis.max),
    ];
    let mut sets = vec![RegionSet {
        parent: 0,
        regions: axes,
    }];
    for plot in &xy.plots {
        let mut regions = vec![
            TAG_PLOT,
            usize::from(plot.kind == PlotKind::Line),
            plot.points.len(),
        ];
        for p in &plot.points {
            let flags = (usize::from(p.present) * PRESENT) | (usize::from(p.has_x) * HAS_X);
            regions.extend([
                flags,
                p.slot.map_or(0, |slot| slot + 1),
                zigzag(p.x),
                zigzag(p.value),
            ]);
        }
        sets.push(RegionSet {
            parent: sets.len(),
            regions,
        });
    }
    sets
}

fn chart_of(input: &Input) -> Chart {
    let mut xy = Xy::default();
    let mut chart = Chart {
        kind: Kind::XyChart,
        title: String::new(),
        config: input.options.config.clone(),
        xy: None,
        radar: None,
        gantt: None,
    };
    for set in &input.region_sets {
        decode_region(&mut xy, &set.regions);
    }
    for label in &input.labels {
        decode_label(&mut chart, &mut xy, &label.id, &label.text);
    }
    chart.xy = Some(xy);
    chart
}

fn decode_region(xy: &mut Xy, r: &[usize]) {
    match r.first() {
        Some(&TAG_AXES) if r.len() >= AXES_FIELDS => {
            xy.orientation = if r[1] == 1 {
                Orientation::Horizontal
            } else {
                Orientation::Vertical
            };
            xy.x_axis = XAxis {
                band: r[2] == 1,
                categories: Vec::new(),
                min: unzigzag(r[3]),
                max: unzigzag(r[4]),
            };
            xy.y_axis = YAxis {
                min: unzigzag(r[5]),
                max: unzigzag(r[6]),
            };
        }
        Some(&TAG_PLOT) if r.len() >= PLOT_HEADER => xy.plots.push(decode_plot(r)),
        _ => {}
    }
}

fn decode_plot(r: &[usize]) -> Plot {
    let kind = if r[1] == 1 {
        PlotKind::Line
    } else {
        PlotKind::Bar
    };
    let points = r[PLOT_HEADER..]
        .as_chunks::<PER_POINT>()
        .0
        .iter()
        .take(r[2])
        .map(|c| Point {
            present: c[0] & PRESENT != 0,
            has_x: c[0] & HAS_X != 0,
            slot: c[1].checked_sub(1),
            x: unzigzag(c[2]),
            value: unzigzag(c[3]),
            label: String::new(),
        })
        .collect();
    Plot {
        kind,
        title: String::new(),
        points,
    }
}

fn decode_label(chart: &mut Chart, xy: &mut Xy, id: &str, text: &str) {
    if let Some(rest) = id.strip_prefix("legend.") {
        if let Some(plot) = rest.parse::<usize>().ok().and_then(|i| xy.plots.get_mut(i)) {
            plot.title = text.to_owned();
        }
        return;
    }
    if let Some(rest) = id.strip_prefix('p') {
        decode_point_label(xy, rest, text);
        return;
    }
    match id {
        "title" => chart.title = text.to_owned(),
        "x.title" => xy.x_title = text.to_owned(),
        "y.title" => xy.y_title = text.to_owned(),
        _ if xy.x_axis.band && id.starts_with("x.t") => xy.x_axis.categories.push(text.to_owned()),
        _ => {}
    }
}

fn decode_point_label(xy: &mut Xy, id: &str, text: &str) {
    let Some((plot, point)) = id.split_once(".l") else {
        return;
    };
    let (Ok(i), Ok(j)) = (plot.parse::<usize>(), point.parse::<usize>()) else {
        return;
    };
    if let Some(target) = xy.plots.get_mut(i).and_then(|p| p.points.get_mut(j)) {
        target.label = text.to_owned();
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    chart::layout(&chart_of(input), &options)
}

#[cfg(test)]
mod tests;
