//! The gantt adapter and family entry (`spec/layout/charts.md`).
//!
//! [`from_gantt`] authors the model-stage input: the dump skeleton as boxes and labels,
//! the resolved settings as options, and the task dates and flags as region sets,
//! because the closed [`Input`] has no chart payload. [`layout`] decodes that input again
//! and runs the chart family.

use std::collections::BTreeMap;

use crate::model::chart::{Chart, Gantt, GanttRow, GanttRowKind, GanttTask, Kind};
use crate::model::gantt as mg;
use crate::scene::{Direction, DumpOptions, DumpValue, Profile, Scene, TextRole};

use super::chart;
use super::input::{Box as InputBox, Input, Label as InputLabel, RegionSet, Spacing};
use super::layered::LayoutError;

const KIND: &str = "gantt";
const MILESTONE: usize = 1;
const VERT: usize = 2;
const CRIT: usize = 4;
const ACTIVE: usize = 8;
const DONE: usize = 16;
const FIELDS: usize = 5;
const INTEGER_KEYS: [&str; 5] = [
    "barGap",
    "barHeight",
    "leftPadding",
    "rightPadding",
    "topPadding",
];

pub(crate) fn from_gantt(
    model: &mg::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    let payload = payload(model);
    options.profile = profile;
    options.config = config_of(&payload);
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

fn task_of(task: &mg::Task) -> GanttTask {
    GanttTask {
        label: task.label.clone(),
        section: task.section,
        start: task.start_seconds,
        end: task.end_seconds,
        render_end: if task.has_render_end {
            task.render_end
        } else {
            task.end_seconds
        },
        milestone: task.milestone,
        vert: task.vert,
        crit: task.crit,
        active: task.active,
        done: task.done,
    }
}

fn row_of(row: &mg::Row) -> GanttRow {
    GanttRow {
        kind: match row.kind {
            mg::RowKind::Section => GanttRowKind::Section,
            mg::RowKind::Task => GanttRowKind::Task,
        },
        index: row.index,
    }
}

fn payload(model: &mg::Model) -> Chart {
    let (tick_every, tick_unit) = model
        .tick_rule()
        .map_or((0, String::new()), |(every, unit)| (every, unit.to_owned()));
    let rows = model
        .rows
        .iter()
        .filter(|row| {
            row.kind == mg::RowKind::Section
                || !model.tasks.get(row.index).is_some_and(|task| task.vert)
        })
        .map(row_of)
        .collect();
    let gantt = Gantt {
        sections: model.sections.iter().map(|s| s.label.clone()).collect(),
        tasks: model.tasks.iter().map(task_of).collect(),
        rows,
        excludes: model.excludes.clone(),
        includes: model.includes.clone(),
        weekend: model.weekend.clone(),
        weekday: model.effective_weekday(),
        top_axis: model.effective_top_axis(),
        tick_every,
        tick_unit,
        axis_form: model.effective_axis_format(),
    };
    let config = INTEGER_KEYS
        .iter()
        .filter_map(|key| {
            model
                .config_integer(key)
                .map(|n| ((*key).to_owned(), DumpValue::Integer(n)))
        })
        .collect();
    Chart {
        kind: Kind::Gantt,
        title: model.title_label.clone(),
        config,
        xy: None,
        radar: None,
        gantt: Some(gantt),
    }
}

fn config_of(chart: &Chart) -> BTreeMap<String, DumpValue> {
    let mut out = chart.config.clone();
    let Some(g) = &chart.gantt else {
        return out;
    };
    let text = |value: &str| DumpValue::String(value.to_owned());
    out.insert("axisFormat".into(), text(&g.axis_form));
    out.insert("weekday".into(), text(&g.weekday));
    out.insert("weekend".into(), text(&g.weekend));
    if !g.excludes.is_empty() {
        out.insert("excludes".into(), text(&g.excludes.join(",")));
    }
    if !g.includes.is_empty() {
        out.insert("includes".into(), text(&g.includes.join(",")));
    }
    if g.tick_every > 0 {
        out.insert(
            "tickInterval".into(),
            text(&format!("{}{}", g.tick_every, g.tick_unit)),
        );
    }
    if g.top_axis {
        out.insert("topAxis".into(), DumpValue::Bool(true));
    }
    out
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

fn flags_of(task: &GanttTask) -> usize {
    [
        (task.milestone, MILESTONE),
        (task.vert, VERT),
        (task.crit, CRIT),
        (task.active, ACTIVE),
        (task.done, DONE),
    ]
    .iter()
    .filter(|(on, _)| *on)
    .fold(0, |flags, (_, flag)| flags | flag)
}

fn regions(chart: &Chart) -> Vec<RegionSet> {
    let Some(gantt) = &chart.gantt else {
        return Vec::new();
    };
    gantt
        .tasks
        .iter()
        .enumerate()
        .map(|(i, task)| RegionSet {
            parent: i,
            regions: vec![
                flags_of(task),
                task.section.map_or(0, |section| section + 1),
                zigzag(task.start),
                zigzag(task.end),
                zigzag(task.render_end),
            ],
        })
        .collect()
}

fn text_of(value: &DumpValue) -> String {
    match value {
        DumpValue::String(text) => text.clone(),
        _ => String::new(),
    }
}

fn tokens_of(value: &DumpValue) -> Vec<String> {
    text_of(value).split(',').map(str::to_owned).collect()
}

fn decode_tick(g: &mut Gantt, text: &str) {
    let digits = text.bytes().take_while(u8::is_ascii_digit).count();
    let Some((count, unit)) = text.split_at_checked(digits) else {
        return;
    };
    if let Ok(every) = count.parse::<i64>() {
        g.tick_every = every;
        g.tick_unit = unit.to_owned();
    }
}

fn decode_config(chart: &mut Chart, g: &mut Gantt, key: &str, value: &DumpValue) {
    match key {
        "axisFormat" => g.axis_form = text_of(value),
        "weekday" => g.weekday = text_of(value),
        "weekend" => g.weekend = text_of(value),
        "excludes" => g.excludes = tokens_of(value),
        "includes" => g.includes = tokens_of(value),
        "topAxis" => g.top_axis = matches!(value, DumpValue::Bool(true)),
        "tickInterval" => decode_tick(g, &text_of(value)),
        _ => {
            chart.config.insert(key.to_owned(), value.clone());
        }
    }
}

fn decode_task(r: &[usize], label: &str) -> GanttTask {
    GanttTask {
        label: label.to_owned(),
        section: r[1].checked_sub(1),
        start: unzigzag(r[2]),
        end: unzigzag(r[3]),
        render_end: unzigzag(r[4]),
        milestone: r[0] & MILESTONE != 0,
        vert: r[0] & VERT != 0,
        crit: r[0] & CRIT != 0,
        active: r[0] & ACTIVE != 0,
        done: r[0] & DONE != 0,
    }
}

fn decode_box(g: &mut Gantt, texts: &BTreeMap<&str, &str>, id: &str) {
    let Some((kind, index)) = id
        .split_at_checked(1)
        .filter(|(kind, _)| matches!(*kind, "s" | "t"))
        .and_then(|(kind, rest)| Some((kind, rest.parse::<usize>().ok()?)))
    else {
        return;
    };
    if kind == "s" {
        let label = texts.get(format!("{id}.label").as_str()).copied();
        g.sections.push(label.unwrap_or_default().to_owned());
        g.rows.push(GanttRow {
            kind: GanttRowKind::Section,
            index: g.sections.len() - 1,
        });
        return;
    }
    if g.tasks.get(index).is_some_and(|task| !task.vert) {
        g.rows.push(GanttRow {
            kind: GanttRowKind::Task,
            index,
        });
    }
}

fn chart_of(input: &Input) -> Chart {
    let texts: BTreeMap<&str, &str> = input
        .labels
        .iter()
        .map(|l| (l.id.as_str(), l.text.as_str()))
        .collect();
    let mut chart = Chart {
        kind: Kind::Gantt,
        title: texts.get("title").copied().unwrap_or_default().to_owned(),
        config: BTreeMap::new(),
        xy: None,
        radar: None,
        gantt: None,
    };
    let mut g = Gantt::default();
    for (key, value) in &input.options.config {
        decode_config(&mut chart, &mut g, key, value);
    }
    for set in input
        .region_sets
        .iter()
        .filter(|s| s.regions.len() >= FIELDS)
    {
        let id = format!("t{}.label", g.tasks.len());
        let label = texts.get(id.as_str()).copied().unwrap_or_default();
        g.tasks.push(decode_task(&set.regions, label));
    }
    for b in &input.boxes {
        decode_box(&mut g, &texts, &b.id);
    }
    chart.gantt = Some(g);
    chart
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    chart::layout(&chart_of(input), &options)
}

#[cfg(test)]
mod tests;
