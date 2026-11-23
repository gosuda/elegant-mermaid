//! The wardley adapter and family entry (`spec/layout/charts.md`).
//!
//! [`from_wardley`] authors the model-stage input: the dump skeleton as boxes, routes,
//! and labels, the honoured config keys as options, and the payload as region sets,
//! because the closed [`Input`] has no chart payload. [`layout`] decodes that input
//! again and runs the chart family.

use crate::model::wardley as mw;
use crate::scene::{Direction, DumpOptions, DumpValue, Profile, Scene, TextRole};

use super::chart::{
    Wardley, WardleyAnnotation, WardleyDump, WardleyFlow, WardleyForce, WardleyLink, WardleyNode,
    WardleyNote, WardleyPipeline, WardleyPoint, WardleyStrategy, WardleyTrend, decode_wardley,
    layout_wardley,
};
use super::input::{
    Box as InputBox, Input, Label as InputLabel, RegionSet, Route as InputRoute, Spacing,
};
use super::layered::LayoutError;

const KIND: &str = "wardley";
const DEFAULT_STAGES: [&str; 4] = ["Genesis", "Custom Built", "Product", "Commodity"];

pub(crate) fn from_wardley(
    model: &mw::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.set_kind_config(model
        .config
        .iter()
        .map(|entry| (entry.key.clone(), DumpValue::Integer(entry.value)))
        .collect());
    options.profile = profile;
    let payload = payload(model);
    let skeleton = payload.skeleton();
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
    let routes = skeleton
        .routes
        .into_iter()
        .map(|r| InputRoute {
            id: r.id,
            from: r.from,
            to: r.to,
            orthogonal: false,
            marker_start: r.marker_start,
            marker_end: r.marker_end,
            line: r.stroke,
            min_length: 1,
            from_side: None,
            to_side: None,
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
        routes,
        labels,
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: payload
            .regions()
            .into_iter()
            .map(|regions| RegionSet { parent: 0, regions })
            .collect(),
        spacing: Spacing::default(),
    })
}

fn strategy_of(strategy: mw::Strategy) -> WardleyStrategy {
    match strategy {
        mw::Strategy::None => WardleyStrategy::None,
        mw::Strategy::Build => WardleyStrategy::Build,
        mw::Strategy::Buy => WardleyStrategy::Buy,
        mw::Strategy::Outsource => WardleyStrategy::Outsource,
        mw::Strategy::Market => WardleyStrategy::Market,
    }
}

fn flow_of(flow: mw::Flow) -> WardleyFlow {
    match flow {
        mw::Flow::None => WardleyFlow::None,
        mw::Flow::Forward => WardleyFlow::Forward,
        mw::Flow::Backward => WardleyFlow::Backward,
        mw::Flow::Bidirectional => WardleyFlow::Bidirectional,
    }
}

fn node_of(n: &mw::Node) -> WardleyNode {
    WardleyNode {
        label: n.label.clone(),
        x: n.x,
        y: n.y,
        anchor: n.anchor,
        inertia: n.inertia,
        pipeline_parent: n.pipeline_parent,
        has_offset: n.has_offset,
        offset_x: n.offset_x,
        offset_y: n.offset_y,
        strategy: strategy_of(n.strategy),
    }
}

fn payload(model: &mw::Model) -> Wardley {
    let pipelines = pipelines_of(model);
    let stages = if model.stages.is_empty() {
        DEFAULT_STAGES.map(str::to_owned).to_vec()
    } else {
        model.stages.clone()
    };
    Wardley {
        title: model.title.clone(),
        stages,
        boundaries: model.boundaries.clone(),
        nodes: model.nodes.iter().map(node_of).collect(),
        links: links_of(model, &pipelines),
        pipelines,
        trends: model
            .trends
            .iter()
            .filter_map(|t| {
                Some(WardleyTrend {
                    node: model.node_index(&t.node)?,
                    target_x: t.target_x,
                    target_y: t.target_y,
                })
            })
            .collect(),
        notes: model
            .notes
            .iter()
            .map(|n| WardleyNote {
                text: n.text.clone(),
                x: n.x,
                y: n.y,
            })
            .collect(),
        accelerators: model.accelerators.iter().map(force_of).collect(),
        deaccelerators: model.deaccelerators.iter().map(force_of).collect(),
        annotations: model
            .annotations
            .iter()
            .map(|a| WardleyAnnotation {
                number: a.number,
                x: a.x,
                y: a.y,
                text: a.text.clone(),
            })
            .collect(),
        box_point: model.box_point.map(|p| WardleyPoint { x: p.x, y: p.y }),
    }
}

fn force_of(f: &mw::Force) -> WardleyForce {
    WardleyForce {
        name: f.name.clone(),
        x: f.x,
        y: f.y,
    }
}

fn pipelines_of(model: &mw::Model) -> Vec<WardleyPipeline> {
    model
        .pipelines
        .iter()
        .filter_map(|p| {
            let parent = model.node_index(&p.node)?;
            let children: Vec<usize> = p
                .components
                .iter()
                .filter_map(|id| model.node_index(id))
                .collect();
            (!children.is_empty()).then_some(WardleyPipeline { parent, children })
        })
        .collect()
}

fn links_of(model: &mw::Model, pipelines: &[WardleyPipeline]) -> Vec<WardleyLink> {
    let spoke = |a: usize, b: usize| {
        pipelines.iter().any(|p| {
            (a == p.parent && p.children.contains(&b)) || (b == p.parent && p.children.contains(&a))
        })
    };
    model
        .links
        .iter()
        .filter_map(|l| {
            let (from, to) = (model.node_index(&l.source)?, model.node_index(&l.target)?);
            (!spoke(from, to)).then(|| WardleyLink {
                from,
                to,
                dashed: l.dashed,
                label: l.label.clone(),
                flow: flow_of(l.flow),
            })
        })
        .collect()
}

pub(crate) fn from_input(input: &Input) -> Result<Wardley, LayoutError> {
    decode_wardley(&WardleyDump {
        routes: input
            .routes
            .iter()
            .map(|r| crate::scene::SceneRoute {
                id: r.id.clone(),
                from: r.from.clone(),
                to: r.to.clone(),
                orthogonal: false,
                points: Vec::new(),
                marker_start: r.marker_start.clone(),
                marker_end: r.marker_end.clone(),
                stroke: r.line.clone(),
            })
            .collect(),
        labels: input
            .labels
            .iter()
            .map(|l| crate::scene::SceneLabel {
                id: l.id.clone(),
                owner: l.owner.clone(),
                text: l.text.clone(),
                rect: super::chart::ZERO_RECT,
                lines: Vec::new(),
            })
            .collect(),
        regions: input
            .region_sets
            .iter()
            .map(|set| set.regions.clone())
            .collect(),
    })
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    layout_wardley(&from_input(input)?, &options)
}

#[cfg(test)]
mod tests;
