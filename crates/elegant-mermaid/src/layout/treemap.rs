//! Treemap model-stage relations and the chart-family entry.
use super::chart::{Treemap, TreemapNode, layout_treemap, treemap_normalize, treemap_skeleton};
use super::input::{Box as InputBox, Input, Label, RegionSet, Spacing};
use super::layered::LayoutError;
use crate::geom::GeomError;
use crate::model::treemap as model;
use crate::scene::{Direction, DumpOptions, Profile, Scene, TextRole};

pub fn from_treemap(
    m: &model::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.config.clone_from(&m.config);
    options.profile = profile;
    let mut sums = m
        .nodes
        .iter()
        .map(|n| if n.children.is_empty() { n.value } else { 0 })
        .collect::<Vec<_>>();
    for i in (0..m.nodes.len()).rev() {
        if let Some(parent) = m.nodes[i].parent {
            sums[parent] = sums[parent]
                .checked_add(sums[i])
                .ok_or(GeomError::Overflow)?;
        }
    }
    let nodes = m
        .nodes
        .iter()
        .enumerate()
        .map(|(i, n)| TreemapNode {
            name: n.name.clone(),
            value_text: if sums[i] != 0 {
                model::format_value(sums[i])
            } else {
                String::new()
            },
            value: if n.children.is_empty() { n.value } else { 0 },
            parent: n.parent,
            index: n.index,
        })
        .collect();
    let chart = Treemap {
        title: m.title.clone(),
        config: m.config.clone(),
        nodes,
    };
    let skeleton = treemap_skeleton(&chart)?;
    let leaves = m
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, n)| n.children.is_empty())
        .map(|(i, n)| (i, n.value))
        .collect::<Vec<_>>();
    let raw = leaves.iter().map(|(_, v)| *v).collect::<Vec<_>>();
    let normalized = treemap_normalize(&raw)?;
    let mut values = vec![0; m.nodes.len()];
    for ((i, _), v) in leaves.into_iter().zip(normalized) {
        values[i] = usize::try_from(v).map_err(|_| GeomError::Overflow)?;
    }
    Ok(Input {
        kind: "treemap",
        profile,
        direction: Direction::Tb,
        options,
        boxes: skeleton
            .boxes
            .into_iter()
            .map(|b| InputBox {
                id: b.id,
                role: b.role,
                shape: String::new(),
                icon: false,
                parent: b.parent,
                exclusive: b.exclusive,
                text: String::new(),
                direction: String::new(),
            })
            .collect(),
        labels: skeleton
            .labels
            .into_iter()
            .map(|l| Label {
                id: l.id,
                owner: l.owner,
                role: TextRole::Label,
                text: l.text,
            })
            .collect(),
        routes: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: vec![RegionSet {
            parent: 0,
            regions: values,
        }],
        spacing: Spacing::default(),
    })
}
fn payload(input: &Input) -> Result<Treemap, LayoutError> {
    let text = |id: &str| {
        input
            .labels
            .iter()
            .find(|l| l.id == id)
            .map_or_else(String::new, |l| l.text.clone())
    };
    let mut chart = Treemap {
        title: text("title"),
        config: input.options.config.clone(),
        nodes: Vec::new(),
    };
    let values = input
        .region_sets
        .first()
        .map_or(&[][..], |r| r.regions.as_slice());
    let mut ids = Vec::new();
    for b in input.boxes.iter().filter(|b| b.id != "root") {
        let i = chart.nodes.len();
        let parent = ids.iter().position(|id| id == &b.parent);
        let value =
            i64::try_from(values.get(i).copied().unwrap_or(0)).map_err(|_| GeomError::Overflow)?;
        chart.nodes.push(TreemapNode {
            name: text(&format!("{}.name", b.id)),
            value_text: text(&format!("{}.value", b.id)),
            value,
            parent,
            index: i,
        });
        ids.push(b.id.clone());
    }
    Ok(chart)
}
pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    layout_treemap(&payload(input)?, &options)
}
