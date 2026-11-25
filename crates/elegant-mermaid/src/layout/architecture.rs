//! The architecture kind adapter (`spec/layout/grid.md`): [`from_architecture`] authors
//! the model-stage dump and [`layout`] feeds the grid family with measured sizes, then
//! draws the scene under both profiles.

mod paint;
mod plan;

use std::collections::BTreeMap;

use crate::geom::GeomError;
use crate::icons::{IconRef, Placement};
use crate::model::architecture as ma;
use crate::scene::{BoxRole, Direction, DumpOptions, DumpValue, Profile, Scene, TextRole};

use super::input::{
    Box as InputBox, Input, Label as InputLabel, Route as InputRoute, RouteSide, Spacing,
};
use super::layered::LayoutError;

pub(crate) const KIND: &str = "architecture";

pub(crate) fn from_architecture(
    model: &ma::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.set_kind_config(
        model
            .config
            .iter()
            .map(|entry| (entry.key.clone(), DumpValue::Integer(entry.value)))
            .collect::<BTreeMap<_, _>>(),
    );
    options.profile = profile;
    options.direction = Direction::Tb;
    let aligns = alignment_suffixes(model);
    let mut boxes = Vec::with_capacity(model.groups.len() + model.nodes.len());
    for g in &model.groups {
        boxes.push(InputBox {
            icon: false,
            id: g.id.clone(),
            role: BoxRole::Group,
            shape: shape_text("group", "icon", &g.icon),
            parent: g.parent.clone(),
            exclusive: false,
            text: g.title.clone(),
            direction: String::new(),
        });
    }
    for n in &model.nodes {
        boxes.push(node_box(
            n,
            aligns.get(n.id.as_str()).map_or("", String::as_str),
        ));
    }
    let ids = route_ids(&boxes, model.edges.len());
    let mut routes = Vec::with_capacity(model.edges.len());
    let mut labels = Vec::new();
    for (edge, id) in model.edges.iter().zip(&ids) {
        routes.push(InputRoute {
            id: id.clone(),
            from: edge.from.clone(),
            to: edge.to.clone(),
            orthogonal: true,
            marker_start: marker(edge.from_into).into(),
            marker_end: marker(edge.to_into).into(),
            line: "normal".into(),
            min_length: 0,
            from_side: Some(side_of(&edge.from_side)),
            to_side: Some(side_of(&edge.to_side)),
        });
        if !edge.title.is_empty() {
            labels.push(InputLabel {
                id: format!("{id}.label"),
                owner: id.clone(),
                role: TextRole::Label,
                text: edge.title.clone(),
            });
        }
    }
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
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    })
}

pub(crate) fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let planner = plan::Planner::new(input)?;
    let result = super::grid::architecture::architecture(&planner.grid_input()?, planner.params())?;
    let dump = planner.fill(&result)?;
    let groups = planner.groups(&result);
    Ok((Scene::new(result.canvas, dump, groups), result.budget))
}

fn marker(into: bool) -> &'static str {
    if into { "point" } else { "" }
}

fn side_of(letter: &str) -> RouteSide {
    match letter {
        "L" => RouteSide::Left,
        "R" => RouteSide::Right,
        "T" => RouteSide::Up,
        _ => RouteSide::Down,
    }
}

fn route_ids(boxes: &[InputBox], count: usize) -> Vec<String> {
    let mut next = 0usize;
    let mut ids = Vec::with_capacity(count);
    while ids.len() < count {
        let id = format!("e{next}");
        next += 1;
        if !boxes.iter().any(|node| node.id == id) {
            ids.push(id);
        }
    }
    ids
}

fn node_box(node: &ma::Node, align: &str) -> InputBox {
    let mut shape = if node.junction {
        "junction".to_owned()
    } else if node.icon_text.is_empty() {
        shape_text("service", "icon", &node.icon)
    } else {
        shape_text("service", "icontext", &escape_shape(&node.icon_text))
    };
    shape.push_str(align);
    InputBox {
        icon: false,
        id: node.id.clone(),
        role: BoxRole::Node,
        shape,
        parent: node.parent.clone(),
        exclusive: true,
        text: node.title.clone(),
        direction: String::new(),
    }
}

fn shape_text(kind: &str, key: &str, value: &str) -> String {
    if value.is_empty() {
        kind.to_owned()
    } else {
        format!("{kind};{key}={value}")
    }
}

fn alignment_suffixes(model: &ma::Model) -> BTreeMap<&str, String> {
    let mut out: BTreeMap<&str, String> = BTreeMap::new();
    for (i, alignment) in model.alignments.iter().enumerate() {
        let axis = if alignment.direction == "column" {
            "c"
        } else {
            "r"
        };
        for (pos, id) in alignment.members.iter().enumerate() {
            out.entry(id.as_str())
                .or_default()
                .push_str(&format!(";align={i}:{axis}:{pos}"));
        }
    }
    out
}

fn escape_shape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        if matches!(c, '%' | ';' | '=') || u32::from(c) < 0x20 || c == '\u{7f}' {
            out.push_str(&format!("%{:02X}", u32::from(c)));
        } else {
            out.push(c);
        }
    }
    out
}

fn unescape_shape(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            let pair = (hex_digit(bytes[i + 1]), hex_digit(bytes[i + 2]));
            if let (Some(high), Some(low)) = pair {
                out.push(high * 16 + low);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn hex_digit(byte: u8) -> Option<u8> {
    char::from(byte)
        .to_digit(16)
        .and_then(|digit| u8::try_from(digit).ok())
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct ShapeSpec {
    pub kind: String,
    pub icon: String,
    pub icon_text: String,
    pub aligns: Vec<AlignMember>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct AlignMember {
    pub set: usize,
    pub pos: usize,
    pub column: bool,
}

pub(crate) fn parse_shape(shape: &str) -> ShapeSpec {
    let mut fields = shape.split(';');
    let mut spec = ShapeSpec {
        kind: fields.next().unwrap_or_default().to_owned(),
        ..ShapeSpec::default()
    };
    for field in fields {
        let (key, value) = field.split_once('=').unwrap_or((field, ""));
        match key {
            "icon" => spec.icon = value.to_owned(),
            "icontext" => spec.icon_text = unescape_shape(value),
            "align" => spec.aligns.extend(parse_align_member(value)),
            _ => {}
        }
    }
    spec
}

fn parse_align_member(value: &str) -> Option<AlignMember> {
    let parts: Vec<&str> = value.split(':').collect();
    let [set, axis, pos] = parts.as_slice() else {
        return None;
    };
    Some(AlignMember {
        set: set.parse().ok()?,
        pos: pos.parse().ok()?,
        column: *axis == "c",
    })
}

/// The icons the model names: a badge for each group and a centred icon for each service.
pub(crate) fn icon_refs(model: &ma::Model) -> Vec<IconRef<'_>> {
    let badges = model
        .groups
        .iter()
        .filter(|group| !group.icon.is_empty())
        .map(|group| IconRef {
            owner: &group.id,
            name: &group.icon,
            span: group.span,
            placement: Placement::Badge,
        });
    let services = model
        .nodes
        .iter()
        .filter(|node| !node.junction && !node.icon.is_empty())
        .map(|node| IconRef {
            owner: &node.id,
            name: &node.icon,
            span: node.span,
            placement: Placement::Service,
        });
    badges.chain(services).collect()
}

#[cfg(test)]
mod tests;
