use super::chart::sankey;
use super::input::{Box as InputBox, Input, Label, RegionSet, Route, Spacing};
use crate::geom::GeomError;
use crate::model::sankey::{Link, Model, Node, Value, ValueKind};
use crate::scene::{Direction, DumpOptions, Profile, Scene, TextRole};
use crate::source::Span;
use std::collections::BTreeMap;

pub(crate) fn from_sankey(
    model: &Model,
    _profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.set_kind_config(model.config.clone());
    options.profile = Profile::Vector;
    let skeleton = sankey::skeleton(model)?;
    let boxes = skeleton
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
        .collect();
    let labels = skeleton
        .labels
        .into_iter()
        .map(|l| Label {
            id: l.id,
            owner: l.owner,
            role: TextRole::Label,
            text: l.text,
        })
        .collect();
    let mut routes = Vec::with_capacity(model.links.len());
    let mut regions = Vec::with_capacity(2 * model.links.len());
    for (i, link) in model.links.iter().enumerate() {
        let kind = match link.value.kind {
            ValueKind::Finite => 0,
            ValueKind::NonFinite => 1,
            ValueKind::Overflow => 2,
        };
        let value = link.value.thousandths;
        let magnitude = usize::try_from(value.unsigned_abs()).map_err(|_| GeomError::Overflow)?;
        let encoded = magnitude.checked_mul(2).ok_or(GeomError::Overflow)?;
        regions.extend([kind, if value < 0 { encoded - 1 } else { encoded }]);
        routes.push(Route {
            id: sankey::link_id(i),
            from: sankey::node_id(link.source),
            to: sankey::node_id(link.target),
            orthogonal: false,
            marker_start: String::new(),
            marker_end: String::new(),
            line: String::new(),
            min_length: 1,
            from_side: None,
            to_side: None,
        });
    }
    Ok(Input {
        kind: "sankey",
        profile: Profile::Vector,
        direction: Direction::Tb,
        options,
        boxes,
        routes,
        labels,
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: vec![RegionSet { parent: 0, regions }],
        spacing: Spacing::default(),
    })
}

fn model_of(input: &Input) -> Result<Model, GeomError> {
    let mut model = Model {
        config: input.options.config.clone(),
        ..Model::default()
    };
    let mut indices = BTreeMap::new();
    let span = Span { start: 0, end: 0 };
    for (i, b) in input.boxes.iter().enumerate() {
        indices.insert(b.id.as_str(), i);
        model.nodes.push(Node {
            id: String::new(),
            label: Some(String::new()),
            span,
        });
    }
    for label in &input.labels {
        let index = *indices.get(label.owner.as_str()).ok_or(GeomError::Domain)?;
        model.nodes[index].label = Some(label.text.clone());
    }
    let regions = input.region_sets.first().ok_or(GeomError::Domain)?;
    if regions.regions.len()
        != input
            .routes
            .len()
            .checked_mul(2)
            .ok_or(GeomError::Overflow)?
    {
        return Err(GeomError::Domain);
    }
    for (route, pair) in input.routes.iter().zip(regions.regions.as_chunks::<2>().0) {
        let source = *indices.get(route.from.as_str()).ok_or(GeomError::Domain)?;
        let target = *indices.get(route.to.as_str()).ok_or(GeomError::Domain)?;
        let kind = match pair[0] {
            0 => ValueKind::Finite,
            1 => ValueKind::NonFinite,
            2 => ValueKind::Overflow,
            _ => return Err(GeomError::Domain),
        };
        let half = i64::try_from(pair[1] / 2).map_err(|_| GeomError::Overflow)?;
        let thousandths = if pair[1] % 2 == 1 { -half - 1 } else { half };
        model.links.push(Link {
            source,
            target,
            value: Value { kind, thousandths },
            span,
        });
    }
    Ok(model)
}

pub fn layout(input: &Input) -> Result<(Scene, bool), GeomError> {
    sankey::layout(&model_of(input)?, &input.options)
}
