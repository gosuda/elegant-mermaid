//! The region-set encoding of the Wardley payload and its decoder.
//!
//! The closed `Input` has no chart payload, so the model stage writes the payload as
//! integer region sets, and the layout decodes them again together with the routes and
//! labels of the skeleton.

use std::collections::BTreeMap;

use crate::geom::GeomError;
use crate::scene::{SceneLabel, SceneRoute};

use super::LayoutError;
use super::wardley::{
    MARKER_POINT, STROKE_DASHED, TITLE_ID, Wardley, WardleyAnnotation, WardleyFlow, WardleyForce,
    WardleyLink, WardleyNode, WardleyNote, WardleyPipeline, WardleyPoint, WardleyStrategy,
    WardleyTrend, accelerator_id, annotation_id, annotation_prefix, deaccelerator_id, node_id,
};

const TAG_MAP: usize = 0;
const TAG_NODE: usize = 1;
const TAG_PIPELINE: usize = 2;
const TAG_TREND: usize = 3;
const TAG_ACCELERATOR: usize = 4;
const TAG_DEACCELERATOR: usize = 5;
const TAG_ANNOTATION: usize = 6;
const TAG_BOX: usize = 7;
const TAG_NOTE: usize = 8;

const FLAG_ANCHOR: usize = 1;
const FLAG_INERTIA: usize = 2;
const FLAG_PIPELINE_PARENT: usize = 4;
const FLAG_OFFSET: usize = 8;

const NODE_FIELDS: usize = 7;
const PIPELINE_HEADER: usize = 3;
const TREND_FIELDS: usize = 4;
const FORCE_FIELDS: usize = 3;
const ANNOTATION_FIELDS: usize = 4;
const MAP_HEADER: usize = 3;

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

fn unsigned(value: i64) -> usize {
    usize::try_from(value).unwrap_or(0)
}

fn signed(value: usize) -> Result<i64, LayoutError> {
    i64::try_from(value).map_err(|_| GeomError::Domain)
}

fn strategy_of(code: usize) -> Result<WardleyStrategy, LayoutError> {
    match code {
        0 => Ok(WardleyStrategy::None),
        1 => Ok(WardleyStrategy::Build),
        2 => Ok(WardleyStrategy::Buy),
        3 => Ok(WardleyStrategy::Outsource),
        4 => Ok(WardleyStrategy::Market),
        _ => Err(GeomError::Domain),
    }
}

fn strategy_code(strategy: WardleyStrategy) -> usize {
    match strategy {
        WardleyStrategy::None => 0,
        WardleyStrategy::Build => 1,
        WardleyStrategy::Buy => 2,
        WardleyStrategy::Outsource => 3,
        WardleyStrategy::Market => 4,
    }
}

impl Wardley {
    pub fn regions(&self) -> Vec<Vec<usize>> {
        let mut sets = vec![self.map_region()];
        sets.extend(self.nodes.iter().map(node_region));
        for p in &self.pipelines {
            let mut set = vec![TAG_PIPELINE, p.parent, p.children.len()];
            set.extend(&p.children);
            sets.push(set);
        }
        for t in &self.trends {
            sets.push(vec![
                TAG_TREND,
                t.node,
                unsigned(t.target_x),
                unsigned(t.target_y),
            ]);
        }
        for f in &self.accelerators {
            sets.push(vec![TAG_ACCELERATOR, unsigned(f.x), unsigned(f.y)]);
        }
        for f in &self.deaccelerators {
            sets.push(vec![TAG_DEACCELERATOR, unsigned(f.x), unsigned(f.y)]);
        }
        for a in &self.annotations {
            sets.push(vec![
                TAG_ANNOTATION,
                unsigned(a.number),
                unsigned(a.x),
                unsigned(a.y),
            ]);
        }
        if let Some(point) = self.box_point {
            sets.push(vec![TAG_BOX, unsigned(point.x), unsigned(point.y)]);
        }
        for n in &self.notes {
            sets.push(vec![TAG_NOTE, unsigned(n.x), unsigned(n.y)]);
        }
        sets
    }

    fn map_region(&self) -> Vec<usize> {
        let mut set = vec![TAG_MAP, self.stages.len(), self.boundaries.len()];
        set.extend(self.boundaries.iter().map(|b| unsigned(*b)));
        set
    }
}

fn node_region(n: &WardleyNode) -> Vec<usize> {
    let flags = [
        (n.anchor, FLAG_ANCHOR),
        (n.inertia, FLAG_INERTIA),
        (n.pipeline_parent, FLAG_PIPELINE_PARENT),
        (n.has_offset, FLAG_OFFSET),
    ]
    .iter()
    .filter(|(on, _)| *on)
    .fold(0, |acc, (_, bit)| acc | bit);
    vec![
        TAG_NODE,
        flags,
        strategy_code(n.strategy),
        unsigned(n.x),
        unsigned(n.y),
        zigzag(n.offset_x),
        zigzag(n.offset_y),
    ]
}

pub struct WardleyDump {
    pub routes: Vec<SceneRoute>,
    pub labels: Vec<SceneLabel>,
    pub regions: Vec<Vec<usize>>,
}

pub fn decode_wardley(dump: &WardleyDump) -> Result<Wardley, LayoutError> {
    let labels: BTreeMap<&str, &str> = dump
        .labels
        .iter()
        .map(|l| (l.id.as_str(), l.text.as_str()))
        .collect();
    let mut w = Wardley {
        title: text_of(&labels, TITLE_ID),
        ..Wardley::default()
    };
    for set in &dump.regions {
        w.decode_region(set, &labels)?;
    }
    for route in &dump.routes {
        w.decode_route(route, &labels)?;
    }
    w.validate()?;
    Ok(w)
}

fn text_of(labels: &BTreeMap<&str, &str>, id: &str) -> String {
    labels.get(id).copied().unwrap_or("").to_owned()
}

fn short_region(set: &[usize], fields: usize) -> Result<(), LayoutError> {
    if set.len() < fields {
        return Err(GeomError::Domain);
    }
    Ok(())
}

impl Wardley {
    fn decode_region(
        &mut self,
        set: &[usize],
        labels: &BTreeMap<&str, &str>,
    ) -> Result<(), LayoutError> {
        let Some(&tag) = set.first() else {
            return Ok(());
        };
        match tag {
            TAG_MAP => self.decode_map(set, labels),
            TAG_NODE => self.decode_node(set, labels),
            TAG_PIPELINE => self.decode_pipeline(set),
            TAG_TREND => self.decode_trend(set),
            TAG_ACCELERATOR | TAG_DEACCELERATOR => self.decode_force(set, labels),
            TAG_ANNOTATION => self.decode_annotation(set, labels),
            TAG_BOX => self.decode_box(set),
            TAG_NOTE => self.decode_note(set, labels),
            _ => Err(GeomError::Domain),
        }
    }

    fn decode_map(
        &mut self,
        set: &[usize],
        labels: &BTreeMap<&str, &str>,
    ) -> Result<(), LayoutError> {
        short_region(set, MAP_HEADER)?;
        if set.len() != MAP_HEADER + set[2] {
            return Err(GeomError::Domain);
        }
        for k in 0..set[1] {
            self.stages.push(text_of(labels, &format!("st{k}")));
        }
        for &b in &set[MAP_HEADER..] {
            self.boundaries.push(signed(b)?);
        }
        Ok(())
    }

    fn decode_node(
        &mut self,
        set: &[usize],
        labels: &BTreeMap<&str, &str>,
    ) -> Result<(), LayoutError> {
        short_region(set, NODE_FIELDS)?;
        let flags = set[1];
        let label = text_of(labels, &format!("{}.label", node_id(self.nodes.len())));
        self.nodes.push(WardleyNode {
            label,
            x: signed(set[3])?,
            y: signed(set[4])?,
            strategy: strategy_of(set[2])?,
            anchor: flags & FLAG_ANCHOR != 0,
            inertia: flags & FLAG_INERTIA != 0,
            pipeline_parent: flags & FLAG_PIPELINE_PARENT != 0,
            has_offset: flags & FLAG_OFFSET != 0,
            offset_x: unzigzag(set[5]),
            offset_y: unzigzag(set[6]),
        });
        Ok(())
    }

    fn decode_pipeline(&mut self, set: &[usize]) -> Result<(), LayoutError> {
        short_region(set, PIPELINE_HEADER)?;
        if set.len() != PIPELINE_HEADER + set[2] {
            return Err(GeomError::Domain);
        }
        self.pipelines.push(WardleyPipeline {
            parent: set[1],
            children: set[PIPELINE_HEADER..].to_vec(),
        });
        Ok(())
    }

    fn decode_trend(&mut self, set: &[usize]) -> Result<(), LayoutError> {
        short_region(set, TREND_FIELDS)?;
        self.trends.push(WardleyTrend {
            node: set[1],
            target_x: signed(set[2])?,
            target_y: signed(set[3])?,
        });
        Ok(())
    }

    fn decode_force(
        &mut self,
        set: &[usize],
        labels: &BTreeMap<&str, &str>,
    ) -> Result<(), LayoutError> {
        short_region(set, FORCE_FIELDS)?;
        let (x, y) = (signed(set[1])?, signed(set[2])?);
        if set[0] == TAG_ACCELERATOR {
            let name = text_of(
                labels,
                &format!("{}.label", accelerator_id(self.accelerators.len())),
            );
            self.accelerators.push(WardleyForce { name, x, y });
            return Ok(());
        }
        let name = text_of(
            labels,
            &format!("{}.label", deaccelerator_id(self.deaccelerators.len())),
        );
        self.deaccelerators.push(WardleyForce { name, x, y });
        Ok(())
    }

    fn decode_annotation(
        &mut self,
        set: &[usize],
        labels: &BTreeMap<&str, &str>,
    ) -> Result<(), LayoutError> {
        short_region(set, ANNOTATION_FIELDS)?;
        let number = signed(set[1])?;
        let shown = text_of(
            labels,
            &format!("{}.text", annotation_id(self.annotations.len())),
        );
        let text = shown
            .strip_prefix(&annotation_prefix(number))
            .unwrap_or(&shown)
            .to_owned();
        self.annotations.push(WardleyAnnotation {
            number,
            x: signed(set[2])?,
            y: signed(set[3])?,
            text,
        });
        Ok(())
    }

    fn decode_box(&mut self, set: &[usize]) -> Result<(), LayoutError> {
        short_region(set, FORCE_FIELDS)?;
        self.box_point = Some(WardleyPoint {
            x: signed(set[1])?,
            y: signed(set[2])?,
        });
        Ok(())
    }

    fn decode_note(
        &mut self,
        set: &[usize],
        labels: &BTreeMap<&str, &str>,
    ) -> Result<(), LayoutError> {
        short_region(set, FORCE_FIELDS)?;
        let text = text_of(labels, &format!("note{}", self.notes.len()));
        self.notes.push(WardleyNote {
            text,
            x: signed(set[1])?,
            y: signed(set[2])?,
        });
        Ok(())
    }

    fn decode_route(
        &mut self,
        route: &SceneRoute,
        labels: &BTreeMap<&str, &str>,
    ) -> Result<(), LayoutError> {
        let Some(rest) = route.id.strip_prefix('l') else {
            return Ok(());
        };
        if rest.parse::<usize>().ok() != Some(self.links.len()) {
            return Err(GeomError::Domain);
        }
        let (Some(from), Some(to)) = (node_index(&route.from), node_index(&route.to)) else {
            return Err(GeomError::Domain);
        };
        self.links.push(WardleyLink {
            from,
            to,
            dashed: route.stroke == STROKE_DASHED,
            label: text_of(labels, &format!("{}.label", route.id)),
            flow: flow_of_markers(route),
        });
        Ok(())
    }

    fn validate(&self) -> Result<(), LayoutError> {
        let count = self.nodes.len();
        let links_ok = self.links.iter().all(|l| l.from < count && l.to < count);
        let pipelines_ok = self.pipelines.iter().all(|p| {
            p.parent < count && !p.children.is_empty() && p.children.iter().all(|&c| c < count)
        });
        let trends_ok = self.trends.iter().all(|t| t.node < count);
        if links_ok && pipelines_ok && trends_ok {
            Ok(())
        } else {
            Err(GeomError::Domain)
        }
    }
}

fn node_index(id: &str) -> Option<usize> {
    id.strip_prefix('n')?.parse().ok()
}

fn flow_of_markers(route: &SceneRoute) -> WardleyFlow {
    match (
        route.marker_start == MARKER_POINT,
        route.marker_end == MARKER_POINT,
    ) {
        (true, true) => WardleyFlow::Bidirectional,
        (true, false) => WardleyFlow::Backward,
        (false, true) => WardleyFlow::Forward,
        (false, false) => WardleyFlow::None,
    }
}
