//! Measurement, grid input, and the layout dump of the architecture kind.

use std::collections::BTreeMap;

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::geom::{self, Rect, Size};
use crate::layout::grid::architecture::{
    ArchAlign, ArchEdge, ArchGroup, ArchInput, ArchLayout, ArchNode, ArchParams,
};
use crate::layout::input::Input;
use crate::layout::layered::LayoutError;
use crate::measure::{self, Metric, Role, StyledLine};
use crate::scene::{BoxRole, Dump, DumpValue, Profile, Run, SceneBox, SceneLabel, SceneRoute};

use super::{AlignMember, KIND, ShapeSpec, parse_shape};

#[derive(Debug, Clone, Default)]
pub(super) struct Measured {
    pub texts: Vec<String>,
    pub runs: Vec<Vec<Run>>,
    width: i32,
}

impl Measured {
    fn of(lines: &[StyledLine<'_>]) -> Self {
        Self {
            width: lines.iter().map(|line| line.width).max().unwrap_or(0),
            texts: lines.iter().map(|line| line.text.clone()).collect(),
            runs: lines
                .iter()
                .map(|line| {
                    line.runs
                        .iter()
                        .map(|run| Run {
                            text: run.text.to_string(),
                            bold: run.bold,
                            italic: run.italic,
                        })
                        .collect()
                })
                .collect(),
        }
    }

    fn extent(&self, line_height: i32) -> Size {
        let limit = geom::COORD_LIMIT;
        let height = i64::try_from(self.texts.len()).unwrap_or(limit) * i64::from(line_height);
        Size {
            w: clamp(i64::from(self.width), limit),
            h: clamp(height, limit),
        }
    }

    /// The first `count` lines.
    pub(super) fn head(&self, count: usize) -> Self {
        Self {
            texts: self.texts[..count].to_vec(),
            runs: self.runs[..count].to_vec(),
            width: self.width,
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.texts.is_empty()
    }
}

fn clamp(value: i64, limit: i64) -> i32 {
    i32::try_from(value.min(limit)).unwrap_or(i32::MAX)
}

fn lookup(profile: Profile, name: &str) -> Result<i32, LayoutError> {
    let key = format!("{}.{name}", profile.as_str());
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(LayoutError::Domain)
}

pub(super) struct Constants {
    pub params: ArchParams,
    pub border: i32,
    pub corner: i32,
    pub junction: i32,
}

impl Constants {
    fn load(profile: Profile, config: &BTreeMap<String, DumpValue>) -> Result<Self, LayoutError> {
        let get = |name: &str| lookup(profile, name);
        let mut c = Self {
            params: ArchParams {
                pitch_x: get("architecture.pitch_x")?,
                pitch_y: get("architecture.pitch_y")?,
                label_wrap: get("architecture.label_wrap")?,
                icon_w: get("architecture.icon_width")?,
                icon_h: get("architecture.icon_height")?,
                padding: get("architecture.padding")?,
                line_height: get("line_h")?,
                badge: get("architecture.badge")?,
                inset: get("architecture.title_inset")?,
                label_gap: get("architecture.label_gap")?,
                thickness: get("architecture.line_thickness")?,
                margin: get("canvas_margin")?,
                gutter: i32::from(profile == Profile::Cell),
                fuel: get("architecture.bfs_cap")?,
                ring_cap: get("architecture.ring_cap")?,
            },
            border: get("node_border")?,
            corner: get("corner_radius")?,
            junction: get("architecture.junction_size")?,
        };
        for (key, value) in config {
            let DumpValue::Integer(value) = value else {
                continue;
            };
            if let Some(px) = i32::try_from(*value).ok().filter(|px| *px >= 0) {
                c.configure(profile, key, px);
            }
        }
        Ok(c)
    }

    fn configure(&mut self, profile: Profile, key: &str, px: i32) {
        let cell = profile == Profile::Cell;
        let wide = i64::from(px);
        let params = &mut self.params;
        match (key, cell) {
            ("padding", true) => params.padding = scaled(geom::floor_div(2 * wide + 20, 40)),
            ("padding", false) => params.padding = px.saturating_mul(64),
            ("iconSize", true) if px > 0 => {
                params.icon_w = scaled(geom::floor_div(14 * wide + 80, 160)).max(1);
                params.icon_h = scaled(geom::floor_div(6 * wide + 80, 160)).max(1);
            }
            ("iconSize", false) if px > 0 => {
                params.icon_w = px.saturating_mul(64);
                params.icon_h = px.saturating_mul(64);
            }
            _ => {}
        }
    }
}

fn scaled(value: i64) -> i32 {
    i32::try_from(value).unwrap_or(i32::MAX)
}

pub(super) struct Planner<'a> {
    pub input: &'a Input,
    pub profile: Profile,
    pub c: Constants,
    group_at: Vec<usize>,
    node_at: Vec<usize>,
    group_index: BTreeMap<&'a str, usize>,
    node_index: BTreeMap<&'a str, usize>,
    specs: Vec<ShapeSpec>,
    group_specs: Vec<ShapeSpec>,
    pub titles: Vec<Measured>,
    pub labels: Vec<Measured>,
    pub icon_texts: Vec<Measured>,
    pub edge_labels: Vec<Measured>,
}

fn metric_of(profile: Profile) -> Metric {
    match profile {
        Profile::Cell => Metric::Cell,
        Profile::Vector => Metric::for_role(Role::Label),
    }
}

impl<'a> Planner<'a> {
    pub(super) fn new(input: &'a Input) -> Result<Self, LayoutError> {
        let mut p = Self {
            input,
            profile: input.profile,
            c: Constants::load(input.profile, &input.options.config)?,
            group_at: Vec::new(),
            node_at: Vec::new(),
            group_index: BTreeMap::new(),
            node_index: BTreeMap::new(),
            specs: Vec::new(),
            group_specs: Vec::new(),
            titles: Vec::new(),
            labels: Vec::new(),
            icon_texts: Vec::new(),
            edge_labels: Vec::new(),
        };
        for (i, b) in input.boxes.iter().enumerate() {
            let spec = parse_shape(&b.shape);
            if b.role == BoxRole::Group {
                p.group_index.insert(b.id.as_str(), p.group_at.len());
                p.group_at.push(i);
                p.group_specs.push(spec);
            } else {
                p.node_index.insert(b.id.as_str(), p.node_at.len());
                p.node_at.push(i);
                p.specs.push(spec);
            }
        }
        p.measure()?;
        Ok(p)
    }

    pub(super) fn params(&self) -> ArchParams {
        self.c.params
    }

    pub(super) fn spec(&self, node: usize) -> &ShapeSpec {
        &self.specs[node]
    }

    pub(super) fn group_id(&self, group: usize) -> &str {
        &self.input.boxes[self.group_at[group]].id
    }

    pub(super) fn node_id(&self, node: usize) -> &str {
        &self.input.boxes[self.node_at[node]].id
    }

    pub(super) fn node_count(&self) -> usize {
        self.node_at.len()
    }

    pub(super) fn group_count(&self) -> usize {
        self.group_at.len()
    }

    fn lines(&self, text: &str, wrap: i32) -> Result<Measured, LayoutError> {
        if text.is_empty() {
            return Ok(Measured::default());
        }
        let lines = measure::styled_lines(text, wrap, metric_of(self.profile))
            .map_err(|_| LayoutError::Overflow)?;
        Ok(Measured::of(&lines))
    }

    fn measure(&mut self) -> Result<(), LayoutError> {
        let params = self.c.params;
        for i in &self.group_at {
            let measured = self.lines(&self.input.boxes[*i].text, i32::MAX)?;
            self.titles.push(measured);
        }
        for (k, i) in self.node_at.iter().enumerate() {
            let label = self.lines(&self.input.boxes[*i].text, params.label_wrap)?;
            let inner_wrap = (params.icon_w - 2 * params.inset).max(1);
            let inner = self.lines(&self.specs[k].icon_text, inner_wrap)?;
            self.labels.push(label);
            self.icon_texts.push(inner);
        }
        for route in &self.input.routes {
            let measured = match self.label_of(&route.id) {
                Some(j) => self.lines(&self.input.labels[j].text, i32::MAX)?,
                None => Measured::default(),
            };
            self.edge_labels.push(measured);
        }
        Ok(())
    }

    fn label_of(&self, owner: &str) -> Option<usize> {
        self.input
            .labels
            .iter()
            .position(|label| label.owner == owner)
    }

    fn parent_of(&self, id: &str) -> Result<Option<usize>, LayoutError> {
        if id.is_empty() {
            return Ok(None);
        }
        self.group_index
            .get(id)
            .map(|g| Some(*g))
            .ok_or(LayoutError::Domain)
    }

    pub(super) fn grid_input(&self) -> Result<ArchInput, LayoutError> {
        let params = self.c.params;
        let line = params.line_height;
        let mut out = ArchInput::default();
        for (k, i) in self.group_at.iter().enumerate() {
            out.groups.push(ArchGroup {
                parent: self.parent_of(&self.input.boxes[*i].parent)?,
                title: self.titles[k].extent(line),
                icon: !self.group_specs[k].icon.is_empty(),
            });
        }
        for (k, i) in self.node_at.iter().enumerate() {
            let junction = self.specs[k].kind == "junction";
            let side = self.c.junction;
            out.nodes.push(ArchNode {
                parent: self.parent_of(&self.input.boxes[*i].parent)?,
                junction,
                icon: if junction {
                    Size { w: side, h: side }
                } else {
                    Size {
                        w: params.icon_w,
                        h: params.icon_h,
                    }
                },
                label: self.labels[k].extent(line),
            });
        }
        for (k, route) in self.input.routes.iter().enumerate() {
            let from = *self
                .node_index
                .get(route.from.as_str())
                .ok_or(LayoutError::Domain)?;
            let to = *self
                .node_index
                .get(route.to.as_str())
                .ok_or(LayoutError::Domain)?;
            out.edges.push(ArchEdge {
                from,
                to,
                from_side: route.from_side.ok_or(LayoutError::Domain)?,
                to_side: route.to_side.ok_or(LayoutError::Domain)?,
                label: self.edge_labels[k].extent(line),
            });
        }
        out.aligns = self.align_sets();
        Ok(out)
    }

    fn align_sets(&self) -> Vec<ArchAlign> {
        let mut sets: BTreeMap<usize, (bool, Vec<(usize, usize)>)> = BTreeMap::new();
        for (node, spec) in self.specs.iter().enumerate() {
            for AlignMember { set, pos, column } in &spec.aligns {
                let entry = sets.entry(*set).or_insert_with(|| (*column, Vec::new()));
                entry.0 = *column;
                entry.1.push((*pos, node));
            }
        }
        sets.into_values()
            .map(|(column, mut list)| {
                list.sort_unstable();
                ArchAlign {
                    column,
                    members: list.into_iter().map(|(_, node)| node).collect(),
                }
            })
            .collect()
    }

    pub(super) fn fill(&self, result: &ArchLayout) -> Result<Dump, LayoutError> {
        let mut dump = Dump::new(KIND, self.input.options.clone());
        let (mut groups, mut nodes) = (0usize, 0usize);
        for b in &self.input.boxes {
            let rect = if b.role == BoxRole::Group {
                groups += 1;
                result.frames[groups - 1]
            } else {
                nodes += 1;
                result.boxes[nodes - 1]
            };
            dump.boxes.push(SceneBox {
                id: b.id.clone(),
                role: b.role,
                rect,
                parent: b.parent.clone(),
                exclusive: b.exclusive,
            });
        }
        for (route, points) in self.input.routes.iter().zip(&result.routes) {
            dump.routes.push(SceneRoute {
                id: route.id.clone(),
                from: route.from.clone(),
                to: route.to.clone(),
                orthogonal: true,
                points: points.clone(),
                marker_start: route.marker_start.clone(),
                marker_end: route.marker_end.clone(),
                stroke: route.line.clone(),
            });
        }
        for label in &self.input.labels {
            let k = self
                .input
                .routes
                .iter()
                .position(|route| route.id == label.owner)
                .ok_or(LayoutError::Domain)?;
            let rect: Rect = result.edge_labels[k];
            dump.labels.push(SceneLabel {
                id: label.id.clone(),
                owner: label.owner.clone(),
                text: label.text.clone(),
                rect,
                lines: self.edge_labels[k].texts.clone(),
            });
        }
        Ok(dump)
    }
}
