//! The gitgraph adapter and family entry (`spec/layout/lanes.md`, Gitgraph).
//!
//! [`from_gitgraph`] authors the model-stage dump: one group box per branch, one
//! zero-size node box per commit, one route per parent link or cherry-pick, and label
//! records for branch names, commit ids, and tags. [`layout`] decodes that input again,
//! measures the texts, runs the lanes planner, and fills the dump coordinates.

use std::collections::{BTreeMap, BTreeSet};

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::geom::{GeomError, Rect};
use crate::measure::{self, Metric, Role};
use crate::model::gitgraph as mg;
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, DumpValue, Profile, Run, Scene, SceneBox, SceneLabel,
    SceneRoute, TextRole,
};

use super::input::{Box as InputBox, Input, Label as InputLabel, Route as InputRoute, Spacing};
use super::lanes::{self, Branch, Commit, GitGraphInput, GitGraphResult, Link, Text};
use super::layered::LayoutError;

const KIND: &str = "gitgraph";
const BRANCH_SHAPE: &str = "branch";
const SHOW_BRANCHES: &str = "showBranches";
const SHOW_COMMIT_IDS: &str = "showCommitLabel";
const ROTATE_LABELS: &str = "rotateCommitLabel";

pub(crate) fn from_gitgraph(
    model: &mg::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.config = model
        .config
        .iter()
        .map(|(key, value)| (key.clone(), DumpValue::Bool(*value)))
        .collect();
    options.profile = profile;
    let mut author = Author {
        model,
        input: Input {
            kind: KIND,
            profile,
            direction: direction_of(&model.direction),
            options,
            boxes: Vec::new(),
            routes: Vec::new(),
            labels: Vec::new(),
            groups: Vec::new(),
            sizes: Vec::new(),
            attachments: Vec::new(),
            region_sets: Vec::new(),
            spacing: Spacing::default(),
        },
        used: BTreeSet::new(),
        lane_ids: Vec::new(),
        commit_ids: Vec::new(),
        commit_at: BTreeMap::new(),
    };
    author.lanes();
    author.commits();
    author.links();
    author.labels();
    Ok(author.input)
}

fn direction_of(name: &str) -> Direction {
    match name {
        "LR" => Direction::Lr,
        "TB" => Direction::Tb,
        "BT" => Direction::Bt,
        _ => Direction::Rl,
    }
}

fn config_flag(options: &DumpOptions, key: &str, fallback: bool) -> bool {
    match options.config.get(key) {
        Some(DumpValue::Bool(value)) => *value,
        _ => fallback,
    }
}

struct Author<'m> {
    model: &'m mg::Model,
    input: Input,
    used: BTreeSet<String>,
    lane_ids: Vec<String>,
    commit_ids: Vec<String>,
    commit_at: BTreeMap<String, usize>,
}

fn commit_shape(commit: &mg::Commit) -> String {
    if commit.kind == mg::CommitKind::CherryPick {
        return "cherry-pick".to_owned();
    }
    let base = if commit.kind == mg::CommitKind::Merge {
        "merge"
    } else {
        "commit"
    };
    let variant = match commit.commit_type {
        mg::CommitType::Reverse => "reverse",
        mg::CommitType::Highlight => "highlight",
        mg::CommitType::Normal => return base.to_owned(),
    };
    if base == "commit" {
        variant.to_owned()
    } else {
        format!("{base}-{variant}")
    }
}

impl Author<'_> {
    fn unique(&mut self, wanted: &str) -> String {
        let mut candidate = wanted.to_owned();
        let mut ordinal = 1;
        while !self.used.insert(candidate.clone()) {
            candidate = format!("{wanted}~{ordinal}");
            ordinal += 1;
        }
        candidate
    }

    fn lanes(&mut self) {
        for (index, branch) in self.model.branches.iter().enumerate() {
            let id = self.unique(&format!("lane{index}"));
            self.lane_ids.push(id.clone());
            let mut shape = BRANCH_SHAPE.to_owned();
            if branch.has_order {
                shape.push_str(&format!(":{}", branch.order));
            }
            self.input.boxes.push(InputBox {
                icon: false,
                id,
                role: BoxRole::Group,
                shape,
                parent: String::new(),
                exclusive: false,
                text: branch.name.clone(),
                direction: String::new(),
            });
        }
    }

    fn commits(&mut self) {
        for (index, commit) in self.model.commits.iter().enumerate() {
            let id = self.unique(&commit.id);
            self.commit_ids.push(id.clone());
            self.commit_at.insert(commit.id.clone(), index);
            self.input.boxes.push(InputBox {
                icon: false,
                id: id.clone(),
                role: BoxRole::Node,
                shape: commit_shape(commit),
                parent: self.lane_ids[commit.branch].clone(),
                exclusive: true,
                text: id,
                direction: String::new(),
            });
        }
    }

    fn links(&mut self) {
        for (to, commit) in self.model.commits.iter().enumerate() {
            for parent in &commit.parents {
                if let Some(&from) = self.commit_at.get(parent)
                    && from < to
                {
                    self.link(from, to, "normal");
                }
            }
            if commit.pick.is_empty() {
                continue;
            }
            if let Some(&from) = self.commit_at.get(&commit.pick)
                && from != to
            {
                self.link(from, to, "dotted");
            }
        }
    }

    fn link(&mut self, from: usize, to: usize, line: &str) {
        let id = self.unique(&format!("e{}", self.input.routes.len()));
        self.input.routes.push(InputRoute {
            id,
            from: self.commit_ids[from].clone(),
            to: self.commit_ids[to].clone(),
            orthogonal: true,
            marker_start: String::new(),
            marker_end: String::new(),
            line: line.to_owned(),
            min_length: 1,
            from_side: None,
            to_side: None,
        });
    }

    fn labels(&mut self) {
        if config_flag(&self.input.options, SHOW_BRANCHES, true) {
            for (index, branch) in self.model.branches.iter().enumerate() {
                let owner = self.lane_ids[index].clone();
                self.label(&owner, ".label", TextRole::Label, &branch.name);
            }
        }
        let commit_labels = config_flag(&self.input.options, SHOW_COMMIT_IDS, true);
        for (index, commit) in self.model.commits.iter().enumerate() {
            let owner = self.commit_ids[index].clone();
            if commit_labels {
                self.label(&owner, ".label", TextRole::Body, &commit.id);
            }
            for (k, tag) in commit.tags.iter().enumerate() {
                self.label(&owner, &format!(".tag{k}"), TextRole::Body, tag);
            }
        }
    }

    fn label(&mut self, owner: &str, suffix: &str, role: TextRole, text: &str) {
        let id = self.unique(&format!("{owner}{suffix}"));
        self.input.labels.push(InputLabel {
            id,
            owner: owner.to_owned(),
            role,
            text: text.to_owned(),
        });
    }
}

#[derive(Clone, Copy)]
enum Slot {
    Branch(usize),
    Commit(usize),
    Tag(usize, usize),
}

struct Decoded {
    graph: GitGraphInput,
    slots: Vec<Slot>,
}

fn lane_order(shape: &str) -> i64 {
    shape
        .strip_prefix("branch:")
        .and_then(|order| order.parse::<i64>().ok())
        .unwrap_or(0)
}

fn commit_kind(shape: &str) -> String {
    if shape.is_empty() {
        "commit".to_owned()
    } else {
        shape.to_owned()
    }
}

fn decode(input: &Input) -> Result<Decoded, LayoutError> {
    let mut decoded = Decoded {
        graph: GitGraphInput {
            direction: input.direction,
            show_branches: config_flag(&input.options, SHOW_BRANCHES, true),
            rotate_labels: config_flag(&input.options, ROTATE_LABELS, true),
            branches: Vec::new(),
            commits: Vec::new(),
            links: Vec::new(),
        },
        slots: Vec::new(),
    };
    let mut lane_at: BTreeMap<&str, usize> = BTreeMap::new();
    let mut commit_at: BTreeMap<&str, usize> = BTreeMap::new();
    for item in &input.boxes {
        if item.role == BoxRole::Group {
            lane_at.insert(&item.id, decoded.graph.branches.len());
            decoded.graph.branches.push(Branch {
                id: item.id.clone(),
                order: lane_order(&item.shape),
                label: None,
            });
            continue;
        }
        let lane = *lane_at.entry(&item.parent).or_insert_with(|| {
            decoded.graph.branches.push(Branch {
                id: item.parent.clone(),
                order: 0,
                label: None,
            });
            decoded.graph.branches.len() - 1
        });
        commit_at.insert(&item.id, decoded.graph.commits.len());
        decoded.graph.commits.push(Commit {
            id: item.id.clone(),
            branch: lane,
            kind: commit_kind(&item.shape),
            label: None,
            tags: Vec::new(),
        });
    }
    for route in &input.routes {
        let from = commit_at.get(route.from.as_str()).copied();
        let to = commit_at.get(route.to.as_str()).copied();
        let (Some(from), Some(to)) = (from, to) else {
            return Err(LayoutError::Domain);
        };
        decoded.graph.links.push(Link {
            id: route.id.clone(),
            from,
            to,
            pick: route.line == "dotted",
        });
    }
    decoded.attach(input, &lane_at, &commit_at)?;
    Ok(decoded)
}

impl Decoded {
    fn attach(
        &mut self,
        input: &Input,
        lane_at: &BTreeMap<&str, usize>,
        commit_at: &BTreeMap<&str, usize>,
    ) -> Result<(), LayoutError> {
        let commit_labels = config_flag(&input.options, SHOW_COMMIT_IDS, true);
        for label in &input.labels {
            let text = measure_text(input.profile, label)?;
            if let Some(&lane) = lane_at.get(label.owner.as_str()) {
                self.graph.branches[lane].label = Some(text);
                self.slots.push(Slot::Branch(lane));
                continue;
            }
            let Some(&at) = commit_at.get(label.owner.as_str()) else {
                return Err(LayoutError::Domain);
            };
            let commit = &mut self.graph.commits[at];
            if commit_labels && commit.label.is_none() {
                commit.label = Some(text);
                self.slots.push(Slot::Commit(at));
                continue;
            }
            self.slots.push(Slot::Tag(at, commit.tags.len()));
            commit.tags.push(text);
        }
        Ok(())
    }

    fn label_geometry<'a>(
        &'a self,
        slot: Slot,
        result: &GitGraphResult,
    ) -> Option<(Rect, &'a Text)> {
        match slot {
            Slot::Branch(branch) => Some((
                result.branch_labels[branch],
                self.graph.branches[branch].label.as_ref()?,
            )),
            Slot::Commit(commit) => Some((
                result.commit_labels[commit],
                self.graph.commits[commit].label.as_ref()?,
            )),
            Slot::Tag(commit, tag) => Some((
                result.tag_labels[commit][tag],
                &self.graph.commits[commit].tags[tag],
            )),
        }
    }
}

fn line_height(profile: Profile) -> Result<i32, LayoutError> {
    let key = format!("{}.line_h", profile.as_str());
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(LayoutError::Domain)
}

fn measure_text(profile: Profile, label: &InputLabel) -> Result<Text, LayoutError> {
    let height = line_height(profile)?;
    let metric = if profile == Profile::Cell {
        Metric::cell()
    } else if label.role == TextRole::Body {
        Metric::for_role(Role::Body)
    } else {
        Metric::for_role(Role::Label)
    };
    let lines =
        measure::styled_lines(&label.text, i32::MAX, metric).map_err(|_| LayoutError::Overflow)?;
    let widest = lines.iter().map(|line| line.width).max().unwrap_or(0);
    let count = i32::try_from(lines.len()).map_err(|_| LayoutError::Overflow)?;
    Ok(Text {
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
        lines: lines.iter().map(|line| line.text.clone()).collect(),
        w: widest,
        h: count.checked_mul(height).ok_or(LayoutError::Overflow)?,
        role: label.role,
    })
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let decoded = decode(input)?;
    let result = lanes::git_graph(&decoded.graph, input.profile)?;
    let dump = decoded.dump(input, &result)?;
    Ok((Scene::new(result.canvas, dump, result.groups), false))
}

impl Decoded {
    fn dump(&self, input: &Input, result: &GitGraphResult) -> Result<Dump, LayoutError> {
        let mut options = input.options.clone();
        options.profile = input.profile;
        options.direction = input.direction;
        let mut dump = Dump::new(KIND, options);
        let (mut lane, mut commit) = (0, 0);
        for item in &input.boxes {
            let rect = if item.role == BoxRole::Group {
                lane += 1;
                result.lanes[lane - 1]
            } else {
                commit += 1;
                let at = result.points[commit - 1];
                Rect {
                    x: at.x,
                    y: at.y,
                    w: 0,
                    h: 0,
                }
            };
            dump.boxes.push(SceneBox {
                id: item.id.clone(),
                role: item.role,
                rect,
                parent: item.parent.clone(),
                exclusive: item.exclusive,
            });
        }
        for (index, route) in input.routes.iter().enumerate() {
            dump.routes.push(SceneRoute {
                id: route.id.clone(),
                from: route.from.clone(),
                to: route.to.clone(),
                orthogonal: route.orthogonal,
                points: result.routes[index].clone(),
                marker_start: route.marker_start.clone(),
                marker_end: route.marker_end.clone(),
                stroke: route.line.clone(),
            });
        }
        for (index, label) in input.labels.iter().enumerate() {
            let (rect, text) = self
                .label_geometry(self.slots[index], result)
                .ok_or(LayoutError::Domain)?;
            dump.labels.push(SceneLabel {
                id: label.id.clone(),
                owner: label.owner.clone(),
                text: label.text.clone(),
                rect,
                lines: text.lines.clone(),
            });
        }
        Ok(dump)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
