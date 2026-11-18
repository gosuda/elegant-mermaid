//! The gitgraph planner of the lanes family (`spec/layout/lanes.md`, Gitgraph).
//!
//! Lanes sort by `(order, declaration index)`, a commit sits at the level of its longest
//! parent chain, and every commit box has zero size. Under `LR` the gap between levels
//! grows with the label widths and the gap between lanes with the label and tag bands.
//! `TB` and `BT` transpose the two axes and widen the lane pitch by the side text extent.

use crate::geom::{Point, Rect, Size};
use crate::layout::layered::LayoutError;
use crate::scene::{Direction, Group, Profile, Run, TextRole};

use super::constants::{GitgraphConstants, load_gitgraph};

#[derive(Debug, Clone)]
pub(crate) struct Text {
    pub runs: Vec<Vec<Run>>,
    pub lines: Vec<String>,
    pub w: i32,
    pub h: i32,
    pub role: TextRole,
}

#[derive(Debug, Clone)]
pub(crate) struct Branch {
    pub id: String,
    pub order: i64,
    pub label: Option<Text>,
}

#[derive(Debug, Clone)]
pub(crate) struct Commit {
    pub id: String,
    pub branch: usize,
    pub kind: String,
    pub label: Option<Text>,
    pub tags: Vec<Text>,
}

#[derive(Debug, Clone)]
pub(crate) struct Link {
    pub id: String,
    pub from: usize,
    pub to: usize,
    pub pick: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct GitGraphInput {
    pub direction: Direction,
    pub show_branches: bool,
    pub rotate_labels: bool,
    pub branches: Vec<Branch>,
    pub commits: Vec<Commit>,
    pub links: Vec<Link>,
}

#[derive(Debug)]
pub(crate) struct GitGraphResult {
    pub canvas: Size,
    pub lanes: Vec<Rect>,
    pub points: Vec<Point>,
    pub routes: Vec<Vec<Point>>,
    pub branch_labels: Vec<Rect>,
    pub commit_labels: Vec<Rect>,
    pub tag_labels: Vec<Vec<Rect>>,
    pub groups: Vec<Group>,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Vec2 {
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Area {
    pub x: i64,
    pub y: i64,
    pub w: i64,
    pub h: i64,
}

impl Area {
    pub fn right(self) -> i64 {
        self.x + self.w
    }

    pub fn bottom(self) -> i64 {
        self.y + self.h
    }

    pub fn union(self, other: Area) -> Area {
        let x = self.x.min(other.x);
        let y = self.y.min(other.y);
        Area {
            x,
            y,
            w: self.right().max(other.right()) - x,
            h: self.bottom().max(other.bottom()) - y,
        }
    }
}

pub(super) fn half(value: i64) -> i64 {
    value.div_euclid(2)
}

pub(super) struct Planner<'a> {
    pub input: &'a GitGraphInput,
    pub c: GitgraphConstants,
    pub profile: Profile,
    pub rank: Vec<usize>,
    pub by_rank: Vec<usize>,
    pub lane_at: Vec<i64>,
    pub level: Vec<usize>,
    pub reach: Vec<i64>,
    pub step: Vec<i64>,
    pub max_step: i64,
    pub pitch: i64,
    pub points: Vec<Vec2>,
    pub routes: Vec<Vec<Vec2>>,
    pub lanes: Vec<Area>,
    pub branches: Vec<Area>,
    pub labels: Vec<Area>,
    pub tags: Vec<Vec<Area>>,
    pub starts: Vec<Vec2>,
    pub ends: Vec<Vec2>,
}

pub(crate) fn git_graph(
    input: &GitGraphInput,
    profile: Profile,
) -> Result<GitGraphResult, LayoutError> {
    if input.direction == Direction::Rl {
        return Err(LayoutError::Domain);
    }
    let mut planner = Planner {
        input,
        c: load_gitgraph(profile)?,
        profile,
        rank: Vec::new(),
        by_rank: Vec::new(),
        lane_at: Vec::new(),
        level: Vec::new(),
        reach: Vec::new(),
        step: Vec::new(),
        max_step: 0,
        pitch: 0,
        points: Vec::new(),
        routes: Vec::new(),
        lanes: Vec::new(),
        branches: Vec::new(),
        labels: Vec::new(),
        tags: Vec::new(),
        starts: Vec::new(),
        ends: Vec::new(),
    };
    planner.rank_lanes();
    planner.advance();
    planner.measure_pitch();
    planner.measure_lanes();
    planner.place_commits();
    planner.place_lanes();
    planner.place_routes();
    planner.result()
}

impl Planner<'_> {
    fn rank_lanes(&mut self) {
        let mut order: Vec<usize> = (0..self.input.branches.len()).collect();
        order.sort_by_key(|&branch| (self.input.branches[branch].order, branch));
        self.rank = vec![0; order.len()];
        for (position, &branch) in order.iter().enumerate() {
            self.rank[branch] = position;
        }
        self.by_rank = order;
    }

    fn advance(&mut self) {
        let count = self.input.commits.len();
        let mut parents: Vec<Vec<usize>> = vec![Vec::new(); count];
        for link in &self.input.links {
            if !link.pick && link.from < link.to {
                parents[link.to].push(link.from);
            }
        }
        self.level = vec![0; count];
        let mut last_on_lane: Vec<Option<usize>> = vec![None; self.input.branches.len()];
        let mut levels = 0;
        for (index, from) in parents.iter().enumerate() {
            let branch = self.input.commits[index].branch;
            self.level[index] = last_on_lane[branch].map_or(0, |level| level + 1);
            for &parent in from {
                self.level[index] = self.level[index].max(self.level[parent] + 1);
            }
            last_on_lane[branch] = Some(self.level[index]);
            levels = levels.max(self.level[index] + 1);
        }
        self.reach = self.level_reach(levels);
        let axis = self.level_axis(levels);
        self.step = self.level.iter().map(|&level| axis[level]).collect();
        self.max_step = axis.last().copied().unwrap_or(0);
    }

    fn level_reach(&self, levels: usize) -> Vec<i64> {
        let mut reach = vec![0; levels];
        if self.vertical() {
            return reach;
        }
        for (index, commit) in self.input.commits.iter().enumerate() {
            let level = self.level[index];
            reach[level] = reach[level].max(self.text_width(commit));
        }
        reach
    }

    fn level_axis(&self, levels: usize) -> Vec<i64> {
        let mut axis = vec![0; levels];
        for level in 1..levels {
            axis[level] =
                axis[level - 1] + self.level_gap(self.reach[level - 1], self.reach[level]);
        }
        axis
    }

    fn level_gap(&self, before: i64, after: i64) -> i64 {
        if self.vertical() {
            return self.c.commit_step;
        }
        self.c
            .commit_step
            .max(half(before + after + 1) + self.c.label_gap)
    }

    fn text_width(&self, commit: &Commit) -> i64 {
        let label = commit.label.as_ref().map_or(0, |text| i64::from(text.w));
        commit.tags.iter().fold(label, |widest, tag| {
            widest.max(i64::from(tag.w) + 2 * self.c.tag_pad)
        })
    }

    fn turn_back(&self, commit: usize) -> i64 {
        let back = half(self.c.commit_step);
        if self.vertical() {
            return back;
        }
        back.max(half(self.reach[self.level[commit]]) + half(self.c.label_gap + 1))
    }

    pub fn vertical(&self) -> bool {
        self.input.direction != Direction::Lr
    }

    fn at(&self, commit_axis: i64, lane_axis: i64) -> Vec2 {
        match self.input.direction {
            Direction::Tb => Vec2 {
                x: lane_axis,
                y: commit_axis,
            },
            Direction::Bt => Vec2 {
                x: lane_axis,
                y: self.max_step - commit_axis,
            },
            _ => Vec2 {
                x: commit_axis,
                y: lane_axis,
            },
        }
    }

    fn lane_axis(&self, branch: usize) -> i64 {
        self.lane_at[branch]
    }

    fn measure_pitch(&mut self) {
        self.pitch = self.c.lane_pitch;
        if self.input.rotate_labels {
            self.pitch += self.c.rotation_extra;
        }
        if !self.vertical() {
            return;
        }
        let widest = self
            .input
            .commits
            .iter()
            .map(|commit| self.side_extent(commit))
            .max()
            .unwrap_or(0);
        self.pitch = (self.pitch + widest).max(self.widest_plate() + self.c.label_gap);
    }

    fn widest_plate(&self) -> i64 {
        (0..self.input.branches.len())
            .filter_map(|branch| self.shown_label(branch))
            .map(|label| i64::from(label.w) + 2 * self.c.branch_pad_x)
            .max()
            .unwrap_or(0)
    }

    fn measure_lanes(&mut self) {
        self.lane_at = vec![0; self.by_rank.len()];
        for position in 1..self.by_rank.len() {
            let (upper, lower) = (self.by_rank[position - 1], self.by_rank[position]);
            self.lane_at[lower] = self.lane_at[upper] + self.lane_gap(upper, lower);
        }
    }

    fn lane_gap(&self, upper: usize, lower: usize) -> i64 {
        if self.vertical() {
            return self.pitch;
        }
        self.pitch
            .max(self.label_band(upper) + self.tag_band(lower))
    }

    fn label_band(&self, branch: usize) -> i64 {
        self.input
            .commits
            .iter()
            .filter(|commit| commit.branch == branch)
            .filter_map(|commit| commit.label.as_ref())
            .map(|text| self.c.label_offset + i64::from(text.h))
            .max()
            .unwrap_or(0)
    }

    fn tag_band(&self, branch: usize) -> i64 {
        self.input
            .commits
            .iter()
            .filter(|commit| commit.branch == branch && !commit.tags.is_empty())
            .map(|commit| self.c.tag_offset + self.c.tag_pad + self.tag_stack(&commit.tags))
            .max()
            .unwrap_or(0)
    }

    fn tag_stack(&self, tags: &[Text]) -> i64 {
        let gaps = i64::try_from(tags.len().saturating_sub(1)).unwrap_or(0);
        tags.iter().map(|tag| i64::from(tag.h)).sum::<i64>() + 2 * self.c.tag_pad * gaps
    }

    fn lane_end_clearance(&self) -> i64 {
        i64::from(self.is_cell())
    }

    fn side_extent(&self, commit: &Commit) -> i64 {
        let (label, tags) = self.place_beside(commit, Vec2::default());
        let mut extent = if commit.label.is_some() {
            label.right()
        } else {
            0
        };
        for tag in tags {
            extent = extent.max(tag.right());
        }
        extent
    }

    fn place_commits(&mut self) {
        let count = self.input.commits.len();
        self.points = Vec::with_capacity(count);
        self.labels = Vec::with_capacity(count);
        self.tags = Vec::with_capacity(count);
        for (index, commit) in self.input.commits.iter().enumerate() {
            let at = self.at(self.step[index], self.lane_axis(commit.branch));
            let (label, tags) = self.place_texts(commit, at);
            self.points.push(at);
            self.labels.push(label);
            self.tags.push(tags);
        }
    }

    fn place_texts(&self, commit: &Commit, at: Vec2) -> (Area, Vec<Area>) {
        if self.vertical() {
            return self.place_beside(commit, at);
        }
        let label = commit.label.as_ref().map_or_else(Area::default, |text| {
            let (w, h) = (i64::from(text.w), i64::from(text.h));
            Area {
                x: at.x - half(w),
                y: at.y + self.c.label_offset,
                w,
                h,
            }
        });
        let mut raised = 0;
        let tags = commit
            .tags
            .iter()
            .map(|tag| {
                let (w, h) = (i64::from(tag.w), i64::from(tag.h));
                let area = Area {
                    x: at.x - half(w),
                    y: at.y - self.c.tag_offset - raised - h,
                    w,
                    h,
                };
                raised += h + 2 * self.c.tag_pad;
                area
            })
            .collect();
        (label, tags)
    }

    fn place_beside(&self, commit: &Commit, at: Vec2) -> (Area, Vec<Area>) {
        let mut cursor = self.c.label_offset;
        let mut label = Area::default();
        if let Some(text) = &commit.label {
            let (w, h) = (i64::from(text.w), i64::from(text.h));
            label = Area {
                x: at.x + cursor,
                y: at.y - half(h),
                w,
                h,
            };
            cursor += w + self.c.label_offset;
        }
        let tags = commit
            .tags
            .iter()
            .map(|tag| {
                let (w, h) = (i64::from(tag.w), i64::from(tag.h));
                let area = Area {
                    x: at.x + cursor,
                    y: at.y - half(h),
                    w,
                    h,
                };
                cursor += w + self.c.label_offset;
                area
            })
            .collect();
        (label, tags)
    }

    pub fn shown_label(&self, branch: usize) -> Option<&Text> {
        if !self.input.show_branches {
            return None;
        }
        self.input.branches[branch].label.as_ref()
    }

    fn place_lanes(&mut self) {
        let count = self.input.branches.len();
        self.lanes = vec![Area::default(); count];
        self.branches = vec![Area::default(); count];
        self.starts = vec![Vec2::default(); count];
        self.ends = vec![Vec2::default(); count];
        let start = -self.c.label_gap;
        let end = self.max_step + half(self.c.commit_step);
        for branch in 0..count {
            let lane = self.lane_axis(branch);
            let (from, to) = (self.at(start, lane), self.at(end, lane));
            self.starts[branch] = from;
            self.ends[branch] = to;
            self.lanes[branch] = lane_band(from, to);
            if let Some(label) = self.shown_label(branch) {
                let w = i64::from(label.w) + 2 * self.c.branch_pad_x;
                let h = i64::from(label.h) + 2 * self.c.branch_pad_y;
                self.branches[branch] = self.anchor_label(from, w, h);
            }
        }
    }

    fn anchor_label(&self, from: Vec2, w: i64, h: i64) -> Area {
        match self.input.direction {
            Direction::Tb => Area {
                x: from.x - half(w),
                y: from.y - h,
                w,
                h,
            },
            Direction::Bt => Area {
                x: from.x - half(w),
                y: from.y + self.lane_end_clearance(),
                w,
                h,
            },
            _ => Area {
                x: from.x - w,
                y: from.y - half(h),
                w,
                h,
            },
        }
    }

    fn place_routes(&mut self) {
        self.routes = self
            .input
            .links
            .iter()
            .map(|link| self.route(link))
            .collect();
    }

    fn route(&self, link: &Link) -> Vec<Vec2> {
        let from = &self.input.commits[link.from];
        let to = &self.input.commits[link.to];
        let (from_lane, to_lane) = (self.lane_axis(from.branch), self.lane_axis(to.branch));
        let (start, end) = (self.step[link.from], self.step[link.to]);
        if from.branch == to.branch {
            return vec![self.at(start, from_lane), self.at(end, to_lane)];
        }
        let turn = end - self.turn_back(link.to);
        vec![
            self.at(start, from_lane),
            self.at(turn, from_lane),
            self.at(turn, to_lane),
            self.at(end, to_lane),
        ]
    }
}

fn lane_band(from: Vec2, to: Vec2) -> Area {
    Area {
        x: from.x.min(to.x),
        y: from.y.min(to.y),
        w: (to.x - from.x).abs(),
        h: (to.y - from.y).abs(),
    }
}
