//! Extent, canvas margin, and the integer frame of the gitgraph planner.

use crate::geom::{COORD_LIMIT, Point, Rect, Size};
use crate::layout::layered::LayoutError;
use crate::scene::Profile;

use super::gitgraph::{Area, GitGraphResult, Planner, Vec2};

pub(super) struct Frame {
    dx: i64,
    dy: i64,
    overflow: bool,
}

impl Frame {
    fn fit(&mut self, value: i64) -> i32 {
        if value.abs() > COORD_LIMIT {
            self.overflow = true;
            return 0;
        }
        i32::try_from(value).unwrap_or(0)
    }

    pub fn point(&mut self, at: Vec2) -> Point {
        Point {
            x: self.fit(at.x + self.dx),
            y: self.fit(at.y + self.dy),
        }
    }

    pub fn rect(&mut self, area: Area) -> Rect {
        Rect {
            x: self.fit(area.x + self.dx),
            y: self.fit(area.y + self.dy),
            w: self.fit(area.w),
            h: self.fit(area.h),
        }
    }

    fn points(&mut self, route: &[Vec2]) -> Vec<Point> {
        route.iter().map(|&at| self.point(at)).collect()
    }
}

impl Planner<'_> {
    pub fn is_cell(&self) -> bool {
        self.profile == Profile::Cell
    }

    fn point_area(&self, at: Vec2) -> Area {
        if self.is_cell() {
            return Area {
                x: at.x,
                y: at.y,
                w: 1,
                h: 1,
            };
        }
        Area {
            x: at.x,
            y: at.y,
            w: 0,
            h: 0,
        }
    }

    fn marker_area(&self, at: Vec2) -> Area {
        if self.is_cell() {
            return Area {
                x: at.x,
                y: at.y,
                w: 1,
                h: 1,
            };
        }
        let r = self.c.commit_radius;
        Area {
            x: at.x - r,
            y: at.y - r,
            w: 2 * r,
            h: 2 * r,
        }
    }

    fn extent(&self) -> Area {
        let mut all: Vec<Area> = Vec::new();
        for branch in 0..self.input.branches.len() {
            all.push(self.lanes[branch]);
            all.push(self.point_area(self.starts[branch]));
            all.push(self.point_area(self.ends[branch]));
            if self.shown_label(branch).is_some() {
                all.push(self.branches[branch]);
            }
        }
        let pad = self.c.tag_pad;
        for (index, commit) in self.input.commits.iter().enumerate() {
            all.push(self.marker_area(self.points[index]));
            if commit.label.is_some() {
                all.push(self.labels[index]);
            }
            for tag in &self.tags[index] {
                all.push(Area {
                    x: tag.x - pad,
                    y: tag.y - pad,
                    w: tag.w + 2 * pad,
                    h: tag.h + 2 * pad,
                });
            }
        }
        for route in &self.routes {
            for &at in route {
                all.push(self.point_area(at));
            }
        }
        all.into_iter().reduce(Area::union).unwrap_or_default()
    }

    pub fn result(&self) -> Result<GitGraphResult, LayoutError> {
        let extent = self.extent();
        let margin = self.c.canvas_margin;
        let mut frame = Frame {
            dx: margin - extent.x,
            dy: margin - extent.y,
            overflow: false,
        };
        let mut result = GitGraphResult {
            canvas: Size {
                w: frame.fit(extent.w + 2 * margin),
                h: frame.fit(extent.h + 2 * margin),
            },
            lanes: Vec::new(),
            points: Vec::new(),
            routes: Vec::new(),
            branch_labels: Vec::new(),
            commit_labels: Vec::new(),
            tag_labels: Vec::new(),
            groups: Vec::new(),
        };
        for branch in 0..self.input.branches.len() {
            result.lanes.push(frame.rect(self.lanes[branch]));
            result
                .branch_labels
                .push(frame.rect(self.branch_text(branch)));
        }
        for index in 0..self.input.commits.len() {
            result.points.push(frame.point(self.points[index]));
            result.commit_labels.push(frame.rect(self.labels[index]));
            let tags = self.tags[index]
                .iter()
                .map(|&tag| frame.rect(tag))
                .collect();
            result.tag_labels.push(tags);
        }
        for route in &self.routes {
            result.routes.push(frame.points(route));
        }
        if frame.overflow {
            return Err(LayoutError::Overflow);
        }
        result.groups = self.paint(&mut frame, &result);
        if frame.overflow {
            return Err(LayoutError::Overflow);
        }
        Ok(result)
    }

    fn branch_text(&self, branch: usize) -> Area {
        let Some(label) = self.shown_label(branch) else {
            return Area::default();
        };
        let outer = self.branches[branch];
        Area {
            x: outer.x + self.c.branch_pad_x,
            y: outer.y + self.c.branch_pad_y,
            w: i64::from(label.w),
            h: i64::from(label.h),
        }
    }
}
