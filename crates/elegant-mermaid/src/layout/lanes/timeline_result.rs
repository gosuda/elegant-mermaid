//! Extent, canvas margin, and the integer frame of the timeline planner.

use crate::geom::{COORD_LIMIT, Point, Rect, Size};
use crate::layout::layered::LayoutError;
use crate::scene::Profile;

use super::gitgraph::{Area, Vec2};
use super::timeline::{Planner, TimelineResult};

pub(super) struct Shift {
    dx: i64,
    dy: i64,
    overflow: bool,
}

impl Shift {
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

    pub fn overflowed(&self) -> bool {
        self.overflow
    }
}

impl Planner<'_> {
    pub fn is_cell(&self) -> bool {
        self.profile == Profile::Cell
    }

    fn point_area(&self, at: Vec2) -> Area {
        let side = i64::from(self.is_cell());
        Area {
            x: at.x,
            y: at.y,
            w: side,
            h: side,
        }
    }

    fn extent(&self) -> Area {
        let mut extent = self.point_area(self.axis[0]);
        extent = extent.union(self.point_area(self.axis[1]));
        if self.input.title.is_some() {
            extent = extent.union(self.title);
        }
        for area in &self.sections {
            extent = extent.union(*area);
        }
        for (i, period) in self.periods.iter().enumerate() {
            extent = extent.union(*period);
            for area in &self.events[i] {
                extent = extent.union(*area);
            }
            for &at in self.routes[i].iter().flatten() {
                extent = extent.union(self.point_area(at));
            }
        }
        extent
    }

    pub fn result(&self) -> Result<TimelineResult, LayoutError> {
        let extent = self.extent();
        let margin = self.c.canvas_margin;
        let mut shift = Shift {
            dx: margin - extent.x,
            dy: margin - extent.y,
            overflow: false,
        };
        let canvas = Size {
            w: shift.fit(extent.w + 2 * margin),
            h: shift.fit(extent.h + 2 * margin),
        };
        let title = if self.input.title.is_some() {
            shift.rect(self.title)
        } else {
            Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            }
        };
        let sections = self.sections.iter().map(|&a| shift.rect(a)).collect();
        let mut periods = Vec::new();
        let mut events = Vec::new();
        let mut routes = Vec::new();
        for (i, period) in self.periods.iter().enumerate() {
            periods.push(shift.rect(*period));
            events.push(self.events[i].iter().map(|&a| shift.rect(a)).collect());
            routes.push(self.routes[i].iter().map(|r| shift.points(r)).collect());
        }
        if shift.overflowed() {
            return Err(LayoutError::Overflow);
        }
        let mut result = TimelineResult {
            canvas,
            title,
            sections,
            periods,
            events,
            routes,
            groups: Vec::new(),
        };
        result.groups = self.paint(&mut shift, &result);
        if shift.overflowed() {
            return Err(LayoutError::Overflow);
        }
        Ok(result)
    }
}
