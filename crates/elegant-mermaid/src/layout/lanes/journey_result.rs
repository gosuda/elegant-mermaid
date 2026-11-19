//! Extent, canvas margin, and the integer frame of the journey planner.

use crate::geom::{COORD_LIMIT, Point, Rect, Size};
use crate::layout::layered::LayoutError;
use crate::scene::Profile;

use super::gitgraph::{Area, Vec2};
use super::journey::{JourneyResult, Planner};

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

    fn point(&mut self, at: Vec2) -> Point {
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

    fn rects(&mut self, areas: &[Area]) -> Vec<Rect> {
        areas.iter().map(|&area| self.rect(area)).collect()
    }
}

impl Planner<'_> {
    pub fn is_cell(&self) -> bool {
        self.profile == Profile::Cell
    }

    fn face_area(&self, at: Vec2) -> Area {
        if self.is_cell() {
            return Area {
                x: at.x,
                y: at.y,
                w: 1,
                h: 1,
            };
        }
        let r = self.c.face_radius;
        Area {
            x: at.x - r,
            y: at.y - r,
            w: 2 * r,
            h: 2 * r,
        }
    }

    fn extent(&self) -> Area {
        let mut all: Vec<Area> = Vec::new();
        if self.input.title.is_some() {
            all.push(self.title);
        }
        all.extend(&self.frames);
        all.extend(&self.tasks);
        all.extend(self.faces.iter().map(|&at| self.face_area(at)));
        all.split_first()
            .map_or_else(Area::default, |(first, rest)| {
                rest.iter().fold(*first, |extent, area| extent.union(*area))
            })
    }

    pub fn result(&self) -> Result<JourneyResult, LayoutError> {
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
        let mut result = JourneyResult {
            canvas,
            title: Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            },
            frames: shift.rects(&self.frames),
            bands: shift.rects(&self.bands),
            tasks: shift.rects(&self.tasks),
            people: shift.rects(&self.people),
            faces: Vec::new(),
            groups: Vec::new(),
        };
        if self.input.title.is_some() {
            result.title = shift.rect(self.title);
        }
        result.faces = self.faces.iter().map(|&at| shift.point(at)).collect();
        if shift.overflow {
            return Err(LayoutError::Overflow);
        }
        result.groups = self.paint(&mut shift, &result);
        if shift.overflow {
            return Err(LayoutError::Overflow);
        }
        Ok(result)
    }
}
