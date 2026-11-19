//! The timeline planner of the lanes family (`spec/layout/lanes.md`, Timeline).
//!
//! Periods take consecutive slot columns, sections first-come after the periods that
//! precede the first section. A section band spans its periods, and an empty section keeps
//! one slot. Events stack under their period. `TD` puts the periods in one column, the
//! events in a second column, and an axis between the two.

use crate::geom::{Point, Rect, Size};
use crate::layout::layered::LayoutError;
use crate::scene::{Direction, Group, Profile};

use super::gitgraph::{Area, Text, Vec2, half};
use super::timeline_constants::{TimelineConstants, load_timeline};

#[derive(Debug, Clone)]
pub(crate) struct TimelineTitle {
    pub id: String,
    pub label: Text,
}

#[derive(Debug, Clone)]
pub(crate) struct TimelineSection {
    pub id: String,
    pub label: Text,
}

#[derive(Debug, Clone)]
pub(crate) struct TimelineEvent {
    pub id: String,
    pub link: String,
    pub label: Text,
}

#[derive(Debug, Clone)]
pub(crate) struct TimelinePeriod {
    pub id: String,
    pub section: Option<usize>,
    pub label: Text,
    pub events: Vec<TimelineEvent>,
}

#[derive(Debug, Clone)]
pub(crate) struct TimelineInput {
    pub direction: Direction,
    pub title: Option<TimelineTitle>,
    pub sections: Vec<TimelineSection>,
    pub periods: Vec<TimelinePeriod>,
}

#[derive(Debug)]
pub(crate) struct TimelineResult {
    pub canvas: Size,
    pub title: Rect,
    pub sections: Vec<Rect>,
    pub periods: Vec<Rect>,
    pub events: Vec<Vec<Rect>>,
    pub routes: Vec<Vec<Vec<Point>>>,
    pub groups: Vec<Group>,
}

pub(super) struct Planner<'a> {
    pub input: &'a TimelineInput,
    pub c: TimelineConstants,
    pub profile: Profile,
    pub slot: Vec<usize>,
    pub first: Vec<usize>,
    pub span: Vec<usize>,
    pub card_w: i64,
    pub period_h: i64,
    pub section_h: i64,
    pub title: Area,
    pub sections: Vec<Area>,
    pub periods: Vec<Area>,
    pub events: Vec<Vec<Area>>,
    pub routes: Vec<Vec<Vec<Vec2>>>,
    pub axis: [Vec2; 2],
}

pub(crate) fn timeline(
    input: &TimelineInput,
    profile: Profile,
) -> Result<TimelineResult, LayoutError> {
    let periods = input.periods.len();
    let mut planner = Planner {
        input,
        c: load_timeline(profile)?,
        profile,
        slot: vec![0; periods],
        first: vec![0; input.sections.len()],
        span: vec![0; input.sections.len()],
        card_w: 0,
        period_h: 0,
        section_h: 0,
        title: Area::default(),
        sections: Vec::new(),
        periods: Vec::new(),
        events: Vec::new(),
        routes: Vec::new(),
        axis: [Vec2::default(); 2],
    };
    planner.assign()?;
    planner.size();
    planner.place();
    planner.result()
}

impl Planner<'_> {
    pub fn vertical(&self) -> bool {
        self.input.direction != Direction::Lr
    }

    fn assign(&mut self) -> Result<(), LayoutError> {
        let sections = self.input.sections.len();
        if self
            .input
            .periods
            .iter()
            .any(|period| period.section.is_some_and(|section| section >= sections))
        {
            return Err(LayoutError::Domain);
        }
        let mut next = self.fill(None, 0);
        for section in 0..sections {
            self.first[section] = next;
            self.span[section] = (self.fill(Some(section), next) - next).max(1);
            next += self.span[section];
        }
        Ok(())
    }

    fn fill(&mut self, section: Option<usize>, base: usize) -> usize {
        let input = self.input;
        let mut n = base;
        for (i, period) in input.periods.iter().enumerate() {
            if period.section == section {
                self.slot[i] = n;
                n += 1;
            }
        }
        n
    }

    fn members(&self, section: Option<usize>) -> Vec<usize> {
        self.input
            .periods
            .iter()
            .enumerate()
            .filter(|(_, period)| period.section == section)
            .map(|(i, _)| i)
            .collect()
    }

    fn band_slots(&self, section: usize) -> i64 {
        if self.vertical() {
            return 1;
        }
        i64::try_from(self.span[section]).unwrap_or(1)
    }

    fn size(&mut self) {
        let input = self.input;
        let pad = 2 * self.c.card_padding;
        self.card_w = self.c.card_width;
        for period in &input.periods {
            self.card_w = self.card_w.max(i64::from(period.label.w) + pad);
            self.period_h = self.period_h.max(i64::from(period.label.h) + pad);
            for event in &period.events {
                self.card_w = self.card_w.max(i64::from(event.label.w) + pad);
            }
        }
        for (s, section) in input.sections.iter().enumerate() {
            let n = self.band_slots(s);
            let need = i64::from(section.label.w) + pad - (n - 1) * self.c.column_gap;
            if need > 0 {
                self.card_w = self.card_w.max((need + n - 1).div_euclid(n));
            }
            self.section_h = self.section_h.max(i64::from(section.label.h) + pad);
        }
    }

    fn content_top(&self) -> i64 {
        self.input
            .title
            .as_ref()
            .map_or(0, |title| i64::from(title.label.h) + self.c.event_gap)
    }

    fn event_height(&self, event: &TimelineEvent) -> i64 {
        i64::from(event.label.h) + 2 * self.c.card_padding
    }

    fn place(&mut self) {
        let sections = self.input.sections.len();
        let periods = self.input.periods.len();
        self.sections = vec![Area::default(); sections];
        self.periods = vec![Area::default(); periods];
        self.events = vec![Vec::new(); periods];
        self.routes = vec![Vec::new(); periods];
        let (left, right) = if self.vertical() {
            self.place_vertical()
        } else {
            self.place_horizontal()
        };
        if let Some(title) = &self.input.title {
            let w = i64::from(title.label.w);
            self.title = Area {
                x: left + half(right - left - w),
                y: 0,
                w,
                h: i64::from(title.label.h),
            };
        }
    }

    fn place_horizontal(&mut self) -> (i64, i64) {
        let top = self.content_top();
        let mut period_top = top;
        if !self.input.sections.is_empty() {
            period_top += self.section_h + self.c.section_gap;
        }
        let pitch = self.card_w + self.c.column_gap;
        let left = self.c.left_margin;
        let column = move |slot: usize| left + i64::try_from(slot).unwrap_or(0) * pitch;
        let mut right = left;
        for s in 0..self.input.sections.len() {
            let n = i64::try_from(self.span[s]).unwrap_or(1);
            let area = Area {
                x: column(self.first[s]),
                y: top,
                w: n * pitch - self.c.column_gap,
                h: self.section_h,
            };
            right = right.max(area.right());
            self.sections[s] = area;
        }
        let bottom = period_top + self.period_h;
        for i in 0..self.input.periods.len() {
            let area = Area {
                x: column(self.slot[i]),
                y: period_top,
                w: self.card_w,
                h: self.period_h,
            };
            right = right.max(area.right());
            self.periods[i] = area;
            self.stack_column(i, bottom + self.c.section_gap);
        }
        let axis_y = bottom + half(self.c.section_gap);
        self.axis = [
            Vec2 { x: 0, y: axis_y },
            Vec2 {
                x: right + self.c.column_gap,
                y: axis_y,
            },
        ];
        (self.c.left_margin, right)
    }

    fn stack_column(&mut self, i: usize, top: i64) {
        let input = self.input;
        let period = self.periods[i];
        let cx = period.x + half(self.card_w);
        let (mut above, mut y) = (period, top);
        for event in &input.periods[i].events {
            let area = Area {
                x: period.x,
                y,
                w: self.card_w,
                h: self.event_height(event),
            };
            self.events[i].push(area);
            self.routes[i].push(vec![
                Vec2 {
                    x: cx,
                    y: above.bottom(),
                },
                Vec2 { x: cx, y: area.y },
            ]);
            above = area;
            y = area.bottom() + self.c.event_gap;
        }
    }

    fn place_vertical(&mut self) -> (i64, i64) {
        let x = self.c.left_margin;
        let event_x = x + self.card_w + self.c.column_gap;
        let axis_x = x + self.card_w + half(self.c.column_gap);
        let top = self.content_top();
        let mut y = top;
        let steps = std::iter::once(None).chain((0..self.input.sections.len()).map(Some));
        for section in steps {
            if let Some(s) = section {
                self.sections[s] = Area {
                    x,
                    y,
                    w: self.card_w,
                    h: self.section_h,
                };
                y += self.section_h + self.c.section_gap;
            }
            for i in self.members(section) {
                y = self.row(i, y, axis_x, event_x) + self.c.section_gap;
            }
        }
        let bottom = top.max(y - self.c.section_gap);
        self.axis = [
            Vec2 { x: axis_x, y: top },
            Vec2 {
                x: axis_x,
                y: bottom + self.c.section_gap,
            },
        ];
        (x, event_x + self.card_w)
    }

    fn row(&mut self, i: usize, y: i64, axis_x: i64, event_x: i64) -> i64 {
        let input = self.input;
        let period = Area {
            x: self.c.left_margin,
            y,
            w: self.card_w,
            h: self.period_h,
        };
        self.periods[i] = period;
        let from = Vec2 {
            x: period.right(),
            y: y + half(self.period_h),
        };
        let mut bottom = period.bottom();
        let mut next = y;
        for event in &input.periods[i].events {
            let area = Area {
                x: event_x,
                y: next,
                w: self.card_w,
                h: self.event_height(event),
            };
            self.events[i].push(area);
            let to = Vec2 {
                x: area.x,
                y: area.y + half(area.h),
            };
            self.routes[i].push(elbow(from, to, axis_x));
            bottom = bottom.max(area.bottom());
            next = area.bottom() + self.c.event_gap;
        }
        bottom
    }
}

fn elbow(from: Vec2, to: Vec2, axis_x: i64) -> Vec<Vec2> {
    if from.y == to.y {
        return vec![from, to];
    }
    vec![
        from,
        Vec2 {
            x: axis_x,
            y: from.y,
        },
        Vec2 { x: axis_x, y: to.y },
        to,
    ]
}
