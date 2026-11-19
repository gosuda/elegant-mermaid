//! The journey planner of the lanes family (`spec/layout/lanes.md`, Journey).
//!
//! Tasks take consecutive columns. A section band spans its tasks, and a task with no
//! section has no band. A face sits at the height of its score, above the task cards.

use crate::geom::{Point, Rect, Size};
use crate::layout::layered::LayoutError;
use crate::scene::{Group, Profile};

use super::gitgraph::{Area, Text, Vec2, half};
use super::journey_constants::{JourneyConstants, load_journey};

#[derive(Debug, Clone)]
pub(crate) struct JourneyTitle {
    pub id: String,
    pub label: Text,
}

#[derive(Debug, Clone)]
pub(crate) struct JourneySection {
    pub id: String,
    pub label: Text,
}

#[derive(Debug, Clone)]
pub(crate) struct JourneyTask {
    pub id: String,
    pub band: Option<usize>,
    pub score: i64,
    pub label: Text,
    pub people: Option<Text>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct JourneyInput {
    pub title: Option<JourneyTitle>,
    pub sections: Vec<JourneySection>,
    pub tasks: Vec<JourneyTask>,
    pub task_width: i64,
    pub task_height: i64,
    pub band_height: i64,
    pub column_gap: i64,
}

#[derive(Debug)]
pub(crate) struct JourneyResult {
    pub canvas: Size,
    pub title: Rect,
    pub frames: Vec<Rect>,
    pub bands: Vec<Rect>,
    pub tasks: Vec<Rect>,
    pub people: Vec<Rect>,
    pub faces: Vec<Point>,
    pub groups: Vec<Group>,
}

pub(super) struct Planner<'a> {
    pub input: &'a JourneyInput,
    pub c: JourneyConstants,
    pub profile: Profile,
    pub first: Vec<usize>,
    pub last: Vec<usize>,
    pub band_h: i64,
    pub task_h: i64,
    pub band_top: i64,
    pub title: Area,
    pub frames: Vec<Area>,
    pub bands: Vec<Area>,
    pub tasks: Vec<Area>,
    pub faces: Vec<Vec2>,
    pub sections: Vec<Area>,
    pub names: Vec<Area>,
    pub people: Vec<Area>,
}

pub(crate) fn journey(
    input: &JourneyInput,
    profile: Profile,
) -> Result<JourneyResult, LayoutError> {
    let sections = input.sections.len();
    let mut planner = Planner {
        input,
        c: load_journey(profile, input)?,
        profile,
        first: vec![0; sections],
        last: vec![0; sections],
        band_h: 0,
        task_h: 0,
        band_top: 0,
        title: Area::default(),
        frames: Vec::new(),
        bands: Vec::new(),
        tasks: Vec::new(),
        faces: Vec::new(),
        sections: Vec::new(),
        names: Vec::new(),
        people: Vec::new(),
    };
    planner.group()?;
    planner.size();
    planner.place();
    planner.result()
}

impl Planner<'_> {
    fn group(&mut self) -> Result<(), LayoutError> {
        let input = self.input;
        let sections = input.sections.len();
        let mut seen = vec![false; sections];
        for (k, task) in input.tasks.iter().enumerate() {
            if task.band.is_some_and(|band| band >= sections)
                || task.score < self.c.score_min
                || task.score > self.c.score_max
            {
                return Err(LayoutError::Domain);
            }
            let Some(band) = task.band else {
                continue;
            };
            if !seen[band] {
                seen[band] = true;
                self.first[band] = k;
            }
            self.last[band] = k;
        }
        for (band, &present) in seen.iter().enumerate() {
            if !present || !self.consecutive(band) {
                return Err(LayoutError::Domain);
            }
        }
        Ok(())
    }

    fn consecutive(&self, band: usize) -> bool {
        self.input.tasks[self.first[band]..=self.last[band]]
            .iter()
            .all(|task| task.band == Some(band))
    }

    fn size(&mut self) {
        let input = self.input;
        self.band_h = self.c.band_height;
        self.task_h = self.c.task_height;
        for section in &input.sections {
            self.band_h = self
                .band_h
                .max(i64::from(section.label.h) + 2 * self.c.pad_y);
        }
        for task in &input.tasks {
            self.task_h = self.task_h.max(text_height(task) + 2 * self.c.pad_y);
        }
    }

    fn pitch(&self) -> i64 {
        self.c.task_width + self.c.column_gap
    }

    fn column(&self, k: usize) -> i64 {
        i64::try_from(k).unwrap_or(0) * self.pitch()
    }

    fn face_y(&self, score: i64) -> i64 {
        self.band_top
            + self.band_h
            + (self.c.score_max - score) * self.c.score_step
            + self.c.score_step
    }

    fn place(&mut self) {
        let input = self.input;
        if let Some(title) = &input.title {
            self.title = Area {
                x: 0,
                y: 0,
                w: i64::from(title.label.w),
                h: i64::from(title.label.h),
            };
            self.band_top = self.title.h + self.c.score_step;
        }
        let band_bottom = self.band_top + self.band_h;
        let task_top = band_bottom + (self.c.score_max - self.c.score_min + 2) * self.c.score_step;
        for (b, section) in input.sections.iter().enumerate() {
            let x = self.column(self.first[b]);
            let count = i64::try_from(self.last[b] - self.first[b]).unwrap_or(0);
            let w = count * self.pitch() + self.c.task_width;
            let band = Area {
                x,
                y: self.band_top,
                w,
                h: self.band_h,
            };
            self.frames.push(Area {
                h: task_top + self.task_h - self.band_top,
                ..band
            });
            self.bands.push(band);
            self.sections
                .push(self.centred(band, i64::from(section.label.h)));
        }
        for (k, task) in input.tasks.iter().enumerate() {
            let card = Area {
                x: self.column(k),
                y: task_top,
                w: self.c.task_width,
                h: self.task_h,
            };
            self.tasks.push(card);
            self.faces.push(Vec2 {
                x: card.x + half(card.w),
                y: self.face_y(task.score),
            });
            self.place_text(card, task);
        }
    }

    fn centred(&self, card: Area, height: i64) -> Area {
        Area {
            x: card.x + self.c.pad_x,
            y: card.y + half(card.h - height),
            w: card.w - 2 * self.c.pad_x,
            h: height,
        }
    }

    fn place_text(&mut self, card: Area, task: &JourneyTask) {
        let block = self.centred(card, text_height(task));
        let name = Area {
            h: i64::from(task.label.h),
            ..block
        };
        self.names.push(name);
        self.people.push(
            task.people
                .as_ref()
                .map_or_else(Area::default, |people| Area {
                    y: name.bottom(),
                    h: i64::from(people.h),
                    ..block
                }),
        );
    }
}

fn text_height(task: &JourneyTask) -> i64 {
    i64::from(task.label.h) + task.people.as_ref().map_or(0, |people| i64::from(people.h))
}
