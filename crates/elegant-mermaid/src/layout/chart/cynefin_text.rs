//! Text measurement and text items for the cynefin and info plans.

use crate::geom::Point;
use crate::measure::{self, Metric, Role};
use crate::scene::{Align, Item, Profile, Run, TextItem, TextRole, TextStyle};

use super::{Area, LayoutError, to_i32};

const VECTOR_UNITS_PER_PX: i64 = 64;

#[derive(Debug, Clone, Default)]
pub(crate) struct TextBox {
    pub plain: Vec<String>,
    pub runs: Vec<Vec<Run>>,
    pub w: i64,
    pub h: i64,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct TextSpec {
    pub profile: Profile,
    pub role: Role,
    pub size: i32,
}

pub(crate) fn text_role(role: Role) -> TextRole {
    match role {
        Role::Title => TextRole::Title,
        Role::Body => TextRole::Body,
        _ => TextRole::Label,
    }
}

pub(crate) fn point_of(x: i64, y: i64) -> Result<Point, LayoutError> {
    Ok(Point {
        x: to_i32(x)?,
        y: to_i32(y)?,
    })
}

impl TextSpec {
    pub(crate) fn of_role(profile: Profile, role: Role) -> TextSpec {
        TextSpec {
            profile,
            role,
            size: role.size_px(),
        }
    }

    fn line_height(self) -> i64 {
        if self.profile == Profile::Cell {
            return 1;
        }
        measure::round_half_up(
            i64::from(self.size) * VECTOR_UNITS_PER_PX * i64::from(self.role.line_height_px()),
            i64::from(self.role.size_px()),
        )
    }

    fn metric(self) -> Metric {
        if self.profile == Profile::Cell {
            Metric::cell()
        } else {
            Metric::Vector {
                size_px: self.size,
                weight: self.role.weight(),
                font_family: false,
            }
        }
    }

    pub(crate) fn measure(self, text: &str) -> Result<TextBox, LayoutError> {
        let lines = measure::styled_lines(text, i32::MAX, self.metric())?;
        let widest = lines
            .iter()
            .map(|line| i64::from(line.width))
            .max()
            .unwrap_or(0);
        let height = i64::try_from(lines.len()).unwrap_or(i64::MAX) * self.line_height();
        let runs = lines
            .iter()
            .map(|line| {
                line.runs
                    .iter()
                    .map(|run| Run {
                        text: run.text.to_owned(),
                        bold: run.bold,
                        italic: run.italic,
                    })
                    .collect()
            })
            .collect();
        let plain = lines.iter().map(|line| line.text.clone()).collect();
        Ok(TextBox {
            plain,
            runs,
            w: widest,
            h: height,
        })
    }

    pub(crate) fn item(self, text: &TextBox, at: Area, align: Align) -> Result<Item, LayoutError> {
        Ok(Item::Text(TextItem {
            rect: at.to_rect()?,
            role: text_role(self.role),
            size: self.size,
            align,
            style: TextStyle::Text,
            series: 0,
            lines: text.runs.clone(),
        }))
    }
}

pub(crate) fn right(area: Area) -> i64 {
    area.x + area.w
}

pub(crate) fn bottom(area: Area) -> i64 {
    area.y + area.h
}
