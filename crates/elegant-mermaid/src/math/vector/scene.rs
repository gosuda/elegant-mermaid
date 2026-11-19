//! Scene emission of vector math boxes (math-13, math-20; spec/scene.md).
//!
//! One math run inside a measured line emits its leaves: glyph leaves
//! become body-role text items at their own baselines and sizes, rule
//! leaves become rule-styled rectangles, and path leaves become
//! rule-styled polylines. Lines without math keep the single text item the
//! layered pipeline always emitted, byte for byte.

use crate::geom::{GeomError, Point, Rect};
use crate::math::vector::{self, FormulaBox, Leaf};
use crate::measure::{StyledLine, StyledRun, Weight};
use crate::scene::{
    Align, Item, PolylineItem, RectItem, Run, Shape, ShapeStyle, TextItem, TextRole, TextStyle,
};

const BODY_LINE_HEIGHT: i64 = 1280;
const TITLE_LINE_HEIGHT: i64 = 1536;
const BASELINE_FRACTION: i64 = 35;
const BASELINE_SCALE: i64 = 100;

/// The text attributes and lines of one label, as the layered pipeline
/// passes them to the scene.
pub struct LabelText<'a> {
    /// The text box.
    pub rect: Rect,
    /// The text role.
    pub role: TextRole,
    /// The size in px.
    pub size: i32,
    /// The horizontal alignment.
    pub align: Align,
    /// The text style.
    pub style: TextStyle,
    /// The series index of the fill the text sits on.
    pub series: u8,
    /// The measured lines.
    pub lines: &'a [StyledLine<'a>],
}

/// The scene items of one label: a single text item when no line carries a
/// math run, otherwise the lines split at their math runs with absolutely
/// positioned math leaves. Shapes come before text items in the result.
pub fn label_items(label: LabelText<'_>) -> Result<Vec<Item>, GeomError> {
    if !has_math(label.lines) {
        return Ok(vec![Item::Text(TextItem {
            rect: label.rect,
            role: label.role,
            size: label.size,
            align: label.align,
            style: label.style,
            series: label.series,
            lines: label.lines.iter().map(line_runs).collect(),
        })]);
    }
    let placement = Placement {
        role: label.role,
        size: label.size,
        style: label.style,
        line_height: match label.role {
            TextRole::Title => TITLE_LINE_HEIGHT,
            _ => BODY_LINE_HEIGHT,
        },
    };
    let mut items = Vec::new();
    for (index, line) in label.lines.iter().enumerate() {
        let baseline = placement.baseline(label.rect.y, index)?;
        emit_line(
            &mut items,
            &placement,
            label.rect,
            label.align,
            line,
            baseline,
        )?;
    }
    Ok(shapes_first(items))
}

struct Placement {
    role: TextRole,
    size: i32,
    style: TextStyle,
    line_height: i64,
}

impl Placement {
    fn baseline(&self, top: i32, line: usize) -> Result<i64, GeomError> {
        let index = i64::try_from(line).map_err(|_| GeomError::Overflow)?;
        let scaled = i64::from(self.size)
            .checked_mul(64)
            .and_then(|v| v.checked_mul(BASELINE_FRACTION))
            .map(|v| v / BASELINE_SCALE)
            .ok_or(GeomError::Overflow)?;
        i64::from(top)
            .checked_add(
                index
                    .checked_mul(self.line_height)
                    .ok_or(GeomError::Overflow)?,
            )
            .and_then(|v| v.checked_add(self.line_height / 2 + scaled))
            .ok_or(GeomError::Overflow)
    }

    fn above(&self, baseline: i64) -> Result<i64, GeomError> {
        let scaled = i64::from(self.size)
            .checked_mul(64)
            .and_then(|v| v.checked_mul(BASELINE_FRACTION))
            .map(|v| v / BASELINE_SCALE)
            .ok_or(GeomError::Overflow)?;
        baseline
            .checked_sub(self.line_height / 2 + scaled)
            .ok_or(GeomError::Overflow)
    }

    fn segment(
        &self,
        x: i32,
        width: i64,
        baseline: i64,
        runs: Vec<Run>,
    ) -> Result<Item, GeomError> {
        let drop = baseline
            .checked_sub(self.above(baseline)?)
            .ok_or(GeomError::Overflow)?;
        Ok(Item::Text(TextItem {
            rect: Rect {
                x,
                y: narrow(baseline - drop)?,
                w: narrow(width)?,
                h: narrow(drop)?,
            },
            role: self.role,
            size: self.size,
            align: Align::Start,
            style: self.style,
            series: 0,
            lines: vec![runs],
        }))
    }
}

fn narrow(value: i64) -> Result<i32, GeomError> {
    i32::try_from(value).map_err(|_| GeomError::Overflow)
}

fn has_math(lines: &[StyledLine<'_>]) -> bool {
    lines
        .iter()
        .any(|line| line.runs.iter().any(|run| run.math.is_some()))
}

fn line_runs(line: &StyledLine<'_>) -> Vec<Run> {
    line.runs
        .iter()
        .map(|run| Run {
            text: run.text.to_string(),
            bold: run.bold,
            italic: run.italic,
        })
        .collect()
}

fn emit_line(
    items: &mut Vec<Item>,
    placement: &Placement,
    rect: Rect,
    align: Align,
    line: &StyledLine<'_>,
    baseline: i64,
) -> Result<(), GeomError> {
    let mut x = i64::from(line_left(rect, align, line.width)?);
    let mut segment: Option<(i32, i64, Vec<Run>)> = None;
    for run in &line.runs {
        if run.math.is_some() {
            flush_segment(items, placement, &mut segment, baseline)?;
            if let Some(formula) = run.math.as_ref() {
                items.extend(formula_items(
                    formula,
                    narrow(x)?,
                    baseline,
                    placement.style,
                )?);
            }
        } else {
            match segment.as_mut() {
                Some((_, width, runs)) => {
                    *width += i64::from(run.width);
                    runs.push(plain_run(run));
                }
                None => segment = Some((narrow(x)?, i64::from(run.width), vec![plain_run(run)])),
            }
        }
        x += i64::from(run.width);
    }
    flush_segment(items, placement, &mut segment, baseline)
}

fn flush_segment(
    items: &mut Vec<Item>,
    placement: &Placement,
    segment: &mut Option<(i32, i64, Vec<Run>)>,
    baseline: i64,
) -> Result<(), GeomError> {
    if let Some((x, width, runs)) = segment.take() {
        items.push(placement.segment(x, width, baseline, runs)?);
    }
    Ok(())
}

fn plain_run(run: &StyledRun<'_>) -> Run {
    Run {
        text: run.text.to_string(),
        bold: run.bold,
        italic: run.italic,
    }
}

fn line_left(rect: Rect, align: Align, width: i32) -> Result<i32, GeomError> {
    let offset = match align {
        Align::Start => 0,
        Align::Middle => i64::from(rect.w) / 2 - i64::from(width) / 2,
        Align::End => i64::from(rect.w) - i64::from(width),
    };
    narrow(i64::from(rect.x) + offset)
}

fn formula_items(
    formula: &FormulaBox,
    origin_x: i32,
    baseline_y: i64,
    style: TextStyle,
) -> Result<Vec<Item>, GeomError> {
    let mut items = Vec::new();
    for leaf in &formula.leaves {
        items.push(leaf_item(leaf, formula, origin_x, baseline_y, style)?);
    }
    Ok(items)
}

fn leaf_item(
    leaf: &Leaf,
    formula: &FormulaBox,
    origin_x: i32,
    baseline_y: i64,
    style: TextStyle,
) -> Result<Item, GeomError> {
    match leaf {
        Leaf::Glyph { .. } => glyph_item(leaf, origin_x, baseline_y, style),
        Leaf::Rule { rect, .. } => Ok(Item::Rect(RectItem {
            shape: Shape::plain(ShapeStyle::Rule),
            rect: translate_rect(rect, formula, origin_x, baseline_y)?,
        })),
        Leaf::Path { points, .. } => Ok(Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Rule),
            points: translate_points(points, formula, origin_x, baseline_y)?,
            corner: 0,
        })),
    }
}

fn glyph_item(
    leaf: &Leaf,
    origin_x: i32,
    baseline_y: i64,
    style: TextStyle,
) -> Result<Item, GeomError> {
    let Leaf::Glyph {
        codepoint,
        weight,
        size,
        shear,
        x,
        baseline: _,
    } = leaf
    else {
        return Err(GeomError::Domain);
    };
    let px = glyph_size_px(*size)?;
    let scaled = i64::from(px)
        .checked_mul(64)
        .and_then(|v| v.checked_mul(BASELINE_FRACTION))
        .map(|v| v / BASELINE_SCALE)
        .ok_or(GeomError::Overflow)?;
    let top = baseline_y
        .checked_sub(BODY_LINE_HEIGHT / 2)
        .and_then(|v| v.checked_sub(scaled))
        .ok_or(GeomError::Overflow)?;
    let advance = leaf.box_rect()?.w;
    let at = Point {
        x: origin_x.checked_add(*x).ok_or(GeomError::Overflow)?,
        y: narrow(top)?,
    };
    let height = baseline_y.checked_sub(top).ok_or(GeomError::Overflow)?;
    Ok(Item::Text(TextItem {
        rect: Rect {
            x: at.x,
            y: at.y,
            w: advance,
            h: narrow(height)?,
        },
        role: TextRole::Body,
        size: px,
        align: Align::Start,
        style,
        series: 0,
        lines: vec![vec![Run {
            text: vector::font_codepoint(*codepoint).to_string(),
            bold: *weight == Weight::Semibold,
            italic: *shear,
        }]],
    }))
}

fn translate_rect(
    rect: &Rect,
    formula: &FormulaBox,
    origin_x: i32,
    baseline_y: i64,
) -> Result<Rect, GeomError> {
    Ok(Rect {
        x: origin_x.checked_add(rect.x).ok_or(GeomError::Overflow)?,
        y: narrow(
            baseline_y
                .checked_sub(i64::from(formula.a))
                .and_then(|v| v.checked_add(i64::from(rect.y)))
                .ok_or(GeomError::Overflow)?,
        )?,
        w: rect.w,
        h: rect.h,
    })
}

fn translate_points(
    points: &[Point],
    formula: &FormulaBox,
    origin_x: i32,
    baseline_y: i64,
) -> Result<Vec<Point>, GeomError> {
    points
        .iter()
        .map(|p| {
            Ok(Point {
                x: origin_x.checked_add(p.x).ok_or(GeomError::Overflow)?,
                y: narrow(
                    baseline_y
                        .checked_sub(i64::from(formula.a))
                        .and_then(|v| v.checked_add(i64::from(p.y)))
                        .ok_or(GeomError::Overflow)?,
                )?,
            })
        })
        .collect()
}

fn glyph_size_px(size_units: i32) -> Result<i32, GeomError> {
    narrow(
        i64::from(size_units)
            .checked_add(32)
            .map(|v| v / 64)
            .ok_or(GeomError::Overflow)?,
    )
}

fn shapes_first(items: Vec<Item>) -> Vec<Item> {
    let (shapes, texts): (Vec<_>, Vec<_>) = items
        .into_iter()
        .partition(|item| matches!(item, Item::Rect(_) | Item::Polyline(_)));
    shapes.into_iter().chain(texts).collect()
}
