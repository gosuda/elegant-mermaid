use super::LayoutError;
use crate::geom::{Point, Rect, Size};

pub fn target<'a>(
    profile: crate::scene::Profile,
    max_width: u32,
    boxes: impl IntoIterator<Item = &'a Rect>,
    routes: impl IntoIterator<Item = &'a [Point]>,
) -> Result<i32, LayoutError> {
    if profile == crate::scene::Profile::Cell && max_width > 0 {
        return i32::try_from(max_width).map_err(|_| LayoutError::Overflow);
    }
    let mut area = 0i64;
    for rect in boxes {
        area = area
            .checked_add(i64::from(rect.w) * i64::from(rect.h))
            .ok_or(LayoutError::Overflow)?;
    }
    for points in routes {
        let Some(first) = points.first() else {
            continue;
        };
        let (mut left, mut top, mut right, mut bottom) = (first.x, first.y, first.x, first.y);
        for p in points {
            left = left.min(p.x);
            top = top.min(p.y);
            right = right.max(p.x);
            bottom = bottom.max(p.y);
        }
        let size = (i64::from(right) - i64::from(left))
            .checked_mul(i64::from(bottom) - i64::from(top))
            .ok_or(LayoutError::Overflow)?;
        area = area.checked_add(size).ok_or(LayoutError::Overflow)?;
    }
    let numerator = i64::from(super::pipeline::constant(profile, "component_aspect_num"));
    let denominator = i64::from(super::pipeline::constant(profile, "component_aspect_den"));
    if numerator <= 0 || denominator <= 0 {
        return Err(LayoutError::Domain);
    }
    let area = area.checked_mul(numerator).ok_or(LayoutError::Overflow)? / denominator;
    i32::try_from(crate::geom::isqrt(area)?).map_err(|_| LayoutError::Overflow)
}

pub fn shelves(sizes: &[Size], target: i32, gap: i32) -> Result<Vec<Point>, LayoutError> {
    let (mut x, mut y, mut height) = (0i64, 0i64, 0i64);
    let mut origins = Vec::with_capacity(sizes.len());
    for size in sizes {
        if x > 0 && x + i64::from(size.w) > i64::from(target) {
            x = 0;
            y += height + i64::from(gap);
            height = 0;
        }
        origins.push(Point {
            x: i32::try_from(x).map_err(|_| LayoutError::Overflow)?,
            y: i32::try_from(y).map_err(|_| LayoutError::Overflow)?,
        });
        x += i64::from(size.w) + i64::from(gap);
        height = height.max(i64::from(size.h));
    }
    Ok(origins)
}
