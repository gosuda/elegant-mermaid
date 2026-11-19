use super::LayoutError;
use crate::geom::{Point, Rect, Size};

struct Shelf {
    gap: i64,
    target: i64,
    x: i64,
    y: i64,
    row_height: i64,
    width: i64,
    items: usize,
}

impl Shelf {
    fn new(target: i64, gap: i32) -> Self {
        Self {
            gap: i64::from(gap),
            target,
            x: 0,
            y: 0,
            row_height: 0,
            width: 0,
            items: 0,
        }
    }
    fn place(&mut self, size: &Size) -> (i64, i64) {
        let w = i64::from(size.w);
        if self.items > 0 && self.x + w > self.target {
            self.x = 0;
            self.y += self.row_height + self.gap;
            self.row_height = 0;
            self.items = 0;
        }
        let origin = (self.x, self.y);
        self.x += w + self.gap;
        self.width = self.width.max(origin.0 + w);
        self.row_height = self.row_height.max(i64::from(size.h));
        self.items += 1;
        origin
    }
    fn area(&self) -> Result<i64, LayoutError> {
        self.width
            .checked_mul(self.y + self.row_height)
            .ok_or(LayoutError::Overflow)
    }
}

fn shelf_area(sizes: &[Size], gap: i32, target: i64) -> Result<i64, LayoutError> {
    let mut shelf = Shelf::new(target, gap);
    for size in sizes {
        shelf.place(size);
    }
    shelf.area()
}

fn min_area_target(sizes: &[Size], gap: i32, aspect: i64) -> Result<i64, LayoutError> {
    let mut best = aspect;
    let mut best_area = shelf_area(sizes, gap, aspect)?;
    let mut prefix = -i64::from(gap);
    for size in sizes {
        prefix += i64::from(size.w) + i64::from(gap);
        let area = shelf_area(sizes, gap, prefix)?;
        if area < best_area {
            best = prefix;
            best_area = area;
        }
    }
    Ok(best)
}

pub fn target<'a>(
    profile: crate::scene::Profile,
    max_width: u32,
    boxes: impl IntoIterator<Item = &'a Rect>,
    routes: impl IntoIterator<Item = &'a [Point]>,
    sizes: &[Size],
    gap: i32,
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
    let aspect = i32::try_from(crate::geom::isqrt(area)?).map_err(|_| LayoutError::Overflow)?;
    if sizes.len() < 2 {
        return Ok(aspect);
    }
    i32::try_from(min_area_target(sizes, gap, i64::from(aspect))?)
        .map_err(|_| LayoutError::Overflow)
}

pub fn shelves(sizes: &[Size], target: i32, gap: i32) -> Result<Vec<Point>, LayoutError> {
    let mut shelf = Shelf::new(i64::from(target), gap);
    let mut origins = Vec::with_capacity(sizes.len());
    for size in sizes {
        let (x, y) = shelf.place(size);
        origins.push(Point {
            x: i32::try_from(x).map_err(|_| LayoutError::Overflow)?,
            y: i32::try_from(y).map_err(|_| LayoutError::Overflow)?,
        });
    }
    Ok(origins)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
mod tests {
    use super::*;
    use crate::scene::Profile;

    fn squares(n: usize) -> (Vec<Rect>, Vec<Size>) {
        let boxes = vec![
            Rect {
                x: 0,
                y: 0,
                w: 10,
                h: 10,
            };
            n
        ];
        (boxes, vec![Size { w: 10, h: 10 }; n])
    }
    fn cell_target(n: usize, max_width: u32) -> i32 {
        let (boxes, sizes) = squares(n);
        target(
            Profile::Cell,
            max_width,
            &boxes,
            std::iter::empty::<&[Point]>(),
            &sizes,
            2,
        )
        .unwrap()
    }

    #[test]
    fn minimises_packed_area() {
        let (_, sizes) = squares(3);
        assert_eq!(cell_target(3, 0), 10);
        assert_eq!(shelf_area(&sizes, 2, 24).unwrap(), 22 * 22);
        assert_eq!(shelf_area(&sizes, 2, 10).unwrap(), 10 * 34);
        let origins = shelves(&sizes, 10, 2).unwrap();
        assert_eq!(origins[2], Point { x: 0, y: 24 });
    }
    #[test]
    fn ties_keep_aspect_target() {
        assert_eq!(cell_target(2, 0), 20);
    }
    #[test]
    fn max_width_skips_area_search() {
        assert_eq!(cell_target(3, 24), 24);
    }
}
