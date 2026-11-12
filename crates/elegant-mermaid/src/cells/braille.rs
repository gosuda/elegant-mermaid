use super::{Canvas, Token, canvas::max_token};
use crate::geom::{GeomError, Point, cos_q15, floor_div, sin_q15};
fn point(x: i64, y: i64) -> Result<Point, GeomError> {
    Ok(Point {
        x: i32::try_from(x).map_err(|_| GeomError::Overflow)?,
        y: i32::try_from(y).map_err(|_| GeomError::Overflow)?,
    })
}
pub fn dot_bit(x: i32, y: i32) -> u8 {
    const B: [[u8; 4]; 2] = [[1, 2, 4, 64], [8, 16, 32, 128]];
    let column = usize::from(x.rem_euclid(2) != 0);
    let row = usize::from(u8::try_from(y.rem_euclid(4)).unwrap_or(0));
    B[column][row]
}
pub fn cell_dot(p: Point) -> Result<Point, GeomError> {
    point(2 * i64::from(p.x), 4 * i64::from(p.y) + 2)
}
impl Canvas {
    pub fn new_braille(w: i32, h: i32) -> Result<Self, GeomError> {
        if w < 0 || h < 0 {
            return Err(GeomError::Domain);
        }
        Self::new(
            i32::try_from((i64::from(w) + 511) / 512).map_err(|_| GeomError::Overflow)?,
            i32::try_from((i64::from(h) + 1023) / 1024).map_err(|_| GeomError::Overflow)?,
        )
    }
    pub fn put_dot(&mut self, x: i32, y: i32, ink: Token) {
        if x < 0 || y < 0 {
            return;
        }
        self.put(x / 2, y / 4, |c| {
            c.dots |= dot_bit(x, y);
            c.token = max_token(c.token, Some(ink))
        })
    }
    pub fn stroke_dots(&mut self, a: Point, b: Point, ink: Token) -> Result<(), GeomError> {
        let (mut x, mut y) = (i64::from(a.x), i64::from(a.y));
        let (tx, ty) = (i64::from(b.x), i64::from(b.y));
        let dx = (tx - x).abs();
        let dy = -(ty - y).abs();
        let sx = if x < tx { 1 } else { -1 };
        let sy = if y < ty { 1 } else { -1 };
        let mut err = dx + dy;
        for _ in 0..dx - dy + 1 {
            self.put_dot(
                i32::try_from(x).map_err(|_| GeomError::Overflow)?,
                i32::try_from(y).map_err(|_| GeomError::Overflow)?,
                ink,
            );
            if x == tx && y == ty {
                return Ok(());
            }
            let e2 = 2 * err;
            if e2 >= dy {
                err += dy;
                x += sx
            }
            if e2 <= dx {
                err += dx;
                y += sy
            }
        }
        Ok(())
    }
    pub fn stroke(&mut self, points: &[Point], ink: Token) -> Result<(), GeomError> {
        for pair in points.windows(2) {
            let a = pair[0];
            let b = pair[1];
            self.stroke_dots(
                point(
                    floor_div(i64::from(a.x), 256),
                    floor_div(i64::from(a.y), 256),
                )?,
                point(
                    floor_div(i64::from(b.x), 256),
                    floor_div(i64::from(b.y), 256),
                )?,
                ink,
            )?
        }
        Ok(())
    }
    pub fn fill(&mut self, points: &[Point], ink: Token) -> Result<(), GeomError> {
        let rows = self.height().checked_mul(4).ok_or(GeomError::Overflow)?;
        let columns = self.width().checked_mul(2).ok_or(GeomError::Overflow)?;
        for y in 0..rows {
            for x in 0..columns {
                if polygon_inside(points, 256 * i64::from(x) + 128, 256 * i64::from(y) + 128)? {
                    self.put_dot(x, y, ink)
                }
            }
        }
        Ok(())
    }
}
pub fn polygon_inside(points: &[Point], px: i64, py: i64) -> Result<bool, GeomError> {
    let mut inside = false;
    for (a, b) in points
        .iter()
        .zip(points.iter().cycle().skip(1))
        .take(points.len())
    {
        inside ^= edge_cross(*a, *b, px, py)?
    }
    Ok(inside)
}
fn edge_cross(a: Point, b: Point, px: i64, py: i64) -> Result<bool, GeomError> {
    let (x1, y1, x2, y2) = (
        i64::from(a.x),
        i64::from(a.y),
        i64::from(b.x),
        i64::from(b.y),
    );
    if (y1 > py) == (y2 > py) {
        return Ok(false);
    }
    let u = (x2 - x1)
        .checked_mul(py.checked_sub(y1).ok_or(GeomError::Overflow)?)
        .ok_or(GeomError::Overflow)?;
    let v = x1
        .checked_sub(px)
        .ok_or(GeomError::Overflow)?
        .checked_mul(y2 - y1)
        .ok_or(GeomError::Overflow)?;
    let n = u
        .checked_add(v)
        .ok_or(GeomError::Overflow)?
        .checked_mul(y2 - y1)
        .ok_or(GeomError::Overflow)?;
    Ok(n > 0)
}
pub fn arc(center: Point, radius: i32, start: i32, sweep: i32) -> Result<Vec<Point>, GeomError> {
    let n = 4.max((i64::from(sweep).abs() + 1023) / 1024);
    (0..=n)
        .map(|k| {
            let a = i32::try_from(
                (i64::from(start) + floor_div(i64::from(sweep) * k, n)).rem_euclid(65536),
            )
            .map_err(|_| GeomError::Overflow)?;
            point(
                i64::from(center.x)
                    + floor_div(2 * i64::from(radius) * i64::from(cos_q15(a)) + 32768, 65536),
                i64::from(center.y)
                    + floor_div(2 * i64::from(radius) * i64::from(sin_q15(a)) + 32768, 65536),
            )
        })
        .collect()
}
pub fn ellipse(center: Point, rx: i32, ry: i32) -> Result<Vec<Point>, GeomError> {
    (0..64)
        .map(|j| {
            point(
                i64::from(center.x)
                    + floor_div(i64::from(rx) * i64::from(cos_q15(j * 1024)), 32768),
                i64::from(center.y)
                    - floor_div(i64::from(ry) * i64::from(sin_q15(j * 1024)), 32768),
            )
        })
        .collect()
}
pub fn cubic(p: [Point; 4]) -> Result<Vec<Point>, GeomError> {
    (0..=16)
        .map(|k| {
            let t = 16 - k;
            let weights = [t * t * t, 3 * k * t * t, 3 * k * k * t, k * k * k];
            let x = p
                .iter()
                .zip(weights)
                .map(|(p, w)| i64::from(p.x) * w)
                .sum::<i64>();
            let y = p
                .iter()
                .zip(weights)
                .map(|(p, w)| i64::from(p.y) * w)
                .sum::<i64>();
            point(floor_div(x + 2048, 4096), floor_div(y + 2048, 4096))
        })
        .collect()
}
