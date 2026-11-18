use super::{Layout, Placer};
use crate::geom::{COORD_LIMIT, GeomError, Point, Rect, Size, floor_div};

struct Placement {
    left: Vec<i64>,
    y: Vec<i64>,
    right: Vec<bool>,
}

impl Placer<'_> {
    pub(super) fn layout(&self) -> Result<Layout, GeomError> {
        let at = self.positions();
        let mut boxes = Vec::with_capacity(self.nodes.len());
        for (i, node) in self.nodes.iter().enumerate() {
            let top = at.y[i] - floor_div(i64::from(node.height), 2);
            boxes.push(rect(
                at.left[i],
                top,
                i64::from(node.width),
                i64::from(node.height),
            )?);
        }
        let mut routes: Vec<Vec<Point>> = vec![Vec::new()];
        for (i, node) in self.nodes.iter().enumerate().skip(1) {
            let parent = node.parent.ok_or(GeomError::Domain)?;
            let ends = (at.y[parent], at.y[i]);
            routes.push(if at.right[i] {
                self.route_right(boxes[parent], boxes[i], ends)?
            } else {
                self.route_left(boxes[parent], boxes[i], ends)?
            });
        }
        Ok(Layout { boxes, routes })
    }

    fn positions(&self) -> Placement {
        let n = self.nodes.len();
        let mut at = Placement {
            left: vec![0; n],
            y: vec![0; n],
            right: vec![false; n],
        };
        at.left[0] = -floor_div(i64::from(self.nodes[0].width), 2);
        let mut root_children = 0;
        for i in 1..n {
            let parent = self.nodes[i].parent.unwrap_or(0);
            at.right[i] = at.right[parent];
            if parent == 0 {
                at.right[i] = root_children % 2 == 0;
                root_children += 1;
            }
            at.y[i] = at.y[parent] + self.dy[i];
            at.left[i] = self.child_left(&at, i, parent);
        }
        at
    }

    fn child_left(&self, at: &Placement, i: usize, parent: usize) -> i64 {
        if at.right[i] {
            return at.left[parent]
                + i64::from(self.nodes[parent].width)
                + i64::from(self.gaps.level);
        }
        at.left[parent] - i64::from(self.gaps.level) - i64::from(self.nodes[i].width)
    }

    fn route_right(
        &self,
        parent: Rect,
        child: Rect,
        ends: (i64, i64),
    ) -> Result<Vec<Point>, GeomError> {
        let from = i64::from(parent.x) + i64::from(parent.w);
        let trunk = from + floor_div(i64::from(self.gaps.level), 2);
        elbow(from, i64::from(child.x), trunk, ends)
    }

    fn route_left(
        &self,
        parent: Rect,
        child: Rect,
        ends: (i64, i64),
    ) -> Result<Vec<Point>, GeomError> {
        let from = i64::from(parent.x);
        let trunk = from - floor_div(i64::from(self.gaps.level), 2);
        elbow(from, i64::from(child.x) + i64::from(child.w), trunk, ends)
    }
}

fn rect(x: i64, y: i64, w: i64, h: i64) -> Result<Rect, GeomError> {
    for v in [x, y, x + w, y + h] {
        if !(-COORD_LIMIT..=COORD_LIMIT).contains(&v) {
            return Err(GeomError::Overflow);
        }
    }
    Ok(Rect {
        x: narrow(x)?,
        y: narrow(y)?,
        w: narrow(w)?,
        h: narrow(h)?,
    })
}

fn narrow(v: i64) -> Result<i32, GeomError> {
    i32::try_from(v).map_err(|_| GeomError::Overflow)
}

fn point(x: i64, y: i64) -> Result<Point, GeomError> {
    Ok(Point {
        x: narrow(x)?,
        y: narrow(y)?,
    })
}

fn elbow(from: i64, to: i64, trunk: i64, ends: (i64, i64)) -> Result<Vec<Point>, GeomError> {
    let start = point(from, ends.0)?;
    let end = point(to, ends.1)?;
    if ends.0 == ends.1 {
        return Ok(vec![start, end]);
    }
    Ok(vec![
        start,
        point(trunk, ends.0)?,
        point(trunk, ends.1)?,
        end,
    ])
}

#[derive(Clone, Copy)]
struct Bounds {
    min_x: i64,
    min_y: i64,
    max_x: i64,
    max_y: i64,
}

impl Bounds {
    fn include(&mut self, x: i64, y: i64) {
        self.min_x = self.min_x.min(x);
        self.min_y = self.min_y.min(y);
        self.max_x = self.max_x.max(x);
        self.max_y = self.max_y.max(y);
    }
}

fn bounds(layout: &Layout) -> Option<Bounds> {
    let first = layout.boxes.first()?;
    let mut b = Bounds {
        min_x: i64::from(first.x),
        min_y: i64::from(first.y),
        max_x: i64::from(first.x),
        max_y: i64::from(first.y),
    };
    for r in &layout.boxes {
        b.include(i64::from(r.x), i64::from(r.y));
        b.include(
            i64::from(r.x) + i64::from(r.w),
            i64::from(r.y) + i64::from(r.h),
        );
    }
    for p in layout.routes.iter().flatten() {
        b.include(i64::from(p.x), i64::from(p.y));
    }
    Some(b)
}

/// Translates the layout so its bounding box starts at `margin` and returns the canvas.
pub fn normalize(layout: &mut Layout, margin: i32) -> Result<Size, GeomError> {
    let margin = i64::from(margin);
    let Some(b) = bounds(layout) else {
        return Ok(Size {
            w: narrow(2 * margin)?,
            h: narrow(2 * margin)?,
        });
    };
    let dx = margin - b.min_x;
    let dy = margin - b.min_y;
    let w = b.max_x - b.min_x + 2 * margin;
    let h = b.max_y - b.min_y + 2 * margin;
    if w > COORD_LIMIT || h > COORD_LIMIT {
        return Err(GeomError::Overflow);
    }
    for r in &mut layout.boxes {
        r.x = narrow(i64::from(r.x) + dx)?;
        r.y = narrow(i64::from(r.y) + dy)?;
    }
    for p in layout.routes.iter_mut().flatten() {
        p.x = narrow(i64::from(p.x) + dx)?;
        p.y = narrow(i64::from(p.y) + dy)?;
    }
    Ok(Size {
        w: narrow(w)?,
        h: narrow(h)?,
    })
}
