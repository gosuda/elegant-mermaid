use super::{Builder, COORD_LIMIT, Kind, to_i32};
use crate::geom::{GeomError, Point, Rect};

struct Site<'a> {
    routes: &'a [Vec<Point>],
    leaves: Vec<Rect>,
    frames: Vec<Rect>,
    placed: Vec<Rect>,
    canvas: Rect,
}

fn manhattan(a: Point, b: Point) -> i64 {
    (i64::from(a.x) - i64::from(b.x)).abs() + (i64::from(a.y) - i64::from(b.y)).abs()
}

fn rect_of(x: i64, y: i64, w: i64, h: i64) -> Rect {
    Rect {
        x: to_i32(x),
        y: to_i32(y),
        w: to_i32(w),
        h: to_i32(h),
    }
}

fn overlaps(a: Rect, b: Rect) -> bool {
    a.x < b.x + b.w && b.x < a.x + a.w && a.y < b.y + b.h && b.y < a.y + a.h
}

fn strictly_inside(outer: Rect, inner: Rect) -> bool {
    i64::from(outer.x) < i64::from(inner.x)
        && i64::from(inner.x) + i64::from(inner.w) < i64::from(outer.x) + i64::from(outer.w)
        && i64::from(outer.y) < i64::from(inner.y)
        && i64::from(inner.y) + i64::from(inner.h) < i64::from(outer.y) + i64::from(outer.h)
}

fn segment_touches(a: Point, b: Point, thick: i32, r: Rect) -> bool {
    let (x0, x1) = (a.x.min(b.x), a.x.max(b.x) + thick);
    let (y0, y1) = (a.y.min(b.y), a.y.max(b.y) + thick);
    x0 < r.x + r.w && r.x < x1 && y0 < r.y + r.h && r.y < y1
}

impl Builder<'_> {
    pub(super) fn connect(
        &self,
        canvas: &mut Rect,
    ) -> Result<(Vec<Vec<Point>>, Vec<Rect>), GeomError> {
        let routes = self.route()?;
        let labels = self.place_labels(&routes, canvas)?;
        Ok((routes, labels))
    }

    fn place_labels(
        &self,
        routes: &[Vec<Point>],
        canvas: &mut Rect,
    ) -> Result<Vec<Rect>, GeomError> {
        let mut labels = vec![super::zero_rect(); routes.len()];
        let mut site = Site {
            routes,
            leaves: self.rects_of(Kind::Leaf),
            frames: self.rects_of(Kind::Composite),
            placed: Vec::new(),
            canvas: *canvas,
        };
        let margin = i64::from(self.params.padding).max(1);
        let spill_x = i64::from(canvas.w) + margin;
        let mut spill_y = margin;
        for (k, edge) in self.input.edges.iter().enumerate() {
            if edge.label.w == 0 && edge.label.h == 0 {
                continue;
            }
            let rect = match self.fit_label(&site, &routes[k], edge.label.w, edge.label.h) {
                Some(rect) => rect,
                None => {
                    let (w, h) = (i64::from(edge.label.w), i64::from(edge.label.h));
                    if spill_x + w + margin > COORD_LIMIT || spill_y + h + margin > COORD_LIMIT {
                        return Err(GeomError::Overflow);
                    }
                    let rect = rect_of(spill_x, spill_y, w, h);
                    spill_y += h + margin;
                    canvas.w = canvas
                        .w
                        .max(to_i32(i64::from(rect.x) + i64::from(rect.w) + margin));
                    canvas.h = canvas.h.max(to_i32(spill_y));
                    site.canvas = *canvas;
                    rect
                }
            };
            labels[k] = rect;
            site.placed.push(rect);
        }
        Ok(labels)
    }

    fn fit_label(&self, site: &Site<'_>, route: &[Point], w: i32, h: i32) -> Option<Rect> {
        self.candidates(route, i64::from(w), i64::from(h))
            .into_iter()
            .find(|candidate| self.vacant(site, *candidate))
    }

    fn candidates(&self, route: &[Point], w: i64, h: i64) -> Vec<Rect> {
        let mut order: Vec<usize> = (0..route.len().saturating_sub(1))
            .filter(|i| manhattan(route[*i], route[*i + 1]) > 0)
            .collect();
        order.sort_by_key(|i| std::cmp::Reverse(manhattan(route[*i], route[*i + 1])));
        order
            .into_iter()
            .flat_map(|i| self.beside(route[i], route[i + 1], w, h))
            .collect()
    }

    fn beside(&self, from: Point, to: Point, w: i64, h: i64) -> [Rect; 2] {
        let mx = (i64::from(from.x) + i64::from(to.x)) / 2;
        let my = (i64::from(from.y) + i64::from(to.y)) / 2;
        let off = i64::from(self.params.padding) / 2;
        let thick = i64::from(self.params.line_thickness);
        if from.y == to.y {
            return [
                rect_of(mx - w / 2, my - off - h, w, h),
                rect_of(mx - w / 2, my + thick + off, w, h),
            ];
        }
        [
            rect_of(mx + thick + off, my - h / 2, w, h),
            rect_of(mx - off - w, my - h / 2, w, h),
        ]
    }

    fn vacant(&self, site: &Site<'_>, r: Rect) -> bool {
        if !strictly_inside(site.canvas, r) {
            return false;
        }
        if site
            .frames
            .iter()
            .any(|frame| overlaps(*frame, r) && !strictly_inside(*frame, r))
        {
            return false;
        }
        if site
            .leaves
            .iter()
            .chain(&site.placed)
            .any(|other| overlaps(r, *other))
        {
            return false;
        }
        let thick = self.params.line_thickness;
        !site.routes.iter().any(|route| {
            route
                .windows(2)
                .any(|pair| segment_touches(pair[0], pair[1], thick, r))
        })
    }
}
