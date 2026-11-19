//! Geometry, ports, gutter routes, edge labels, and the final translation.

use std::cmp::Ordering;

use super::{ArchLayout, ArchNode, Area, Builder, Cell, EMPTY, Pt, sized};
use crate::geom::{self, GeomError, Point, Rect, Size};
use crate::layout::input::RouteSide;

#[derive(Clone, Copy)]
struct PortEnd {
    p: Pt,
    g: Pt,
    line: i64,
    vertical: bool,
    at: Cell,
}

#[derive(Clone, Copy)]
struct EndRef {
    edge: usize,
    to: bool,
}

fn side_index(side: RouteSide) -> usize {
    match side {
        RouteSide::Up => 0,
        RouteSide::Down => 1,
        RouteSide::Left => 2,
        RouteSide::Right => 3,
    }
}

const SIDES: [RouteSide; 4] = [
    RouteSide::Up,
    RouteSide::Down,
    RouteSide::Left,
    RouteSide::Right,
];

struct Site {
    region: Area,
    fixed: Vec<Area>,
    placed: Vec<Area>,
}

struct Translation {
    dx: i64,
    dy: i64,
    bad: bool,
}

impl Translation {
    fn check(&mut self, v: i64) -> i32 {
        if !(0..=geom::COORD_LIMIT).contains(&v) {
            self.bad = true;
            return 0;
        }
        i32::try_from(v).unwrap_or(0)
    }

    fn rects(&mut self, input: &[Area]) -> Vec<Rect> {
        input
            .iter()
            .map(|r| {
                if r.x1 == r.x0 && r.y1 == r.y0 {
                    return Rect {
                        x: 0,
                        y: 0,
                        w: 0,
                        h: 0,
                    };
                }
                Rect {
                    x: self.check(r.x0 + self.dx),
                    y: self.check(r.y0 + self.dy),
                    w: self.check(r.x1 - r.x0),
                    h: self.check(r.y1 - r.y0),
                }
            })
            .collect()
    }

    fn points(&mut self, input: &[Pt]) -> Vec<Point> {
        input
            .iter()
            .map(|p| Point {
                x: self.check(p.x + self.dx),
                y: self.check(p.y + self.dy),
            })
            .collect()
    }
}

fn length(a: Pt, c: Pt) -> i64 {
    (a.x - c.x).max(c.x - a.x) + (a.y - c.y).max(c.y - a.y)
}

fn widened(a: Pt, c: Pt, thick: i64) -> Area {
    Area {
        x0: a.x.min(c.x) - thick,
        y0: a.y.min(c.y) - thick,
        x1: a.x.max(c.x) + thick,
        y1: a.y.max(c.y) + thick,
    }
}

impl Builder<'_> {
    pub(super) fn geometry(&mut self) {
        let input = self.input;
        self.boxes = Vec::with_capacity(self.real);
        self.icons = Vec::with_capacity(self.real);
        self.labels = Vec::with_capacity(self.real);
        for (i, n) in input.nodes.iter().enumerate() {
            let c = self.pos[i];
            let (iw, ih) = (i64::from(n.icon.w), i64::from(n.icon.h));
            let x = c.x * self.px + geom::floor_div(self.px - iw, 2);
            let y = if n.junction {
                c.y * self.py + geom::floor_div(self.py - ih, 2)
            } else {
                c.y * self.py + self.top
            };
            self.icons.push(Area {
                x0: x,
                y0: y,
                x1: x + iw,
                y1: y + ih,
            });
            let label_x = x + geom::floor_div(iw - i64::from(n.label.w), 2);
            self.labels.push(sized(label_x, y + ih, n.label));
            self.boxes.push(Area {
                x0: x,
                y0: y,
                x1: x + iw,
                y1: y + ih + i64::from(n.label.h) + self.under_label(n),
            });
        }
        let inset = i64::from(self.p.inset);
        let badge_side = i64::from(self.p.badge);
        self.titles = Vec::with_capacity(input.groups.len());
        self.badges = Vec::with_capacity(input.groups.len());
        for (g, entry) in input.groups.iter().enumerate() {
            let f = self.frame[g];
            let (lead, badge) = if entry.icon {
                (badge_side + inset, badge_side)
            } else {
                (0, 0)
            };
            self.badges.push(Area {
                x0: f.x0 + inset,
                y0: f.y0 + inset,
                x1: f.x0 + inset + badge,
                y1: f.y0 + inset + badge,
            });
            self.titles
                .push(sized(f.x0 + inset + lead, f.y0 + inset, entry.title));
        }
    }

    fn under_label(&self, n: &ArchNode) -> i64 {
        if n.label.h > 0 {
            i64::from(self.p.thickness)
        } else {
            0
        }
    }

    fn vline(&self, k: i64) -> i64 {
        k * self.px - self.shift
    }

    fn hline(&self, k: i64) -> i64 {
        k * self.py - self.shift
    }

    pub(super) fn route(&mut self) {
        let ends = self.assign_ports();
        self.routes = ends
            .iter()
            .map(|pair| self.path(pair[0], pair[1]))
            .collect();
    }

    fn assign_ports(&self) -> Vec<[PortEnd; 2]> {
        let input = self.input;
        let mut slots: Vec<[Vec<EndRef>; 4]> = (0..self.real).map(|_| Default::default()).collect();
        for (i, e) in input.edges.iter().enumerate() {
            slots[e.from][side_index(e.from_side)].push(EndRef { edge: i, to: false });
            slots[e.to][side_index(e.to_side)].push(EndRef { edge: i, to: true });
        }
        let blank = PortEnd {
            p: Pt { x: 0, y: 0 },
            g: Pt { x: 0, y: 0 },
            line: 0,
            vertical: false,
            at: Cell::default(),
        };
        let mut out = vec![[blank; 2]; input.edges.len()];
        for (n, sides) in slots.iter_mut().enumerate() {
            for (s, list) in sides.iter_mut().enumerate() {
                let side = SIDES[s];
                list.sort_by(|x, y| self.compare_ends(side, *x, *y));
                for (k, r) in list.iter().enumerate() {
                    out[r.edge][usize::from(r.to)] = self.end(n, side, k, list.len());
                }
            }
        }
        out
    }

    fn compare_ends(&self, side: RouteSide, x: EndRef, y: EndRef) -> Ordering {
        self.other_key(side, x)
            .cmp(&self.other_key(side, y))
            .then(x.edge.cmp(&y.edge))
            .then(x.to.cmp(&y.to))
    }

    fn other_key(&self, side: RouteSide, r: EndRef) -> i64 {
        let e = self.input.edges[r.edge];
        let other = if r.to { e.from } else { e.to };
        match side {
            RouteSide::Left | RouteSide::Right => self.pos[other].y,
            RouteSide::Up | RouteSide::Down => self.pos[other].x,
        }
    }

    fn end(&self, n: usize, side: RouteSide, index: usize, count: usize) -> PortEnd {
        let (i, k) = if self.input.nodes[n].junction {
            (0, 1)
        } else {
            (index, count)
        };
        let (b, icon, c) = (self.boxes[n], self.icons[n], self.pos[n]);
        let along = |length: i64| {
            geom::floor_div(
                i64::try_from(i + 1).unwrap_or(0) * length,
                i64::try_from(k + 1).unwrap_or(1),
            )
        };
        match side {
            RouteSide::Up => {
                let p = Pt {
                    x: icon.x0 + along(icon.x1 - icon.x0),
                    y: b.y0,
                };
                let line = self.hline(c.y);
                PortEnd {
                    p,
                    g: Pt { x: p.x, y: line },
                    line,
                    vertical: false,
                    at: c,
                }
            }
            RouteSide::Down => {
                let p = Pt {
                    x: icon.x0 + along(icon.x1 - icon.x0),
                    y: b.y1,
                };
                let line = self.hline(c.y + 1);
                PortEnd {
                    p,
                    g: Pt { x: p.x, y: line },
                    line,
                    vertical: false,
                    at: c,
                }
            }
            RouteSide::Left => {
                let p = Pt {
                    x: b.x0,
                    y: icon.y0 + along(icon.y1 - icon.y0),
                };
                let line = self.vline(c.x);
                PortEnd {
                    p,
                    g: Pt { x: line, y: p.y },
                    line,
                    vertical: true,
                    at: c,
                }
            }
            RouteSide::Right => {
                let p = Pt {
                    x: b.x1,
                    y: icon.y0 + along(icon.y1 - icon.y0),
                };
                let line = self.vline(c.x + 1);
                PortEnd {
                    p,
                    g: Pt { x: line, y: p.y },
                    line,
                    vertical: true,
                    at: c,
                }
            }
        }
    }

    fn path(&self, a: PortEnd, c: PortEnd) -> Vec<Pt> {
        let mut points = if a.vertical == c.vertical && a.line == c.line {
            vec![a.p, a.g, c.g, c.p]
        } else if a.vertical && c.vertical {
            let y = self.hline(a.at.y);
            vec![a.p, a.g, Pt { x: a.line, y }, Pt { x: c.line, y }, c.g, c.p]
        } else if !a.vertical && !c.vertical {
            let x = self.vline(a.at.x);
            vec![a.p, a.g, Pt { x, y: a.line }, Pt { x, y: c.line }, c.g, c.p]
        } else if a.vertical {
            vec![
                a.p,
                a.g,
                Pt {
                    x: a.line,
                    y: c.line,
                },
                c.g,
                c.p,
            ]
        } else {
            vec![
                a.p,
                a.g,
                Pt {
                    x: c.line,
                    y: a.line,
                },
                c.g,
                c.p,
            ]
        };
        points.dedup();
        points
    }

    fn content(&self) -> Area {
        let mut all = EMPTY;
        for group in [
            &self.boxes,
            &self.labels,
            &self.frame,
            &self.titles,
            &self.badges,
        ] {
            for r in group {
                all = all.union(*r);
            }
        }
        for p in self.routes.iter().flatten() {
            all = all.union(Area {
                x0: p.x,
                y0: p.y,
                x1: p.x,
                y1: p.y,
            });
        }
        all
    }

    fn place_labels(&self, content: Area) -> Vec<Area> {
        let margin = i64::from(self.p.margin);
        let mut site = Site {
            region: content.inflate(margin),
            fixed: Vec::new(),
            placed: Vec::new(),
        };
        for group in [&self.boxes, &self.labels, &self.titles, &self.badges] {
            site.fixed.extend(group.iter().copied());
        }
        let blank = Area::default();
        let mut out = vec![blank; self.input.edges.len()];
        let spill_x = site.region.x1 + margin;
        let mut spill_y = site.region.y0 + margin;
        for (i, e) in self.input.edges.iter().enumerate() {
            if e.label.w == 0 && e.label.h == 0 {
                continue;
            }
            let r = match self.fit(&site, &self.routes[i], e.label) {
                Some(r) => r,
                None => {
                    let r = sized(spill_x, spill_y, e.label);
                    spill_y += i64::from(e.label.h) + margin;
                    site.region.x1 = site.region.x1.max(r.x1 + margin);
                    site.region.y1 = site.region.y1.max(spill_y);
                    r
                }
            };
            out[i] = r;
            site.placed.push(r);
        }
        out
    }

    fn fit(&self, site: &Site, route: &[Pt], size: Size) -> Option<Area> {
        self.candidates(route, size)
            .into_iter()
            .find(|r| self.label_clear(site, *r))
    }

    fn candidates(&self, route: &[Pt], size: Size) -> Vec<Area> {
        let mut order: Vec<usize> = (0..route.len().saturating_sub(1))
            .filter(|i| route[*i] != route[*i + 1])
            .collect();
        order.sort_by(|i, j| {
            length(route[*j], route[*j + 1]).cmp(&length(route[*i], route[*i + 1]))
        });
        order
            .into_iter()
            .flat_map(|i| self.beside(route[i], route[i + 1], size))
            .collect()
    }

    fn beside(&self, from: Pt, to: Pt, size: Size) -> [Area; 2] {
        let mx = geom::floor_div(from.x + to.x, 2);
        let my = geom::floor_div(from.y + to.y, 2);
        let (w, h) = (i64::from(size.w), i64::from(size.h));
        let off = i64::from(self.p.label_gap);
        let thick = i64::from(self.p.thickness);
        if from.y == to.y {
            return [
                sized(mx - geom::floor_div(w, 2), my - off - h, size),
                sized(mx - geom::floor_div(w, 2), my + thick + off, size),
            ];
        }
        [
            sized(mx + thick + off, my - geom::floor_div(h, 2), size),
            sized(mx - off - w, my - geom::floor_div(h, 2), size),
        ]
    }

    fn label_clear(&self, site: &Site, r: Area) -> bool {
        if !r.strictly_inside(site.region) {
            return false;
        }
        if self
            .frame
            .iter()
            .any(|f| r.overlaps(*f) && !r.strictly_inside(*f))
        {
            return false;
        }
        if site
            .fixed
            .iter()
            .chain(&site.placed)
            .any(|other| r.overlaps(*other))
        {
            return false;
        }
        let thick = i64::from(self.p.thickness);
        !self.routes.iter().any(|route| {
            route
                .windows(2)
                .any(|w| r.overlaps(widened(w[0], w[1], thick)))
        })
    }

    pub(super) fn finish(&self) -> Result<ArchLayout, GeomError> {
        let mut all = self.content();
        if all == EMPTY {
            all = Area::default();
        }
        let labels = self.place_labels(all);
        for r in &labels {
            if r.x1 > r.x0 && r.y1 > r.y0 {
                all = all.union(*r);
            }
        }
        let margin = i64::from(self.p.margin);
        let mut t = Translation {
            dx: margin - all.x0,
            dy: margin - all.y0,
            bad: false,
        };
        let mut out = ArchLayout {
            boxes: t.rects(&self.boxes),
            icons: t.rects(&self.icons),
            labels: t.rects(&self.labels),
            frames: t.rects(&self.frame),
            titles: t.rects(&self.titles),
            group_icons: t.rects(&self.badges),
            routes: Vec::new(),
            edge_labels: t.rects(&labels),
            canvas: Size { w: 0, h: 0 },
            budget: self.budget,
        };
        out.routes = self.routes.iter().map(|route| t.points(route)).collect();
        let width = all.x1 - all.x0 + 2 * margin;
        let height = all.y1 - all.y0 + 2 * margin;
        out.canvas = Size {
            w: t.check(width),
            h: t.check(height),
        };
        if t.bad {
            return Err(GeomError::Overflow);
        }
        Ok(out)
    }
}
