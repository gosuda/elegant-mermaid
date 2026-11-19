//! Display-list primitives of the Wardley plan: nodes, strategy halos, pipeline frames,
//! force arrows, annotation markers, and the map decoration.

use crate::geom::{GeomError, Point, floor_div};
use crate::scene::{
    EllipseItem, Item, Line, MarkerAxis, MarkerName, MarkerRefItem, PathCommand, PathItem,
    PolygonItem, PolylineItem, RectItem, Shape, ShapeStyle, SymbolName, SymbolRefItem, Width,
};

use super::wardley::{MARKER_POINT, WardleyNode, WardleyStrategy};
use super::wardley_plan::{Plan, Pt};
use super::{Area, LayoutError, to_i32};

pub(super) fn point_of(x: i64, y: i64) -> Result<Point, LayoutError> {
    Ok(Point {
        x: to_i32(x)?,
        y: to_i32(y)?,
    })
}

fn points_of(points: &[Pt]) -> Result<Vec<Point>, LayoutError> {
    points.iter().map(|q| point_of(q.x, q.y)).collect()
}

fn circle(shape: Shape, at: Pt, r: i64) -> Result<Item, LayoutError> {
    Ok(Item::Ellipse(EllipseItem {
        shape,
        cx: to_i32(at.x)?,
        cy: to_i32(at.y)?,
        rx: to_i32(r)?,
        ry: to_i32(r)?,
    }))
}

fn rectangle(shape: Shape, area: Area) -> Result<Item, LayoutError> {
    Ok(Item::Rect(RectItem {
        shape,
        rect: area.to_rect()?,
    }))
}

fn polygon(shape: Shape, points: &[Pt]) -> Result<Item, LayoutError> {
    Ok(Item::Polygon(PolygonItem {
        shape,
        points: points_of(points)?,
    }))
}

pub(super) fn open_path(shape: Shape, points: &[Pt]) -> Result<Item, LayoutError> {
    path(shape, points, &[])
}

fn closed_path(shape: Shape, points: &[Pt]) -> Result<Item, LayoutError> {
    path(shape, points, &[PathCommand::Close])
}

fn path(shape: Shape, points: &[Pt], tail: &[PathCommand]) -> Result<Item, LayoutError> {
    let mut commands = Vec::with_capacity(points.len() + tail.len());
    for (i, q) in points.iter().enumerate() {
        let at = point_of(q.x, q.y)?;
        commands.push(if i == 0 {
            PathCommand::Move(at)
        } else {
            PathCommand::Line(at)
        });
    }
    commands.extend_from_slice(tail);
    Ok(Item::Path(PathItem { shape, commands }))
}

fn symbol(name: &'static str, style: ShapeStyle, at: Pt) -> Result<Item, LayoutError> {
    Ok(Item::SymbolRef(SymbolRefItem {
        symbol: SymbolName::new(name).ok_or(GeomError::Domain)?,
        at: point_of(at.x, at.y)?,
        style,
    }))
}

pub(super) fn marker(at: Pt, axis: MarkerAxis) -> Result<Item, LayoutError> {
    Ok(Item::MarkerRef(MarkerRefItem {
        marker: MarkerName::new(MARKER_POINT).ok_or(GeomError::Domain)?,
        at: point_of(at.x, at.y)?,
        axis,
    }))
}

fn styled(style: ShapeStyle) -> Shape {
    Shape::plain(style)
}

fn lined(style: ShapeStyle, line: Line) -> Shape {
    Shape::plain(style).with_line(line)
}

fn cell_symbol(n: &WardleyNode) -> (&'static str, ShapeStyle) {
    if n.pipeline_parent {
        return ("box-hollow", ShapeStyle::MarkHollow);
    }
    match n.strategy {
        WardleyStrategy::Build => ("diamond-hollow", ShapeStyle::MarkHollow),
        WardleyStrategy::Buy => ("diamond", ShapeStyle::Mark),
        WardleyStrategy::Outsource => ("disc", ShapeStyle::Mark),
        WardleyStrategy::Market => ("bullseye", ShapeStyle::Mark),
        WardleyStrategy::None => ("ring", ShapeStyle::MarkHollow),
    }
}

impl Plan<'_> {
    pub(super) fn node_items(&self, k: usize) -> Result<Vec<Item>, LayoutError> {
        let n = &self.w.nodes[k];
        let at = self.pos[k];
        if n.anchor {
            return Ok(Vec::new());
        }
        if self.cell {
            self.cell_node(n, at)
        } else {
            self.vector_node(n, at)
        }
    }

    fn cell_node(&self, n: &WardleyNode, at: Pt) -> Result<Vec<Item>, LayoutError> {
        let (name, style) = cell_symbol(n);
        let mut items = vec![symbol(name, style, at)?];
        if n.inertia {
            let bar = Area::new(at.x + self.c.inertia_gap, at.y, 1, 1);
            items.push(rectangle(styled(ShapeStyle::Ink), bar)?);
        }
        Ok(items)
    }

    fn vector_node(&self, n: &WardleyNode, at: Pt) -> Result<Vec<Item>, LayoutError> {
        let c = self.c;
        let mut items = Vec::new();
        if n.pipeline_parent {
            let half = floor_div(c.square_size, 2);
            let square = Area::new(at.x - half, at.y - half, c.square_size, c.square_size);
            items.push(rectangle(styled(ShapeStyle::Node), square)?);
        } else {
            items.extend(self.strategy_shapes(n, at)?);
            items.push(circle(styled(ShapeStyle::MarkHollow), at, c.node_radius)?);
        }
        if n.inertia {
            let reach = self.reach(n);
            let x = at.x + reach + c.inertia_gap;
            let bar =
                styled(ShapeStyle::InkLine).with_width(Width::Units(to_i32(c.inertia_width)?));
            let ends = [Pt { x, y: at.y - reach }, Pt { x, y: at.y + reach }];
            items.push(Item::Polyline(PolylineItem {
                shape: bar,
                points: points_of(&ends)?,
                corner: 0,
            }));
        }
        Ok(items)
    }

    fn strategy_shapes(&self, n: &WardleyNode, at: Pt) -> Result<Vec<Item>, LayoutError> {
        let outer = 2 * self.c.node_radius;
        match n.strategy {
            WardleyStrategy::Build => Ok(vec![circle(
                lined(ShapeStyle::MarkHollow, Line::Dashed),
                at,
                outer,
            )?]),
            WardleyStrategy::Buy => Ok(vec![circle(styled(ShapeStyle::Mark), at, outer)?]),
            WardleyStrategy::Outsource => Ok(vec![circle(styled(ShapeStyle::Ink), at, outer)?]),
            WardleyStrategy::Market => self.market_shapes(at, outer),
            WardleyStrategy::None => Ok(Vec::new()),
        }
    }

    fn market_shapes(&self, at: Pt, outer: i64) -> Result<Vec<Item>, LayoutError> {
        let c = self.c;
        let side = floor_div(7 * c.market_ring, 8);
        let drop = floor_div(c.market_ring, 2);
        let corners = [
            Pt {
                x: at.x,
                y: at.y - c.market_ring,
            },
            Pt {
                x: at.x - side,
                y: at.y + drop,
            },
            Pt {
                x: at.x + side,
                y: at.y + drop,
            },
        ];
        let mut items = vec![
            circle(styled(ShapeStyle::MarkHollow), at, outer)?,
            polygon(styled(ShapeStyle::Rule), &corners)?,
        ];
        for q in corners {
            items.push(circle(styled(ShapeStyle::MarkHollow), q, c.market_dot)?);
        }
        Ok(items)
    }

    pub(super) fn ghost_items(&self, k: usize) -> Result<Vec<Item>, LayoutError> {
        let at = self.ghosts[k];
        if self.cell {
            return Ok(vec![symbol("ring", ShapeStyle::MarkHollow, at)?]);
        }
        Ok(vec![circle(
            lined(ShapeStyle::MarkHollow, Line::Dotted),
            at,
            self.c.node_radius,
        )?])
    }

    fn force_points(&self, a: Area) -> Vec<Pt> {
        let c = self.c;
        let half = c.arrow_shaft + c.arrow_head;
        let (cy, x0, x1) = (a.y + half, a.x, a.x + a.w - c.edge);
        let tip = x1 - c.arrow_tip;
        [
            (x0, cy - c.arrow_shaft),
            (tip, cy - c.arrow_shaft),
            (tip, cy - half),
            (x1, cy),
            (tip, cy + half),
            (tip, cy + c.arrow_shaft),
            (x0, cy + c.arrow_shaft),
        ]
        .map(|(x, y)| Pt { x, y })
        .to_vec()
    }

    pub(super) fn accelerator_items(&self, a: Area) -> Result<Vec<Item>, LayoutError> {
        Ok(vec![polygon(
            styled(ShapeStyle::MarkHollow),
            &self.force_points(a),
        )?])
    }

    pub(super) fn deaccelerator_items(&self, a: Area) -> Result<Vec<Item>, LayoutError> {
        let (left, right) = (a.x, a.x + a.w - self.c.edge);
        let mirrored: Vec<Pt> = self
            .force_points(a)
            .into_iter()
            .map(|q| Pt {
                x: left + right - q.x,
                y: q.y,
            })
            .collect();
        Ok(vec![polygon(styled(ShapeStyle::MarkHollow), &mirrored)?])
    }

    pub(super) fn annotation_items(&self, k: usize) -> Result<Vec<Item>, LayoutError> {
        if self.cell {
            return Ok(Vec::new());
        }
        Ok(vec![circle(
            styled(ShapeStyle::MarkHollow),
            self.points[k],
            self.c.annotation_radius,
        )?])
    }

    pub(super) fn box_items(&self) -> Result<Vec<Item>, LayoutError> {
        Ok(vec![rectangle(styled(ShapeStyle::Note), self.box_area)?])
    }

    pub(super) fn frame_items(&self, k: usize) -> Result<Vec<Item>, LayoutError> {
        let r = self.frames[k];
        let (x1, y1) = (r.x + r.w - self.c.edge, r.y + r.h - self.c.edge);
        let corners = [
            Pt { x: r.x, y: r.y },
            Pt { x: x1, y: r.y },
            Pt { x: x1, y: y1 },
            Pt { x: r.x, y: y1 },
        ];
        Ok(vec![closed_path(styled(ShapeStyle::Group), &corners)?])
    }

    pub(super) fn decor_items(&self) -> Result<Vec<Item>, LayoutError> {
        let pl = self.plot;
        let (right, bottom) = (pl.x + pl.w, pl.y + pl.h);
        let axes = [
            Pt { x: pl.x, y: pl.y },
            Pt { x: pl.x, y: bottom },
            Pt {
                x: right,
                y: bottom,
            },
        ];
        let mut items = vec![open_path(styled(ShapeStyle::Rule), &axes)?];
        for i in 1..self.w.stages.len() {
            let (_, x) = self.stage_span(i - 1);
            let divider = [Pt { x, y: pl.y }, Pt { x, y: bottom }];
            items.push(open_path(lined(ShapeStyle::Rule, Line::Dotted), &divider)?);
        }
        Ok(items)
    }
}
