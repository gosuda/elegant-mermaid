//! The grid layout family (`spec/layout/grid.md`): the block engine that the
//! architecture, kanban, and packet kinds reuse. It receives measured sizes and
//! relations in declaration order and returns integer rectangles, routes, and label
//! rectangles. Every coordinate is an integer in profile units.

pub(crate) mod architecture;
mod kanban;
mod label;
pub(crate) mod packet;
mod route;

pub(crate) use kanban::{
    KanbanCard, KanbanInput, KanbanLayout, KanbanParams, KanbanSection, kanban,
};

use crate::geom::{self, GeomError, Point, Rect, Size};

const MAX_TRACKS: i64 = 1 << 14;
const MAX_DEPTH: usize = 66;
const COORD_LIMIT: i64 = geom::COORD_LIMIT;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    Leaf,
    Space,
    Composite,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Block {
    pub parent: Option<usize>,
    pub kind: Kind,
    pub span: i32,
    pub columns: i32,
    pub size: Size,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Edge {
    pub from: usize,
    pub to: usize,
    pub label: Size,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Input {
    pub columns: i32,
    pub blocks: Vec<Block>,
    pub edges: Vec<Edge>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Params {
    pub padding: i32,
    pub bend_cost: i32,
    pub line_thickness: i32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Layout {
    pub rects: Vec<Rect>,
    pub routes: Vec<Vec<Point>>,
    pub labels: Vec<Rect>,
    pub canvas: Size,
}

#[derive(Debug, Clone, Default)]
struct Plan {
    order: Vec<usize>,
    col: Vec<i64>,
    row: Vec<i64>,
    eff: Vec<i64>,
    ncols: i64,
    nrows: i64,
    unit: i64,
    rows: Vec<i64>,
    width: i64,
    height: i64,
}

struct Builder<'a> {
    input: &'a Input,
    params: Params,
    gap_x: i64,
    gap_y: i64,
    children: Vec<Vec<usize>>,
    plans: Vec<Plan>,
    rects: Vec<Rect>,
    vlines: Vec<i64>,
    hlines: Vec<i64>,
}

pub(crate) fn block(input: &Input, params: Params) -> Result<Layout, GeomError> {
    let mut builder = Builder {
        input,
        params,
        gap_x: 0,
        gap_y: 0,
        children: Vec::new(),
        plans: Vec::new(),
        rects: Vec::new(),
        vlines: Vec::new(),
        hlines: Vec::new(),
    };
    builder.validate()?;
    builder.gaps();
    let root = input.blocks.len();
    builder.plans = vec![Plan::default(); root + 1];
    builder.rects = vec![zero_rect(); root + 1];
    builder.measure(root, 0)?;
    let mut canvas = Rect {
        x: 0,
        y: 0,
        w: to_i32(builder.plans[root].width),
        h: to_i32(builder.plans[root].height),
    };
    builder.place(root, canvas)?;
    let (routes, labels) = builder.connect(&mut canvas)?;
    builder.rects[root] = canvas;
    Ok(Layout {
        rects: builder.rects,
        routes,
        labels,
        canvas: Size {
            w: canvas.w,
            h: canvas.h,
        },
    })
}

const fn zero_rect() -> Rect {
    Rect {
        x: 0,
        y: 0,
        w: 0,
        h: 0,
    }
}

fn to_i32(value: i64) -> i32 {
    i32::try_from(value).unwrap_or(i32::MAX)
}

fn ceil_div(a: i64, b: i64) -> i64 {
    geom::floor_div(a + b - 1, b)
}

fn product(a: i64, b: i64) -> Result<i64, GeomError> {
    if a == 0 || b == 0 {
        return Ok(0);
    }
    if a > COORD_LIMIT / b {
        return Err(GeomError::Overflow);
    }
    Ok(a * b)
}

fn within(value: i64) -> Result<i64, GeomError> {
    if !(0..=COORD_LIMIT).contains(&value) {
        return Err(GeomError::Overflow);
    }
    Ok(value)
}

impl Edge {
    fn valid(&self, blocks: usize) -> bool {
        self.from < blocks && self.to < blocks && self.label.w >= 0 && self.label.h >= 0
    }
}

impl Builder<'_> {
    fn validate(&mut self) -> Result<(), GeomError> {
        let n = self.input.blocks.len();
        if self.params.padding < 0 {
            return Err(GeomError::Domain);
        }
        self.children = vec![Vec::new(); n + 1];
        for i in 0..n {
            let slot = self.slot(i)?;
            self.children[slot].push(i);
        }
        if self.input.edges.iter().any(|edge| !edge.valid(n)) {
            return Err(GeomError::Domain);
        }
        Ok(())
    }

    fn slot(&self, i: usize) -> Result<usize, GeomError> {
        let n = self.input.blocks.len();
        let block = &self.input.blocks[i];
        if block.size.w < 0 || block.size.h < 0 {
            return Err(GeomError::Domain);
        }
        let Some(parent) = block.parent else {
            return Ok(n);
        };
        if parent >= n || parent == i || self.input.blocks[parent].kind != Kind::Composite {
            return Err(GeomError::Domain);
        }
        Ok(parent)
    }

    fn gaps(&mut self) {
        let (mut label_w, mut label_h) = (0i64, 0i64);
        for edge in &self.input.edges {
            label_w = label_w.max(i64::from(edge.label.w));
            label_h = label_h.max(i64::from(edge.label.h));
        }
        let mut corridor = i64::from(self.params.padding);
        if !self.input.edges.is_empty() {
            corridor *= 2;
        }
        self.gap_x = corridor + label_w;
        self.gap_y = corridor + label_h;
    }

    fn measure(&mut self, i: usize, depth: usize) -> Result<(i64, i64), GeomError> {
        let root = self.input.blocks.len();
        if i != root && self.input.blocks[i].kind != Kind::Composite {
            let size = self.input.blocks[i].size;
            return Ok((i64::from(size.w), i64::from(size.h)));
        }
        if depth > MAX_DEPTH {
            return Err(GeomError::Domain);
        }
        let plan = self.tracks(i, depth)?;
        let measured = (plan.width, plan.height);
        self.plans[i] = plan;
        Ok(measured)
    }

    fn column_limit(&self, i: usize) -> i64 {
        if i == self.input.blocks.len() {
            return i64::from(self.input.columns.max(0));
        }
        i64::from(self.input.blocks[i].columns.max(0))
    }

    fn tracks(&mut self, i: usize, depth: usize) -> Result<Plan, GeomError> {
        let order = std::mem::take(&mut self.children[i]);
        let mut plan = Plan::default();
        let columns = self.column_limit(i);
        let mut position = 0i64;
        let mut widths = Vec::with_capacity(order.len());
        let mut heights = Vec::with_capacity(order.len());
        for child in order.iter().copied() {
            let (w, h) = self.measure(child, depth + 1)?;
            let block = self.input.blocks[child];
            let mut span = i64::from(block.span.max(1));
            let (mut col, mut row) = (position, 0i64);
            if columns > 0 {
                col = position % columns;
                row = position / columns;
                span = span.min(columns - col);
            }
            plan.col.push(col);
            plan.row.push(row);
            plan.eff.push(span);
            plan.ncols = plan.ncols.max(col + span);
            plan.nrows = plan.nrows.max(row + 1);
            let sized = block.kind != Kind::Space;
            widths.push(if sized { w } else { 0 });
            heights.push(if sized { h } else { 0 });
            position += span;
        }
        if plan.ncols > MAX_TRACKS || plan.nrows > MAX_TRACKS {
            return Err(GeomError::Overflow);
        }
        plan.order = order;
        self.size(&mut plan, &widths, &heights)?;
        Ok(plan)
    }

    fn size(&self, plan: &mut Plan, widths: &[i64], heights: &[i64]) -> Result<(), GeomError> {
        for (k, width) in widths.iter().enumerate() {
            plan.unit = plan.unit.max(ceil_div(*width, plan.eff[k]));
        }
        let nrows = usize::try_from(plan.nrows).map_err(|_| GeomError::Overflow)?;
        plan.rows = vec![0; nrows];
        for (k, height) in heights.iter().enumerate() {
            let row = usize::try_from(plan.row[k]).map_err(|_| GeomError::Overflow)?;
            plan.rows[row] = plan.rows[row].max(*height);
        }
        let body = product(plan.ncols, plan.unit)?;
        let margins = product(plan.ncols + 1, self.gap_x)?;
        plan.width = within(body + margins)?;
        let rows: i64 = plan.rows.iter().sum();
        let spacing = product(plan.nrows + 1, self.gap_y)?;
        plan.height = within(rows + spacing)?;
        Ok(())
    }

    fn place(&mut self, i: usize, frame: Rect) -> Result<(), GeomError> {
        let plan = std::mem::take(&mut self.plans[i]);
        let pad = i64::from(self.params.padding);
        for j in 0..=plan.ncols {
            self.vlines
                .push(i64::from(frame.x) + j * (plan.unit + self.gap_x) + pad);
        }
        let mut top = i64::from(frame.y);
        let mut row_top = vec![top];
        for rows in &plan.rows {
            self.hlines.push(top + pad);
            top += rows + self.gap_y;
            row_top.push(top);
        }
        self.hlines.push(top + pad);
        for (k, child) in plan.order.iter().copied().enumerate() {
            let row = usize::try_from(plan.row[k]).map_err(|_| GeomError::Overflow)?;
            let x = i64::from(frame.x) + self.gap_x + plan.col[k] * (plan.unit + self.gap_x);
            let w = plan.unit * plan.eff[k] + self.gap_x * (plan.eff[k] - 1);
            let y = row_top[row] + self.gap_y;
            let h = plan.rows[row];
            if y + h > COORD_LIMIT || x + w > COORD_LIMIT {
                return Err(GeomError::Overflow);
            }
            self.rects[child] = Rect {
                x: to_i32(x),
                y: to_i32(y),
                w: to_i32(w),
                h: to_i32(h),
            };
            if self.input.blocks[child].kind == Kind::Composite {
                self.place(child, self.rects[child])?;
            }
        }
        Ok(())
    }

    fn rects_of(&self, kind: Kind) -> Vec<Rect> {
        self.input
            .blocks
            .iter()
            .zip(&self.rects)
            .filter(|(block, _)| block.kind == kind)
            .map(|(_, rect)| *rect)
            .collect()
    }
}

fn sorted_unique(mut values: Vec<i64>) -> Vec<i32> {
    values.sort_unstable();
    values.dedup();
    values.into_iter().map(to_i32).collect()
}

#[cfg(test)]
mod tests;
