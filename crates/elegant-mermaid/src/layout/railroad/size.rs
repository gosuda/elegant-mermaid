use super::tree::{Constants, Kind, Node, Params, Pt};
use crate::geom::{GeomError, floor_div};

pub(super) struct Shape<'a> {
    pub node: &'a Node,
    pub kids: Vec<Shape<'a>>,
    pub offsets: Vec<Pt>,
    pub w: i64,
    pub up: i64,
    pub down: i64,
}

impl Shape<'_> {
    pub(super) fn height(&self) -> i64 {
        self.up + self.down
    }

    pub(super) fn centre(&self) -> i64 {
        self.up
    }
}

pub(super) fn measure<'a>(node: &'a Node, p: &Params) -> Result<Shape<'a>, GeomError> {
    let (min, max) = node.kind.arity();
    if node.children.len() < min || node.children.len() > max {
        return Err(GeomError::Domain);
    }
    let kids = node
        .children
        .iter()
        .map(|child| measure(child, p))
        .collect::<Result<Vec<_>, _>>()?;
    let mut shape = Shape {
        node,
        kids,
        offsets: Vec::new(),
        w: 0,
        up: 0,
        down: 0,
    };
    size(&mut shape, p)?;
    if shape.w > i64::from(i32::MAX) || shape.height() > i64::from(i32::MAX) {
        return Err(GeomError::Overflow);
    }
    Ok(shape)
}

fn size(shape: &mut Shape<'_>, p: &Params) -> Result<(), GeomError> {
    let k = &p.constants;
    match shape.node.kind {
        Kind::Sequence => size_sequence(shape, k),
        Kind::Choice => size_choice(shape, k),
        Kind::Optional | Kind::ZeroOrMore | Kind::OneOrMore => size_wrapper(shape, k),
        Kind::Terminal | Kind::NonTerminal | Kind::Special => return size_leaf(shape, p),
    }
    Ok(())
}

fn size_leaf(shape: &mut Shape<'_>, p: &Params) -> Result<(), GeomError> {
    let width = p.metric.width(&shape.node.text)?;
    let k = &p.constants;
    let height = k.line_height + 2 * k.pad_y;
    shape.w = i64::from(width) + 2 * k.pad_x;
    shape.up = floor_div(height, 2);
    shape.down = height - shape.up;
    Ok(())
}

fn size_sequence(shape: &mut Shape<'_>, k: &Constants) {
    let mut x = 0;
    for kid in &shape.kids {
        shape.offsets.push(Pt { x, y: 0 });
        x += kid.w + k.hsep;
        shape.up = shape.up.max(kid.up);
        shape.down = shape.down.max(kid.down);
    }
    shape.w = x - k.hsep;
    for (offset, kid) in shape.offsets.iter_mut().zip(&shape.kids) {
        offset.y = shape.up - kid.up;
    }
}

fn size_choice(shape: &mut Shape<'_>, k: &Constants) {
    let mut widest = 0;
    let mut total = 0;
    for kid in &shape.kids {
        widest = widest.max(kid.w);
        total += kid.height() + k.vsep;
    }
    total -= k.vsep;
    let arc = k.arc_radius;
    let mut y = 0;
    for kid in &shape.kids {
        shape.offsets.push(Pt {
            x: 2 * arc + floor_div(widest - kid.w, 2),
            y,
        });
        y += kid.height() + k.vsep;
    }
    shape.w = widest + 4 * arc;
    shape.up = floor_div(total, 2);
    shape.down = total - shape.up;
}

fn size_wrapper(shape: &mut Shape<'_>, k: &Constants) {
    let arc = k.arc_radius;
    let kid = &shape.kids[0];
    let mut child_y = 2 * arc;
    let mut height = kid.height() + 2 * arc;
    match shape.node.kind {
        Kind::ZeroOrMore => height += 2 * arc,
        Kind::OneOrMore => child_y = 0,
        _ => {}
    }
    shape.offsets = vec![Pt {
        x: 2 * arc,
        y: child_y,
    }];
    shape.w = kid.w + 4 * arc;
    shape.up = child_y + kid.up;
    shape.down = height - shape.up;
}
