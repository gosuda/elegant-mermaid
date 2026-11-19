use super::*;
use crate::layout::input::AttachmentSide;

pub(super) struct Footprint {
    pub size: Size,
    pub target: Rect,
    pub notes: Vec<Rect>,
}

pub(super) struct NoteSize {
    pub size: Size,
    pub side: AttachmentSide,
}

pub(super) struct FootprintInput<'a> {
    pub target: Size,
    pub notes: &'a [NoteSize],
    pub direction: Direction,
    pub gap: i32,
}

pub(super) fn footprint(input: FootprintInput<'_>) -> Result<Footprint, LayoutError> {
    let target = oriented(input.target, input.direction);
    let notes: Vec<_> = input
        .notes
        .iter()
        .map(|note| oriented(note.size, input.direction))
        .collect();
    let mut left = i64::from(input.gap);
    let mut right = i64::from(input.gap);
    let mut height = target.h;
    for (note, size) in input.notes.iter().zip(&notes) {
        let extent = i64::from(size.w) + i64::from(input.gap);
        match note.side {
            AttachmentSide::Left => left += extent,
            AttachmentSide::Right => right += extent,
        }
        height = height.max(size.h);
    }
    let width = narrow(left + i64::from(target.w) + right)?;
    let height = narrow(i64::from(height) + 2 * i64::from(input.gap))?;
    let target = Rect {
        x: narrow(left)?,
        y: (height - target.h) / 2,
        w: target.w,
        h: target.h,
    };
    let extent = Size {
        w: width,
        h: height,
    };
    let mut left = i64::from(input.gap);
    let mut right = i64::from(target.x) + i64::from(target.w) + i64::from(input.gap);
    let mut rectangles = Vec::with_capacity(notes.len());
    for (note, size) in input.notes.iter().zip(notes) {
        let cursor = match note.side {
            AttachmentSide::Left => &mut left,
            AttachmentSide::Right => &mut right,
        };
        let rect = Rect {
            x: narrow(*cursor)?,
            y: (height - size.h) / 2,
            w: size.w,
            h: size.h,
        };
        *cursor += i64::from(size.w) + i64::from(input.gap);
        rectangles.push(inverse(rect, extent, input.direction));
    }
    Ok(Footprint {
        size: oriented(extent, input.direction),
        target: inverse(target, extent, input.direction),
        notes: rectangles,
    })
}

fn oriented(size: Size, direction: Direction) -> Size {
    if matches!(direction, Direction::Lr | Direction::Rl) {
        Size {
            w: size.h,
            h: size.w,
        }
    } else {
        size
    }
}

fn inverse(rect: Rect, extent: Size, direction: Direction) -> Rect {
    match direction {
        Direction::Tb => rect,
        Direction::Bt => Rect {
            y: extent.h - rect.y - rect.h,
            ..rect
        },
        Direction::Lr => Rect {
            x: rect.y,
            y: rect.x,
            w: rect.h,
            h: rect.w,
        },
        Direction::Rl => Rect {
            x: rect.y,
            y: extent.w - rect.x - rect.w,
            w: rect.h,
            h: rect.w,
        },
    }
}

pub(super) fn translated(rect: Rect, offset: Point) -> Result<Rect, LayoutError> {
    Ok(Rect {
        x: narrow(i64::from(rect.x) + i64::from(offset.x))?,
        y: narrow(i64::from(rect.y) + i64::from(offset.y))?,
        ..rect
    })
}
