use super::{Axis, Band, LayoutError, narrow};
use crate::geom::Point;
use crate::layout::layered::pipeline;
use crate::scene::{self, GroupRole, Item};

pub(super) struct LaneFrame {
    id: String,
    near: i64,
    length: i64,
}

pub(super) fn lane_frames(axis: Axis, bands: &[Band], boxes: &[scene::SceneBox]) -> Vec<LaneFrame> {
    let mut frames = Vec::new();
    for band in bands {
        let Some(boxed) = boxes.iter().find(|boxed| boxed.id == band.id) else {
            continue;
        };
        frames.push(LaneFrame {
            id: band.id.clone(),
            near: i64::from(axis.start(boxed.rect)) + band.shift - band.start,
            length: i64::from(axis.len(boxed.rect)),
        });
    }
    frames
}

fn attach_end(
    axis: Axis,
    frames: &[LaneFrame],
    boxes: &[scene::SceneBox],
    id: &str,
    point: Point,
) -> Result<Option<Point>, LayoutError> {
    let Some(frame) = frames.iter().find(|frame| frame.id == id) else {
        return Ok(None);
    };
    let Some(boxed) = boxes.iter().find(|boxed| boxed.id == id) else {
        return Ok(None);
    };
    let start = i64::from(axis.start(boxed.rect));
    let lo = start + frame.near;
    let hi = lo + frame.length;
    let cross = i64::from(axis.value(point));
    if cross == hi {
        Ok(Some(axis.with(
            point,
            narrow(start + i64::from(axis.len(boxed.rect)))?,
        )))
    } else if cross == lo {
        Ok(Some(axis.with(point, axis.start(boxed.rect))))
    } else {
        Ok(None)
    }
}

pub(super) fn attach_lane_ends(
    dump: &mut scene::Dump,
    items: &mut [scene::Group],
    axis: Axis,
    frames: &[LaneFrame],
) -> Result<(), LayoutError> {
    for index in 0..dump.routes.len() {
        let Some(first) = dump.routes[index].points.first().copied() else {
            continue;
        };
        let Some(last) = dump.routes[index].points.last().copied() else {
            continue;
        };
        let head = {
            let route = &dump.routes[index];
            attach_end(axis, frames, &dump.boxes, &route.from, first)?
        };
        let tail = {
            let route = &dump.routes[index];
            attach_end(axis, frames, &dump.boxes, &route.to, last)?
        };
        if head.is_none() && tail.is_none() {
            continue;
        }
        let mut raw = Vec::with_capacity(dump.routes[index].points.len() + 2);
        if let Some(point) = head {
            raw.push(point);
        }
        raw.extend_from_slice(&dump.routes[index].points);
        if let Some(point) = tail {
            raw.push(point);
        }
        let points = super::routing::simplify(raw);
        if points == dump.routes[index].points {
            continue;
        }
        let owner = dump.routes[index].id.clone();
        let previous = std::mem::replace(&mut dump.routes[index].points, points);
        retarget(items, &owner, &previous, &dump.routes[index].points);
    }
    Ok(())
}

fn retarget(items: &mut [scene::Group], owner: &str, previous: &[Point], points: &[Point]) {
    for group in items.iter_mut() {
        if group.role != GroupRole::Edge || group.owner != owner {
            continue;
        }
        for item in &mut group.items {
            match item {
                Item::Polyline(line) => {
                    line.points.clear();
                    line.points.extend_from_slice(points);
                }
                Item::MarkerRef(marker) => {
                    if previous.first() == Some(&marker.at) {
                        let at = points.first().copied().unwrap_or(marker.at);
                        marker.axis =
                            pipeline::marker_axis(points.get(1).copied().unwrap_or(at), at);
                        marker.at = at;
                    } else if previous.last() == Some(&marker.at) {
                        let at = points.last().copied().unwrap_or(marker.at);
                        let before = if points.len() > 1 {
                            points[points.len() - 2]
                        } else {
                            at
                        };
                        marker.axis = pipeline::marker_axis(before, at);
                        marker.at = at;
                    }
                }
                _ => {}
            }
        }
    }
}
