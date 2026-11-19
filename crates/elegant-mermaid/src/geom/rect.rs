use super::{Axis, GeomError, Rect, Size, floor_div, rect_from, rect_is_valid};

pub fn translate(r: Rect, dx: i32, dy: i32) -> Result<Rect, GeomError> {
    if !rect_is_valid(&r) {
        return Err(GeomError::Domain);
    }
    rect_from(
        i64::from(r.x) + i64::from(dx),
        i64::from(r.y) + i64::from(dy),
        i64::from(r.w),
        i64::from(r.h),
    )
}

pub fn inflate(r: Rect, d: i32) -> Result<Rect, GeomError> {
    if !rect_is_valid(&r) {
        return Err(GeomError::Domain);
    }
    let delta = i64::from(d);
    let width = i64::from(r.w) + 2 * delta;
    let height = i64::from(r.h) + 2 * delta;
    if width < 0 || height < 0 {
        return Err(GeomError::Domain);
    }
    rect_from(
        i64::from(r.x) - delta,
        i64::from(r.y) - delta,
        width,
        height,
    )
}

pub fn union(a: Rect, b: Rect) -> Result<Rect, GeomError> {
    if !rect_is_valid(&a) || !rect_is_valid(&b) {
        return Err(GeomError::Domain);
    }
    let left = i64::from(a.x).min(i64::from(b.x));
    let top = i64::from(a.y).min(i64::from(b.y));
    let right = (i64::from(a.x) + i64::from(a.w)).max(i64::from(b.x) + i64::from(b.w));
    let bottom = (i64::from(a.y) + i64::from(a.h)).max(i64::from(b.y) + i64::from(b.h));
    rect_from(left, top, right - left, bottom - top)
}

pub fn intersects(a: Rect, b: Rect) -> Result<bool, GeomError> {
    if !rect_is_valid(&a) || !rect_is_valid(&b) {
        return Err(GeomError::Domain);
    }
    let low_x = i64::from(a.x).max(i64::from(b.x));
    let high_x = (i64::from(a.x) + i64::from(a.w)).min(i64::from(b.x) + i64::from(b.w));
    let low_y = i64::from(a.y).max(i64::from(b.y));
    let high_y = (i64::from(a.y) + i64::from(a.h)).min(i64::from(b.y) + i64::from(b.h));
    Ok(low_x < high_x && low_y < high_y)
}

pub fn contains(outer: Rect, inner: Rect) -> Result<bool, GeomError> {
    if !rect_is_valid(&outer) || !rect_is_valid(&inner) {
        return Err(GeomError::Domain);
    }
    let outer_right = i64::from(outer.x) + i64::from(outer.w);
    let outer_bottom = i64::from(outer.y) + i64::from(outer.h);
    let inner_right = i64::from(inner.x) + i64::from(inner.w);
    let inner_bottom = i64::from(inner.y) + i64::from(inner.h);
    Ok(i64::from(outer.x) <= i64::from(inner.x)
        && inner_right <= outer_right
        && i64::from(outer.y) <= i64::from(inner.y)
        && inner_bottom <= outer_bottom)
}

pub fn place_after(axis: Axis, a: Rect, gap: i32, s: Size) -> Result<Rect, GeomError> {
    if !rect_is_valid(&a) || gap < 0 || s.w < 0 || s.h < 0 {
        return Err(GeomError::Domain);
    }
    let distance = i64::from(gap);
    match axis {
        Axis::X => rect_from(
            i64::from(a.x) + i64::from(a.w) + distance,
            i64::from(a.y),
            i64::from(s.w),
            i64::from(s.h),
        ),
        Axis::Y => rect_from(
            i64::from(a.x),
            i64::from(a.y) + i64::from(a.h) + distance,
            i64::from(s.w),
            i64::from(s.h),
        ),
    }
}

pub fn compact(axis: Axis, gap: i32, items: &[Rect]) -> Result<Vec<Rect>, GeomError> {
    if gap < 0 || items.iter().any(|item| !rect_is_valid(item)) {
        return Err(GeomError::Domain);
    }
    let distance = i64::from(gap);
    let mut out: Vec<Rect> = Vec::with_capacity(items.len());
    for item in items {
        let position = match out.last() {
            None => axis_start(axis, item),
            Some(last) => {
                let prior = axis_start(axis, last) + axis_length(axis, last) + distance;
                prior.max(axis_start(axis, item))
            }
        };
        out.push(moved_rect(axis, item, position)?);
    }
    Ok(out)
}

fn axis_start(axis: Axis, r: &Rect) -> i64 {
    match axis {
        Axis::X => i64::from(r.x),
        Axis::Y => i64::from(r.y),
    }
}

fn axis_length(axis: Axis, r: &Rect) -> i64 {
    match axis {
        Axis::X => i64::from(r.w),
        Axis::Y => i64::from(r.h),
    }
}

fn moved_rect(axis: Axis, r: &Rect, position: i64) -> Result<Rect, GeomError> {
    match axis {
        Axis::X => rect_from(position, i64::from(r.y), i64::from(r.w), i64::from(r.h)),
        Axis::Y => rect_from(i64::from(r.x), position, i64::from(r.w), i64::from(r.h)),
    }
}

pub fn isqrt(n: i64) -> Result<i64, GeomError> {
    if n < 0 {
        return Err(GeomError::Domain);
    }
    if n < 2 {
        return Ok(n);
    }
    let mut lo: i64 = 1;
    let mut hi: i64 = 3_037_000_500;
    while lo < hi {
        let mid = lo + floor_div(hi - lo + 1, 2);
        match mid.checked_mul(mid) {
            Some(square) if square <= n => lo = mid,
            _ => hi = mid - 1,
        }
    }
    Ok(lo)
}

#[cfg(test)]
mod tests {
    use super::super::testing::Xorshift32;
    use super::{compact, contains, inflate, intersects, isqrt, place_after, translate, union};
    use crate::geom::{Axis, GeomError, Rect, Size};

    fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
        Rect { x, y, w, h }
    }

    fn doubled(value: i32) -> i64 {
        i64::from(value) * 2
    }

    fn doubled_edge(start: i32, length: i32) -> i64 {
        (i64::from(start) + i64::from(length)) * 2
    }

    fn interior_point(x: i64, y: i64, r: Rect) -> bool {
        x > doubled(r.x)
            && x < doubled_edge(r.x, r.w)
            && y > doubled(r.y)
            && y < doubled_edge(r.y, r.h)
    }

    fn naive_intersects(a: Rect, b: Rect) -> bool {
        let left = doubled(a.x).max(doubled(b.x)) + 1;
        let right = doubled_edge(a.x, a.w).min(doubled_edge(b.x, b.w));
        let top = doubled(a.y).max(doubled(b.y)) + 1;
        let bottom = doubled_edge(a.y, a.h).min(doubled_edge(b.y, b.h));
        let mut x = left;
        while x < right {
            let mut y = top;
            while y < bottom {
                if interior_point(x, y, a) && interior_point(x, y, b) {
                    return true;
                }
                y += 1;
            }
            x += 1;
        }
        false
    }

    fn naive_contains(outer: Rect, inner: Rect) -> bool {
        let mut x = doubled(inner.x);
        while x <= doubled_edge(inner.x, inner.w) {
            let mut y = doubled(inner.y);
            while y <= doubled_edge(inner.y, inner.h) {
                let inside = x >= doubled(outer.x)
                    && x <= doubled_edge(outer.x, outer.w)
                    && y >= doubled(outer.y)
                    && y <= doubled_edge(outer.y, outer.h);
                if !inside {
                    return false;
                }
                y += 1;
            }
            x += 1;
        }
        true
    }

    fn naive_union(a: Rect, b: Rect) -> Rect {
        let left = a.x.min(b.x);
        let top = a.y.min(b.y);
        let right = doubled_edge(a.x, a.w).max(doubled_edge(b.x, b.w)) / 2;
        let bottom = doubled_edge(a.y, a.h).max(doubled_edge(b.y, b.h)) / 2;
        Rect {
            x: left,
            y: top,
            w: i32::try_from(right - i64::from(left)).unwrap_or(0),
            h: i32::try_from(bottom - i64::from(top)).unwrap_or(0),
        }
    }

    fn axis_coord(axis: Axis, r: &Rect) -> i64 {
        match axis {
            Axis::X => i64::from(r.x),
            Axis::Y => i64::from(r.y),
        }
    }

    fn axis_extent(axis: Axis, r: &Rect) -> i64 {
        match axis {
            Axis::X => i64::from(r.w),
            Axis::Y => i64::from(r.h),
        }
    }

    fn naive_compact(axis: Axis, gap: i32, items: &[Rect]) -> Vec<Rect> {
        let mut out: Vec<Rect> = Vec::new();
        for item in items {
            let position = match out.last() {
                None => axis_coord(axis, item),
                Some(last) => {
                    let prior = axis_coord(axis, last) + axis_extent(axis, last) + i64::from(gap);
                    prior.max(axis_coord(axis, item))
                }
            };
            let mut placed = *item;
            match axis {
                Axis::X => placed.x = i32::try_from(position).unwrap_or(item.x),
                Axis::Y => placed.y = i32::try_from(position).unwrap_or(item.y),
            }
            out.push(placed);
        }
        out
    }

    fn random_rect(rng: &mut Xorshift32) -> Rect {
        rect(
            rng.i32_in(-40, 40),
            rng.i32_in(-40, 40),
            rng.i32_in(0, 12),
            rng.i32_in(0, 12),
        )
    }

    #[test]
    fn intersects_matches_interior_point_scan() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let a = random_rect(&mut rng);
            let b = random_rect(&mut rng);
            assert_eq!(intersects(a, b), Ok(naive_intersects(a, b)), "case {case}");
        }
    }

    #[test]
    fn intersects_hand_cases() {
        assert_eq!(intersects(rect(0, 0, 10, 10), rect(5, 5, 10, 10)), Ok(true));
        assert_eq!(
            intersects(rect(0, 0, 10, 10), rect(10, 0, 10, 10)),
            Ok(false)
        );
        assert_eq!(intersects(rect(0, 0, 10, 10), rect(0, 0, 0, 10)), Ok(false));
        assert_eq!(
            intersects(rect(0, 0, 10, 10), rect(-1, -1, 1, 1)),
            Ok(false)
        );
        assert_eq!(intersects(rect(0, 0, 10, 10), rect(-1, -1, 2, 2)), Ok(true));
    }

    #[test]
    fn contains_matches_point_scan() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let outer = random_rect(&mut rng);
            let inner = random_rect(&mut rng);
            assert_eq!(
                contains(outer, inner),
                Ok(naive_contains(outer, inner)),
                "case {case}"
            );
        }
    }

    #[test]
    fn contains_is_inclusive_on_edges() {
        let outer = rect(0, 0, 10, 10);
        assert_eq!(contains(outer, outer), Ok(true));
        assert_eq!(contains(outer, rect(10, 10, 0, 0)), Ok(true));
        assert_eq!(contains(outer, rect(1, 1, 20, 2)), Ok(false));
        assert_eq!(contains(rect(0, 0, 0, 0), rect(0, 0, 0, 0)), Ok(true));
    }

    #[test]
    fn union_matches_naive_bounds() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let a = random_rect(&mut rng);
            let b = random_rect(&mut rng);
            assert_eq!(union(a, b), Ok(naive_union(a, b)), "case {case}");
        }
    }

    #[test]
    fn translate_and_inflate_follow_formulas() {
        let a = rect(10, 20, 30, 40);
        assert_eq!(translate(a, 5, -7), Ok(rect(15, 13, 30, 40)));
        assert_eq!(inflate(a, 2), Ok(rect(8, 18, 34, 44)));
        assert_eq!(inflate(a, -1), Ok(rect(11, 21, 28, 38)));
        assert_eq!(inflate(rect(0, 0, 3, 3), -2), Err(GeomError::Domain));
        assert_eq!(translate(rect(0, 0, -1, 0), 0, 0), Err(GeomError::Domain));
    }

    #[test]
    fn transforms_match_independent_coordinate_formulas() {
        for case in 0..2000 {
            let mut rng = Xorshift32::new(case);
            let a = random_rect(&mut rng);
            let dx = rng.i32_in(-100, 100);
            let dy = rng.i32_in(-100, 100);
            assert_eq!(translate(a, dx, dy), Ok(rect(a.x + dx, a.y + dy, a.w, a.h)));
            let d = rng.i32_in(0, 20);
            assert_eq!(
                inflate(a, d),
                Ok(rect(a.x - d, a.y - d, a.w + 2 * d, a.h + 2 * d))
            );
            let size = Size { w: d, h: d + 1 };
            assert_eq!(
                place_after(Axis::X, a, d, size),
                Ok(rect(a.x + a.w + d, a.y, d, d + 1))
            );
            assert_eq!(
                place_after(Axis::Y, a, d, size),
                Ok(rect(a.x, a.y + a.h + d, d, d + 1))
            );
        }
    }

    #[test]
    fn translates_boundary_coordinates_without_wrapping() {
        for value in [i32::MIN, -1, 0, 1, i32::MAX] {
            let a = rect(value, value, 0, 0);
            assert_eq!(translate(a, 0, 0), Ok(a));
            let expected = value
                .checked_add(1)
                .map(|v| rect(v, value, 0, 0))
                .ok_or(GeomError::Overflow);
            assert_eq!(translate(a, 1, 0), expected);
        }
    }

    #[test]
    fn isqrt_matches_linear_search() {
        for case in 0..2000 {
            let mut rng = Xorshift32::new(case);
            let n = i64::from(rng.i32_in(0, 100000));
            let mut root = 0;
            while (root + 1) * (root + 1) <= n {
                root += 1;
            }
            assert_eq!(isqrt(n), Ok(root));
        }
    }

    #[test]
    fn place_after_follows_axis() {
        let a = rect(0, 0, 10, 20);
        let size = Size { w: 4, h: 6 };
        assert_eq!(place_after(Axis::X, a, 3, size), Ok(rect(13, 0, 4, 6)));
        assert_eq!(place_after(Axis::Y, a, 3, size), Ok(rect(0, 23, 4, 6)));
        assert_eq!(place_after(Axis::X, a, -1, size), Err(GeomError::Domain));
        assert_eq!(
            place_after(Axis::X, a, 0, Size { w: -1, h: 0 }),
            Err(GeomError::Domain)
        );
    }

    #[test]
    fn compact_matches_recurrence() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let gap = rng.i32_in(0, 6);
            let count = usize::try_from(rng.i32_in(0, 6)).unwrap_or(0);
            let mut items = Vec::new();
            for _ in 0..count {
                items.push(random_rect(&mut rng));
            }
            let axis = if rng.i32_in(0, 1) == 0 {
                Axis::X
            } else {
                Axis::Y
            };
            assert_eq!(
                compact(axis, gap, &items),
                Ok(naive_compact(axis, gap, &items)),
                "case {case}"
            );
        }
    }

    #[test]
    fn compact_hand_cases() {
        assert_eq!(compact(Axis::X, 2, &[]), Ok(Vec::new()));
        let items = [rect(10, 5, 4, 4), rect(0, 6, 4, 4), rect(12, 7, 4, 4)];
        assert_eq!(
            compact(Axis::X, 2, &items),
            Ok(vec![
                rect(10, 5, 4, 4),
                rect(16, 6, 4, 4),
                rect(22, 7, 4, 4)
            ])
        );
        assert_eq!(compact(Axis::X, -1, &items), Err(GeomError::Domain));
        assert_eq!(
            compact(Axis::Y, 1, &[rect(3, 0, 1, 2), rect(4, 0, 1, 3)]),
            Ok(vec![rect(3, 0, 1, 2), rect(4, 3, 1, 3)])
        );
    }

    #[test]
    fn isqrt_matches_definition() {
        assert_eq!(isqrt(-1), Err(GeomError::Domain));
        assert_eq!(isqrt(0), Ok(0));
        assert_eq!(isqrt(1), Ok(1));
        assert_eq!(isqrt(2), Ok(1));
        assert_eq!(isqrt(4), Ok(2));
        assert_eq!(isqrt(8), Ok(2));
        assert_eq!(isqrt(9), Ok(3));
        assert_eq!(isqrt(1 << 62), Ok(1 << 31));
        assert_eq!(isqrt(i64::MAX), Ok(3_037_000_499));
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let n = rng.i32_in(0, i32::MAX);
            let Ok(m) = isqrt(i64::from(n)) else {
                unreachable!("isqrt must accept nonnegative input: n={n}");
            };
            assert!(
                m * m <= i64::from(n),
                "integer root square must not exceed input: n={n}, root={m}"
            );
            assert!(
                (m + 1) * (m + 1) > i64::from(n),
                "next integer square must exceed input: n={n}, root={m}"
            );
        }
    }

    #[test]
    fn domain_precedes_overflow() {
        let invalid = rect(0, 0, -5, 0);
        assert_eq!(translate(invalid, 0, 0), Err(GeomError::Domain));
        assert_eq!(inflate(invalid, 0), Err(GeomError::Domain));
        assert_eq!(union(invalid, rect(0, 0, 1, 1)), Err(GeomError::Domain));
        assert_eq!(
            intersects(invalid, rect(0, 0, 1, 1)),
            Err(GeomError::Domain)
        );
        assert_eq!(contains(invalid, rect(0, 0, 1, 1)), Err(GeomError::Domain));
        assert_eq!(
            place_after(Axis::X, invalid, -1, Size { w: 1, h: 1 }),
            Err(GeomError::Domain)
        );
        assert_eq!(compact(Axis::X, -1, &[invalid]), Err(GeomError::Domain));
        assert_eq!(compact(Axis::X, 0, &[invalid]), Err(GeomError::Domain));
        assert_eq!(
            place_after(Axis::X, rect(0, 0, 1, 1), 0, Size { w: 0, h: -1 }),
            Err(GeomError::Domain)
        );
        assert_eq!(compact(Axis::Y, 0, &[invalid]), Err(GeomError::Domain));
        assert_eq!(union(rect(0, 0, 1, 1), invalid), Err(GeomError::Domain));
        assert_eq!(contains(rect(0, 0, 1, 1), invalid), Err(GeomError::Domain));
        assert_eq!(
            place_after(Axis::X, invalid, 0, Size { w: 0, h: 0 }),
            Err(GeomError::Domain)
        );
    }

    #[test]
    fn place_after_checks_far_edge_overflow_on_both_axes() {
        let size = Size { w: 1, h: 1 };
        let a = rect(i32::MAX, i32::MAX, 0, 0);
        assert_eq!(place_after(Axis::X, a, 0, size), Err(GeomError::Overflow));
        assert_eq!(place_after(Axis::Y, a, 0, size), Err(GeomError::Overflow));
    }

    #[test]
    fn overflow_reported_for_valid_inputs() {
        let big = rect(i32::MAX - 1, 0, 1, 1);
        assert_eq!(translate(big, 1, 0), Err(GeomError::Overflow));
        assert_eq!(
            inflate(rect(0, 0, i32::MAX, 1), 1),
            Err(GeomError::Overflow)
        );
        assert_eq!(
            union(rect(i32::MIN, 0, 0, 0), rect(0, 0, i32::MAX, 1)),
            Err(GeomError::Overflow)
        );
        assert_eq!(
            compact(Axis::X, i32::MAX, &[rect(0, 0, 10, 10), rect(0, 0, 1, 1)]),
            Err(GeomError::Overflow)
        );
        assert_eq!(
            compact(Axis::X, 0, &[rect(5, 0, 1, 1)]),
            Ok(vec![rect(5, 0, 1, 1)])
        );
    }
}
