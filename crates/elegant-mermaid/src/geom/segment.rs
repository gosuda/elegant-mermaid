use super::{COORD_LIMIT, GeomError, Point, Rect, Segment};

pub fn segments_cross(s: Segment, t: Segment) -> Result<bool, GeomError> {
    if !axis_aligned(&s) || !axis_aligned(&t) {
        return Err(GeomError::Domain);
    }
    if s.a == s.b || t.a == t.b {
        return Ok(false);
    }
    let s_vertical = s.a.x == s.b.x;
    let t_vertical = t.a.x == t.b.x;
    match (s_vertical, t_vertical) {
        (true, true) => Ok(s.a.x == t.a.x && overlap(s.a.y, s.b.y, t.a.y, t.b.y)),
        (false, false) => Ok(s.a.y == t.a.y && overlap(s.a.x, s.b.x, t.a.x, t.b.x)),
        (true, false) => Ok(between(s.a.y, s.b.y, t.a.y) && between(t.a.x, t.b.x, s.a.x)),
        (false, true) => Ok(between(t.a.y, t.b.y, s.a.y) && between(s.a.x, s.b.x, t.a.x)),
    }
}

fn axis_aligned(s: &Segment) -> bool {
    s.a.x == s.b.x || s.a.y == s.b.y
}

fn overlap(lo1: i32, hi1: i32, lo2: i32, hi2: i32) -> bool {
    let low = i64::from(lo1).min(i64::from(hi1));
    let high = i64::from(lo1).max(i64::from(hi1));
    let other_low = i64::from(lo2).min(i64::from(hi2));
    let other_high = i64::from(lo2).max(i64::from(hi2));
    low.max(other_low) < high.min(other_high)
}

fn between(lo: i32, hi: i32, value: i32) -> bool {
    let low = lo.min(hi);
    let high = lo.max(hi);
    low < value && value < high
}

pub fn is_orthogonal(p: &[Point]) -> bool {
    p.windows(2)
        .all(|pair| pair[0].x == pair[1].x || pair[0].y == pair[1].y)
}

pub fn polyline_hits_rect(p: &[Point], r: Rect) -> Result<bool, GeomError> {
    if !super::rect_is_valid(&r) || !within_limit(r) || !p.iter().all(within_limit_point) {
        return Err(GeomError::Domain);
    }
    if r.w == 0 || r.h == 0 {
        return Ok(false);
    }
    match p.len() {
        0 => Ok(false),
        1 => Ok(!misses_axes(p[0], p[0], &r)),
        _ => Ok(p.windows(2).any(|pair| hits(pair[0], pair[1], &r))),
    }
}

fn within_limit(r: Rect) -> bool {
    let x = i64::from(r.x);
    let y = i64::from(r.y);
    let right = x + i64::from(r.w);
    let bottom = y + i64::from(r.h);
    [x, y, right, bottom]
        .iter()
        .all(|value| value.abs() <= COORD_LIMIT)
}

fn within_limit_point(p: &Point) -> bool {
    i64::from(p.x).abs() <= COORD_LIMIT && i64::from(p.y).abs() <= COORD_LIMIT
}

fn hits(p: Point, q: Point, r: &Rect) -> bool {
    if misses_axes(p, q, r) {
        return false;
    }
    if p == q {
        return true;
    }
    !separated_by_normal(p, q, r)
}

fn misses_axes(p: Point, q: Point, r: &Rect) -> bool {
    let x0 = i64::from(r.x);
    let x1 = x0 + i64::from(r.w);
    let y0 = i64::from(r.y);
    let y1 = y0 + i64::from(r.h);
    let px = i64::from(p.x);
    let py = i64::from(p.y);
    let qx = i64::from(q.x);
    let qy = i64::from(q.y);
    px.max(qx) <= x0 || px.min(qx) >= x1 || py.max(qy) <= y0 || py.min(qy) >= y1
}

fn separated_by_normal(p: Point, q: Point, r: &Rect) -> bool {
    let nx = i64::from(p.y) - i64::from(q.y);
    let ny = i64::from(q.x) - i64::from(p.x);
    let c = nx * i64::from(p.x) + ny * i64::from(p.y);
    let x0 = i64::from(r.x);
    let y0 = i64::from(r.y);
    let x1 = x0 + i64::from(r.w);
    let y1 = y0 + i64::from(r.h);
    let corners = [
        nx * x0 + ny * y0,
        nx * x1 + ny * y0,
        nx * x0 + ny * y1,
        nx * x1 + ny * y1,
    ];
    let least = corners[0].min(corners[1]).min(corners[2]).min(corners[3]);
    let greatest = corners[0].max(corners[1]).max(corners[2]).max(corners[3]);
    c <= least || c >= greatest
}

pub fn count_inversions(xs: &[i32]) -> Result<i32, GeomError> {
    let n = xs.len();
    if n < 2 {
        return Ok(0);
    }
    let mut buffer = xs.to_vec();
    let mut scratch = xs.to_vec();
    let mut total: i64 = 0;
    let mut run = 1;
    while run < n {
        let mut start = 0;
        while start < n {
            let mid = (start + run).min(n);
            let end = (start + 2 * run).min(n);
            total += merge_run(
                &buffer[start..mid],
                &buffer[mid..end],
                &mut scratch[start..end],
            );
            start += 2 * run;
        }
        std::mem::swap(&mut buffer, &mut scratch);
        run *= 2;
    }
    i32::try_from(total).map_err(|_| GeomError::Overflow)
}

fn merge_run(left: &[i32], right: &[i32], out: &mut [i32]) -> i64 {
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;
    let mut inversions: i64 = 0;
    while i < left.len() && j < right.len() {
        if right[j] < left[i] {
            out[k] = right[j];
            inversions += i64::try_from(left.len() - i).unwrap_or(0);
            j += 1;
        } else {
            out[k] = left[i];
            i += 1;
        }
        k += 1;
    }
    while i < left.len() {
        out[k] = left[i];
        i += 1;
        k += 1;
    }
    while j < right.len() {
        out[k] = right[j];
        j += 1;
        k += 1;
    }
    inversions
}

#[cfg(test)]
mod tests {
    use super::super::testing::Xorshift32;
    use super::{count_inversions, is_orthogonal, polyline_hits_rect, segments_cross};
    use crate::geom::{COORD_LIMIT, GeomError, Point, Rect, Segment};

    fn point(x: i32, y: i32) -> Point {
        Point { x, y }
    }

    fn segment(x1: i32, y1: i32, x2: i32, y2: i32) -> Segment {
        Segment {
            a: point(x1, y1),
            b: point(x2, y2),
        }
    }

    fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
        Rect { x, y, w, h }
    }

    fn doubled(value: i32) -> i64 {
        i64::from(value) * 2
    }

    fn interior_of_segment(s: Segment, x2: i64, y2: i64) -> bool {
        if s.a == s.b {
            return false;
        }
        if s.a.x == s.b.x {
            x2 == doubled(s.a.x)
                && y2 > doubled(s.a.y).min(doubled(s.b.y))
                && y2 < doubled(s.a.y).max(doubled(s.b.y))
        } else {
            y2 == doubled(s.a.y)
                && x2 > doubled(s.a.x).min(doubled(s.b.x))
                && x2 < doubled(s.a.x).max(doubled(s.b.x))
        }
    }

    fn brute_cross(s: Segment, t: Segment) -> bool {
        let span = doubled(8);
        let mut x2 = -span;
        while x2 <= span {
            let mut y2 = -span;
            while y2 <= span {
                if interior_of_segment(s, x2, y2) && interior_of_segment(t, x2, y2) {
                    return true;
                }
                y2 += 1;
            }
            x2 += 1;
        }
        false
    }

    fn random_segment(rng: &mut Xorshift32) -> Segment {
        let x1 = rng.i32_in(-3, 3);
        let y1 = rng.i32_in(-3, 3);
        if rng.i32_in(0, 1) == 0 {
            segment(x1, y1, rng.i32_in(-3, 3), y1)
        } else {
            segment(x1, y1, x1, rng.i32_in(-3, 3))
        }
    }

    #[test]
    fn segments_cross_matches_half_integer_scan() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let s = random_segment(&mut rng);
            let t = random_segment(&mut rng);
            assert_eq!(
                segments_cross(s, t),
                Ok(brute_cross(s, t)),
                "case {case} s={s:?} t={t:?}"
            );
        }
    }

    fn sampled_segment_hits(a: Point, b: Point, r: Rect) -> bool {
        (0..=720).any(|t| {
            let x = i64::from(a.x) * (720 - t) + i64::from(b.x) * t;
            let y = i64::from(a.y) * (720 - t) + i64::from(b.y) * t;
            x > i64::from(r.x) * 720
                && x < (i64::from(r.x) + i64::from(r.w)) * 720
                && y > i64::from(r.y) * 720
                && y < (i64::from(r.y) + i64::from(r.h)) * 720
        })
    }

    #[test]
    fn polyline_hits_rect_matches_rational_parameter_scan() {
        for case in 0..2000 {
            let mut rng = Xorshift32::new(case);
            let a = point(rng.i32_in(-3, 3), rng.i32_in(-3, 3));
            let b = point(rng.i32_in(-3, 3), rng.i32_in(-3, 3));
            let r = rect(
                rng.i32_in(-3, 3),
                rng.i32_in(-3, 3),
                rng.i32_in(0, 3),
                rng.i32_in(0, 3),
            );
            assert_eq!(
                polyline_hits_rect(&[a, b], r),
                Ok(sampled_segment_hits(a, b, r))
            );
            assert_eq!(is_orthogonal(&[a, b]), a.x == b.x || a.y == b.y);
        }
    }

    #[test]
    fn segments_cross_hand_cases() {
        let vertical = segment(0, 0, 0, 10);
        let horizontal = segment(-5, 5, 5, 5);
        assert_eq!(segments_cross(vertical, horizontal), Ok(true));
        assert_eq!(segments_cross(horizontal, vertical), Ok(true));
        assert_eq!(
            segments_cross(segment(0, 0, 0, 10), segment(0, 10, 5, 10)),
            Ok(false)
        );
        assert_eq!(
            segments_cross(segment(0, 0, 0, 10), segment(5, 5, 5, 15)),
            Ok(false)
        );
        assert_eq!(
            segments_cross(segment(0, 0, 0, 10), segment(0, 3, 0, 20)),
            Ok(true)
        );
        assert_eq!(
            segments_cross(segment(0, 0, 0, 10), segment(0, 10, 0, 20)),
            Ok(false)
        );
        assert_eq!(segments_cross(segment(0, 0, 0, 0), horizontal), Ok(false));
        assert_eq!(
            segments_cross(segment(0, 0, 3, 4), horizontal),
            Err(GeomError::Domain)
        );
    }

    #[test]
    fn is_orthogonal_hand_cases() {
        assert!(
            is_orthogonal(&[]),
            "empty polyline must be orthogonal: points=[]"
        );
        assert!(
            is_orthogonal(&[point(1, 2)]),
            "single-point polyline must be orthogonal: points=[(1,2)]"
        );
        assert!(
            is_orthogonal(&[point(0, 0), point(0, 0)]),
            "zero-length segment must be orthogonal: points=[(0,0),(0,0)]"
        );
        assert!(
            is_orthogonal(&[point(0, 0), point(4, 0), point(4, 9)]),
            "axis-aligned elbow must be orthogonal: points=[(0,0),(4,0),(4,9)]"
        );
        assert!(
            !is_orthogonal(&[point(0, 0), point(4, 3)]),
            "diagonal segment must not be orthogonal: points=[(0,0),(4,3)]"
        );
        assert!(
            !is_orthogonal(&[point(0, 0), point(1, 0), point(2, 1)]),
            "polyline containing diagonal must not be orthogonal: points=[(0,0),(1,0),(2,1)]"
        );
    }

    #[test]
    fn polyline_hits_rect_hand_cases() {
        let r = rect(0, 0, 10, 10);
        assert_eq!(polyline_hits_rect(&[point(5, 5)], r), Ok(true));
        assert_eq!(polyline_hits_rect(&[point(0, 5)], r), Ok(false));
        assert_eq!(polyline_hits_rect(&[point(10, 10)], r), Ok(false));
        assert_eq!(
            polyline_hits_rect(&[point(0, 0), point(10, 0)], r),
            Ok(false)
        );
        assert_eq!(
            polyline_hits_rect(&[point(-5, 5), point(15, 5)], r),
            Ok(true)
        );
        assert_eq!(
            polyline_hits_rect(&[point(0, 0), point(10, 10)], r),
            Ok(true)
        );
        assert_eq!(
            polyline_hits_rect(&[point(10, 0), point(0, 10)], r),
            Ok(true)
        );
    }

    #[test]
    fn polyline_hits_rect_boundary_cases() {
        let r = rect(0, 0, 10, 10);
        assert_eq!(
            polyline_hits_rect(&[point(-1, 0), point(11, 0)], r),
            Ok(false)
        );
        assert_eq!(
            polyline_hits_rect(&[point(-4, 6), point(6, -4)], r),
            Ok(true)
        );
        assert_eq!(
            polyline_hits_rect(&[point(-4, 6), point(-4, 20)], r),
            Ok(false)
        );
        assert_eq!(polyline_hits_rect(&[], r), Ok(false));
        assert_eq!(
            polyline_hits_rect(&[point(5, 5)], rect(0, 0, 0, 10)),
            Ok(false)
        );
        assert_eq!(
            polyline_hits_rect(&[point(5, 5)], rect(0, 0, 10, 0)),
            Ok(false)
        );
        assert_eq!(
            polyline_hits_rect(&[point(1, 1), point(9, 1)], rect(0, 0, 1, 1)),
            Ok(false)
        );
        assert_eq!(
            polyline_hits_rect(&[point(0, 0), point(3, 1)], rect(0, 0, 10, 10)),
            Ok(true)
        );
        assert_eq!(
            polyline_hits_rect(&[point(0, 0), point(10, 10)], rect(2, 2, 2, 2)),
            Ok(true)
        );
        assert_eq!(
            polyline_hits_rect(&[point(5, 5)], rect(0, 0, -1, 10)),
            Err(GeomError::Domain)
        );
    }

    #[test]
    fn polyline_hits_rect_rejects_coordinates_beyond_limit() {
        let far = i32::try_from(COORD_LIMIT + 1).unwrap_or(i32::MAX);
        assert_eq!(
            polyline_hits_rect(&[point(far, 0)], rect(0, 0, 1, 1)),
            Err(GeomError::Domain)
        );
        let edge = i32::try_from(COORD_LIMIT + 1).unwrap_or(i32::MAX);
        assert_eq!(
            polyline_hits_rect(&[point(0, 0)], rect(edge, 0, 1, 1)),
            Err(GeomError::Domain)
        );
    }

    #[test]
    fn segment_operations_report_domain_not_overflow() {
        let far = i32::try_from(COORD_LIMIT + 1).unwrap_or(i32::MAX);
        assert_eq!(
            polyline_hits_rect(&[point(far, far)], rect(0, 0, -1, 1)),
            Err(GeomError::Domain)
        );
        assert_eq!(
            segments_cross(segment(far, 0, far, 4), segment(far - 1, 2, far + 1, 2)),
            Ok(true)
        );
        assert_eq!(
            segments_cross(segment(0, 0, 1, 1), segment(-1, 0, 1, 0)),
            Err(GeomError::Domain)
        );
        assert_eq!(
            polyline_hits_rect(&[point(0, 0), point(far, 0)], rect(0, 0, 4, 4)),
            Err(GeomError::Domain)
        );
    }

    #[test]
    fn count_inversions_matches_quadratic_count() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let count = usize::try_from(rng.i32_in(0, 8)).unwrap_or(0);
            let mut xs = Vec::new();
            for _ in 0..count {
                xs.push(rng.i32_in(-3, 3));
            }
            let mut expected: i64 = 0;
            for i in 0..xs.len() {
                for j in i + 1..xs.len() {
                    if xs[i] > xs[j] {
                        expected += 1;
                    }
                }
            }
            assert_eq!(
                count_inversions(&xs),
                Ok(i32::try_from(expected).unwrap_or(0)),
                "case {case}"
            );
        }
    }

    #[test]
    fn count_inversions_hand_cases() {
        assert_eq!(count_inversions(&[]), Ok(0));
        assert_eq!(count_inversions(&[5]), Ok(0));
        assert_eq!(count_inversions(&[1, 2, 3]), Ok(0));
        assert_eq!(count_inversions(&[3, 2, 1]), Ok(3));
        assert_eq!(count_inversions(&[2, 2, 2]), Ok(0));
        assert_eq!(count_inversions(&[2, 1, 2, 1]), Ok(3));
    }

    #[test]
    fn count_inversions_overflow() {
        let count = 70_000usize;
        let mut xs = Vec::with_capacity(count);
        for i in 0..count {
            xs.push(i32::try_from(count - i).unwrap_or(0));
        }
        assert_eq!(count_inversions(&xs), Err(GeomError::Overflow));
    }
}
