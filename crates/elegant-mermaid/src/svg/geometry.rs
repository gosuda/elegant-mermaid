use super::{ConfigError, Point, Rect};
use crate::outlines::Command;
use crate::scene::{MarkerAxis, MarkerRefItem, PathCommand};
pub(super) fn number(v: i64) -> String {
    let h = (i128::from(v).abs() * 100 + 32) / 64;
    let mut s = (h / 100).to_string();
    if h % 100 != 0 {
        s.push_str(&format!(".{:02}", h % 100));
        s = s.trim_end_matches('0').into();
    }
    if v < 0 && h > 0 {
        s.insert(0, '-');
    }
    s
}
pub(super) fn glyph_path(commands: &[Command]) -> String {
    let n = |v: i32| number(v.into());
    commands
        .iter()
        .map(|c| match *c {
            Command::Move(x, y) => format!("M{} {}", n(x), n(y)),
            Command::Line(x, y) => format!("L{} {}", n(x), n(y)),
            Command::Quad(cx, cy, x, y) => format!("Q{} {} {} {}", n(cx), n(cy), n(x), n(y)),
            Command::Close => "Z".into(),
        })
        .collect::<Vec<_>>()
        .join(" ")
}
fn pair(p: Point) -> String {
    format!("{} {}", number(p.x.into()), number(p.y.into()))
}
pub(super) fn points(ps: &[Point]) -> String {
    ps.iter()
        .map(|p| format!("{},{}", number(p.x.into()), number(p.y.into())))
        .collect::<Vec<_>>()
        .join(" ")
}
pub(super) fn rect_attrs(r: Rect) -> String {
    format!(
        "x='{}' y='{}' width='{}' height='{}'",
        number(r.x.into()),
        number(r.y.into()),
        number(r.w.into()),
        number(r.h.into())
    )
}
fn direction(a: Point, b: Point) -> (i64, i64, i64) {
    let x = i64::from(b.x) - i64::from(a.x);
    let y = i64::from(b.y) - i64::from(a.y);
    (x.signum(), y.signum(), x.abs() + y.abs())
}
pub(super) fn rounded(ps: &[Point], limit: i32) -> String {
    let Some(first) = ps.first() else {
        return String::new();
    };
    let mut s = format!("M {}", pair(*first));
    for w in ps.windows(3) {
        s.push_str(&corner(w[0], w[1], w[2], limit));
    }
    if let Some(last) = ps.last().filter(|_| ps.len() > 1) {
        s.push_str(&format!(" L {}", pair(*last)));
    }
    s
}
fn corner(a: Point, p: Point, c: Point, limit: i32) -> String {
    let (ux, uy, l1) = direction(a, p);
    let (vx, vy, l2) = direction(p, c);
    let cross = ux * vy - uy * vx;
    let r = i64::from(limit).min(512).min(l1.min(l2) / 2);
    if cross == 0 || ux.abs() + uy.abs() != 1 || vx.abs() + vy.abs() != 1 || r <= 0 {
        return format!(" L {}", pair(p));
    }
    format!(
        " L {} {} A {} {} 0 0 {} {} {}",
        number(i64::from(p.x) - r * ux),
        number(i64::from(p.y) - r * uy),
        number(r),
        number(r),
        u8::from(cross > 0),
        number(i64::from(p.x) + r * vx),
        number(i64::from(p.y) + r * vy)
    )
}
pub(super) fn path(cs: &[PathCommand]) -> Result<String, ConfigError> {
    Ok(cs
        .iter()
        .map(command)
        .collect::<Result<Vec<_>, _>>()?
        .join(" "))
}
fn command(c: &PathCommand) -> Result<String, ConfigError> {
    Ok(match *c {
        PathCommand::Move(p) => format!("M {}", pair(p)),
        PathCommand::Line(p) => format!("L {}", pair(p)),
        PathCommand::Curve { c1, c2, to } => format!("C {} {} {}", pair(c1), pair(c2), pair(to)),
        PathCommand::Close => "Z".into(),
        PathCommand::Arc {
            centre,
            r,
            start,
            sweep,
        } => {
            let a = i32::try_from((i64::from(start) + i64::from(sweep)).rem_euclid(65536))
                .map_err(|_| ConfigError::Overflow)?;
            let x = i64::from(centre.x)
                + (2 * i64::from(r) * i64::from(crate::geom::cos_q15(a)) + 32768).div_euclid(65536);
            let y = i64::from(centre.y)
                + (2 * i64::from(r) * i64::from(crate::geom::sin_q15(a)) + 32768).div_euclid(65536);
            format!(
                "A {} {} 0 {} {} {} {}",
                number(r.into()),
                number(r.into()),
                u8::from(i64::from(sweep).abs() > 32768),
                u8::from(sweep > 0),
                number(x),
                number(y)
            )
        }
    })
}
pub(super) fn marker_point(
    p: (i32, i32),
    anchor: (i32, i32),
    m: &MarkerRefItem,
) -> Result<Point, ConfigError> {
    let x = i64::from(p.0) - i64::from(anchor.0);
    let y = i64::from(p.1) - i64::from(anchor.1);
    let (x, y) = match m.axis {
        MarkerAxis::PlusX => (x, y),
        MarkerAxis::MinusX => (-x, -y),
        MarkerAxis::PlusY => (-y, x),
        MarkerAxis::MinusY => (y, -x),
    };
    Ok(Point {
        x: i32::try_from(x + i64::from(m.at.x)).map_err(|_| ConfigError::Overflow)?,
        y: i32::try_from(y + i64::from(m.at.y)).map_err(|_| ConfigError::Overflow)?,
    })
}
