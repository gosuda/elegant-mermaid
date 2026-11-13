use super::{BoxRole, Direction, Dump, Scene};
use crate::geom::{GeomError, Point, Rect, isqrt};

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Metrics {
    pub hard_ok: bool,
    pub nodes: i64,
    pub mean_node_extent: i64,
    pub crossings: i64,
    pub bends: i64,
    pub against_flow_edges: i64,
    pub total_route_length: i64,
    pub canvas_area: i64,
    pub soft_cost: i64,
}

impl Metrics {
    pub fn json(&self) -> String {
        format!(
            "{{\"schema\":1,\"hard_ok\":{},\"nodes\":{},\"mean_node_extent\":{},\"crossings\":{},\"bends\":{},\"against_flow_edges\":{},\"total_route_length\":{},\"canvas_area\":{},\"soft_cost\":{}}}\n",
            self.hard_ok,
            self.nodes,
            self.mean_node_extent,
            self.crossings,
            self.bends,
            self.against_flow_edges,
            self.total_route_length,
            self.canvas_area,
            self.soft_cost
        )
    }
}

pub(crate) fn soft_cost(terms: &Metrics) -> Result<i64, GeomError> {
    let Metrics {
        crossings: c,
        bends: b,
        against_flow_edges: a,
        total_route_length: t,
        canvas_area: k,
        mean_node_extent: m,
        nodes: n,
        ..
    } = *terms;
    let denominator = m
        .checked_mul(m)
        .and_then(|v| v.checked_mul(n.max(1)))
        .ok_or(GeomError::Overflow)?;
    c.checked_mul(10)
        .and_then(|v| b.checked_mul(2).and_then(|b| v.checked_add(b)))
        .and_then(|v| a.checked_mul(5).and_then(|a| v.checked_add(a)))
        .and_then(|v| v.checked_add(t / m))
        .and_then(|v| v.checked_add(k / denominator))
        .ok_or(GeomError::Overflow)
}

pub fn measure(scene: &Scene, unwritten_clusters: usize) -> Result<Metrics, GeomError> {
    let dump = scene.dump_part();
    let mut result = Metrics::default();
    let mut extent = 0i64;
    for b in dump.boxes.iter().filter(|b| b.role == BoxRole::Node) {
        result.nodes = add(result.nodes, 1)?;
        extent = add(extent, (i64::from(b.rect.w) + i64::from(b.rect.h)) / 2)?;
    }
    result.mean_node_extent = (extent / result.nodes.max(1)).max(1);
    let routes: Vec<_> = dump.routes.iter().map(|r| clean(&r.points)).collect();
    for (index, points) in routes.iter().enumerate() {
        let (bends, length) = route_stats(points)?;
        result.bends = add(result.bends, bends)?;
        result.total_route_length = add(result.total_route_length, length)?;
        result.against_flow_edges = add(result.against_flow_edges, against(dump, index)?)?;
        for other in &routes[..index] {
            result.crossings = add(result.crossings, crossings(points, other)?)?;
        }
    }
    result.canvas_area = area(dump)?;
    result.soft_cost = soft_cost(&result)?;
    result.hard_ok = scene.check()? && unwritten_clusters == 0;
    Ok(result)
}

fn add(a: i64, b: i64) -> Result<i64, GeomError> {
    a.checked_add(b).ok_or(GeomError::Overflow)
}

fn clean(points: &[Point]) -> std::borrow::Cow<'_, [Point]> {
    if points.windows(2).all(|pair| pair[0] != pair[1]) {
        return std::borrow::Cow::Borrowed(points);
    }
    let mut out = Vec::with_capacity(points.len());
    for p in points {
        if out.last() != Some(p) {
            out.push(*p);
        }
    }
    std::borrow::Cow::Owned(out)
}

fn vector(a: Point, b: Point) -> (i64, i64) {
    (
        i64::from(b.x) - i64::from(a.x),
        i64::from(b.y) - i64::from(a.y),
    )
}

fn cross(a: (i64, i64), b: (i64, i64)) -> Result<i64, GeomError> {
    a.0.checked_mul(b.1)
        .and_then(|p| a.1.checked_mul(b.0).and_then(|q| p.checked_sub(q)))
        .ok_or(GeomError::Overflow)
}

fn dot(a: (i64, i64), b: (i64, i64)) -> Result<i64, GeomError> {
    a.0.checked_mul(b.0)
        .and_then(|p| a.1.checked_mul(b.1).and_then(|q| p.checked_add(q)))
        .ok_or(GeomError::Overflow)
}

fn route_stats(points: &[Point]) -> Result<(i64, i64), GeomError> {
    let mut length = 0;
    let mut bends = 0;
    for pair in points.windows(2) {
        let d = vector(pair[0], pair[1]);
        length = add(length, isqrt(dot(d, d)?)?)?;
    }
    for triple in points.windows(3) {
        let a = vector(triple[0], triple[1]);
        let b = vector(triple[1], triple[2]);
        if cross(a, b)? != 0 || dot(a, b)? < 0 {
            bends = add(bends, 1)?;
        }
    }
    Ok((bends, length))
}

fn orientation(a: Point, b: Point, p: Point) -> Result<i64, GeomError> {
    Ok(cross(vector(a, b), vector(a, p))?.signum())
}

fn proper(a: &[Point], b: &[Point]) -> Result<bool, GeomError> {
    Ok(
        orientation(a[0], a[1], b[0])? * orientation(a[0], a[1], b[1])? == -1
            && orientation(b[0], b[1], a[0])? * orientation(b[0], b[1], a[1])? == -1,
    )
}

fn crossings(a: &[Point], b: &[Point]) -> Result<i64, GeomError> {
    let mut count = 0;
    for x in a.windows(2) {
        for y in b.windows(2) {
            count = add(count, i64::from(proper(x, y)?))?;
        }
    }
    Ok(count)
}

fn centre(rect: Rect, direction: Direction) -> i64 {
    match direction {
        Direction::Lr | Direction::Rl => 2 * i64::from(rect.x) + i64::from(rect.w),
        Direction::Tb | Direction::Bt => 2 * i64::from(rect.y) + i64::from(rect.h),
    }
}

fn against(dump: &Dump, index: usize) -> Result<i64, GeomError> {
    let route = &dump.routes[index];
    let from = dump
        .boxes
        .iter()
        .find(|b| b.id == route.from)
        .ok_or(GeomError::Domain)?;
    let to = dump
        .boxes
        .iter()
        .find(|b| b.id == route.to)
        .ok_or(GeomError::Domain)?;
    let direction = dump.options.direction;
    let delta = centre(to.rect, direction) - centre(from.rect, direction);
    let sign = if matches!(direction, Direction::Bt | Direction::Rl) {
        -1
    } else {
        1
    };
    Ok(i64::from(sign * delta < 0))
}

fn area(dump: &Dump) -> Result<i64, GeomError> {
    let mut bounds: Option<(i64, i64, i64, i64)> = None;
    for rect in dump
        .boxes
        .iter()
        .map(|b| b.rect)
        .chain(dump.labels.iter().map(|l| l.rect))
    {
        include(&mut bounds, i64::from(rect.x), i64::from(rect.y));
        include(
            &mut bounds,
            i64::from(rect.x) + i64::from(rect.w),
            i64::from(rect.y) + i64::from(rect.h),
        );
    }
    for p in dump.routes.iter().flat_map(|r| &r.points) {
        include(&mut bounds, i64::from(p.x), i64::from(p.y));
    }
    let Some((x, y, right, bottom)) = bounds else {
        return Ok(0);
    };
    (right - x)
        .checked_mul(bottom - y)
        .ok_or(GeomError::Overflow)
}

fn include(bounds: &mut Option<(i64, i64, i64, i64)>, x: i64, y: i64) {
    *bounds = Some(match *bounds {
        Some((l, t, r, b)) => (l.min(x), t.min(y), r.max(x), b.max(y)),
        None => (x, y, x, y),
    });
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use crate::{
        geom::Size,
        scene::{DumpOptions, SceneBox, SceneRoute},
    };

    #[test]
    fn metrics() {
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        for (id, x) in [("A", 0), ("B", 20)] {
            dump.boxes.push(SceneBox {
                id: id.into(),
                role: BoxRole::Node,
                rect: Rect {
                    x,
                    y: 0,
                    w: 10,
                    h: 10,
                },
                parent: String::new(),
                exclusive: true,
            });
        }
        dump.options.direction = Direction::Lr;
        dump.routes.push(SceneRoute {
            id: "e0".into(),
            from: "A".into(),
            to: "B".into(),
            orthogonal: true,
            points: vec![
                Point { x: 10, y: 5 },
                Point { x: 10, y: 5 },
                Point { x: 20, y: 5 },
            ],
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        });
        let scene = Scene::new(Size { w: 30, h: 10 }, dump, Vec::new());
        assert_eq!(
            measure(&scene, 0).unwrap(),
            Metrics {
                hard_ok: true,
                nodes: 2,
                mean_node_extent: 10,
                crossings: 0,
                bends: 0,
                against_flow_edges: 0,
                total_route_length: 10,
                canvas_area: 300,
                soft_cost: 2
            }
        );
        assert_eq!(
            route_stats(&[
                Point { x: 0, y: 0 },
                Point { x: 3, y: 4 },
                Point { x: 0, y: 0 }
            ])
            .unwrap(),
            (1, 10)
        );
        assert_eq!(
            crossings(
                &[Point { x: 0, y: 0 }, Point { x: 10, y: 10 }],
                &[Point { x: 0, y: 10 }, Point { x: 10, y: 0 }]
            )
            .unwrap(),
            1
        );
        let mut crossing_dump = scene.dump_part().clone();
        crossing_dump.routes.push(SceneRoute {
            id: "e1".into(),
            from: "B".into(),
            to: "A".into(),
            orthogonal: true,
            points: vec![Point { x: 15, y: 0 }, Point { x: 15, y: 10 }],
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        });
        let crossing_scene = Scene::new(Size { w: 30, h: 10 }, crossing_dump, Vec::new());
        assert_eq!(
            measure(&crossing_scene, 0).unwrap(),
            Metrics {
                hard_ok: false,
                nodes: 2,
                mean_node_extent: 10,
                crossings: 1,
                bends: 0,
                against_flow_edges: 1,
                total_route_length: 20,
                canvas_area: 300,
                soft_cost: 18
            }
        );
        let decoded = read_dump(&scene.dump()).unwrap();
        assert_eq!(measure(&decoded, 0).unwrap(), measure(&scene, 0).unwrap());
        let truncated = measure(&scene, 1).unwrap();
        assert!(
            !truncated.hard_ok,
            "one unwritten cluster must fail hard constraints; metrics: {truncated:?}, scene: {scene:?}"
        );
        assert_eq!(
            soft_cost(&Metrics {
                mean_node_extent: i64::MAX,
                ..Default::default()
            }),
            Err(GeomError::Overflow)
        );
        assert_eq!(
            soft_cost(&Metrics {
                crossings: 2,
                bends: 3,
                against_flow_edges: 4,
                total_route_length: 51,
                canvas_area: 900,
                mean_node_extent: 10,
                nodes: 3,
                ..Default::default()
            })
            .unwrap(),
            54
        );
    }
}

#[derive(Debug, thiserror::Error)]
#[error("malformed layout dump: {0}")]
pub struct DumpError(String);

impl From<&str> for DumpError {
    fn from(message: &str) -> Self {
        Self(message.into())
    }
}

pub fn read_dump(source: &str) -> Result<Scene, DumpError> {
    let escaped = source.replace('\'', "\\u0027");
    let (root, diagnostics) =
        crate::syntax::config_value::parse_config_json(&escaped, 0, escaped.len());
    if !diagnostics.is_empty() {
        return Err("malformed layout dump".into());
    }
    decode_dump(&root)
}

type Value = crate::syntax::config_value::ConfigValue;

fn member<'a>(value: &'a Value, key: &str) -> Result<&'a Value, DumpError> {
    let Value::Mapping(entries) = value else {
        return Err("expected object".into());
    };
    entries
        .iter()
        .find(|e| e.key == key)
        .map(|e| &e.value)
        .ok_or_else(|| DumpError(format!("missing {key}")))
}

fn text(value: &Value) -> Result<&str, DumpError> {
    match value {
        Value::String(s) => Ok(s),
        _ => Err("expected string".into()),
    }
}

fn integer(value: &Value) -> Result<i32, DumpError> {
    match value {
        Value::Integer(s) => s.parse().map_err(|_| "invalid integer".into()),
        _ => Err("expected integer".into()),
    }
}

fn boolean(value: &Value) -> Result<bool, DumpError> {
    match value {
        Value::Bool(b) => Ok(*b),
        _ => Err("expected boolean".into()),
    }
}

fn array(value: &Value) -> Result<&[Value], DumpError> {
    match value {
        Value::Sequence(items) => Ok(items),
        _ => Err("expected array".into()),
    }
}

fn rect(value: &Value) -> Result<Rect, DumpError> {
    Ok(Rect {
        x: integer(member(value, "x")?)?,
        y: integer(member(value, "y")?)?,
        w: integer(member(value, "w")?)?,
        h: integer(member(value, "h")?)?,
    })
}

fn decode_dump(root: &Value) -> Result<Scene, DumpError> {
    if integer(member(root, "version")?)? != 1 || text(member(root, "stage")?)? != "layout" {
        return Err("expected version 1 layout dump".into());
    }
    if text(member(root, "profile")?)? != "vector" {
        return Err("--metrics needs --profile vector".into());
    }
    let options = member(root, "options")?;
    let direction = match text(member(options, "direction")?)? {
        "TB" => Direction::Tb,
        "BT" => Direction::Bt,
        "LR" => Direction::Lr,
        "RL" => Direction::Rl,
        _ => return Err("invalid direction".into()),
    };
    let mut dump = Dump::new(
        "flowchart",
        super::DumpOptions {
            direction,
            ..Default::default()
        },
    );
    dump.boxes = array(member(root, "boxes")?)?
        .iter()
        .map(decode_box)
        .collect::<Result<_, _>>()?;
    dump.routes = array(member(root, "routes")?)?
        .iter()
        .map(decode_route)
        .collect::<Result<_, _>>()?;
    dump.labels = array(member(root, "labels")?)?
        .iter()
        .map(decode_label)
        .collect::<Result<_, _>>()?;
    let canvas = member(root, "canvas")?;
    let canvas = crate::geom::Size {
        w: integer(member(canvas, "w")?)?,
        h: integer(member(canvas, "h")?)?,
    };
    super::well_formed(canvas, &dump).map_err(|e| DumpError(e.to_string()))?;
    Ok(Scene::new(canvas, dump, Vec::new()))
}

fn decode_box(value: &Value) -> Result<super::SceneBox, DumpError> {
    Ok(super::SceneBox {
        id: text(member(value, "id")?)?.into(),
        role: BoxRole::from_name(text(member(value, "role")?)?).ok_or("invalid box role")?,
        rect: rect(value)?,
        parent: text(member(value, "parent")?)?.into(),
        exclusive: boolean(member(value, "exclusive")?)?,
    })
}

fn decode_route(value: &Value) -> Result<super::SceneRoute, DumpError> {
    Ok(super::SceneRoute {
        id: text(member(value, "id")?)?.into(),
        from: text(member(value, "from")?)?.into(),
        to: text(member(value, "to")?)?.into(),
        orthogonal: boolean(member(value, "orthogonal")?)?,
        points: array(member(value, "points")?)?
            .iter()
            .map(decode_point)
            .collect::<Result<_, _>>()?,
        marker_start: String::new(),
        marker_end: String::new(),
        stroke: String::new(),
    })
}

fn decode_point(value: &Value) -> Result<Point, DumpError> {
    let items = array(value)?;
    let [x, y] = items else {
        return Err("expected point".into());
    };
    Ok(Point {
        x: integer(x)?,
        y: integer(y)?,
    })
}

fn decode_label(value: &Value) -> Result<super::SceneLabel, DumpError> {
    Ok(super::SceneLabel {
        id: text(member(value, "id")?)?.into(),
        owner: text(member(value, "owner")?)?.into(),
        text: text(member(value, "text")?)?.into(),
        rect: rect(value)?,
        lines: array(member(value, "lines")?)?
            .iter()
            .map(|v| text(v).map(str::to_owned))
            .collect::<Result<_, _>>()?,
    })
}
