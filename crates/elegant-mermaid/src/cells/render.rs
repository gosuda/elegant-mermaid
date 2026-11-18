use super::{Canvas, Charset, ColorMode, Style, Token, braille, canvas::max_token};
use crate::{
    geom::{GeomError, Point, Rect},
    scene::*,
    theme::{self, Theme, ThemeError},
};

#[derive(Clone, Debug)]
pub struct Options {
    pub charset: Charset,
    pub color: ColorMode,
    pub theme: String,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            charset: Charset::Unicode,
            color: ColorMode::None,
            theme: String::new(),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RenderResult {
    pub text: String,
    pub refused_clusters: usize,
    pub route_conflicts: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("cells: expected {} profile, got {}", want.as_str(), got.as_str())]
pub struct ProfileError {
    pub want: Profile,
    pub got: Profile,
}
#[derive(Debug, thiserror::Error)]
pub enum RenderError {
    #[error(transparent)]
    Profile(#[from] ProfileError),
    #[error(transparent)]
    Geometry(#[from] GeomError),
    #[error(transparent)]
    Theme(#[from] ThemeError),
}
pub fn render(scene: &Scene, options: &Options) -> Result<RenderResult, RenderError> {
    match scene.profile() {
        Profile::Vector => super::raster::render_braille(scene, options),
        Profile::Cell => render_cells(scene, options),
    }
}
fn render_cells(scene: &Scene, options: &Options) -> Result<RenderResult, RenderError> {
    let theme = theme::resolve(&options.theme)?;
    let size = scene.canvas();
    let mut canvas = Canvas::new(size.w, size.h)?;
    let mut labels = Vec::new();
    for group in scene.items() {
        for item in &group.items {
            if let Item::Text(label) = item {
                labels.push(label);
            } else {
                canvas.draw(item, options.charset, &theme)?;
            }
        }
    }
    let refused_clusters = canvas.place_all(&labels, &theme)?;
    Ok(RenderResult {
        text: canvas.serialise(options.charset, options.color, |token| theme.colour(token)),
        refused_clusters,
        route_conflicts: route_conflicts(scene),
    })
}
fn line_style(shape: Shape, base: Style) -> Style {
    match (shape.line, shape.width) {
        (Line::Double, _) => Style::Double,
        (Line::Dashed | Line::Dotted, _) => Style::Dotted,
        (_, Width::Emphasis) => Style::Heavy,
        _ => base,
    }
}
pub(super) fn named_token(name: &str, series: u8) -> Token {
    if name == "series" {
        return Token::ALL[7 + usize::from(series % 12)];
    }
    Token::ALL
        .into_iter()
        .find(|token| token.id() == name)
        .unwrap_or(Token::Foreground)
}
fn paint(shape: Shape, theme: &Theme) -> (Token, u8) {
    let Some(row) = crate::r#gen::styles::STYLES
        .iter()
        .find(|row| row.name == shape.style.name())
    else {
        return (Token::Line, 1);
    };
    if row.cell == 2 {
        (named_token(row.fill, shape.series), row.cell)
    } else {
        (
            theme.stroke(named_token(row.stroke, shape.series)),
            row.cell,
        )
    }
}
fn checked_point(x: i64, y: i64) -> Result<Point, GeomError> {
    Ok(Point {
        x: i32::try_from(x).map_err(|_| GeomError::Overflow)?,
        y: i32::try_from(y).map_err(|_| GeomError::Overflow)?,
    })
}
fn symbol_glyph(charset: Charset, name: &str) -> u32 {
    super::join::symbol(charset, name).unwrap_or(0)
}
impl Canvas {
    fn ink_symbol(&mut self, at: Point, glyph: u32, ink: Token) {
        self.put(at.x, at.y, |cell| {
            cell.symbol = cell.symbol.max(glyph);
            cell.token = max_token(cell.token, Some(ink));
        });
    }
    fn marker(&mut self, marker: &MarkerRefItem, charset: Charset) {
        let Some(row) = crate::r#gen::markers::MARKERS
            .iter()
            .find(|row| row.name == marker.marker.as_str())
        else {
            return;
        };
        let axis = match marker.axis {
            MarkerAxis::PlusX => 0,
            MarkerAxis::MinusX => 1,
            MarkerAxis::PlusY => 2,
            MarkerAxis::MinusY => 3,
        };
        let glyphs = if charset == Charset::Ascii {
            row.ascii
        } else {
            row.cell
        };
        if let Some(glyph) = glyphs.get(axis) {
            self.ink_symbol(marker.at, *glyph, Token::Line);
        }
    }
    fn draw(&mut self, item: &Item, charset: Charset, theme: &Theme) -> Result<(), GeomError> {
        match item {
            Item::Rect(v) => self.rectangle(v.rect, v.shape, Style::Light, charset, theme),
            Item::RoundRect(v) => self.rectangle(v.rect, v.shape, Style::Rounded, charset, theme),
            Item::Polyline(v) => self.draw_polyline(v, theme),
            Item::Polygon(v) => self.polygon(v, charset, theme),
            Item::Ellipse(v) => self.draw_ellipse(v, charset, theme),
            Item::Path(v) => self.path(v, theme),
            Item::MarkerRef(v) => {
                self.marker(v, charset);
                Ok(())
            }
            Item::SymbolRef(v) => {
                self.ink_symbol(
                    v.at,
                    symbol_glyph(charset, v.symbol.as_str()),
                    paint(Shape::plain(v.style), theme).0,
                );
                Ok(())
            }
            Item::Text(_) => Ok(()),
        }
    }
    fn rectangle(
        &mut self,
        rect: Rect,
        shape: Shape,
        base: Style,
        charset: Charset,
        theme: &Theme,
    ) -> Result<(), GeomError> {
        checked_point(
            i64::from(rect.x) + i64::from(rect.w),
            i64::from(rect.y) + i64::from(rect.h),
        )?;
        let (ink, cell) = paint(shape, theme);
        if cell == 0 || rect.w <= 0 || rect.h <= 0 {
            return Ok(());
        }
        if rect.w.min(rect.h) == 1 {
            return self.thin_rect(rect, shape, charset, theme);
        }
        let right = rect.x + rect.w - 1;
        let bottom = rect.y + rect.h - 1;
        let points = [
            Point {
                x: rect.x,
                y: rect.y,
            },
            Point {
                x: right,
                y: rect.y,
            },
            Point {
                x: right,
                y: bottom,
            },
            Point {
                x: rect.x,
                y: bottom,
            },
            Point {
                x: rect.x,
                y: rect.y,
            },
        ];
        self.orthogonal(&points, line_style(shape, base), ink);
        Ok(())
    }
    fn thin_rect(
        &mut self,
        rect: Rect,
        shape: Shape,
        charset: Charset,
        theme: &Theme,
    ) -> Result<(), GeomError> {
        let (ink, cell) = paint(shape, theme);
        if cell == 2 {
            for y in rect.y.max(0)..(rect.y + rect.h).min(self.height()) {
                for x in rect.x.max(0)..(rect.x + rect.w).min(self.width()) {
                    self.put(x, y, |v| {
                        v.dots = 255;
                        v.token = max_token(v.token, Some(ink));
                    });
                }
            }
        } else if rect.w == 1 && rect.h == 1 {
            self.ink_symbol(
                Point {
                    x: rect.x,
                    y: rect.y,
                },
                symbol_glyph(charset, "box-hollow"),
                ink,
            );
        } else {
            self.put_segment(
                Point {
                    x: rect.x,
                    y: rect.y,
                },
                Point {
                    x: rect.x + rect.w - 1,
                    y: rect.y + rect.h - 1,
                },
                line_style(shape, Style::Light),
                ink,
            );
        }
        Ok(())
    }
    fn orthogonal(&mut self, points: &[Point], style: Style, ink: Token) {
        for pair in points.windows(2) {
            self.put_segment(pair[0], pair[1], style, ink);
        }
    }
    fn dot_lines(&mut self, points: &[Point], ink: Token) -> Result<(), GeomError> {
        for pair in points.windows(2) {
            self.stroke_dots(pair[0], pair[1], ink)?;
        }
        Ok(())
    }
    fn draw_polyline(&mut self, line: &PolylineItem, theme: &Theme) -> Result<(), GeomError> {
        let (ink, cell) = paint(line.shape, theme);
        if cell == 0 {
            return Ok(());
        }
        if line
            .points
            .windows(2)
            .all(|p| p[0].x == p[1].x || p[0].y == p[1].y)
        {
            self.orthogonal(&line.points, line_style(line.shape, Style::Light), ink);
            return Ok(());
        }
        let dots = line
            .points
            .iter()
            .copied()
            .map(braille::cell_dot)
            .collect::<Result<Vec<_>, _>>()?;
        self.dot_lines(&dots, ink)
    }
    fn polygon(
        &mut self,
        polygon: &PolygonItem,
        charset: Charset,
        theme: &Theme,
    ) -> Result<(), GeomError> {
        let (ink, cell) = paint(polygon.shape, theme);
        let Some(first) = polygon.points.first().copied() else {
            return Ok(());
        };
        if cell == 0 {
            return Ok(());
        }
        let (mut lo, mut hi) = (first, first);
        for p in &polygon.points {
            lo.x = lo.x.min(p.x);
            lo.y = lo.y.min(p.y);
            hi.x = hi.x.max(p.x);
            hi.y = hi.y.max(p.y);
        }
        if i64::from(hi.x) - i64::from(lo.x) <= 1 && i64::from(hi.y) - i64::from(lo.y) <= 1 {
            self.ink_symbol(
                lo,
                symbol_glyph(
                    charset,
                    if cell == 2 {
                        "diamond"
                    } else {
                        "diamond-hollow"
                    },
                ),
                ink,
            );
            return Ok(());
        }
        let mut points = polygon
            .points
            .iter()
            .copied()
            .map(braille::cell_dot)
            .collect::<Result<Vec<_>, _>>()?;
        points.push(braille::cell_dot(first)?);
        self.dot_lines(&points, ink)
    }
    fn draw_ellipse(
        &mut self,
        ellipse: &EllipseItem,
        charset: Charset,
        theme: &Theme,
    ) -> Result<(), GeomError> {
        let (ink, cell) = paint(ellipse.shape, theme);
        if cell == 0 {
            return Ok(());
        }
        let center = Point {
            x: ellipse.cx,
            y: ellipse.cy,
        };
        if ellipse.rx <= 1 && ellipse.ry <= 1 {
            self.ink_symbol(
                center,
                symbol_glyph(charset, if cell == 2 { "disc" } else { "ring" }),
                ink,
            );
            return Ok(());
        }
        let radii = checked_point(2 * i64::from(ellipse.rx), 4 * i64::from(ellipse.ry))?;
        let mut points = braille::ellipse(braille::cell_dot(center)?, radii.x, radii.y)?;
        if let Some(first) = points.first().copied() {
            points.push(first);
        }
        self.dot_lines(&points, ink)
    }
    fn path(&mut self, path: &PathItem, theme: &Theme) -> Result<(), GeomError> {
        let (ink, cell) = paint(path.shape, theme);
        if cell == 0 {
            return Ok(());
        }
        let mut current = Point { x: 0, y: 0 };
        let mut start = current;
        for command in &path.commands {
            let points = path_points(*command, current, start)?;
            if let Some(next) = points.last() {
                current = *next;
            }
            if matches!(command, PathCommand::Move(_)) {
                start = current;
            }
            self.dot_lines(&points, ink)?;
        }
        Ok(())
    }
}
fn path_points(
    command: PathCommand,
    current: Point,
    start: Point,
) -> Result<Vec<Point>, GeomError> {
    match command {
        PathCommand::Move(p) => Ok(vec![braille::cell_dot(p)?]),
        PathCommand::Line(p) => Ok(vec![current, braille::cell_dot(p)?]),
        PathCommand::Close => Ok(vec![current, start]),
        PathCommand::Curve { c1, c2, to } => braille::cubic([
            current,
            braille::cell_dot(c1)?,
            braille::cell_dot(c2)?,
            braille::cell_dot(to)?,
        ]),
        PathCommand::Arc {
            centre,
            r,
            start,
            sweep,
        } => braille::arc(
            braille::cell_dot(centre)?,
            r.checked_mul(2).ok_or(GeomError::Overflow)?,
            start,
            sweep,
        ),
    }
}
#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests;

fn route_conflicts(scene: &Scene) -> usize {
    let routes = &scene.dump_part().routes;
    let occupied: Vec<_> = routes.iter().map(route_cells).collect();
    let mut conflicts = std::collections::BTreeSet::new();
    for (index, route) in routes.iter().enumerate() {
        for (other, cells) in routes[..index].iter().zip(&occupied[..index]) {
            if shared_endpoint(route, other) {
                continue;
            }
            collect_conflicts(&occupied[index], cells, &mut conflicts);
        }
    }
    let size = scene.canvas();
    conflicts.retain(|(x, y)| *x >= 0 && *y >= 0 && *x < size.w && *y < size.h);
    conflicts.len()
}

fn shared_endpoint(a: &SceneRoute, b: &SceneRoute) -> bool {
    a.from == b.from || a.from == b.to || a.to == b.from || a.to == b.to
}

fn collect_conflicts(
    a: &std::collections::BTreeMap<(i32, i32), u8>,
    b: &std::collections::BTreeMap<(i32, i32), u8>,
    conflicts: &mut std::collections::BTreeSet<(i32, i32)>,
) {
    for (cell, axes) in a {
        if b.get(cell).is_some_and(|other| axes & other != 0) {
            conflicts.insert(*cell);
        }
    }
}

fn route_cells(route: &SceneRoute) -> std::collections::BTreeMap<(i32, i32), u8> {
    let mut cells = std::collections::BTreeMap::new();
    for pair in route.points.windows(2) {
        occupy_segment(pair[0], pair[1], &mut cells);
    }
    cells
}

fn occupy_segment(a: Point, b: Point, cells: &mut std::collections::BTreeMap<(i32, i32), u8>) {
    if a == b {
        return;
    }
    if a.y == b.y {
        for x in a.x.min(b.x)..=a.x.max(b.x) {
            *cells.entry((x, a.y)).or_default() |= 1;
        }
    } else if a.x == b.x {
        for y in a.y.min(b.y)..=a.y.max(b.y) {
            *cells.entry((a.x, y)).or_default() |= 2;
        }
    }
}

#[cfg(test)]
mod metric_tests {
    use super::*;

    #[test]
    fn route_conflicts_respect_axes_and_junctions() {
        let route = |from: &str, to: &str, points| SceneRoute {
            id: String::new(),
            from: from.into(),
            to: to.into(),
            points,
            orthogonal: true,
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        };
        let a = route("A", "B", vec![Point { x: 0, y: 2 }, Point { x: 4, y: 2 }]);
        let b = route("C", "D", vec![Point { x: 2, y: 2 }, Point { x: 6, y: 2 }]);
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        dump.routes = vec![a, b];
        let size = crate::geom::Size { w: 7, h: 5 };
        assert_eq!(
            route_conflicts(&Scene::new(size, dump.clone(), Vec::new())),
            3
        );
        dump.routes[1].points = vec![Point { x: 2, y: 0 }, Point { x: 2, y: 4 }];
        assert_eq!(
            route_conflicts(&Scene::new(size, dump.clone(), Vec::new())),
            0
        );
        dump.routes[1].points = dump.routes[0].points.clone();
        dump.routes[1].from = "A".into();
        assert_eq!(route_conflicts(&Scene::new(size, dump, Vec::new())), 0);
    }
}
