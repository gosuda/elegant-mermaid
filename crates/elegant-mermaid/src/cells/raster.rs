use super::{
    Canvas, Token, braille, colour,
    place::line_start,
    render::{Options, ProfileError, RenderError, RenderResult, named_token},
    serialise::printable,
};
use crate::{
    geom::{GeomError, Point, Rect, floor_div},
    measure,
    scene::{
        EllipseItem, Item, MarkerAxis, MarkerRefItem, PathCommand, PathItem, Profile, Scene, Shape,
        ShapeStyle, TextItem, TextRole,
    },
    theme::{self, Theme},
};

const COLUMN_UNITS: i64 = 512;
const ROW_UNITS: i64 = 1024;
const TITLE_LINE_UNITS: i64 = 1536;
const BODY_LINE_UNITS: i64 = 1280;

#[derive(Clone, Copy)]
struct Ink {
    fill: Token,
    stroke: Token,
    filled: bool,
    stroked: bool,
}

pub fn render_braille(scene: &Scene, options: &Options) -> Result<RenderResult, RenderError> {
    if scene.profile() != Profile::Vector {
        return Err(ProfileError {
            want: Profile::Vector,
            got: scene.profile(),
        }
        .into());
    }
    let theme = theme::resolve(&options.theme)?;
    let size = scene.canvas();
    let mut canvas = Canvas::new_braille(size.w, size.h)?;
    let mut labels = Vec::new();
    for item in scene.items().iter().flat_map(|group| group.items.iter()) {
        match item {
            Item::Text(label) => labels.push(label),
            other => canvas.rasterise(other, &theme)?,
        }
    }
    let refused_clusters = canvas.place_braille(&labels, &theme)?;
    Ok(RenderResult {
        text: canvas.serialise(options.charset, options.color, |token| theme.colour(token)),
        refused_clusters,
        route_conflicts: 0,
    })
}

fn ink_of(shape: Shape, theme: &Theme) -> Ink {
    let Some(row) = crate::r#gen::styles::STYLES
        .iter()
        .find(|row| row.name == shape.style.name())
    else {
        return Ink {
            fill: Token::Line,
            stroke: Token::Line,
            filled: false,
            stroked: true,
        };
    };
    Ink {
        fill: named_token(row.fill, shape.series),
        stroke: theme.stroke(named_token(row.stroke, shape.series)),
        filled: row.cell == 2 && row.fill != "none",
        stroked: row.cell != 0 && row.stroke != "none",
    }
}

fn closed_ring(points: &[Point]) -> Vec<Point> {
    points
        .iter()
        .chain(points.first())
        .copied()
        .collect::<Vec<_>>()
}

fn point(x: i64, y: i64) -> Result<Point, GeomError> {
    Ok(Point {
        x: i32::try_from(x).map_err(|_| GeomError::Overflow)?,
        y: i32::try_from(y).map_err(|_| GeomError::Overflow)?,
    })
}

const ORIGIN: Point = Point { x: 0, y: 0 };

struct Subpath {
    points: Vec<Point>,
    closed: bool,
}

struct PathWalk {
    subpaths: Vec<Subpath>,
    current: Point,
    start: Point,
    open: bool,
}

impl PathWalk {
    fn new() -> Self {
        Self {
            subpaths: Vec::new(),
            current: ORIGIN,
            start: ORIGIN,
            open: false,
        }
    }
    fn begin(&mut self, at: Point) {
        self.subpaths.push(Subpath {
            points: vec![at],
            closed: false,
        });
        self.open = true;
    }
    fn extend(&mut self, points: &[Point]) {
        if !self.open {
            self.begin(self.current);
        }
        if let Some(last) = self.subpaths.last_mut() {
            last.points.extend_from_slice(points);
        }
        if let Some(end) = points.last() {
            self.current = *end;
        }
    }
    fn close(&mut self) {
        if let Some(last) = self.subpaths.last_mut().filter(|_| self.open) {
            last.closed = true;
        }
        self.open = false;
        self.current = self.start;
    }
    fn step(&mut self, command: &PathCommand) -> Result<(), GeomError> {
        match *command {
            PathCommand::Move(p) => {
                self.begin(p);
                self.current = p;
                self.start = p;
            }
            PathCommand::Line(p) => self.extend(&[p]),
            PathCommand::Curve { c1, c2, to } => {
                let points = braille::cubic([self.current, c1, c2, to])?;
                self.extend(points.get(1..).unwrap_or_default());
            }
            PathCommand::Arc {
                centre,
                r,
                start,
                sweep,
            } => self.extend(&braille::arc(centre, r, start, sweep)?),
            PathCommand::Close => self.close(),
        }
        Ok(())
    }
}

fn marker_vertex(
    p: (i32, i32),
    anchor: (i32, i32),
    marker: &MarkerRefItem,
) -> Result<Point, GeomError> {
    let x = i64::from(p.0) - i64::from(anchor.0);
    let y = i64::from(p.1) - i64::from(anchor.1);
    let (x, y) = match marker.axis {
        MarkerAxis::PlusX => (x, y),
        MarkerAxis::MinusX => (-x, -y),
        MarkerAxis::PlusY => (-y, x),
        MarkerAxis::MinusY => (y, -x),
    };
    point(x + i64::from(marker.at.x), y + i64::from(marker.at.y))
}

fn marker_parts<'a>(points: &'a [Point], breaks: &[u32]) -> Result<Vec<&'a [Point]>, GeomError> {
    let mut parts = Vec::new();
    let mut start = 0usize;
    for end in breaks
        .iter()
        .map(|&b| usize::try_from(b))
        .chain(std::iter::once(Ok(points.len())))
    {
        let end = end.map_err(|_| GeomError::Overflow)?;
        parts.push(points.get(start..end).ok_or(GeomError::Domain)?);
        start = end;
    }
    Ok(parts)
}

fn line_units(role: TextRole) -> i64 {
    match role {
        TextRole::Title => TITLE_LINE_UNITS,
        TextRole::Label | TextRole::Body => BODY_LINE_UNITS,
    }
}

fn to_i32(v: i64) -> Result<i32, GeomError> {
    i32::try_from(v).map_err(|_| GeomError::Overflow)
}

impl Canvas {
    fn rasterise(&mut self, item: &Item, theme: &Theme) -> Result<(), GeomError> {
        match item {
            Item::Rect(v) => self.raster_rect(v.rect, v.shape, theme),
            Item::RoundRect(v) => self.raster_rect(v.rect, v.shape, theme),
            Item::Ellipse(v) => self.raster_ellipse(v, theme),
            Item::Polygon(v) => {
                self.raster_polygons(&[v.points.as_slice()], ink_of(v.shape, theme))
            }
            Item::Polyline(v) => self.raster_open(&v.points, ink_of(v.shape, theme)),
            Item::Path(v) => self.raster_path(v, theme),
            Item::MarkerRef(v) => self.raster_marker(v, theme),
            Item::SymbolRef(_) => Err(GeomError::Domain),
            Item::Text(_) => Ok(()),
        }
    }
    fn raster_polygons(&mut self, rings: &[&[Point]], ink: Ink) -> Result<(), GeomError> {
        if ink.filled {
            self.fill_rings(rings, ink.fill)?;
        }
        rings
            .iter()
            .try_for_each(|ring| self.raster_open(&closed_ring(ring), ink))
    }
    fn raster_open(&mut self, points: &[Point], ink: Ink) -> Result<(), GeomError> {
        if ink.stroked {
            self.stroke(points, ink.stroke)?;
        }
        Ok(())
    }
    fn raster_rect(&mut self, rect: Rect, shape: Shape, theme: &Theme) -> Result<(), GeomError> {
        let far = point(
            i64::from(rect.x) + i64::from(rect.w),
            i64::from(rect.y) + i64::from(rect.h),
        )?;
        if rect.w < 0 || rect.h < 0 {
            return Ok(());
        }
        let ring = [
            Point {
                x: rect.x,
                y: rect.y,
            },
            Point {
                x: far.x,
                y: rect.y,
            },
            far,
            Point {
                x: rect.x,
                y: far.y,
            },
        ];
        self.raster_polygons(&[ring.as_slice()], ink_of(shape, theme))
    }
    fn raster_ellipse(&mut self, ellipse: &EllipseItem, theme: &Theme) -> Result<(), GeomError> {
        if ellipse.rx < 0 || ellipse.ry < 0 {
            return Ok(());
        }
        let ring = braille::ellipse(
            Point {
                x: ellipse.cx,
                y: ellipse.cy,
            },
            ellipse.rx,
            ellipse.ry,
        )?;
        self.raster_polygons(&[ring.as_slice()], ink_of(ellipse.shape, theme))
    }
    fn raster_path(&mut self, path: &PathItem, theme: &Theme) -> Result<(), GeomError> {
        let mut walk = PathWalk::new();
        path.commands
            .iter()
            .try_for_each(|command| walk.step(command))?;
        let ink = ink_of(path.shape, theme);
        if ink.filled {
            let rings: Vec<&[Point]> = walk
                .subpaths
                .iter()
                .map(|sp| sp.points.as_slice())
                .collect();
            self.fill_rings(&rings, ink.fill)?;
        }
        for sp in &walk.subpaths {
            let points = if sp.closed {
                closed_ring(&sp.points)
            } else {
                sp.points.clone()
            };
            self.raster_open(&points, ink)?;
        }
        Ok(())
    }
    fn raster_marker(&mut self, marker: &MarkerRefItem, theme: &Theme) -> Result<(), GeomError> {
        let row = crate::r#gen::markers::MARKERS
            .iter()
            .find(|row| row.name == marker.marker.as_str())
            .filter(|row| row.points.len() >= 2)
            .ok_or(GeomError::Domain)?;
        let points = row
            .points
            .iter()
            .map(|&p| marker_vertex(p, row.anchor, marker))
            .collect::<Result<Vec<_>, _>>()?;
        let style = match row.paint {
            "hollow" => ShapeStyle::MarkHollow,
            "open" => ShapeStyle::Edge,
            _ => ShapeStyle::Mark,
        };
        let ink = ink_of(Shape::plain(style), theme);
        let parts = marker_parts(&points, row.breaks)?;
        if row.paint == "open" {
            parts
                .iter()
                .try_for_each(|part| self.raster_open(part, ink))
        } else {
            self.raster_polygons(&parts, ink)
        }
    }
    fn place_braille(&mut self, labels: &[&TextItem], theme: &Theme) -> Result<usize, GeomError> {
        let mut refused = 0usize;
        for label in labels {
            let ink = colour::text_token(theme.name(), label.style.name(), label.series);
            refused = refused
                .checked_add(self.place_braille_text(label, ink)?)
                .ok_or(GeomError::Overflow)?;
        }
        Ok(refused)
    }
    fn place_braille_text(&mut self, label: &TextItem, ink: Token) -> Result<usize, GeomError> {
        let first = floor_div(i64::from(label.rect.x), COLUMN_UNITS);
        let span = measure::ceil_div(
            i64::from(label.rect.x) + i64::from(label.rect.w),
            COLUMN_UNITS,
        ) - first;
        let height = line_units(label.role);
        let mut refused = 0usize;
        for (k, runs) in label.lines.iter().enumerate() {
            let text: String = runs
                .iter()
                .flat_map(|run| run.text.chars())
                .map(printable)
                .collect();
            let width = measure::cell_width(&text)?;
            let line = i64::try_from(k).map_err(|_| GeomError::Overflow)?;
            let row = floor_div(i64::from(label.rect.y) + line * height, ROW_UNITS);
            let col = line_start(label.align, to_i32(first)?, to_i32(span)?, width)?;
            refused += self.place_clusters(&text, col, to_i32(row)?, ink)?;
        }
        Ok(refused)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests;
