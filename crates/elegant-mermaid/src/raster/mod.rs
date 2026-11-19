#[cfg(test)]
mod tests;
mod text;
pub use crate::error::RasterError;
pub use crate::outlines::GlyphOutlines;
use crate::{
    Scene,
    geom::Point,
    scene::*,
    theme::{self, Colour, Theme, Token},
};
pub use text::inter_outlines;
use tiny_skia::{
    FillRule, LineCap, LineJoin, Paint, Path, PathBuilder, Pixmap, Stroke, StrokeDash, Transform,
};

#[derive(Debug, Clone)]
pub struct PngOptions {
    pub scale: u32,
    pub background: String,
}
impl Default for PngOptions {
    fn default() -> Self {
        Self {
            scale: 2,
            background: String::new(),
        }
    }
}
fn invalid() -> RasterError {
    RasterError::InvalidConfig { errors: 1 }
}
fn encode(message: impl ToString) -> RasterError {
    RasterError::Encode {
        message: message.to_string(),
    }
}
pub fn png(scene: &Scene, options: &PngOptions) -> Result<Vec<u8>, RasterError> {
    render(scene, options)?.encode_png().map_err(encode)
}
/// An owned, tightly packed, straight-alpha RGBA8 raster.
pub struct RgbaImage {
    pub width: u32,
    pub height: u32,
    pub pixels: Vec<u8>,
}

/// Rasterise without encoding or copying the pixel allocation.
pub fn rgba(
    scene: &Scene,
    options: &PngOptions,
    theme_name: &str,
) -> Result<RgbaImage, RasterError> {
    let pixmap = render_themed(scene, options, theme_name)?;
    let width = pixmap.width();
    let height = pixmap.height();
    Ok(RgbaImage {
        width,
        height,
        pixels: pixmap.take_demultiplied(),
    })
}

/// Encode tightly packed straight-alpha RGBA8 pixels as PNG.
pub fn encode_rgba(width: u32, height: u32, mut pixels: Vec<u8>) -> Result<Vec<u8>, RasterError> {
    let size = tiny_skia::IntSize::from_wh(width, height).ok_or_else(invalid)?;
    let expected = u64::from(width) * u64::from(height) * 4;
    if u64::try_from(pixels.len()).map_err(|_| invalid())? != expected {
        return Err(invalid());
    }
    for pixel in pixels.as_chunks_mut::<4>().0 {
        let alpha = u16::from(pixel[3]);
        for channel in &mut pixel[..3] {
            *channel =
                u8::try_from((u16::from(*channel) * alpha + 127) / 255).map_err(|_| invalid())?;
        }
    }
    Pixmap::from_vec(pixels, size)
        .ok_or_else(invalid)?
        .encode_png()
        .map_err(encode)
}
fn render(scene: &Scene, options: &PngOptions) -> Result<Pixmap, RasterError> {
    render_themed(scene, options, "")
}

fn render_themed(
    scene: &Scene,
    options: &PngOptions,
    theme_name: &str,
) -> Result<Pixmap, RasterError> {
    if !(1..=8).contains(&options.scale) || scene.profile() != Profile::Vector {
        return Err(invalid());
    }
    let size = scene.canvas();
    let side = |n: i32| {
        u32::try_from((i64::from(n) * i64::from(options.scale) + 63) / 64).map_err(|_| invalid())
    };
    let (width, height) = (side(size.w)?, side(size.h)?);
    if width > 16384 || height > 16384 || u64::from(width) * u64::from(height) > 67108864 {
        return Err(RasterError::PixelsTooLarge { width, height });
    }
    let theme = theme::resolve(theme_name).map_err(|_| invalid())?;
    let bg = if options.background.is_empty() {
        theme.colour(Token::Background)
    } else {
        Colour::parse_hex(&options.background).map_err(|_| invalid())?
    };
    let mut pixmap = Pixmap::new(width, height).ok_or_else(|| encode("empty canvas"))?;
    pixmap.fill(tiny_skia::Color::from_rgba8(bg.r, bg.g, bg.b, 255));
    let outlines = inter_outlines();
    let transform = Transform::from_scale(options.scale as f32 / 64.0, options.scale as f32 / 64.0);
    for group in scene.items() {
        for item in &group.items {
            draw(&mut pixmap, item, &theme, &outlines, transform)?;
        }
    }
    Ok(pixmap)
}
fn colour(theme: &Theme, name: &str, series: u8, stroke: bool) -> Result<Colour, RasterError> {
    let id = if name == "series" {
        format!("series{}", series % 12)
    } else {
        name.to_owned()
    };
    let token = Token::ALL
        .into_iter()
        .find(|t| t.id() == id)
        .ok_or_else(invalid)?;
    Ok(theme.colour(if stroke { theme.stroke(token) } else { token }))
}
fn paint(c: Colour, alpha: u8) -> Paint<'static> {
    let mut p = Paint::default();
    p.set_color_rgba8(c.r, c.g, c.b, alpha);
    p
}
fn constant(name: &str) -> i32 {
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|r| r.name.strip_prefix("vector.") == Some(name))
        .map_or(0, |r| r.value)
}
fn draw_path(
    pix: &mut Pixmap,
    path: &Path,
    shape: Shape,
    theme: &Theme,
    tr: Transform,
) -> Result<(), RasterError> {
    let row = crate::r#gen::styles::STYLES
        .iter()
        .find(|r| r.name == shape.style.name())
        .ok_or_else(invalid)?;
    if row.fill != "none" {
        pix.fill_path(
            path,
            &paint(
                colour(theme, row.fill, shape.series, false)?,
                if row.tint == 1 {
                    constant("paint.tint_alpha") as u8
                } else {
                    255
                },
            ),
            FillRule::Winding,
            tr,
            None,
        );
    }
    if row.stroke == "none" {
        return Ok(());
    }
    let width = match shape.width {
        Width::Normal => 64,
        Width::Emphasis => 128,
        Width::Units(v) => v,
    };
    if width <= 0 {
        return Ok(());
    }
    let pattern = match shape.line {
        Line::Dotted => Some(("paint.dash_dotted_on", "paint.dash_dotted_off")),
        Line::Dashed => Some(("paint.dash_dashed_on", "paint.dash_dashed_off")),
        _ => None,
    };
    let dash = pattern
        .and_then(|(a, b)| StrokeDash::new(vec![constant(a) as f32, constant(b) as f32], 0.0));
    let stroke = Stroke {
        width: width as f32,
        line_cap: LineCap::Round,
        line_join: LineJoin::Round,
        dash,
        ..Stroke::default()
    };
    pix.stroke_path(
        path,
        &paint(
            colour(theme, row.stroke, shape.series, true)?,
            if row.tint == 2 {
                constant("paint.tint_alpha") as u8
            } else {
                255
            },
        ),
        &stroke,
        tr,
        None,
    );
    Ok(())
}
fn points(pb: &mut PathBuilder, ps: &[Point], close: bool) {
    if let Some(p) = ps.first() {
        pb.move_to(p.x as f32, p.y as f32);
        for p in &ps[1..] {
            pb.line_to(p.x as f32, p.y as f32);
        }
        if close {
            pb.close();
        }
    }
}
fn rectangle(pb: &mut PathBuilder, r: crate::geom::Rect) {
    pb.move_to(r.x as f32, r.y as f32);
    pb.line_to((i64::from(r.x) + i64::from(r.w)) as f32, r.y as f32);
    pb.line_to(
        (i64::from(r.x) + i64::from(r.w)) as f32,
        (i64::from(r.y) + i64::from(r.h)) as f32,
    );
    pb.line_to(r.x as f32, (i64::from(r.y) + i64::from(r.h)) as f32);
    pb.close();
}
fn rounded(pb: &mut PathBuilder, v: &RoundRectItem) -> Result<(), RasterError> {
    let r = v.r.max(0).min(v.rect.w / 2).min(v.rect.h / 2);
    if r == 0 {
        rectangle(pb, v.rect);
        return Ok(());
    }
    let x = v.rect.x;
    let y = v.rect.y;
    let right = x.checked_add(v.rect.w).ok_or_else(invalid)?;
    let bottom = y.checked_add(v.rect.h).ok_or_else(invalid)?;
    for (i, (cx, cy, start)) in [
        (right - r, y + r, -16384),
        (right - r, bottom - r, 0),
        (x + r, bottom - r, 16384),
        (x + r, y + r, 32768),
    ]
    .into_iter()
    .enumerate()
    {
        let ps =
            crate::cells::braille::arc(Point { x: cx, y: cy }, r, start, 16384).map_err(encode)?;
        for (j, p) in ps.iter().enumerate() {
            if i == 0 && j == 0 {
                pb.move_to(p.x as f32, p.y as f32);
            } else {
                pb.line_to(p.x as f32, p.y as f32);
            }
        }
    }
    pb.close();
    Ok(())
}
fn commands(pb: &mut PathBuilder, cs: &[PathCommand]) -> Result<(), RasterError> {
    let mut at = Point { x: 0, y: 0 };
    for c in cs {
        match *c {
            PathCommand::Move(p) => {
                pb.move_to(p.x as f32, p.y as f32);
                at = p;
            }
            PathCommand::Line(p) => {
                pb.line_to(p.x as f32, p.y as f32);
                at = p;
            }
            PathCommand::Curve { c1, c2, to } => {
                for p in crate::cells::braille::cubic([at, c1, c2, to])
                    .map_err(encode)?
                    .iter()
                    .skip(1)
                {
                    pb.line_to(p.x as f32, p.y as f32);
                }
                at = to;
            }
            PathCommand::Arc {
                centre,
                r,
                start,
                sweep,
            } => {
                for p in crate::cells::braille::arc(centre, r, start, sweep).map_err(encode)? {
                    pb.line_to(p.x as f32, p.y as f32);
                    at = p;
                }
            }
            PathCommand::Close => pb.close(),
        }
    }
    Ok(())
}
fn marker(pb: &mut PathBuilder, m: &MarkerRefItem) -> Result<Shape, RasterError> {
    let (ax, ay) = m.marker.anchor().ok_or_else(invalid)?;
    let mut ps = Vec::new();
    for &(x, y) in m.marker.points() {
        let (x, y) = (i64::from(x) - i64::from(ax), i64::from(y) - i64::from(ay));
        let (x, y) = match m.axis {
            MarkerAxis::PlusX => (x, y),
            MarkerAxis::MinusX => (-x, -y),
            MarkerAxis::PlusY => (-y, x),
            MarkerAxis::MinusY => (y, -x),
        };
        ps.push(Point {
            x: i32::try_from(x + i64::from(m.at.x)).map_err(encode)?,
            y: i32::try_from(y + i64::from(m.at.y)).map_err(encode)?,
        });
    }
    let row = crate::r#gen::markers::MARKERS
        .iter()
        .find(|r| r.name == m.marker.as_str())
        .ok_or_else(invalid)?;
    let mut start = 0;
    for end in row
        .breaks
        .iter()
        .copied()
        .map(usize::try_from)
        .chain(std::iter::once(Ok(ps.len())))
    {
        let end = end.map_err(encode)?;
        points(
            pb,
            ps.get(start..end).ok_or_else(invalid)?,
            m.marker.paint() != Some("open"),
        );
        start = end;
    }
    Ok(Shape::plain(match m.marker.paint() {
        Some("open") => ShapeStyle::Edge,
        Some("hollow") => ShapeStyle::MarkHollow,
        _ => ShapeStyle::Mark,
    }))
}
fn draw(
    pix: &mut Pixmap,
    item: &Item,
    theme: &Theme,
    outlines: &GlyphOutlines,
    tr: Transform,
) -> Result<(), RasterError> {
    let mut pb = PathBuilder::new();
    let shape = match item {
        Item::Rect(v) => {
            rectangle(&mut pb, v.rect);
            v.shape
        }
        Item::RoundRect(v) => {
            rounded(&mut pb, v)?;
            v.shape
        }
        Item::Ellipse(v) => {
            points(
                &mut pb,
                &crate::cells::braille::ellipse(Point { x: v.cx, y: v.cy }, v.rx, v.ry)
                    .map_err(encode)?,
                true,
            );
            v.shape
        }
        Item::Polygon(v) => {
            points(&mut pb, &v.points, true);
            v.shape
        }
        Item::Polyline(v) => {
            polyline(&mut pb, v)?;
            v.shape
        }
        Item::Path(v) => {
            commands(&mut pb, &v.commands)?;
            v.shape
        }
        Item::MarkerRef(v) => marker(&mut pb, v)?,
        Item::Text(v) => return text::draw(pix, v, theme, outlines, tr),
        Item::SymbolRef(_) => return Err(invalid()),
    };
    if let Some(path) = pb.finish() {
        draw_path(pix, &path, shape, theme, tr)?;
    }
    Ok(())
}
fn polyline(pb: &mut PathBuilder, line: &PolylineItem) -> Result<(), RasterError> {
    let Some(first) = line.points.first() else {
        return Ok(());
    };
    pb.move_to(first.x as f32, first.y as f32);
    for triple in line.points.windows(3) {
        rounded_corner(pb, triple, line.corner)?;
    }
    if let Some(last) = line.points.last() {
        pb.line_to(last.x as f32, last.y as f32);
    }
    Ok(())
}
fn rounded_corner(pb: &mut PathBuilder, ps: &[Point], limit: i32) -> Result<(), RasterError> {
    let (a, p, b) = (ps[0], ps[1], ps[2]);
    let (dx, dy) = (
        i64::from(p.x) - i64::from(a.x),
        i64::from(p.y) - i64::from(a.y),
    );
    let (ex, ey) = (
        i64::from(b.x) - i64::from(p.x),
        i64::from(b.y) - i64::from(p.y),
    );
    let (ux, uy, vx, vy) = (dx.signum(), dy.signum(), ex.signum(), ey.signum());
    let cross = ux * vy - uy * vx;
    let r = i64::from(limit).min((dx.abs() + dy.abs()).min(ex.abs() + ey.abs()) / 2);
    if cross == 0 || ux.abs() + uy.abs() != 1 || vx.abs() + vy.abs() != 1 || r <= 0 {
        pb.line_to(p.x as f32, p.y as f32);
        return Ok(());
    }
    let centre = Point {
        x: i32::try_from(i64::from(p.x) - r * ux + r * vx).map_err(encode)?,
        y: i32::try_from(i64::from(p.y) - r * uy + r * vy).map_err(encode)?,
    };
    let start = match (-vx, -vy) {
        (1, 0) => 0,
        (0, 1) => 16384,
        (-1, 0) => 32768,
        _ => 49152,
    };
    let arc = crate::cells::braille::arc(
        centre,
        i32::try_from(r).map_err(encode)?,
        start,
        i32::try_from(cross * 16384).map_err(encode)?,
    )
    .map_err(encode)?;
    for p in arc {
        pb.line_to(p.x as f32, p.y as f32);
    }
    Ok(())
}
