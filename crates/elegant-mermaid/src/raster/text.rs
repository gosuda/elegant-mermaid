use super::{RasterError, encode, invalid, paint};
use crate::{
    scene::{Align, Run, TextItem, TextRole},
    theme::{TextChoice, Theme, Token},
};
use skrifa::{
    DrawMemory, ScalerFont,
    font::{Font, glyph::outline::PathSink},
};
use tiny_skia::{FillRule, PathBuilder, Pixmap, Transform};

pub struct GlyphOutlines {
    fonts: [Option<ScalerFont>; 2],
}
pub fn inter_outlines() -> GlyphOutlines {
    let bytes: [&[u8]; 2] = [
        include_bytes!("../../assets/fonts/Inter-Regular.ttf"),
        include_bytes!("../../assets/fonts/Inter-SemiBold.ttf"),
    ];
    GlyphOutlines {
        fonts: bytes.map(|data| Font::new(data, 0).map(|font| ScalerFont::unhinted(font, None))),
    }
}
struct Sink<'a> {
    path: &'a mut PathBuilder,
    x: f32,
    y: f32,
    factor: f32,
    italic: bool,
}
impl Sink<'_> {
    fn point(&self, x: f32, y: f32) -> (f32, f32) {
        let height = (y * self.factor + 0.5).floor();
        let shear = if self.italic {
            (13.0 * height / 64.0).floor()
        } else {
            0.0
        };
        (
            self.x + (x * self.factor + 0.5).floor() + shear,
            self.y - height,
        )
    }
}
impl PathSink for Sink<'_> {
    fn move_to(&mut self, x: f32, y: f32) {
        let (x, y) = self.point(x, y);
        self.path.move_to(x, y);
    }
    fn line_to(&mut self, x: f32, y: f32) {
        let (x, y) = self.point(x, y);
        self.path.line_to(x, y);
    }
    fn quad_to(&mut self, cx: f32, cy: f32, x: f32, y: f32) {
        let (cx, cy) = self.point(cx, cy);
        let (x, y) = self.point(x, y);
        self.path.quad_to(cx, cy, x, y);
    }
    fn curve_to(&mut self, ax: f32, ay: f32, bx: f32, by: f32, x: f32, y: f32) {
        let (ax, ay) = self.point(ax, ay);
        let (bx, by) = self.point(bx, by);
        let (x, y) = self.point(x, y);
        self.path.cubic_to(ax, ay, bx, by, x, y);
    }
    fn close(&mut self) {
        self.path.close();
    }
}
fn advance(weight: usize, c: char) -> u16 {
    crate::r#gen::advances::ADVANCES
        .iter()
        .find(|r| usize::from(r.weight) == weight && r.cp == u32::from(c))
        .map_or(1200, |r| r.units)
}
fn weight(t: &TextItem, run: &Run) -> usize {
    usize::from(run.bold || (!run.italic && t.role != TextRole::Body))
}
struct LinePainter<'a> {
    pix: &'a mut Pixmap,
    text: &'a TextItem,
    outlines: &'a GlyphOutlines,
    transform: Transform,
    paint: tiny_skia::Paint<'static>,
    origin: f32,
    baseline: f32,
    prefix: i64,
}
impl LinePainter<'_> {
    fn run(&mut self, run: &Run) -> Result<(), RasterError> {
        let w = weight(self.text, run);
        let scaler = self.outlines.fonts[w].as_ref().ok_or_else(invalid)?;
        let factor = self.text.size as f32 * 64.0 / f32::from(scaler.font().units_per_em());
        for c in run.text.chars() {
            let x = self.origin + (self.prefix as f32 * factor + 0.5).floor();
            let mut path = PathBuilder::new();
            if let Some(outline) = scaler
                .font()
                .charmap()
                .map_unicode(c)
                .and_then(|id| scaler.outline(id))
            {
                outline
                    .draw(
                        DrawMemory::Scratch,
                        &mut Sink {
                            path: &mut path,
                            x,
                            y: self.baseline,
                            factor,
                            italic: run.italic,
                        },
                    )
                    .map_err(encode)?;
            }
            if let Some(path) = path.finish() {
                self.pix
                    .fill_path(&path, &self.paint, FillRule::Winding, self.transform, None);
            }
            self.prefix += i64::from(advance(w, c));
        }
        Ok(())
    }
}
pub(super) fn draw(
    pix: &mut Pixmap,
    t: &TextItem,
    theme: &Theme,
    outlines: &GlyphOutlines,
    tr: Transform,
) -> Result<(), RasterError> {
    let row = crate::r#gen::styles::STYLES
        .iter()
        .find(|r| r.name == t.style.name())
        .ok_or_else(invalid)?;
    let name = if row.fill == "on-series" {
        match theme.series_text(t.series) {
            TextChoice::Background => "bg",
            _ => "fg",
        }
    } else {
        row.fill
    };
    let token = Token::ALL
        .into_iter()
        .find(|t| t.id() == name)
        .ok_or_else(invalid)?;
    let colour = paint(theme.colour(token), 255);
    let lh = if t.role == TextRole::Title {
        1536
    } else {
        1280
    };
    for (k, line) in t.lines.iter().enumerate() {
        let sum: i64 = line
            .iter()
            .map(|r| {
                r.text
                    .chars()
                    .map(|c| i64::from(advance(weight(t, r), c)))
                    .sum::<i64>()
            })
            .sum();
        let width = (sum * i64::from(t.size) * 64 + 2047) / 2048;
        let offset = match t.align {
            Align::Start => 0,
            Align::Middle => (i64::from(t.rect.w) - width).div_euclid(2),
            Align::End => i64::from(t.rect.w) - width,
        };
        let y = i64::from(t.rect.y)
            + i64::try_from(k).map_err(encode)? * i64::from(lh)
            + i64::from(lh / 2)
            + (i64::from(t.size) * 64 * 35) / 100;
        let mut painter = LinePainter {
            pix,
            text: t,
            outlines,
            transform: tr,
            paint: colour.clone(),
            origin: (i64::from(t.rect.x) + offset) as f32,
            baseline: y as f32,
            prefix: 0,
        };
        for run in line {
            painter.run(run)?;
        }
    }
    Ok(())
}
