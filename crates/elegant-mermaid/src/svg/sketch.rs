use super::hand_drawn::{
    Generator, path_segments, polygon_segments, polyline_segments, rect_segments,
};
use super::*;

pub(super) struct Outline<'a> {
    pub(super) tag: &'a str,
    pub(super) attrs: &'a str,
    pub(super) shape: Shape,
    pub(super) segments: &'a [(Point, Point)],
}

const RADIUS_TOKEN: i32 = 512;
const NEO_RADIUS: i32 = 768;

impl Renderer {
    pub(super) fn stroke_width(&self, width: Width) -> i64 {
        match width {
            Width::Normal if self.look.kind == LookKind::Neo => 128,
            Width::Normal => 64,
            Width::Emphasis => 128,
            Width::Units(n) => i64::from(n),
        }
    }

    pub(super) fn radius(&self, r: i32) -> i32 {
        if self.look.kind == LookKind::Neo && r == RADIUS_TOKEN {
            NEO_RADIUS
        } else {
            r
        }
    }

    pub(super) fn sketch(&mut self, p: &Item, index: usize) -> Result<Option<String>, ConfigError> {
        use geometry::{points, rect_attrs};
        let (tag, attrs, shape, segments) = match p {
            Item::Rect(v) => ("rect", rect_attrs(v.rect), v.shape, rect_segments(v.rect)),
            Item::RoundRect(v) if v.r == 0 => {
                ("rect", rect_attrs(v.rect), v.shape, rect_segments(v.rect))
            }
            Item::Polygon(v) => (
                "polygon",
                format!("points='{}'", points(&v.points)),
                v.shape,
                polygon_segments(&v.points),
            ),
            Item::Polyline(v) => (
                "polyline",
                format!("points='{}'", points(&v.points)),
                v.shape,
                polyline_segments(&v.points),
            ),
            Item::Path(v) => {
                let Some(segments) = path_segments(&v.commands) else {
                    return Ok(None);
                };
                (
                    "path",
                    format!("d='{}'", geometry::path(&v.commands)?),
                    v.shape,
                    segments,
                )
            }
            _ => return Ok(None),
        };
        if row(shape.style.name())?.stroke == "none" {
            return Ok(None);
        }
        let mut generator = Generator::new(self.look.seed, index);
        let outline = Outline {
            tag,
            attrs: &attrs,
            shape,
            segments: &segments,
        };
        self.sketch_shape(&outline, &mut generator).map(Some)
    }

    pub(super) fn sketch_shape(
        &mut self,
        outline: &Outline<'_>,
        generator: &mut Generator,
    ) -> Result<String, ConfigError> {
        let Outline {
            tag,
            attrs,
            shape,
            segments,
        } = *outline;
        let name = shape.style.name();
        let r = row(name)?;
        let key = class(name, shape.series);
        let mut out = String::new();
        if r.fill != "none" {
            self.fills.insert(key.clone());
            out.push_str(&format!("<{tag} class='emd-f-{key}' {attrs}/>\n"));
        }
        if r.stroke == "none" {
            return Ok(out);
        }
        self.sketches.insert(key.clone());
        let width = geometry::number(self.stroke_width(shape.width));
        let dash = match shape.line {
            Line::Dotted => " stroke-dasharray='3 3'",
            Line::Dashed => " stroke-dasharray='8 4'",
            _ => "",
        };
        for &(from, to) in segments {
            for pass in generator.segment(from, to) {
                out.push_str(&format!(
                    "<path class='emd-h-{key}' d='{}' stroke-width='{width}'{dash}/>\n",
                    pass.data()
                ));
            }
        }
        Ok(out)
    }

    pub(super) fn fill_rule(&self, key: &str, name: &str, n: u8) -> Result<String, ConfigError> {
        let r = row(name)?;
        let mut s = format!(
            ".emd-f-{key}{{fill:{}",
            self.colour(r.fill, n, Paint::Fill)?
        );
        if r.tint == 1 {
            s.push_str(";fill-opacity:0.4");
        }
        s.push_str("}\n");
        Ok(s)
    }

    pub(super) fn sketch_rule(&self, key: &str, name: &str, n: u8) -> Result<String, ConfigError> {
        let r = row(name)?;
        let mut s = format!(
            ".emd-h-{key}{{fill:none;stroke:{};stroke-linecap:round;stroke-linejoin:round",
            self.colour(r.stroke, n, Paint::Stroke)?
        );
        if r.tint == 2 {
            s.push_str(";stroke-opacity:0.4");
        }
        s.push_str("}\n");
        Ok(s)
    }
}
