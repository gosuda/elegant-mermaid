//! Deterministic integer SVG serialization of the vector display list.
use crate::{
    geom::{Point, Rect},
    interaction::OwnerLink,
    scene::*,
    theme::{self, Colour, TextChoice, Theme, Token},
};
use std::collections::{BTreeMap, BTreeSet};
mod geometry;
#[cfg(test)]
mod link_tests;
#[cfg(test)]
mod markers_tests;
#[cfg(test)]
mod primitive_tests;
#[cfg(test)]
mod tests;
/// Font text is supported; paths require the later glyph-outline renderer.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum TextMode {
    #[default]
    Font,
    Paths,
}
/// Borrowed output options. Empty strings select the theme and font defaults.
#[derive(Debug, Default)]
pub struct Options<'a> {
    pub theme: &'a str,
    pub background: &'a str,
    pub text: TextMode,
    pub id_prefix: &'a str,
    pub title: &'a str,
    pub description: &'a str,
    pub kind: &'a str,
    pub font_family: &'a str,
    pub links: &'a [OwnerLink<'a>],
}
/// Invalid renderer configuration or a marker coordinate outside the integer range.
#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("svg: {0}")]
    Invalid(String),
    #[error(transparent)]
    Theme(#[from] theme::ThemeError),
    #[error(transparent)]
    Colour(#[from] theme::ColourError),
    #[error("svg: coordinate overflow")]
    Overflow,
}
struct Renderer {
    theme: Theme,
    used: BTreeSet<String>,
}
/// Append one complete SVG document, leaving `out` unchanged on failure.
///
/// Only the scene canvas and display list are read. Callers supply a vector scene;
/// cell-only symbols are rejected. No host resources or fonts are accessed.
pub fn write(out: &mut String, scene: &Scene, opts: &Options<'_>) -> Result<(), ConfigError> {
    if opts.text != TextMode::Font {
        return Err(invalid("text paths are not supported"));
    }
    if !valid_prefix(opts.id_prefix) {
        return Err(invalid("invalid ID prefix"));
    }
    let mut r = Renderer {
        theme: theme::resolve(opts.theme)?,
        used: BTreeSet::new(),
    };
    let bg = if opts.background.is_empty() {
        r.theme.colour(Token::Background)
    } else {
        Colour::parse_hex(opts.background)?
    }
    .hex();
    let body = group_body(&mut r, scene, opts)?;
    let w = geometry::number(i64::from(scene.canvas().w));
    let h = geometry::number(i64::from(scene.canvas().h));
    let mut result = header(opts, &w, &h);
    result.push_str(&format!("<style>\n.emd-bg{{fill:{bg}}}\n"));
    result.push_str(&r.styles()?);
    result.push_str(".emd-t-title{font-weight:600}\n.emd-t-label{font-weight:600}\n.emd-t-body{font-weight:400}\n</style>\n");
    result.push_str(&format!(
        "<rect class='emd-bg' x='0' y='0' width='{w}' height='{h}'/>\n"
    ));
    result.push_str(&body);
    result.push_str("</svg>\n");
    out.push_str(&result);
    Ok(())
}

fn group_body(
    renderer: &mut Renderer,
    scene: &Scene,
    opts: &Options<'_>,
) -> Result<String, ConfigError> {
    let mut body = String::new();
    let mut links = BTreeMap::new();
    for link in opts.links {
        links.insert(link.owner, link);
    }
    for (i, g) in scene.items().iter().enumerate() {
        let link = links.get(g.owner.as_str());
        if let Some(link) = link {
            body.push_str(&format!("<a href='{}'>\n", escape(link.url.as_str())));
            if let Some(tooltip) = link.tooltip {
                body.push_str(&format!("<title>{}</title>\n", escape(tooltip)));
            }
        }
        body.push_str(&format!(
            "<g class='emd-{}' id='{}g{}'>\n",
            g.role.as_str(),
            opts.id_prefix,
            i
        ));
        for p in &g.items {
            body.push_str(&renderer.primitive(p)?);
        }
        body.push_str("</g>\n");
        if link.is_some() {
            body.push_str("</a>\n");
        }
    }
    Ok(body)
}
fn invalid(s: impl Into<String>) -> ConfigError {
    ConfigError::Invalid(s.into())
}
fn valid_prefix(s: &str) -> bool {
    s.is_empty()
        || s.bytes().enumerate().all(|(i, b)| {
            b.is_ascii_alphabetic() || i > 0 && (b.is_ascii_digit() || b == b'_' || b == b'-')
        })
}
fn escape(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            '&' => "&amp;".into(),
            '<' => "&lt;".into(),
            '>' => "&gt;".into(),
            '\"' => "&quot;".into(),
            '\'' => "&apos;".into(),
            '\n' | '\r' | '\t' => c.to_string(),
            c if c < ' ' || c == '\u{fffe}' || c == '\u{ffff}' => "�".into(),
            _ => c.to_string(),
        })
        .collect()
}
fn header(o: &Options<'_>, w: &str, h: &str) -> String {
    let title = if o.title.is_empty() {
        format!("Mermaid {} diagram", o.kind)
    } else {
        o.title.into()
    };
    let font = if o.font_family.is_empty() {
        "Inter, 'Helvetica Neue', Arial, sans-serif"
    } else {
        o.font_family
    };
    let mut s = format!(
        "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 {w} {h}' width='{w}' height='{h}' font-family='{}' role='graphics-document document' aria-roledescription='diagram' aria-labelledby='{}title'",
        escape(font),
        o.id_prefix
    );
    if !o.description.is_empty() {
        s.push_str(&format!(" aria-describedby='{}desc'", o.id_prefix));
    }
    s.push_str(&format!(
        ">\n<title id='{}title'>{}</title>\n",
        o.id_prefix,
        escape(&title)
    ));
    if !o.description.is_empty() {
        s.push_str(&format!(
            "<desc id='{}desc'>{}</desc>\n",
            o.id_prefix,
            escape(o.description)
        ));
    }
    s
}
const ORDER: [&str; 22] = [
    "node",
    "group",
    "band",
    "note",
    "edge",
    "rule",
    "mark",
    "mark-hollow",
    "ink",
    "ink-line",
    "series",
    "series-line",
    "series-tint",
    "series-flow",
    "error",
    "warning",
    "success",
    "plate",
    "text",
    "text-muted",
    "text-inverse",
    "text-on-series",
];
fn class(name: &str, n: u8) -> String {
    if name.starts_with("series") || name == "text-on-series" {
        format!("{name}-{n}")
    } else {
        name.into()
    }
}
fn row(name: &str) -> Result<&'static crate::r#gen::styles::Style, ConfigError> {
    crate::r#gen::styles::STYLES
        .iter()
        .find(|s| s.name == name)
        .ok_or_else(|| invalid(format!("unknown style {name}")))
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Paint {
    Fill,
    Stroke,
}
impl Renderer {
    fn colour(&self, name: &str, n: u8, paint: Paint) -> Result<String, ConfigError> {
        if name == "none" {
            return Ok(name.into());
        }
        let id = if name == "series" {
            format!("series{}", n % 12)
        } else {
            name.into()
        };
        let token = Token::ALL
            .into_iter()
            .find(|t| t.id() == id)
            .ok_or_else(|| invalid(format!("unknown colour token {name}")))?;
        Ok(self
            .theme
            .colour(if paint == Paint::Stroke {
                self.theme.stroke(token)
            } else {
                token
            })
            .hex())
    }
    fn styles(&self) -> Result<String, ConfigError> {
        let mut s = String::new();
        for name in ORDER {
            for n in 0..12 {
                let key = class(name, n);
                if self.used.contains(&key) {
                    s.push_str(&self.style_rule(&key, name, n)?);
                }
                if key == name {
                    break;
                }
            }
        }
        Ok(s)
    }
    fn style_rule(&self, key: &str, name: &str, n: u8) -> Result<String, ConfigError> {
        let r = row(name)?;
        let fill = if r.fill == "on-series" {
            match self.theme.series_text(n) {
                TextChoice::Foreground => "fg",
                TextChoice::Background => "bg",
                TextChoice::Plate => return Err(invalid("text-on-series requires plate")),
            }
        } else {
            r.fill
        };
        let mut s = format!(".emd-s-{key}{{fill:{}", self.colour(fill, n, Paint::Fill)?);
        if r.class == 0 {
            s.push_str(&format!(
                ";stroke:{}",
                self.colour(r.stroke, n, Paint::Stroke)?
            ));
        }
        if r.tint == 1 {
            s.push_str(";fill-opacity:0.4");
        }
        if r.tint == 2 {
            s.push_str(";stroke-opacity:0.4");
        }
        s.push_str("}\n");
        Ok(s)
    }
    fn element(&mut self, tag: &str, shape: Shape, g: String) -> Result<String, ConfigError> {
        let name = shape.style.name();
        let r = row(name)?;
        let key = class(name, shape.series);
        self.used.insert(key.clone());
        let mut s = format!("<{tag} class='emd-s-{key}' {g}");
        if r.stroke != "none" {
            let width = match shape.width {
                Width::Normal => 64,
                Width::Emphasis => 128,
                Width::Units(n) => i64::from(n),
            };
            s.push_str(&format!(" stroke-width='{}'", geometry::number(width)));
        }
        match shape.line {
            Line::Dotted => s.push_str(" stroke-dasharray='3 3'"),
            Line::Dashed => s.push_str(" stroke-dasharray='8 4'"),
            _ => {}
        }
        s.push_str("/>\n");
        Ok(s)
    }
    fn primitive(&mut self, p: &Item) -> Result<String, ConfigError> {
        use geometry::{number, points, rect_attrs};
        match p {
            Item::Rect(v) => self.element("rect", v.shape, rect_attrs(v.rect)),
            Item::RoundRect(v) => self.element(
                "rect",
                v.shape,
                format!(
                    "{} rx='{}' ry='{}'",
                    rect_attrs(v.rect),
                    number(v.r.into()),
                    number(v.r.into())
                ),
            ),
            Item::Ellipse(v) => self.element(
                "ellipse",
                v.shape,
                format!(
                    "cx='{}' cy='{}' rx='{}' ry='{}'",
                    number(v.cx.into()),
                    number(v.cy.into()),
                    number(v.rx.into()),
                    number(v.ry.into())
                ),
            ),
            Item::Polygon(v) => self.element(
                "polygon",
                v.shape,
                format!("points='{}'", points(&v.points)),
            ),
            Item::Polyline(v) => {
                if v.corner > 0 {
                    self.element(
                        "path",
                        v.shape,
                        format!("d='{}'", geometry::rounded(&v.points, v.corner)),
                    )
                } else {
                    self.element(
                        "polyline",
                        v.shape,
                        format!("points='{}'", points(&v.points)),
                    )
                }
            }
            Item::Path(v) => self.element(
                "path",
                v.shape,
                format!("d='{}'", geometry::path(&v.commands)?),
            ),
            Item::Text(v) => self.text(v),
            Item::MarkerRef(v) => self.marker(v),
            Item::SymbolRef(_) => Err(invalid("SymbolRef is not a vector primitive")),
        }
    }
    fn marker(&mut self, m: &MarkerRefItem) -> Result<String, ConfigError> {
        if m.marker.points().len() < 2 {
            return Err(invalid(format!(
                "marker lacks outline: {}",
                m.marker.as_str()
            )));
        }
        let anchor = m
            .marker
            .anchor()
            .ok_or_else(|| invalid("marker lacks anchor"))?;
        let ps = m
            .marker
            .points()
            .iter()
            .map(|&p| geometry::marker_point(p, anchor, m))
            .collect::<Result<Vec<_>, _>>()?;
        let (style, tag) = match m.marker.paint() {
            Some("hollow") => (ShapeStyle::MarkHollow, "polygon"),
            Some("open") => (ShapeStyle::Edge, "polyline"),
            _ => (ShapeStyle::Mark, "polygon"),
        };
        let row = crate::r#gen::markers::MARKERS
            .iter()
            .find(|row| row.name == m.marker.as_str())
            .ok_or_else(|| invalid("unknown marker"))?;
        let mut out = String::new();
        let mut start = 0;
        for end in row
            .breaks
            .iter()
            .copied()
            .map(usize::try_from)
            .chain(std::iter::once(Ok(ps.len())))
        {
            let end = end.map_err(|_| ConfigError::Overflow)?;
            let contour = ps
                .get(start..end)
                .ok_or_else(|| invalid("invalid marker contour"))?;
            out.push_str(&self.element(
                tag,
                Shape::plain(style),
                format!("points='{}'", geometry::points(contour)),
            )?);
            start = end;
        }
        Ok(out)
    }
    fn text(&mut self, t: &TextItem) -> Result<String, ConfigError> {
        let key = class(t.style.name(), t.series);
        self.used.insert(key.clone());
        let x = i64::from(t.rect.x)
            + match t.align {
                Align::Start => 0,
                Align::Middle => i64::from(t.rect.w).div_euclid(2),
                Align::End => i64::from(t.rect.w),
            };
        let x = geometry::number(x);
        let mut s = format!(
            "<text class='emd-t-{} emd-s-{key}' x='{x}' font-size='{}' xml:space='preserve'",
            t.role.as_str(),
            t.size
        );
        if t.align != Align::Start {
            s.push_str(&format!(" text-anchor='{}'", t.align.as_str()));
        }
        s.push('>');
        let lh = if t.role == TextRole::Title {
            1536i64
        } else {
            1280
        };
        for (k, line) in t.lines.iter().enumerate() {
            let y = i64::try_from(k)
                .map_err(|_| ConfigError::Overflow)?
                .checked_mul(lh)
                .and_then(|v| v.checked_add(i64::from(t.rect.y)))
                .and_then(|v| v.checked_add(lh / 2))
                .and_then(|v| v.checked_add((i64::from(t.size) * 64 * 35).div_euclid(100)))
                .ok_or(ConfigError::Overflow)?;
            s.push_str(&format!("<tspan x='{x}' y='{}'>", geometry::number(y)));
            for run in line {
                s.push_str(&run_text(run));
            }
            s.push_str("</tspan>");
        }
        s.push_str("</text>\n");
        Ok(s)
    }
}
fn run_text(r: &Run) -> String {
    let mut s = escape(&r.text);
    if r.italic {
        s = format!("<tspan font-style='italic'>{s}</tspan>");
    }
    if r.bold {
        s = format!("<tspan font-weight='600'>{s}</tspan>");
    }
    s
}
