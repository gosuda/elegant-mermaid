//! Vector math box layout (spec/math.md, math-13 and math-20 through math-28).
//!
//! A formula lays out into a [`FormulaBox`] of integer units: width `w`,
//! ascent `a` above the baseline, descent `d` below it, and leaf records.
//! Leaf coordinates are box-local, top-left origin, baseline at `y = a`. A
//! child box occupies `[baseline - d, baseline + a]` in up-coordinates, a
//! glyph box has `a = size` and `d = 0`, and a glyph leaf box is its
//! advance box. Constants scale by `round_half_up(v * em, 1000)` at the
//! formula base em; a script recurses at `round_half_up(700 * parent,
//! 1000)`. Conventions shared with the Go twin: subscript push-down
//! `min(-sub_shift, sup_shift - sup.d - sub.a)`, limit baselines
//! `bigop + bigop_gap + above.d` and `-(bigop_gap + below.a)`, delimiter
//! boxes hanging off the body extent, radical sign scaled up from the box
//! bottom, and the `cdot` font mapping applied to advances and drawing.

pub mod scene;

use crate::r#gen::mathglyph::MATH_GLYPH_MAPPINGS;
use crate::geom::{GeomError, Point, Rect};
use crate::math::syntax::{Delimiter, Expr, ExprKind, Font, Space, SymbolClass};
use crate::measure::Weight;

const SCRIPT_SCALE: i64 = 700;
const BIGOP_SCALE: i64 = 1400;
const FLATTEN_STEPS: i64 = 16;
const FLATTEN_DENOMINATOR: i64 = 256;
const FLATTEN_BIAS: i64 = 128;

/// One laid-out formula: width, ascent, descent, and its leaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormulaBox {
    /// The width in units.
    pub w: i32,
    /// The ascent above the baseline in units.
    pub a: i32,
    /// The descent below the baseline in units.
    pub d: i32,
    /// The leaves, in emission order, box-local.
    pub leaves: Vec<Leaf>,
}

/// One leaf of a formula box, positioned box-local with the baseline at
/// `y = a`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Leaf {
    /// One glyph on its baseline. `codepoint` is the logical character;
    /// advances and drawing use the font mapping of math-17.
    Glyph {
        codepoint: char,
        weight: Weight,
        size: i32,
        shear: bool,
        x: i32,
        baseline: i32,
    },
    /// One stroked rule, such as a fraction bar. A container is excluded
    /// from the leaf-box disjointness property (math-32).
    Rule { rect: Rect, container: bool },
    /// One flattened open polyline, such as a radical sign or a delimiter.
    Path { points: Vec<Point>, container: bool },
}

impl Leaf {
    /// The leaf box: glyphs use the advance box, rules their rectangle, and
    /// paths the bounding box of their points.
    pub fn box_rect(&self) -> Result<Rect, GeomError> {
        match self {
            Leaf::Glyph {
                codepoint,
                weight,
                size,
                x,
                baseline,
                ..
            } => {
                let w = glyph_advance(*codepoint, *weight, *size)?;
                make_rect(
                    i64::from(*x),
                    i64::from(*baseline) - i64::from(*size),
                    i64::from(w),
                    i64::from(*size),
                )
            }
            Leaf::Rule { rect, .. } => Ok(*rect),
            Leaf::Path { points, .. } => path_bounds(points),
        }
    }

    /// Whether the disjointness property skips this leaf as a container.
    pub const fn is_container(&self) -> bool {
        match self {
            Leaf::Glyph { .. } => false,
            Leaf::Rule { container, .. } | Leaf::Path { container, .. } => *container,
        }
    }
}

fn path_bounds(points: &[Point]) -> Result<Rect, GeomError> {
    let Some(first) = points.first() else {
        return make_rect(0, 0, 0, 0);
    };
    let bounds = points.iter().fold(
        (
            i64::from(first.x),
            i64::from(first.x),
            i64::from(first.y),
            i64::from(first.y),
        ),
        |(lo_x, hi_x, lo_y, hi_y), p| {
            (
                lo_x.min(i64::from(p.x)),
                hi_x.max(i64::from(p.x)),
                lo_y.min(i64::from(p.y)),
                hi_y.max(i64::from(p.y)),
            )
        },
    );
    make_rect(bounds.0, bounds.2, bounds.1 - bounds.0, bounds.3 - bounds.2)
}

/// The font codepoint that draws `codepoint` (math-17).
pub(super) fn font_codepoint(codepoint: char) -> char {
    let cp = u32::from(codepoint);
    MATH_GLYPH_MAPPINGS
        .iter()
        .find(|row| row.codepoint == cp)
        .and_then(|row| char::from_u32(row.font_codepoint))
        .unwrap_or(codepoint)
}

/// The advance of one glyph at `size` units, from the mapped font codepoint.
pub(super) fn glyph_advance(codepoint: char, weight: Weight, size: i32) -> Result<i32, GeomError> {
    let units = crate::measure::advance_units(weight, u32::from(font_codepoint(codepoint)));
    let numerator = units
        .checked_mul(i64::from(size))
        .ok_or(GeomError::Overflow)?;
    let scaled = crate::measure::ceil_div(numerator, crate::measure::upem(weight));
    narrow(scaled)
}

fn make_rect(x: i64, y: i64, w: i64, h: i64) -> Result<Rect, GeomError> {
    Ok(Rect {
        x: narrow(x)?,
        y: narrow(y)?,
        w: narrow(w)?,
        h: narrow(h)?,
    })
}

fn narrow(value: i64) -> Result<i32, GeomError> {
    i32::try_from(value).map_err(|_| GeomError::Overflow)
}

fn round_half_up(value: i64, scale: i64) -> Result<i64, GeomError> {
    let doubled = value
        .checked_mul(2)
        .and_then(|v| v.checked_add(scale))
        .ok_or(GeomError::Overflow)?;
    let twice = scale.checked_mul(2).ok_or(GeomError::Overflow)?;
    Ok(crate::geom::floor_div(doubled, twice))
}

/// The constants of math-21 at one base em, in units.
#[derive(Debug, Clone, Copy)]
struct Constants {
    rule: i32,
    axis: i32,
    frac_gap: i32,
    sup_shift: i32,
    sub_shift: i32,
    script_gap: i32,
    rad_gap: i32,
    rad_sign_w: i32,
    delim_w: i32,
    bigop_gap: i32,
    binop_space: i32,
    relop_space: i32,
    thin: i32,
    medium: i32,
    quad: i32,
}

impl Constants {
    fn new(em: i32) -> Result<Self, GeomError> {
        let em64 = i64::from(em);
        let at = |v: i64| {
            narrow(round_half_up(
                v.checked_mul(em64).ok_or(GeomError::Overflow)?,
                1000,
            )?)
        };
        let rule = at(50)?.max(1);
        Ok(Self {
            rule,
            axis: at(250)?,
            frac_gap: at(60)?,
            sup_shift: at(360)?,
            sub_shift: at(150)?,
            script_gap: at(30)?,
            rad_gap: at(60)?,
            rad_sign_w: at(600)?,
            delim_w: at(250)?,
            bigop_gap: at(100)?,
            binop_space: at(222)?,
            relop_space: at(278)?,
            thin: at(167)?,
            medium: at(278)?,
            quad: at(1000)?,
        })
    }
}

#[derive(Clone, Copy)]
struct Context {
    c: Constants,
    em: i32,
    bigop_size: i32,
}

struct Laid {
    w: i32,
    a: i32,
    d: i32,
    leaves: Vec<Leaf>,
}

impl Laid {
    fn new(w: i64, a: i64, d: i64) -> Result<Self, GeomError> {
        Ok(Self {
            w: narrow(w)?,
            a: narrow(a)?,
            d: narrow(d)?,
            leaves: Vec::new(),
        })
    }

    fn empty() -> Self {
        Self {
            w: 0,
            a: 0,
            d: 0,
            leaves: Vec::new(),
        }
    }
}

fn script_size(size: i32) -> Result<i32, GeomError> {
    narrow(round_half_up(SCRIPT_SCALE * i64::from(size), 1000)?)
}

/// Lays a parsed formula out at `size_px`, in units of 1/64 px.
pub fn layout(expression: &Expr<'_>, size_px: i32) -> Result<FormulaBox, GeomError> {
    let em = narrow(
        i64::from(size_px)
            .checked_mul(64)
            .ok_or(GeomError::Overflow)?,
    )?;
    let bigop_size = narrow(round_half_up(BIGOP_SCALE * i64::from(em), 1000)?)?;
    let ctx = Context {
        c: Constants::new(em)?,
        em,
        bigop_size,
    };
    let laid = element(expression, em, &ctx)?;
    Ok(FormulaBox {
        w: laid.w,
        a: laid.a,
        d: laid.d,
        leaves: laid.leaves,
    })
}

fn element(expr: &Expr<'_>, size: i32, ctx: &Context) -> Result<Laid, GeomError> {
    match &expr.kind {
        ExprKind::Row(children) => row_element(children, size, ctx),
        ExprKind::Group(body) => element(body, size, ctx),
        ExprKind::Fraction {
            numerator,
            denominator,
        } => fraction_element(numerator, denominator, size, ctx),
        ExprKind::Scripts {
            base,
            superscript,
            subscript,
        } => scripts_element(
            base,
            superscript.as_deref(),
            subscript.as_deref(),
            size,
            ctx,
        ),
        ExprKind::Radical { index, radicand } => {
            radical_element(index.as_deref(), radicand, size, ctx)
        }
        ExprKind::Delimited { left, body, right } => {
            delimited_element(*left, body, *right, size, ctx)
        }
        ExprKind::Limit { .. } => lim_element(size),
        ExprKind::Space(space) => space_element(*space, ctx),
        ExprKind::Literal(text) => literal_element(text, ctx.em),
        ExprKind::Styled { body, .. } | ExprKind::Text { body } => element(body, size, ctx),
        ExprKind::Glyph { .. } | ExprKind::Symbol { .. } => glyph_element(expr, size, ctx),
    }
}

fn literal_element(text: &str, size: i32) -> Result<Laid, GeomError> {
    let mut parts = Vec::new();
    let mut width = 0i64;
    for character in text.chars() {
        let font = if character.is_ascii_alphabetic() {
            Font::Italic
        } else {
            Font::Roman
        };
        let part = glyph_box(character, font, size)?;
        width += i64::from(part.w);
        parts.push(part);
    }
    let mut laid = Laid::new(width, i64::from(size), 0)?;
    let mut x = 0i64;
    for part in &parts {
        place(&mut laid, part, narrow(x)?, 0)?;
        x += i64::from(part.w);
    }
    Ok(laid)
}

fn glyph_element(expr: &Expr<'_>, size: i32, ctx: &Context) -> Result<Laid, GeomError> {
    let Some((character, font, class)) = glyph_of(expr) else {
        return Ok(Laid::empty());
    };
    let size = match class {
        Some(SymbolClass::Sum | SymbolClass::Product | SymbolClass::Integral) => ctx.bigop_size,
        _ => size,
    };
    glyph_box(character, font, size)
}

fn glyph_of(expr: &Expr<'_>) -> Option<(char, Font, Option<SymbolClass>)> {
    match &expr.kind {
        ExprKind::Literal(text) => {
            let character = text.chars().next()?;
            let font = if character.is_ascii_alphabetic() {
                Font::Italic
            } else {
                Font::Roman
            };
            Some((character, font, None))
        }
        ExprKind::Glyph { character, font } => Some((*character, *font, None)),
        ExprKind::Symbol {
            character,
            font,
            class,
            ..
        } => Some((*character, *font, Some(*class))),
        _ => None,
    }
}

fn glyph_box(character: char, font: Font, size: i32) -> Result<Laid, GeomError> {
    let weight = match font {
        Font::Bold => Weight::Semibold,
        _ => Weight::Regular,
    };
    let advance = glyph_advance(character, weight, size)?;
    Ok(Laid {
        w: advance,
        a: size,
        d: 0,
        leaves: vec![Leaf::Glyph {
            codepoint: character,
            weight,
            size,
            shear: font == Font::Italic,
            x: 0,
            baseline: size,
        }],
    })
}

fn space_element(space: Space, ctx: &Context) -> Result<Laid, GeomError> {
    let w = match space {
        Space::Thin => ctx.c.thin,
        Space::Medium => ctx.c.medium,
        Space::Quad => ctx.c.quad,
    };
    Ok(Laid {
        w,
        a: 0,
        d: 0,
        leaves: Vec::new(),
    })
}

fn lim_element(size: i32) -> Result<Laid, GeomError> {
    let mut width = 0i64;
    let mut laid = Laid {
        w: 0,
        a: size,
        d: 0,
        leaves: Vec::new(),
    };
    for character in ['l', 'i', 'm'] {
        let part = glyph_box(character, Font::Roman, size)?;
        place(&mut laid, &part, narrow(width)?, 0)?;
        width += i64::from(part.w);
    }
    laid.w = narrow(width)?;
    Ok(laid)
}

fn row_element(children: &[Expr<'_>], size: i32, ctx: &Context) -> Result<Laid, GeomError> {
    let mut parts: Vec<(Laid, i64)> = Vec::new();
    let mut cursor = 0i64;
    let mut previous_side = 0i32;
    for child in children {
        let side = child_space(child, ctx)?;
        if !parts.is_empty() {
            cursor = cursor
                .checked_add(i64::from(previous_side) + i64::from(side))
                .ok_or(GeomError::Overflow)?;
        }
        previous_side = side;
        let part = element(child, size, ctx)?;
        let x = cursor;
        cursor = cursor
            .checked_add(i64::from(part.w))
            .ok_or(GeomError::Overflow)?;
        parts.push((part, x));
    }
    let a = parts.iter().map(|(p, _)| p.a).max().unwrap_or(0);
    let d = parts.iter().map(|(p, _)| p.d).max().unwrap_or(0);
    let mut laid = Laid::new(cursor, i64::from(a), i64::from(d))?;
    for (part, x) in &parts {
        place(&mut laid, part, narrow(*x)?, 0)?;
    }
    Ok(laid)
}

fn child_space(expr: &Expr<'_>, ctx: &Context) -> Result<i32, GeomError> {
    match &expr.kind {
        ExprKind::Symbol { class, .. } => Ok(match class {
            SymbolClass::Binary => ctx.c.binop_space,
            SymbolClass::Relation => ctx.c.relop_space,
            _ => 0,
        }),
        ExprKind::Scripts { base, .. } => child_space(base, ctx),
        _ => Ok(0),
    }
}

/// Places `part` with its baseline `baseline_up` above the `laid` baseline.
/// The caller computes `laid.a` and `laid.d` over every part first.
fn place(laid: &mut Laid, part: &Laid, dx: i32, baseline_up: i32) -> Result<(), GeomError> {
    let top = i64::from(laid.a)
        .checked_sub(i64::from(baseline_up))
        .and_then(|v| v.checked_sub(i64::from(part.a)))
        .ok_or(GeomError::Overflow)?;
    for leaf in &part.leaves {
        laid.leaves.push(shift_leaf(leaf, i64::from(dx), top)?);
    }
    Ok(())
}

fn shift_leaf(leaf: &Leaf, dx: i64, dy: i64) -> Result<Leaf, GeomError> {
    let add = |a: i32, b: i64| narrow(i64::from(a).checked_add(b).ok_or(GeomError::Overflow)?);
    match leaf {
        Leaf::Glyph {
            codepoint,
            weight,
            size,
            shear,
            x,
            baseline,
        } => Ok(Leaf::Glyph {
            codepoint: *codepoint,
            weight: *weight,
            size: *size,
            shear: *shear,
            x: add(*x, dx)?,
            baseline: add(*baseline, dy)?,
        }),
        Leaf::Rule { rect, container } => Ok(Leaf::Rule {
            rect: Rect {
                x: add(rect.x, dx)?,
                y: add(rect.y, dy)?,
                w: rect.w,
                h: rect.h,
            },
            container: *container,
        }),
        Leaf::Path { points, container } => {
            let shifted = points
                .iter()
                .map(|p| {
                    Ok(Point {
                        x: add(p.x, dx)?,
                        y: add(p.y, dy)?,
                    })
                })
                .collect::<Result<Vec<_>, GeomError>>()?;
            Ok(Leaf::Path {
                points: shifted,
                container: *container,
            })
        }
    }
}

fn fraction_element(
    numerator: &Expr<'_>,
    denominator: &Expr<'_>,
    size: i32,
    ctx: &Context,
) -> Result<Laid, GeomError> {
    let top = element(numerator, size, ctx)?;
    let bottom = element(denominator, size, ctx)?;
    let bar_w = top.w.max(bottom.w) + 2 * ctx.c.script_gap;
    let bar_bottom = i64::from(ctx.c.axis) - i64::from(ctx.c.rule / 2);
    let bar_top = bar_bottom + i64::from(ctx.c.rule);
    let top_base = bar_top + i64::from(ctx.c.frac_gap) + i64::from(top.d);
    let bottom_base = bar_bottom - i64::from(ctx.c.frac_gap) - i64::from(bottom.a);
    let a = top_base + i64::from(top.a);
    let d = i64::from(bottom.d) - bottom_base;
    let mut laid = Laid::new(i64::from(bar_w), a, d)?;
    let bar = Leaf::Rule {
        rect: make_rect(0, a - bar_top, i64::from(bar_w), i64::from(ctx.c.rule))?,
        container: true,
    };
    laid.leaves.push(bar);
    place(&mut laid, &top, centred(bar_w, top.w), narrow(top_base)?)?;
    place(
        &mut laid,
        &bottom,
        centred(bar_w, bottom.w),
        narrow(bottom_base)?,
    )?;
    Ok(laid)
}

fn centred(total: i32, part: i32) -> i32 {
    (total - part) / 2
}

fn scripts_element(
    base: &Expr<'_>,
    superscript: Option<&Expr<'_>>,
    subscript: Option<&Expr<'_>>,
    size: i32,
    ctx: &Context,
) -> Result<Laid, GeomError> {
    if let ExprKind::Symbol {
        character, class, ..
    } = &base.kind
    {
        match class {
            SymbolClass::Sum | SymbolClass::Product => {
                return bigop_limits(*character, superscript, subscript, ctx);
            }
            SymbolClass::Integral => {
                let glyph = glyph_box(*character, Font::Roman, ctx.bigop_size)?;
                let size = script_size(ctx.bigop_size)?;
                return right_scripts(&glyph, superscript, subscript, size, ctx);
            }
            _ => {}
        }
    }
    let base_size = if is_bigop_glyph(base) {
        ctx.bigop_size
    } else {
        size
    };
    let base_laid = element(base, base_size, ctx)?;
    if matches!(base.kind, ExprKind::Limit { .. }) {
        let size = script_size(size)?;
        return lim_scripts(&base_laid, superscript, subscript, size, ctx);
    }
    let size = script_size(base_size)?;
    right_scripts(&base_laid, superscript, subscript, size, ctx)
}

fn is_bigop_glyph(expr: &Expr<'_>) -> bool {
    matches!(
        &expr.kind,
        ExprKind::Symbol {
            class: SymbolClass::Sum | SymbolClass::Product | SymbolClass::Integral,
            ..
        }
    )
}

fn bigop_limits(
    character: char,
    superscript: Option<&Expr<'_>>,
    subscript: Option<&Expr<'_>>,
    ctx: &Context,
) -> Result<Laid, GeomError> {
    let glyph = glyph_box(character, Font::Roman, ctx.bigop_size)?;
    let size = script_size(ctx.bigop_size)?;
    let above = laid_or_none(superscript, size, ctx)?;
    let below = laid_or_none(subscript, size, ctx)?;
    let above_base = above
        .as_ref()
        .map_or(0, |l| i64::from(glyph.a + ctx.c.bigop_gap + l.d));
    let below_base = below
        .as_ref()
        .map_or(0, |l| -i64::from(ctx.c.bigop_gap + l.a));
    let w = glyph
        .w
        .max(above.as_ref().map_or(0, |l| l.w))
        .max(below.as_ref().map_or(0, |l| l.w));
    let a = match &above {
        Some(l) => (narrow(above_base + i64::from(l.a))?).max(glyph.a),
        None => glyph.a,
    };
    let d = match &below {
        Some(l) => (narrow(i64::from(l.d) - below_base)?).max(glyph.d),
        None => glyph.d,
    };
    let mut laid = Laid::new(i64::from(w), i64::from(a), i64::from(d))?;
    place(&mut laid, &glyph, centred(w, glyph.w), 0)?;
    place_parts(&mut laid, above.as_ref(), above_base)?;
    place_parts(&mut laid, below.as_ref(), below_base)?;
    Ok(laid)
}

fn place_parts(laid: &mut Laid, part: Option<&Laid>, base_up: i64) -> Result<(), GeomError> {
    if let Some(part) = part {
        let x = centred(laid.w, part.w);
        place(laid, part, x, narrow(base_up)?)?;
    }
    Ok(())
}

fn laid_or_none(
    expr: Option<&Expr<'_>>,
    size: i32,
    ctx: &Context,
) -> Result<Option<Laid>, GeomError> {
    expr.map(|expr| element(expr, size, ctx)).transpose()
}

fn right_scripts(
    base_laid: &Laid,
    superscript: Option<&Expr<'_>>,
    subscript: Option<&Expr<'_>>,
    size: i32,
    ctx: &Context,
) -> Result<Laid, GeomError> {
    let sup = laid_or_none(superscript, size, ctx)?;
    let sub = laid_or_none(subscript, size, ctx)?;
    let x0 = i64::from(base_laid.w) + i64::from(ctx.c.script_gap);
    let sup_base = sup.as_ref().map_or(0, |_| i64::from(ctx.c.sup_shift));
    let sub_base = match (&sub, &sup) {
        (Some(s), Some(p)) => (i64::from(ctx.c.sup_shift) - i64::from(p.d) - i64::from(s.a))
            .min(-i64::from(ctx.c.sub_shift)),
        (Some(_), None) => -i64::from(ctx.c.sub_shift),
        _ => 0,
    };
    let script_w = sup
        .as_ref()
        .map_or(0, |l| l.w)
        .max(sub.as_ref().map_or(0, |l| l.w));
    let sup_a = sup.as_ref().map_or(0, |l| l.a);
    let sup_d = sup.as_ref().map_or(0, |l| l.d);
    let sub_a = sub.as_ref().map_or(0, |l| l.a);
    let sub_d = sub.as_ref().map_or(0, |l| l.d);
    let a = narrow(sup_base + i64::from(sup_a))?
        .max(narrow(sub_base + i64::from(sub_a))?)
        .max(base_laid.a);
    let d = narrow(i64::from(sup_d) - sup_base)?
        .max(narrow(i64::from(sub_d) - sub_base)?)
        .max(base_laid.d);
    let mut laid = Laid::new(x0 + i64::from(script_w), i64::from(a), i64::from(d))?;
    place(&mut laid, base_laid, 0, 0)?;
    let script_x = narrow(x0)?;
    if let Some(l) = sup.as_ref() {
        place(&mut laid, l, script_x, narrow(sup_base)?)?;
    }
    if let Some(l) = sub.as_ref() {
        place(&mut laid, l, script_x, narrow(sub_base)?)?;
    }
    Ok(laid)
}

fn lim_scripts(
    base_laid: &Laid,
    superscript: Option<&Expr<'_>>,
    subscript: Option<&Expr<'_>>,
    size: i32,
    ctx: &Context,
) -> Result<Laid, GeomError> {
    let sup = laid_or_none(superscript, size, ctx)?;
    let sub = laid_or_none(subscript, size, ctx)?;
    let Some(row) = script_row(&sup, &sub, ctx)? else {
        let mut laid = Laid::new(
            i64::from(base_laid.w),
            i64::from(base_laid.a),
            i64::from(base_laid.d),
        )?;
        place(&mut laid, base_laid, 0, 0)?;
        return Ok(laid);
    };
    let row_base = -i64::from(ctx.c.bigop_gap + row.a);
    let w = base_laid.w.max(row.w);
    let d = base_laid.d.max(narrow(i64::from(row.d) - row_base)?);
    let mut laid = Laid::new(i64::from(w), i64::from(base_laid.a), i64::from(d))?;
    place(&mut laid, base_laid, centred(w, base_laid.w), 0)?;
    place(&mut laid, &row, centred(w, row.w), narrow(row_base)?)?;
    Ok(laid)
}

fn script_row(
    sup: &Option<Laid>,
    sub: &Option<Laid>,
    ctx: &Context,
) -> Result<Option<Laid>, GeomError> {
    if sup.is_none() && sub.is_none() {
        return Ok(None);
    }
    let mut parts = Vec::new();
    let mut width = 0i64;
    if let Some(part) = sup {
        parts.push(part);
        width += i64::from(part.w);
    }
    if sup.is_some() && sub.is_some() {
        width += i64::from(ctx.c.script_gap);
    }
    if let Some(part) = sub {
        parts.push(part);
        width += i64::from(part.w);
    }
    if parts.is_empty() {
        return Ok(None);
    }
    let a = parts.iter().map(|p| p.a).max().unwrap_or(0);
    let d = parts.iter().map(|p| p.d).max().unwrap_or(0);
    let mut laid = Laid::new(width, i64::from(a), i64::from(d))?;
    let mut x = 0i64;
    for part in parts {
        place(&mut laid, part, narrow(x)?, 0)?;
        x += i64::from(part.w);
    }
    Ok(Some(laid))
}

fn radical_element(
    index: Option<&Expr<'_>>,
    radicand: &Expr<'_>,
    size: i32,
    ctx: &Context,
) -> Result<Laid, GeomError> {
    let rad = element(radicand, size, ctx)?;
    let idx_size = script_size(size)?;
    let idx = laid_or_none(index, idx_size, ctx)?;
    let idx_a = idx.as_ref().map_or(0, |l| l.a);
    let idx_d = idx.as_ref().map_or(0, |l| l.d);
    let a = (rad.a + ctx.c.rad_gap).max(ctx.c.sup_shift + idx_a);
    let index_drop = (i64::from(idx_d) - i64::from(ctx.c.sup_shift)).max(0);
    let d = i64::from(rad.d).max(index_drop);
    let sign_x = idx.as_ref().map_or(0, |l| l.w + ctx.c.script_gap);
    let rad_x = sign_x + ctx.c.rad_sign_w;
    let mut laid = Laid::new(i64::from(rad_x + rad.w), i64::from(a), d)?;
    let box_h = i64::from(laid.a) + i64::from(laid.d);
    let sign = sign_polyline(ctx.c.rad_sign_w, box_h, i64::from(sign_x))?;
    laid.leaves.push(sign);
    if let Some(part) = idx.as_ref() {
        place(&mut laid, part, 0, ctx.c.sup_shift)?;
    }
    place(&mut laid, &rad, sign_x + ctx.c.rad_sign_w, 0)?;
    Ok(laid)
}

fn sign_polyline(sign_w: i32, box_h: i64, sign_x: i64) -> Result<Leaf, GeomError> {
    const PER: [(i64, i64); 4] = [(0, 600), (250, 480), (450, 1000), (1000, 1000)];
    let mut points = Vec::with_capacity(PER.len());
    for (px, py) in PER {
        let x = round_half_up(
            px.checked_mul(i64::from(sign_w))
                .ok_or(GeomError::Overflow)?,
            1000,
        )?
        .checked_add(sign_x)
        .ok_or(GeomError::Overflow)?;
        let up = round_half_up(py.checked_mul(box_h).ok_or(GeomError::Overflow)?, 1000)?;
        points.push(Point {
            x: narrow(x)?,
            y: narrow(box_h.checked_sub(up).ok_or(GeomError::Overflow)?)?,
        });
    }
    Ok(Leaf::Path {
        points,
        container: true,
    })
}

fn delimited_element(
    left: Delimiter,
    body: &Expr<'_>,
    right: Delimiter,
    size: i32,
    ctx: &Context,
) -> Result<Laid, GeomError> {
    let body_laid = element(body, size, ctx)?;
    let height = i64::from(body_laid.a + body_laid.d).max(i64::from(ctx.em));
    let left_box = delimiter_box(left, height, body_laid.a, body_laid.d, ctx)?;
    let right_box = delimiter_box(right, height, body_laid.a, body_laid.d, ctx)?;
    let a = body_laid.a.max(left_box.a).max(right_box.a);
    let d = body_laid.d.max(left_box.d).max(right_box.d);
    let body_x = i64::from(left_box.w);
    let right_x = body_x + i64::from(body_laid.w);
    let mut laid = Laid::new(right_x + i64::from(right_box.w), i64::from(a), i64::from(d))?;
    let left_up = narrow(i64::from(a - left_box.a))?;
    let right_up = narrow(i64::from(a - right_box.a))?;
    place(&mut laid, &left_box, 0, left_up)?;
    place(&mut laid, &body_laid, narrow(body_x)?, 0)?;
    place(&mut laid, &right_box, narrow(right_x)?, right_up)?;
    Ok(laid)
}

fn delimiter_box(
    delimiter: Delimiter,
    height: i64,
    body_a: i32,
    body_d: i32,
    ctx: &Context,
) -> Result<Laid, GeomError> {
    if delimiter == Delimiter::Invisible {
        return Ok(Laid::empty());
    }
    let extra = height
        .checked_sub(i64::from(body_a))
        .and_then(|v| v.checked_sub(i64::from(body_d)))
        .ok_or(GeomError::Overflow)?;
    let a = i64::from(body_a) + round_half_up(extra, 2)?;
    let d = height - a;
    let mut laid = Laid::new(i64::from(ctx.c.delim_w), a, d)?;
    if let Some(points) = delimiter_points(delimiter, i64::from(ctx.c.delim_w), height)? {
        laid.leaves.push(Leaf::Path {
            points,
            container: false,
        });
    }
    Ok(laid)
}

fn delimiter_points(delimiter: Delimiter, w: i64, h: i64) -> Result<Option<Vec<Point>>, GeomError> {
    use Delimiter::*;
    let half = |v: i64| v / 2;
    let point = |x: i64, y: i64| -> Result<Point, GeomError> {
        Ok(Point {
            x: narrow(x)?,
            y: narrow(y)?,
        })
    };
    let line = |coords: &[(i64, i64)]| -> Result<Vec<Point>, GeomError> {
        coords.iter().map(|(x, y)| point(*x, *y)).collect()
    };
    let mirrored = |points: &[Point]| -> Result<Vec<Point>, GeomError> {
        points
            .iter()
            .map(|p| {
                point(
                    w.checked_sub(i64::from(p.x)).ok_or(GeomError::Overflow)?,
                    i64::from(p.y),
                )
            })
            .collect()
    };
    let paren = quadratic((w, 0), (0, half(h)), (w, h))?;
    let brace = line(&[
        (w, 0),
        (half(w), 0),
        (half(w), half(h)),
        (0, half(h)),
        (half(w), half(h)),
        (half(w), h),
        (w, h),
    ])?;
    Ok(match delimiter {
        LeftParen => Some(paren),
        RightParen => Some(mirrored(&paren)?),
        LeftBracket => Some(line(&[(w, 0), (0, 0), (0, h), (w, h)])?),
        RightBracket => Some(line(&[(0, 0), (w, 0), (w, h), (0, h)])?),
        LeftBrace => Some(brace),
        RightBrace => Some(mirrored(&brace)?),
        Bar => Some(line(&[(half(w), 0), (half(w), h)])?),
        Invisible => None,
    })
}

/// Flattens one quadratic Bezier segment into 17 half-up-rounded points
/// (math-27; the shared twin convention of k/16 with `(sum + 128) / 256`).
fn quadratic(p0: (i64, i64), p1: (i64, i64), p2: (i64, i64)) -> Result<Vec<Point>, GeomError> {
    let term = |weight: i64, control: i64| -> Result<i64, GeomError> {
        weight.checked_mul(control).ok_or(GeomError::Overflow)
    };
    let mut points = Vec::with_capacity(17);
    for k in 0..=FLATTEN_STEPS {
        let weight0 = (FLATTEN_STEPS - k) * (FLATTEN_STEPS - k);
        let weight1 = 2 * k * (FLATTEN_STEPS - k);
        let weight2 = k * k;
        let axis = |c0: i64, c1: i64, c2: i64| -> Result<i64, GeomError> {
            let first = term(weight0, c0)?;
            let middle = term(weight1, c1)?;
            let last = term(weight2, c2)?;
            let sum = first
                .checked_add(middle)
                .and_then(|v| v.checked_add(last))
                .ok_or(GeomError::Overflow)?;
            Ok((sum + FLATTEN_BIAS) / FLATTEN_DENOMINATOR)
        };
        points.push(Point {
            x: narrow(axis(p0.0, p1.0, p2.0)?)?,
            y: narrow(axis(p0.1, p1.1, p2.1)?)?,
        });
    }
    Ok(points)
}

#[cfg(test)]
mod tests;
