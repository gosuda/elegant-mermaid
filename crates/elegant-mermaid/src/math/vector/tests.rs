use crate::geom::{GeomError, Rect};
use crate::math::syntax as math_syntax;
use crate::math::vector::scene::{LabelText, label_items};
use crate::math::vector::{self, Leaf};
use crate::measure::{Metric, StyledLine, Weight, advance_sum, ceil_div, styled_lines, upem};
use crate::scene::{Align, Item, ShapeStyle, TextRole, TextStyle};

const LABEL_EM: i32 = 896;
const SCRIPT_EM: i32 = 627;
const RULE: i32 = 45;
const AXIS: i32 = 224;
const FRAC_GAP: i32 = 54;
const SUP_SHIFT: i32 = 323;
const SUB_SHIFT: i32 = 134;
const SCRIPT_GAP: i32 = 27;
const RAD_SIGN_W: i32 = 538;
const DELIM_W: i32 = 224;
const BIGOP_GAP: i32 = 90;
const BINOP_SPACE: i32 = 199;
const RELOP_SPACE: i32 = 249;
const BIGOP_SIZE: i32 = 1254;
const BIGOP_SCRIPT: i32 = 878;

fn advance(text: &str, weight: Weight, size: i32) -> Result<i32, GeomError> {
    let units = advance_sum(text, weight)?;
    i32::try_from(ceil_div(units * i64::from(size), upem(weight))).map_err(|_| GeomError::Overflow)
}

fn vector_metric() -> Metric {
    Metric::Vector {
        size_px: 14,
        weight: Weight::Regular,
        font_family: false,
    }
}

fn lay(source: &str) -> Result<vector::FormulaBox, GeomError> {
    let parsed = math_syntax::parse(source);
    assert!(
        parsed.diagnostics.is_empty(),
        "expected {source:?} to parse, got {:?}",
        parsed.diagnostics
    );
    vector::layout(&parsed.expression, 14)
}

fn glyph_leaves(formula: &vector::FormulaBox) -> Vec<&Leaf> {
    formula
        .leaves
        .iter()
        .filter(|leaf| matches!(leaf, Leaf::Glyph { .. }))
        .collect()
}

#[test]
fn math_leaf_boxes() -> Result<(), GeomError> {
    for seed in 1u32..=500 {
        let mut rng = Rng::new(seed);
        let source = term(&mut rng, 3);
        let parsed = math_syntax::parse(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "seed {seed} generated {source:?} with {:?}",
            parsed.diagnostics
        );
        let formula = vector::layout(&parsed.expression, 14)?;
        let outer_w = i64::from(formula.w);
        let outer_h = i64::from(
            formula
                .a
                .checked_add(formula.d)
                .ok_or(GeomError::Overflow)?,
        );
        let mut inner = Vec::new();
        for leaf in &formula.leaves {
            let rect = leaf.box_rect()?;
            assert!(
                i64::from(rect.x) >= 0
                    && i64::from(rect.y) >= 0
                    && i64::from(rect.x) + i64::from(rect.w) <= outer_w
                    && i64::from(rect.y) + i64::from(rect.h) <= outer_h,
                "seed {seed} leaf {rect:?} outside {outer_w}x{outer_h} for {source:?}"
            );
            if !leaf.is_container() {
                inner.push(rect);
            }
        }
        for (index, first) in inner.iter().enumerate() {
            for second in &inner[index + 1..] {
                assert!(
                    !crate::geom::intersects(*first, *second)?,
                    "seed {seed} leaves {first:?} and {second:?} overlap in {source:?}"
                );
            }
        }
    }
    Ok(())
}

struct Rng(u32);

impl Rng {
    fn new(seed: u32) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        self.0
    }

    fn draw(&mut self, lo: u32, hi: u32) -> u32 {
        lo + self.next() % (hi - lo + 1)
    }

    fn pick<'a>(&mut self, items: &[&'a str]) -> &'a str {
        items[(self.next() as usize) % items.len()]
    }
}

const LITERALS: [&str; 6] = ["x", "y", "1", "2", "+", "="];
const SYMBOLS: [&str; 16] = [
    "alpha", "beta", "Gamma", "sum", "prod", "int", "infty", "pm", "times", "div", "cdot", "le",
    "ge", "ne", "approx", "to",
];
const DELIMITERS: [&str; 6] = ["(", ")", "[", "]", "|", "."];

fn atom(rng: &mut Rng) -> String {
    match rng.draw(0, 4) {
        0 => rng.pick(&LITERALS).to_string(),
        1 => format!("\\{}", rng.pick(&SYMBOLS)),
        2 => match rng.draw(0, 2) {
            0 => "\\,".to_string(),
            1 => "\\;".to_string(),
            _ => "\\quad".to_string(),
        },
        3 => "\\lim".to_string(),
        _ => rng.pick(&LITERALS).to_string(),
    }
}

fn term(rng: &mut Rng, depth: u32) -> String {
    if depth == 0 {
        return atom(rng);
    }
    match rng.draw(0, 5) {
        0 => atom(rng),
        1 => format!(
            "\\frac{{{}}}{{{}}}",
            term(rng, depth - 1),
            term(rng, depth - 1)
        ),
        2 => match rng.draw(0, 2) {
            0 => format!("\\sqrt{{{}}}", term(rng, depth - 1)),
            _ => format!("\\sqrt[{}]{{{}}}", atom(rng), term(rng, depth - 1)),
        },
        3 => match rng.draw(0, 2) {
            0 => format!("{}^{{{}}}", atom(rng), term(rng, depth - 1)),
            1 => format!("{}_{{{}}}", atom(rng), term(rng, depth - 1)),
            _ => format!(
                "{}^{{{}}}_{{{}}}",
                atom(rng),
                atom(rng),
                term(rng, depth - 1)
            ),
        },
        4 => {
            let left = rng.pick(&DELIMITERS);
            let right = rng.pick(&DELIMITERS);
            format!("\\left{}{}\\right{}", left, term(rng, depth - 1), right)
        }
        _ => atom(rng),
    }
}

#[test]
fn fraction_bar_geometry() -> Result<(), GeomError> {
    let formula = lay(r"\frac{a}{b}")?;
    let width =
        advance("a", Weight::Regular, LABEL_EM)?.max(advance("b", Weight::Regular, LABEL_EM)?)
            + 2 * SCRIPT_GAP;
    assert_eq!(formula.w, width);
    let bar_top = AXIS + RULE - RULE / 2;
    assert_eq!(formula.a, bar_top + FRAC_GAP + LABEL_EM);
    let Leaf::Rule { rect, container } = &formula.leaves[0] else {
        return Err(GeomError::Domain);
    };
    assert!(*container);
    assert_eq!(rect.w, width);
    assert_eq!(rect.h, RULE);
    assert_eq!(rect.y, formula.a - bar_top);
    let glyphs = glyph_leaves(&formula);
    assert_eq!(glyphs.len(), 2);
    Ok(())
}

#[test]
fn script_sizes_shrink_recursively() -> Result<(), GeomError> {
    let formula = lay("x^{2}")?;
    assert_eq!(formula.a, SUP_SHIFT + SCRIPT_EM);
    assert_eq!(
        formula.w,
        advance("x", Weight::Regular, LABEL_EM)?
            + SCRIPT_GAP
            + advance("2", Weight::Regular, SCRIPT_EM)?
    );
    let Leaf::Glyph {
        size, x, baseline, ..
    } = glyph_leaves(&formula)[1]
    else {
        return Err(GeomError::Domain);
    };
    assert_eq!(*size, SCRIPT_EM);
    assert_eq!(*baseline, formula.a - SUP_SHIFT);
    assert_eq!(*x, advance("x", Weight::Regular, LABEL_EM)? + SCRIPT_GAP);
    let nested = lay("x^{2^{3}}")?;
    let inner = 439;
    assert_eq!(
        nested.w,
        advance("x", Weight::Regular, LABEL_EM)?
            + SCRIPT_GAP
            + advance("2", Weight::Regular, SCRIPT_EM)?
            + SCRIPT_GAP
            + advance("3", Weight::Regular, inner)?
    );
    Ok(())
}

#[test]
fn dual_scripts_push_subscript_down() -> Result<(), GeomError> {
    let formula = lay("x^{a}_{b}")?;
    let sub_base = (SUP_SHIFT - SCRIPT_EM).min(-SUB_SHIFT);
    assert_eq!(sub_base, -304);
    assert_eq!(formula.d, 304);
    assert_eq!(formula.a, SUP_SHIFT + SCRIPT_EM);
    Ok(())
}

#[test]
fn bigop_limits_clear_the_glyph() -> Result<(), GeomError> {
    let formula = lay(r"\sum_{i}")?;
    let glyph_w = advance("\u{2211}", Weight::Regular, BIGOP_SIZE)?;
    let limit_w = advance("i", Weight::Regular, BIGOP_SCRIPT)?;
    assert_eq!(formula.w, glyph_w.max(limit_w));
    let below_base = -(BIGOP_GAP + BIGOP_SCRIPT);
    assert_eq!(formula.d, -below_base);
    let Leaf::Glyph { baseline, size, .. } = glyph_leaves(&formula)[0] else {
        return Err(GeomError::Domain);
    };
    assert_eq!(*size, BIGOP_SIZE);
    assert_eq!(*baseline, BIGOP_SIZE);
    let Leaf::Glyph { baseline, .. } = glyph_leaves(&formula)[1] else {
        return Err(GeomError::Domain);
    };
    assert_eq!(*baseline, formula.a - below_base);
    Ok(())
}

#[test]
fn radical_sign_points() -> Result<(), GeomError> {
    let formula = lay(r"\sqrt{x}")?;
    assert_eq!(formula.a, LABEL_EM + 54);
    let Leaf::Path { points, container } = &formula.leaves[0] else {
        return Err(GeomError::Domain);
    };
    assert!(*container);
    let box_h = i64::from(formula.a + formula.d);
    let rh = |v: i64| (2 * v + 1000) / 2000;
    let expected_y = |per: i64| -> Result<i32, GeomError> {
        i32::try_from(box_h - rh(per * box_h)).map_err(|_| GeomError::Overflow)
    };
    let expected = vec![
        (0i64, i64::from(expected_y(600)?)),
        (rh(250 * i64::from(RAD_SIGN_W)), i64::from(expected_y(480)?)),
        (rh(450 * i64::from(RAD_SIGN_W)), 0),
        (i64::from(RAD_SIGN_W), 0),
    ];
    for (point, want) in points.iter().zip(&expected) {
        assert_eq!((i64::from(point.x), i64::from(point.y)), *want);
    }
    let radicand = glyph_leaves(&formula);
    assert_eq!(radicand.len(), 1);
    Ok(())
}

#[test]
fn delimiter_shapes_and_invisible() -> Result<(), GeomError> {
    let formula = lay(r"\left(x\right.")?;
    let Leaf::Path { points, container } = &formula.leaves[0] else {
        return Err(GeomError::Domain);
    };
    assert!(!*container);
    assert_eq!(points.first().map(|p| (p.x, p.y)), Some((DELIM_W, 0)));
    assert!(points.iter().all(|p| p.x >= 0 && p.x <= DELIM_W));
    let glyphs = glyph_leaves(&formula);
    assert_eq!(glyphs.len(), 1);
    assert_eq!(
        formula.w,
        DELIM_W + advance("x", Weight::Regular, LABEL_EM)?
    );
    let bar = lay(r"\left|x\right|")?;
    let Leaf::Path { points, .. } = &bar.leaves[0] else {
        return Err(GeomError::Domain);
    };
    assert_eq!(points.len(), 2);
    Ok(())
}

#[test]
fn neighbour_spacing_has_no_edge_space() -> Result<(), GeomError> {
    let formula = lay(r"x\pm y")?;
    let expected = advance("x", Weight::Regular, LABEL_EM)?
        + BINOP_SPACE
        + advance("\u{b1}", Weight::Regular, LABEL_EM)?
        + BINOP_SPACE
        + advance("y", Weight::Regular, LABEL_EM)?;
    assert_eq!(formula.w, expected);
    let leading = lay(r"\pm x")?;
    assert_eq!(
        leading.w,
        advance("\u{b1}", Weight::Regular, LABEL_EM)?
            + BINOP_SPACE
            + advance("x", Weight::Regular, LABEL_EM)?
    );
    let relation = lay("x=y")?;
    assert_eq!(
        relation.w,
        advance("x", Weight::Regular, LABEL_EM)?
            + RELOP_SPACE
            + advance("=", Weight::Regular, LABEL_EM)?
            + RELOP_SPACE
            + advance("y", Weight::Regular, LABEL_EM)?
    );
    Ok(())
}

#[test]
fn cdot_uses_font_mapping() -> Result<(), GeomError> {
    let formula = lay(r"\cdot")?;
    let Leaf::Glyph { codepoint, .. } = glyph_leaves(&formula)[0] else {
        return Err(GeomError::Domain);
    };
    assert_eq!(*codepoint, '\u{22c5}');
    assert_eq!(formula.w, advance("\u{b7}", Weight::Regular, LABEL_EM)?);
    Ok(())
}

#[test]
fn italic_uses_upright_advance() -> Result<(), GeomError> {
    let formula = lay("x")?;
    let Leaf::Glyph {
        shear, baseline, ..
    } = glyph_leaves(&formula)[0]
    else {
        return Err(GeomError::Domain);
    };
    assert!(*shear);
    assert_eq!(*baseline, LABEL_EM);
    assert_eq!(formula.w, advance("x", Weight::Regular, LABEL_EM)?);
    assert_eq!(formula.a, LABEL_EM);
    assert_eq!(formula.d, 0);
    Ok(())
}

#[test]
fn math_span_is_atomic_with_box_width() -> Result<(), GeomError> {
    let text = r"$$\frac{a}{b}$$ tail";
    let lines = styled_lines(text, i32::MAX, vector_metric())?;
    assert_eq!(lines.len(), 1);
    assert_eq!(lines[0].text, text);
    let runs = &lines[0].runs;
    assert_eq!(runs.len(), 2);
    let formula = runs[0].math.as_ref().ok_or(GeomError::Domain)?;
    assert_eq!(runs[0].text, r"$$\frac{a}{b}$$");
    assert_eq!(runs[0].width, formula.w);
    let expected = formula.w + advance(" tail", Weight::Regular, LABEL_EM)?;
    assert_eq!(lines[0].width, expected);
    let narrow = styled_lines(text, 40, vector_metric())?;
    assert!(narrow.len() >= 2);
    assert_eq!(narrow[0].runs.len(), 1);
    assert!(narrow[0].runs[0].math.is_some());
    Ok(())
}

#[test]
fn cell_profile_keeps_literal_math() -> Result<(), GeomError> {
    let text = r"$$\frac{a}{b}$$ tail";
    let lines = styled_lines(text, 100, Metric::Cell)?;
    assert_eq!(lines.len(), 1);
    assert!(lines[0].runs.iter().all(|run| run.math.is_none()));
    assert_eq!(lines[0].width, crate::measure::cell_width(text)?);
    Ok(())
}

#[test]
fn plain_label_emits_one_text_item() -> Result<(), GeomError> {
    let lines = styled_lines("plain tail", 4000, vector_metric())?;
    let rect = Rect {
        x: 100,
        y: 200,
        w: 900,
        h: 1280,
    };
    let items = label_items(LabelText {
        rect,
        role: TextRole::Label,
        size: 14,
        align: Align::Middle,
        style: TextStyle::Text,
        series: 0,
        lines: &lines,
    })?;
    let [Item::Text(text)] = &items[..] else {
        return Err(GeomError::Domain);
    };
    assert_eq!(text.rect, rect);
    assert_eq!(text.role, TextRole::Label);
    assert_eq!(text.align, Align::Middle);
    Ok(())
}

#[test]
fn math_label_emits_shapes_then_text() -> Result<(), GeomError> {
    let lines: Vec<StyledLine<'_>> = styled_lines(r"$$\frac{a}{b}$$", 4000, vector_metric())?;
    let rect = Rect {
        x: 100,
        y: 200,
        w: lines[0].width,
        h: 1280,
    };
    let items = label_items(LabelText {
        rect,
        role: TextRole::Label,
        size: 14,
        align: Align::Middle,
        style: TextStyle::Text,
        series: 0,
        lines: &lines,
    })?;
    let shapes = items
        .iter()
        .take_while(|item| matches!(item, Item::Rect(_) | Item::Polyline(_)))
        .count();
    assert!(shapes >= 1, "fraction bar missing: {items:?}");
    assert!(items.len() > shapes);
    let Item::Rect(bar) = &items[0] else {
        return Err(GeomError::Domain);
    };
    assert_eq!(bar.shape.style, ShapeStyle::Rule);
    let glyphs: Vec<_> = items[shapes..]
        .iter()
        .filter_map(|item| match item {
            Item::Text(text) => Some(text),
            _ => None,
        })
        .collect();
    assert!(glyphs.iter().all(|text| text.role == TextRole::Body));
    Ok(())
}
