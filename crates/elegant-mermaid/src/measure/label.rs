//! Styled label measurement (spec/math.md, math-01 through math-08).
//!
//! One `label::parse` per label yields styled tokens: accepted emphasis
//! becomes bold or italic runs, escapes lose their backslash, accepted br
//! tags force lines, and math segments stay opaque literal text printed with
//! their dollars and no style. Wrapping slices runs by grapheme cluster and
//! never splits a run's styling. Bold measures with the weight 600 advances
//! (math-03), italic with the weight 400 advances (math-04), and every other
//! run with its role's weight. The cell profile ignores style: a cluster
//! counts the same cells whichever style renders it. Unsupported markup and
//! entities stay literal text (math-07, math-08).

use super::segment;
use super::width::{Metric, Weight, advance_sum};
use super::wrap::{GroupScale, RunScale, StyledWidths, WrappedLine, Wrapper};
use crate::geom::GeomError;
use crate::label::{self, Segment};
use crate::math::syntax as math_syntax;
use crate::math::vector as math_vector;
use crate::source::Span;

/// The one-cluster stand-in a vector math span occupies while measuring, so
/// the span stays atomic under wrapping.
const MATH_CLUSTER: char = '\u{E000}';

/// One styled run of a measured label line: the rendered text of one token's
/// intersection with the line, its style, and its own width in profile
/// units.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StyledRun<'a> {
    pub text: &'a str,
    pub bold: bool,
    pub italic: bool,
    pub width: i32,
    /// The laid-out formula box of a math run in the vector profile.
    pub math: Option<crate::math::vector::FormulaBox>,
}

/// One measured line of a styled label.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StyledLine<'a> {
    pub runs: Vec<StyledRun<'a>>,
    /// The rendered text: the run texts joined.
    pub text: String,
    pub width: i32,
    /// Source range in the original label, without standalone style context.
    pub source: Span,
}

struct Token<'a> {
    text: &'a str,
    source: Span,
    bold: bool,
    italic: bool,
    math: Option<math_vector::FormulaBox>,
}

struct Region<'a> {
    tokens: Vec<Token<'a>>,
    source: Span,
}

fn metric_font_family(metric: Metric) -> bool {
    match metric {
        Metric::Vector { font_family, .. } => font_family,
        Metric::Cell => false,
    }
}

fn weight(bold: bool, italic: bool, metric: Metric) -> Weight {
    if italic {
        Weight::Regular
    } else if bold {
        Weight::Semibold
    } else {
        match metric {
            Metric::Vector { weight, .. } => weight,
            Metric::Cell => Weight::Regular,
        }
    }
}

fn run_scale(token: &Token<'_>) -> RunScale {
    RunScale {
        bold: token.bold,
        italic: token.italic,
    }
}

fn group_of(metric: Metric, weight: Weight) -> GroupScale {
    match metric {
        Metric::Cell => GroupScale {
            cell: true,
            size_px: 0,
            weight: Weight::Regular,
            font_family: false,
        },
        Metric::Vector {
            size_px,
            font_family,
            ..
        } => GroupScale {
            cell: false,
            size_px,
            weight,
            font_family,
        },
    }
}

fn group_index(groups: &mut Vec<GroupScale>, group: GroupScale) -> usize {
    if let Some(at) = groups.iter().position(|existing| *existing == group) {
        return at;
    }
    groups.push(group);
    groups.len() - 1
}

fn push_token<'a>(tokens: &mut Vec<Token<'a>>, token: Token<'a>, metric: Metric) {
    if !metric.is_cell() {
        tokens.push(token);
        return;
    }
    let mut start = 0;
    for (at, scalar) in token.text.char_indices() {
        if !matches!(u32::from(scalar), 0..=31 | 127..=159) {
            continue;
        }
        if start < at {
            tokens.push(Token {
                text: &token.text[start..at],
                source: Span {
                    start: token.source.start + start,
                    end: token.source.start + at,
                },
                bold: token.bold,
                italic: token.italic,
                math: None,
            });
        }
        start = at + scalar.len_utf8();
        tokens.push(Token {
            text: "\u{fffd}",
            source: Span {
                start: token.source.start + at,
                end: token.source.start + start,
            },
            bold: token.bold,
            italic: token.italic,
            math: None,
        });
    }
    if start < token.text.len() {
        tokens.push(Token {
            text: &token.text[start..],
            source: Span {
                start: token.source.start + start,
                end: token.source.end,
            },
            bold: token.bold,
            italic: token.italic,
            math: None,
        });
    }
}

fn regions(text: &str, metric: Metric) -> Result<Vec<Region<'_>>, GeomError> {
    let parsed = label::parse(text);
    let end = text.len();
    let mut result = Vec::new();
    let mut at = 0usize;
    for line in &parsed.lines {
        let stop = line.break_span.map_or(end, |br| br.start);
        let mut tokens = Vec::new();
        for segment in &line.segments {
            let token = match segment {
                Segment::Text(t) => Token {
                    text: t.text,
                    source: Span {
                        start: t.span.end - t.text.len(),
                        end: t.span.end,
                    },
                    bold: t.bold,
                    italic: t.italic,
                    math: None,
                },
                Segment::Math(m) => Token {
                    text: &text[m.span.start..m.span.end],
                    source: m.span,
                    bold: false,
                    italic: false,
                    math: math_box(m.source, metric)?,
                },
            };
            push_token(&mut tokens, token, metric);
        }
        result.push(Region {
            tokens,
            source: Span {
                start: at,
                end: stop,
            },
        });
        at = line.break_span.map_or(end, |br| br.end);
    }
    Ok(result)
}

fn math_box(source: &str, metric: Metric) -> Result<Option<math_vector::FormulaBox>, GeomError> {
    let Metric::Vector { size_px, .. } = metric else {
        return Ok(None);
    };
    let parsed = math_syntax::parse(source);
    if !parsed.diagnostics.is_empty() {
        return Ok(None);
    }
    math_vector::layout(&parsed.expression, size_px).map(Some)
}

fn token_at(at: usize, ranges: &[(usize, usize)]) -> usize {
    ranges
        .partition_point(|(_, stop)| *stop <= at)
        .min(ranges.len() - 1)
}

struct RegionTokens<'a> {
    tokens: &'a [Token<'a>],
    rendered: &'a str,
    ranges: &'a [(usize, usize)],
    groups: &'a [usize],
    math: &'a [Option<math_vector::FormulaBox>],
    metric: Metric,
}

impl<'a> RegionTokens<'a> {
    fn unit_parts<'b>(
        &'b self,
        cluster: &'b str,
        start: usize,
        stop: usize,
    ) -> impl Iterator<Item = Result<(usize, i64), GeomError>> + 'b {
        let first = token_at(start, self.ranges);
        let cell = self.metric.is_cell();
        let whole = cell.then(|| {
            self.metric
                .text_units(cluster)
                .map(|units| (self.groups[first], units))
        });
        let beyond = if cell {
            first
        } else {
            token_at(stop - 1, self.ranges) + 1
        };
        whole
            .into_iter()
            .chain((first..beyond).filter_map(move |token| {
                let (from, to) = self.ranges[token];
                let lo = start.max(from);
                let hi = stop.min(to);
                if lo >= hi {
                    return None;
                }
                if let Some(formula) = self.math[token].as_ref() {
                    return Some(Ok((self.groups[token], i64::from(formula.w))));
                }
                let weight = weight(
                    self.tokens[token].bold,
                    self.tokens[token].italic,
                    self.metric,
                );
                Some(
                    advance_sum(&self.rendered[lo..hi], weight)
                        .map(|units| (self.groups[token], units)),
                )
            }))
    }
}

fn measure_region<'a>(
    tokens: &[Token<'a>],
    target: i32,
    metric: Metric,
) -> Result<Vec<StyledLine<'a>>, GeomError> {
    let mut rendered = String::new();
    let mut token_ranges = Vec::with_capacity(tokens.len());
    let mut token_sources = Vec::with_capacity(tokens.len());
    let mut token_texts = Vec::with_capacity(tokens.len());
    let mut token_group = Vec::with_capacity(tokens.len());
    let mut token_math = Vec::with_capacity(tokens.len());
    let mut scales = Vec::with_capacity(tokens.len());
    let mut groups: Vec<GroupScale> = Vec::new();
    for token in tokens {
        let start = rendered.len();
        if token.math.is_some() {
            rendered.push(MATH_CLUSTER);
        } else {
            rendered.push_str(token.text);
        }
        token_ranges.push((start, rendered.len()));
        token_sources.push(token.source);
        token_texts.push(token.text);
        let token_weight = weight(token.bold, token.italic, metric);
        let group = if token.math.is_some() {
            GroupScale {
                cell: true,
                size_px: 0,
                weight: Weight::Regular,
                font_family: metric_font_family(metric),
            }
        } else {
            group_of(metric, token_weight)
        };
        token_group.push(group_index(&mut groups, group));
        token_math.push(token.math.clone());
        scales.push(run_scale(token));
    }
    let region = RegionTokens {
        tokens,
        rendered: &rendered,
        ranges: &token_ranges,
        groups: &token_group,
        math: &token_math,
        metric,
    };
    let clusters = segment(&rendered);
    let mut cluster_span = Vec::with_capacity(clusters.len());
    let mut prefixes = vec![vec![0i64; clusters.len() + 1]; groups.len()];
    let mut at = 0usize;
    for (index, cluster) in clusters.iter().enumerate() {
        let start = at;
        at += cluster.text.len();
        for prefix in &mut prefixes {
            prefix[index + 1] = prefix[index];
        }
        for part in region.unit_parts(cluster.text, start, at) {
            let (group, units) = part?;
            prefixes[group][index + 1] = prefixes[group][index + 1]
                .checked_add(units)
                .ok_or(GeomError::Overflow)?;
        }
        cluster_span.push((start, at));
    }
    let widths = StyledWidths {
        token_texts,
        token_ranges,
        token_sources,
        token_group,
        token_math,
        scales,
        groups,
        cluster_span,
        prefixes,
    };
    let wrapper = Wrapper::styled(clusters, widths);
    let mut lines = Vec::new();
    for line in wrapper.run(target)? {
        match line {
            WrappedLine::Styled(line) => lines.push(line),
            WrappedLine::Plain(_) => {}
        }
    }
    Ok(lines)
}

/// Measures a label into styled lines: accepted br tags force lines
/// (math-05), and each region wraps at `target` without splitting a run or a
/// grapheme cluster. An empty label has no lines, and an empty forced region
/// has one empty line, so plain labels measure and wrap exactly as
/// `measure::wrap` does.
pub fn styled_lines<'a>(
    text: &'a str,
    target: i32,
    metric: Metric,
) -> Result<Vec<StyledLine<'a>>, GeomError> {
    let parsed = regions(text, metric)?;
    let last = parsed.len().saturating_sub(1);
    let mut lines = Vec::new();
    for (index, region) in parsed.iter().enumerate() {
        if region.tokens.is_empty() {
            if index != last {
                lines.push(StyledLine {
                    runs: Vec::new(),
                    text: String::new(),
                    width: 0,
                    source: region.source,
                });
            }
            continue;
        }
        lines.extend(measure_region(&region.tokens, target, metric)?);
    }
    Ok(lines)
}

/// The widest forced line, measured without wrapping and rounded once
/// after combining all selected glyph advances.
pub fn styled_width(text: &str, metric: Metric) -> Result<i32, GeomError> {
    let lines = styled_lines(text, i32::MAX, metric)?;
    Ok(lines.iter().map(|line| line.width).max().unwrap_or(0))
}

#[cfg(test)]
mod tests;
