use super::label::{StyledLine, StyledRun};
use super::width::{Weight, advance_sum, scaled_width, upem};
use super::{Cluster, Metric, segment};
use crate::r#gen::ideographic::IDEOGRAPHIC;
use crate::geom::GeomError;
use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Line<'a> {
    pub text: &'a str,
    pub separator: &'a str,
    pub width: i32,
}
pub fn default_wrap_width(metric: Metric) -> i32 {
    if metric.is_cell() { 32 } else { 12800 }
}
pub fn wrap_target(metric: Metric, kind_target: i32, max_width: i32) -> i32 {
    if kind_target > 0 {
        kind_target
    } else if max_width > 0 {
        max_width
    } else {
        default_wrap_width(metric)
    }
}
fn ideographic(cp: char) -> bool {
    let cp = u32::from(cp);
    let index = IDEOGRAPHIC.partition_point(|row| row.hi < cp);
    IDEOGRAPHIC.get(index).is_some_and(|row| row.lo <= cp)
}
fn boundary(previous: Cluster<'_>, next: Cluster<'_>) -> bool {
    match (previous.last_scalar(), next.first_scalar()) {
        (Some(a), Some(b)) => {
            (a == '-' && b.is_ascii_alphanumeric()) || (ideographic(a) && ideographic(b))
        }
        _ => false,
    }
}
/// How one wrapper computes the width of a cluster range and builds its
/// lines: the plain metric of `measure::wrap`, or the styled runs of a
/// label.
enum Widths<'a> {
    Metric {
        metric: Metric,
        text: &'a str,
        offsets: Vec<usize>,
        prefix: Vec<i64>,
    },
    Styled(StyledWidths<'a>),
}

/// The style flags of one styled run.
pub(crate) struct RunScale {
    pub bold: bool,
    pub italic: bool,
}

/// The scaling of one weight group of a styled region. Groups only bucket
/// the units per weight; the line width is one ceiling of their combined
/// rational sum.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct GroupScale {
    pub cell: bool,
    pub size_px: i32,
    pub weight: Weight,
    pub font_family: bool,
}

impl GroupScale {
    fn width(&self, units: i64) -> Result<i64, GeomError> {
        if self.cell {
            return Ok(units);
        }
        scaled_width(units, self.size_px, self.weight)
    }
}

/// The tokens (runs) and clusters of one styled label region: token byte
/// ranges and styles carry the styling, cluster byte spans and per-weight
/// unit parts carry the atomic measurement.
pub(crate) struct StyledWidths<'a> {
    pub token_texts: Vec<&'a str>,
    pub token_ranges: Vec<(usize, usize)>,
    pub token_sources: Vec<Span>,
    pub token_group: Vec<usize>,
    pub token_math: Vec<Option<crate::math::vector::FormulaBox>>,
    pub scales: Vec<RunScale>,
    pub groups: Vec<GroupScale>,
    pub cluster_span: Vec<(usize, usize)>,
    pub prefixes: Vec<Vec<i64>>,
}

fn scaled_rational(pairs: &[(i64, Weight)], size_px: i32) -> Result<i64, GeomError> {
    if let [(units, weight)] = pairs {
        return scaled_width(*units, size_px, *weight);
    }
    let mut denominator = 1i128;
    for (_, weight) in pairs {
        denominator = denominator
            .checked_mul(i128::from(upem(*weight)))
            .ok_or(GeomError::Overflow)?;
    }
    let mut numerator = 0i128;
    for (units, weight) in pairs {
        let factor = denominator / i128::from(upem(*weight));
        let term = i128::from(*units)
            .checked_mul(factor)
            .ok_or(GeomError::Overflow)?;
        numerator = numerator.checked_add(term).ok_or(GeomError::Overflow)?;
    }
    let size64 = i64::from(size_px)
        .checked_mul(64)
        .ok_or(GeomError::Overflow)?;
    let numerator = numerator
        .checked_mul(i128::from(size64))
        .ok_or(GeomError::Overflow)?;
    let quotient = (numerator + denominator - 1) / denominator;
    i64::try_from(quotient).map_err(|_| GeomError::Overflow)
}

impl<'a> StyledWidths<'a> {
    fn span_width(&self, from: usize, to: usize) -> Result<i32, GeomError> {
        let mut cell_units = 0i64;
        let mut vector: Vec<(i64, Weight)> = Vec::new();
        let mut size_px = 0i32;
        let mut font_family = false;
        for (group, prefix) in self.groups.iter().zip(&self.prefixes) {
            let units = prefix[to] - prefix[from];
            if units == 0 {
                continue;
            }
            font_family |= group.font_family;
            if group.cell {
                cell_units = cell_units.checked_add(units).ok_or(GeomError::Overflow)?;
            } else {
                size_px = group.size_px;
                vector.push((units, group.weight));
            }
        }
        let scaled = if vector.is_empty() {
            cell_units
        } else {
            scaled_rational(&vector, size_px)?
                .checked_add(cell_units)
                .ok_or(GeomError::Overflow)?
        };
        let scaled = if font_family {
            crate::geom::floor_div(scaled.checked_mul(108).ok_or(GeomError::Overflow)?, 100)
        } else {
            scaled
        };
        i32::try_from(scaled).map_err(|_| GeomError::Overflow)
    }

    fn source_start(&self, at: usize) -> usize {
        let token = self
            .token_ranges
            .partition_point(|(_, stop)| *stop <= at)
            .min(self.token_ranges.len() - 1);
        self.source_at(token, at)
    }

    fn source_end(&self, at: usize) -> usize {
        let token = self
            .token_ranges
            .partition_point(|(_, stop)| *stop < at)
            .min(self.token_ranges.len() - 1);
        self.source_at(token, at)
    }

    fn source_at(&self, token: usize, at: usize) -> usize {
        let (start, stop) = self.token_ranges[token];
        let source = self.token_sources[token];
        if at == stop {
            source.end
        } else if stop - start == source.end - source.start {
            source.start + at - start
        } else {
            source.start
        }
    }

    fn line(&self, from: usize, end: usize) -> Result<StyledLine<'a>, GeomError> {
        let start = self.cluster_span[from].0;
        let stop = self.cluster_span[end - 1].1;
        let first = self
            .token_ranges
            .partition_point(|(_, token_stop)| *token_stop <= start)
            .min(self.token_ranges.len() - 1);
        let beyond = self
            .token_ranges
            .partition_point(|(token_start, _)| *token_start < stop);
        let mut runs = Vec::new();
        for token in first..beyond {
            let (token_start, token_stop) = self.token_ranges[token];
            let lo = start.max(token_start);
            let hi = stop.min(token_stop);
            if lo >= hi {
                continue;
            }
            let text = &self.token_texts[token][lo - token_start..hi - token_start];
            if let Some(formula) = self.token_math[token].as_ref() {
                runs.push(StyledRun {
                    text: self.token_texts[token],
                    bold: false,
                    italic: false,
                    width: formula.w,
                    math: Some(formula.clone()),
                });
                continue;
            }
            let group = self.token_group[token];
            let units = if self.groups[group].cell {
                i64::from(super::cell_width(text)?)
            } else {
                advance_sum(text, self.groups[group].weight)?
            };
            runs.push(StyledRun {
                text,
                bold: self.scales[token].bold,
                italic: self.scales[token].italic,
                width: i32::try_from(self.groups[group].width(units)?)
                    .map_err(|_| GeomError::Overflow)?,
                math: None,
            });
        }
        let text: String = runs.iter().map(|run| run.text).collect();
        Ok(StyledLine {
            runs,
            text,
            width: self.span_width(from, end)?,
            source: Span {
                start: self.source_start(start),
                end: self.source_end(stop),
            },
        })
    }
}

/// One wrapped line: the plain line of `measure::wrap`, or a styled line of
/// a label.
pub(crate) enum WrappedLine<'a> {
    Plain(Line<'a>),
    Styled(StyledLine<'a>),
}

pub(super) struct Wrapper<'clusters, 'widths> {
    clusters: Vec<Cluster<'clusters>>,
    widths: Widths<'widths>,
}
impl<'clusters, 'widths> Wrapper<'clusters, 'widths> {
    fn metric(text: &'widths str, metric: Metric) -> Result<Wrapper<'widths, 'widths>, GeomError> {
        let clusters = segment(text);
        let mut offsets = vec![0];
        let mut prefix = vec![0i64];
        let mut offset = 0usize;
        let mut sum = 0i64;
        for cluster in &clusters {
            offset += cluster.text.len();
            sum = sum
                .checked_add(metric.unit_width(cluster)?)
                .ok_or(GeomError::Overflow)?;
            offsets.push(offset);
            prefix.push(sum);
        }
        Ok(Wrapper {
            clusters,
            widths: Widths::Metric {
                metric,
                text,
                offsets,
                prefix,
            },
        })
    }
    pub(super) fn styled(clusters: Vec<Cluster<'clusters>>, widths: StyledWidths<'widths>) -> Self {
        Self {
            clusters,
            widths: Widths::Styled(widths),
        }
    }
    fn width(&self, from: usize, to: usize) -> Result<i32, GeomError> {
        match &self.widths {
            Widths::Metric { metric, prefix, .. } => {
                metric.width_from_units(prefix[to] - prefix[from])
            }
            Widths::Styled(styled) => styled.span_width(from, to),
        }
    }
    fn line(
        &self,
        from: usize,
        end: usize,
        next: usize,
    ) -> Result<WrappedLine<'widths>, GeomError> {
        match &self.widths {
            Widths::Metric { text, offsets, .. } => Ok(WrappedLine::Plain(Line {
                text: &text[offsets[from]..offsets[end]],
                separator: &text[offsets[end]..offsets[next]],
                width: self.width(from, end)?,
            })),
            Widths::Styled(styled) => Ok(WrappedLine::Styled(styled.line(from, end)?)),
        }
    }
    fn end(&self, start: usize, target: i32) -> Result<usize, GeomError> {
        let mut lo = start + 1;
        let mut hi = self.clusters.len();
        if self.width(start, lo)? > target {
            return Ok(lo);
        }
        while lo < hi {
            let mid = lo + (hi - lo).div_ceil(2);
            if self.width(start, mid)? <= target {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        Ok(lo)
    }
    fn opportunities(&self) -> Vec<(usize, usize)> {
        let mut result = Vec::new();
        for i in 1..self.clusters.len() {
            if self.clusters[i].is_space() {
                if !self.clusters[i - 1].is_space() {
                    let end = self.clusters[i..]
                        .iter()
                        .take_while(|c| c.is_space())
                        .count()
                        + i;
                    if end < self.clusters.len() {
                        result.push((i, end));
                    }
                }
            } else if boundary(self.clusters[i - 1], self.clusters[i]) {
                result.push((i, i));
            }
        }
        result
    }
    pub(super) fn run(&self, target: i32) -> Result<Vec<WrappedLine<'widths>>, GeomError> {
        let mut lines = Vec::new();
        let mut start = 0;
        let n = self.clusters.len();
        let opportunities = self.opportunities();
        for _ in 0..n {
            if start == n {
                break;
            }
            let end = self.end(start, target)?;
            let (end, next) = self.choose(&opportunities, start, end);
            lines.push(self.line(start, end, next)?);
            start = next;
        }
        Ok(lines)
    }
    fn choose(&self, opportunities: &[(usize, usize)], start: usize, end: usize) -> (usize, usize) {
        if end == self.clusters.len() {
            let mut last = end;
            while last > start && self.clusters[last - 1].is_space() {
                last -= 1;
            }
            return (if last > start { last } else { end }, end);
        }
        opportunities
            .iter()
            .rev()
            .find(|(at, _)| start < *at && *at <= end)
            .copied()
            .unwrap_or((end, end))
    }
}
fn forced(text: &str) -> Option<(usize, usize)> {
    text.as_bytes().windows(4).enumerate().find_map(|(i, _)| {
        ["<br>", "<br/>", "<br />"]
            .iter()
            .find(|tag| {
                text.get(i..i + tag.len())
                    .is_some_and(|s| s.eq_ignore_ascii_case(tag))
            })
            .map(|tag| (i, tag.len()))
    })
}
fn wrap_all(text: &str, target: i32, metric: Metric) -> Result<Vec<WrappedLine<'_>>, GeomError> {
    let mut lines = Vec::new();
    let mut rest = text;
    while let Some((at, len)) = forced(rest) {
        let mut part = Wrapper::metric(&rest[..at], metric)?.run(target)?;
        match part.last_mut() {
            Some(WrappedLine::Plain(last)) => {
                let sep_start = at - last.separator.len();
                last.separator = &rest[sep_start..at + len];
            }
            _ => part.push(WrappedLine::Plain(Line {
                text: "",
                separator: &rest[..len],
                width: 0,
            })),
        }
        lines.extend(part);
        rest = &rest[at + len..];
    }
    lines.extend(Wrapper::metric(rest, metric)?.run(target)?);
    Ok(lines)
}
pub fn wrap(text: &str, target: i32, metric: Metric) -> Result<Vec<Line<'_>>, GeomError> {
    let mut lines = Vec::new();
    for wrapped in wrap_all(text, target, metric)? {
        if let WrappedLine::Plain(line) = wrapped {
            lines.push(line);
        }
    }
    Ok(lines)
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn measure_wrap_parity_values() -> Result<(), GeomError> {
        let lines = wrap("alpha beta-gamma 日本語テキスト", 8, Metric::Cell)?;
        let got: Vec<_> = lines
            .iter()
            .map(|l| (l.text, l.separator, l.width))
            .collect();
        assert_eq!(
            got,
            vec![
                ("alpha", " ", 5),
                ("beta-", "", 5),
                ("gamma 日", "", 8),
                ("本", "", 2),
                ("語テキス", "", 8),
                ("ト", "", 2)
            ]
        );
        Ok(())
    }
    #[test]
    fn measure_wrap_properties() -> Result<(), GeomError> {
        let alphabet = [
            'a', 'b', ' ', '-', '日', '本', '語', '\u{301}', '👨', '\u{200d}', '👩', '🇦', '🇧',
            '\r', '\n',
        ];
        for case in 1..=2000u32 {
            let mut state = case;
            let mut draw = || {
                state ^= state << 13;
                state ^= state >> 17;
                state ^= state << 5;
                state
            };
            let mut text = String::new();
            for _ in 0..draw() % 40 {
                text.push(alphabet[usize::try_from(draw()).unwrap_or(0) % alphabet.len()]);
            }
            let target = i32::try_from(draw() % 12 + 1).unwrap_or(1);
            let lines = wrap(&text, target, Metric::Cell)?;
            let joined: String = lines.iter().flat_map(|l| [l.text, l.separator]).collect();
            assert_eq!(joined, text);
            let clusters = segment(&text);
            let mut boundaries = vec![0];
            for c in clusters {
                boundaries.push(boundaries.last().copied().unwrap_or(0) + c.text.len());
            }
            let mut offset = 0;
            for line in lines {
                assert!(
                    boundaries.contains(&offset),
                    "measure wrap properties: contract boundaries.contains(&offset) failed; observed offset={:?}, boundaries={:?}",
                    offset,
                    boundaries
                );
                offset += line.text.len();
                assert!(
                    boundaries.contains(&offset),
                    "measure wrap properties: contract boundaries.contains(&offset) failed; observed offset={:?}, boundaries={:?}",
                    offset,
                    boundaries
                );
                assert!(
                    line.width <= target || segment(line.text).len() == 1,
                    "measure wrap properties: contract line.width <= target || segment(line.text).len() == 1 failed; observed text={:?}, target={:?}",
                    text,
                    target
                );
                offset += line.separator.len();
                assert!(
                    boundaries.contains(&offset),
                    "measure wrap properties: contract boundaries.contains(&offset) failed; observed offset={:?}, boundaries={:?}",
                    offset,
                    boundaries
                );
            }
        }
        Ok(())
    }
}
