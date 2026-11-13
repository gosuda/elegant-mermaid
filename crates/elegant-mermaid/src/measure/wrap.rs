use super::{Cluster, Metric, segment};
use crate::r#gen::ideographic::IDEOGRAPHIC;
use crate::geom::GeomError;

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
struct Wrapper<'a> {
    text: &'a str,
    clusters: Vec<Cluster<'a>>,
    offsets: Vec<usize>,
    prefix: Vec<i64>,
    metric: Metric,
}
impl<'a> Wrapper<'a> {
    fn new(text: &'a str, metric: Metric) -> Result<Self, GeomError> {
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
        Ok(Self {
            text,
            clusters,
            offsets,
            prefix,
            metric,
        })
    }
    fn width(&self, from: usize, to: usize) -> Result<i32, GeomError> {
        self.metric
            .width_from_units(self.prefix[to] - self.prefix[from])
    }
    fn line(&self, from: usize, end: usize, next: usize) -> Result<Line<'a>, GeomError> {
        Ok(Line {
            text: &self.text[self.offsets[from]..self.offsets[end]],
            separator: &self.text[self.offsets[end]..self.offsets[next]],
            width: self.width(from, end)?,
        })
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
    fn run(&self, target: i32) -> Result<Vec<Line<'a>>, GeomError> {
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
pub fn wrap(text: &str, target: i32, metric: Metric) -> Result<Vec<Line<'_>>, GeomError> {
    let mut lines = Vec::new();
    let mut rest = text;
    while let Some((at, len)) = forced(rest) {
        let mut part = Wrapper::new(&rest[..at], metric)?.run(target)?;
        if let Some(last) = part.last_mut() {
            let sep_start = at - last.separator.len();
            last.separator = &rest[sep_start..at + len];
        } else {
            part.push(Line {
                text: "",
                separator: &rest[..len],
                width: 0,
            });
        }
        lines.extend(part);
        rest = &rest[at + len..];
    }
    lines.extend(Wrapper::new(rest, metric)?.run(target)?);
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
