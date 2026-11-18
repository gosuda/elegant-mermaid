//! Integer Q40 squarify and shared-boundary strip placement.
use super::super::layered::LayoutError;
use crate::geom::{GeomError, floor_div};
#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Tile {
    pub x0: i64,
    pub y0: i64,
    pub x1: i64,
    pub y1: i64,
}
fn round_div(a: i64, b: i64) -> i64 {
    floor_div(2 * a + b, 2 * b)
}
fn aspect(largest: u128, smallest: u128, sum: u128, alpha: u128) -> Result<u128, LayoutError> {
    let beta = alpha.checked_mul(sum * sum).ok_or(GeomError::Overflow)?;
    if beta == 0 || smallest == 0 {
        return Err(GeomError::Domain);
    }
    Ok(((largest << 80) / beta).max(beta / smallest))
}
fn next_row(
    values: &[i64],
    first: usize,
    area: Tile,
    remaining: i64,
    rho: u64,
) -> Result<(usize, i64), LayoutError> {
    let mut end = first;
    let mut sum;
    loop {
        sum = values[end];
        end += 1;
        if sum != 0 || end == values.len() {
            break;
        }
    }
    if sum == 0 {
        return Ok((end, 0));
    }
    let dx = area.x1 - area.x0;
    let dy = area.y1 - area.y0;
    if dx.min(dy) == 0 {
        return Ok((values.len(), remaining));
    }
    let shorter = u128::try_from(dx.min(dy)).map_err(|_| GeomError::Domain)?;
    let total = u128::try_from(remaining).map_err(|_| GeomError::Domain)?;
    let denominator = shorter * total * u128::from(rho);
    if denominator == 0 {
        return Err(GeomError::Domain);
    }
    let longer = u128::try_from(dx.max(dy)).map_err(|_| GeomError::Domain)?;
    let alpha = (longer << 70) / denominator;
    let mut low = u128::try_from(sum).map_err(|_| GeomError::Domain)?;
    let mut high = low;
    let mut total = low;
    let mut best = aspect(high, low, total, alpha)?;
    while end < values.len() && values[end] != 0 {
        let v = u128::try_from(values[end]).map_err(|_| GeomError::Domain)?;
        let next = aspect(high.max(v), low.min(v), total + v, alpha)?;
        if next > best {
            break;
        }
        best = next;
        total += v;
        low = low.min(v);
        high = high.max(v);
        end += 1;
    }
    sum = i64::try_from(total).map_err(|_| GeomError::Overflow)?;
    Ok((end, sum))
}
pub(super) fn squarify(
    values: &[i64],
    mut area: Tile,
    rho: u64,
    fuel: usize,
) -> Result<(Vec<Tile>, bool), LayoutError> {
    let mut remaining = 0_i64;
    for &v in values {
        if v < 0 {
            return Err(GeomError::Domain);
        }
        remaining = remaining.checked_add(v).ok_or(GeomError::Overflow)?;
    }
    if remaining > 1 << 31 || rho == 0 || area.x1 < area.x0 || area.y1 < area.y0 {
        return Err(GeomError::Domain);
    }
    let mut cells = vec![Tile::default(); values.len()];
    let mut first = 0;
    let mut rows = 0;
    let mut capped = false;
    while first < values.len() {
        let (end, sum) = if rows < fuel {
            next_row(values, first, area, remaining, rho)?
        } else {
            capped = true;
            (values.len(), remaining)
        };
        area = place_row(
            &mut cells[first..end],
            &values[first..end],
            area,
            sum,
            remaining,
        );
        remaining -= sum;
        first = end;
        rows += 1;
    }
    Ok((cells, capped))
}
fn place_row(cells: &mut [Tile], values: &[i64], mut area: Tile, sum: i64, remaining: i64) -> Tile {
    let dx = area.x1 - area.x0;
    let dy = area.y1 - area.y0;
    let dice = dx < dy;
    let (along, across) = if dice { (dx, dy) } else { (dy, dx) };
    let thickness = if sum > 0 && remaining > 0 {
        round_div(across * sum, remaining)
    } else {
        across
    };
    let mut cumulative = 0;
    let mut previous = 0;
    for (cell, v) in cells.iter_mut().zip(values) {
        cumulative += v;
        let boundary = if sum > 0 {
            round_div(along * cumulative, sum)
        } else {
            0
        };
        *cell = if dice {
            Tile {
                x0: area.x0 + previous,
                y0: area.y0,
                x1: area.x0 + boundary,
                y1: area.y0 + thickness,
            }
        } else {
            Tile {
                x0: area.x0,
                y0: area.y0 + previous,
                x1: area.x0 + thickness,
                y1: area.y0 + boundary,
            }
        };
        previous = boundary;
    }
    if dice {
        area.y0 += thickness;
    } else {
        area.x0 += thickness;
    }
    area
}
pub fn normalize(raw: &[i64], bits: u32) -> Result<Vec<i64>, LayoutError> {
    let mut total = 0_i64;
    for &v in raw {
        if v < 0 {
            return Err(GeomError::Domain);
        }
        if v > 1_i64 << 43 {
            return Err(GeomError::Overflow);
        }
        total = total.checked_add(v).ok_or(GeomError::Overflow)?;
    }
    let budget = 1_i64.checked_shl(bits).ok_or(GeomError::Overflow)?;
    if total <= budget {
        return Ok(raw.to_vec());
    }
    let budget = u128::try_from(budget).map_err(|_| GeomError::Overflow)?;
    let total = u128::try_from(total).map_err(|_| GeomError::Domain)?;
    raw.iter()
        .map(|v| {
            let v = u128::try_from(*v).map_err(|_| GeomError::Domain)?;
            i64::try_from(v * budget / total).map_err(|_| GeomError::Overflow)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn treemap_squarify_partitions_area() -> Result<(), LayoutError> {
        for seed in 1..=200_u32 {
            let mut state = seed;
            let mut values = Vec::new();
            for _ in 0..12 {
                state ^= state << 13;
                state ^= state >> 17;
                state ^= state << 5;
                values.push(i64::from(state % 100 + 1));
            }
            let area = Tile {
                x0: 7,
                y0: 11,
                x1: 1007,
                y1: 611,
            };
            let (cells, capped) = squarify(&values, area, 1_737_350_766, 2000)?;
            assert!(!capped);
            assert_eq!(
                cells
                    .iter()
                    .map(|r| (r.x1 - r.x0) * (r.y1 - r.y0))
                    .sum::<i64>(),
                600_000
            );
            for (i, r) in cells.iter().enumerate() {
                assert!(area.x0 <= r.x0 && r.x0 <= r.x1 && r.x1 <= area.x1);
                assert!(area.y0 <= r.y0 && r.y0 <= r.y1 && r.y1 <= area.y1);
                for s in &cells[i + 1..] {
                    assert!(r.x0.max(s.x0) >= r.x1.min(s.x1) || r.y0.max(s.y0) >= r.y1.min(s.y1));
                }
            }
        }
        Ok(())
    }

    #[test]
    fn treemap_normalization_uses_wide_products() -> Result<(), LayoutError> {
        let raw = [1_i64 << 42, 1_i64 << 41, 1_i64 << 40];
        let normalized = normalize(&raw, 24)?;
        let total = raw.iter().sum::<i64>();
        for (n, v) in normalized.iter().zip(raw) {
            assert_eq!(
                i128::from(*n),
                i128::from(v) * (1_i128 << 24) / i128::from(total)
            );
        }
        assert!(normalized.iter().sum::<i64>() <= 1_i64 << 24);
        assert_eq!(normalize(&[-1], 24), Err(GeomError::Domain));
        assert_eq!(
            normalize(&[(1_i64 << 43) + 1], 24),
            Err(GeomError::Overflow)
        );
        Ok(())
    }
}
