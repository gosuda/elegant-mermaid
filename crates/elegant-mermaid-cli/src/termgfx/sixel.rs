use super::{ESC, GfxError, ST, write_decimal};

pub const REGISTERS: usize = 216;

pub fn encode(rgba: &[u8], width: i32, height: i32, out: &mut Vec<u8>) -> Result<(), GfxError> {
    let Ok(columns) = u32::try_from(width) else {
        return Err(GfxError::Buffer);
    };
    let Ok(rows) = u32::try_from(height) else {
        return Err(GfxError::Buffer);
    };
    if !buffer_matches(rgba, columns, rows) {
        return Err(GfxError::Buffer);
    }
    write_header(out, columns, rows);
    write_palette(out);
    write_bands(out, rgba, columns, rows);
    out.extend_from_slice(&ST);
    Ok(())
}

fn buffer_matches(rgba: &[u8], columns: u32, rows: u32) -> bool {
    u64::from(columns)
        .checked_mul(u64::from(rows))
        .and_then(|pixels| pixels.checked_mul(4))
        .and_then(|bytes| usize::try_from(bytes).ok())
        .is_some_and(|bytes| rgba.len() >= bytes)
}

fn write_header(out: &mut Vec<u8>, columns: u32, rows: u32) {
    out.extend_from_slice(&[ESC, b'P']);
    out.extend_from_slice(b"7;0;0q\"1;1;");
    write_decimal(out, columns);
    out.push(b';');
    write_decimal(out, rows);
}

fn write_palette(out: &mut Vec<u8>) {
    for register in 0..REGISTERS {
        let index = u32::try_from(register).unwrap_or(0);
        out.push(b'#');
        write_decimal(out, index);
        out.extend_from_slice(b";2;");
        write_decimal(out, 20 * (index / 36));
        out.push(b';');
        write_decimal(out, 20 * ((index / 6) % 6));
        out.push(b';');
        write_decimal(out, 20 * (index % 6));
    }
}

fn write_bands(out: &mut Vec<u8>, rgba: &[u8], columns: u32, rows: u32) {
    let bands = rows.div_ceil(6).max(1);
    for band in 0..bands {
        let masks = band_masks(rgba, columns, rows, band);
        write_band(out, &masks, band + 1 < bands);
    }
}

fn write_band(out: &mut Vec<u8>, masks: &[[u8; REGISTERS]], more_bands: bool) {
    let used: Vec<usize> = (0..REGISTERS)
        .filter(|register| masks.iter().any(|mask| mask[*register] != 0))
        .collect();
    let last = used.len().saturating_sub(1);
    for (position, register) in used.iter().enumerate() {
        out.push(b'#');
        write_decimal(out, u32::try_from(*register).unwrap_or(0));
        let chars: Vec<u8> = masks.iter().map(|mask| 63 + mask[*register]).collect();
        write_run_length(out, &chars);
        if position < last {
            out.push(b'$');
        }
    }
    if !used.is_empty() && more_bands {
        out.push(b'-');
    }
}

fn band_masks(rgba: &[u8], columns: u32, rows: u32, band: u32) -> Vec<[u8; REGISTERS]> {
    (0..columns)
        .map(|column| column_mask(rgba, columns, rows, band, column))
        .collect()
}

fn column_mask(rgba: &[u8], columns: u32, rows: u32, band: u32, column: u32) -> [u8; REGISTERS] {
    let mut mask = [0u8; REGISTERS];
    for line in 0..6u32 {
        let Some(register) = register_at(rgba, columns, rows, column, 6 * band + line) else {
            continue;
        };
        if let Some(slot) = mask.get_mut(register) {
            *slot |= 1u8 << line;
        }
    }
    mask
}

fn register_at(rgba: &[u8], columns: u32, rows: u32, column: u32, line: u32) -> Option<usize> {
    let pixel = pixel_index(columns, rows, column, line)?;
    let channels = rgba.get(pixel..pixel + 3)?;
    Some(register(
        *channels.first()?,
        *channels.get(1)?,
        *channels.get(2)?,
    ))
}

fn pixel_index(columns: u32, rows: u32, column: u32, line: u32) -> Option<usize> {
    if column >= columns || line >= rows {
        return None;
    }
    let index = (u64::from(line) * u64::from(columns) + u64::from(column)) * 4;
    usize::try_from(index).ok()
}

pub fn register(r: u8, g: u8, b: u8) -> usize {
    36 * level(r) + 6 * level(g) + level(b)
}

fn level(value: u8) -> usize {
    (usize::from(value) * 5 + 127) / 255
}

fn write_run_length(out: &mut Vec<u8>, chars: &[u8]) {
    let mut index = 0;
    while let Some(&first) = chars.get(index) {
        let run = chars[index..].iter().take_while(|c| **c == first).count();
        match run >= 4 {
            true => {
                out.push(b'!');
                write_decimal(out, u32::try_from(run).unwrap_or(u32::MAX));
                out.push(first);
            }
            false => out.extend(std::iter::repeat_n(first, run)),
        }
        index += run;
    }
}

#[cfg(test)]
mod tests {
    use super::{REGISTERS, encode};

    fn naive_register(r: u8, g: u8, b: u8) -> usize {
        let q = |v: u8| (usize::from(v) * 5 + 127) / 255;
        36 * q(r) + 6 * q(g) + q(b)
    }

    fn naive_palette(out: &mut Vec<u8>) {
        for n in 0..216usize {
            out.push(b'#');
            out.extend_from_slice(n.to_string().as_bytes());
            out.extend_from_slice(
                format!(
                    ";2;{};{};{}",
                    20 * (n / 36),
                    20 * ((n / 6) % 6),
                    20 * (n % 6)
                )
                .as_bytes(),
            );
        }
    }

    fn naive_column(rgba: &[u8], width: usize, height: usize, band: usize, x: usize) -> [u8; 216] {
        let mut mask = [0u8; 216];
        for row in 0..6usize {
            let y = band * 6 + row;
            if y >= height {
                continue;
            }
            let base = (y * width + x) * 4;
            let register = naive_register(rgba[base], rgba[base + 1], rgba[base + 2]);
            mask[register] |= 1u8 << row;
        }
        mask
    }

    fn naive_runs(out: &mut Vec<u8>, chars: &[u8]) {
        let mut i = 0;
        while i < chars.len() {
            let mut j = i;
            while j < chars.len() && chars[j] == chars[i] {
                j += 1;
            }
            match j - i >= 4 {
                true => {
                    out.push(b'!');
                    out.extend_from_slice((j - i).to_string().as_bytes());
                    out.push(chars[i]);
                }
                false => out.extend_from_slice(&chars[i..j]),
            }
            i = j;
        }
    }

    fn naive_band(out: &mut Vec<u8>, masks: &[[u8; 216]], more: bool) {
        let used: Vec<usize> = (0..216)
            .filter(|n| masks.iter().any(|m| m[*n] != 0))
            .collect();
        for (position, n) in used.iter().enumerate() {
            out.push(b'#');
            out.extend_from_slice(n.to_string().as_bytes());
            let chars: Vec<u8> = masks.iter().map(|m| 63 + m[*n]).collect();
            naive_runs(out, &chars);
            if position + 1 < used.len() {
                out.push(b'$');
            }
        }
        if !used.is_empty() && more {
            out.push(b'-');
        }
    }

    fn naive(rgba: &[u8], width: usize, height: usize) -> Vec<u8> {
        let mut out = b"\x1bP7;0;0q\"1;1;".to_vec();
        out.extend_from_slice(format!("{width};{height}").as_bytes());
        naive_palette(&mut out);
        let bands = height.div_ceil(6);
        for band in 0..bands {
            let masks: Vec<[u8; 216]> = (0..width)
                .map(|x| naive_column(rgba, width, height, band, x))
                .collect();
            naive_band(&mut out, &masks, band + 1 < bands);
        }
        out.extend_from_slice(b"\x1b\\");
        out
    }

    fn paint(width: usize, height: usize, regions: &[(usize, usize, usize, usize, u8)]) -> Vec<u8> {
        let mut rgba = Vec::with_capacity(width * height * 4);
        for y in 0..height {
            for x in 0..width {
                let tone = regions
                    .iter()
                    .find(|(x0, y0, x1, y1, _)| x >= *x0 && y >= *y0 && x < *x1 && y < *y1)
                    .map(|(_, _, _, _, tone)| *tone)
                    .unwrap_or(0);
                rgba.extend_from_slice(&[tone, tone / 2, 255 - tone, 255]);
            }
        }
        rgba
    }

    fn scale(value: usize) -> i32 {
        i32::try_from(value).unwrap_or(i32::MAX)
    }

    fn render(rgba: &[u8], width: i32, height: i32) -> Vec<u8> {
        let mut out = Vec::new();
        assert!(
            encode(rgba, width, height, &mut out).is_ok(),
            "render: expected {} to hold (observed false)",
            stringify!(encode(rgba, width, height, &mut out).is_ok())
        );
        out
    }

    #[test]
    fn two_by_two_buffer_matches_naive_reference() {
        let rgba = [
            255u8, 0, 0, 255, 0, 255, 0, 255, 0, 0, 255, 255, 255, 255, 255, 255,
        ];
        assert_eq!(render(&rgba, 2, 2), naive(&rgba, 2, 2));
    }

    #[test]
    fn seven_by_thirteen_buffer_matches_naive_reference() {
        let rgba = paint(
            7,
            13,
            &[
                (0, 0, 7, 6, 10),
                (0, 6, 3, 12, 90),
                (3, 6, 4, 9, 200),
                (4, 9, 7, 13, 255),
            ],
        );
        assert_eq!(render(&rgba, 7, 13), naive(&rgba, 7, 13));
    }

    #[test]
    fn every_naive_example_matches_for_its_own_dimensions() {
        for (width, height) in [(1usize, 1usize), (4, 6), (4, 7), (5, 12), (9, 14), (13, 2)] {
            let rgba = paint(
                width,
                height,
                &[(1, 1, 3, 4, 255), (0, 0, width, height, 60)],
            );
            assert_eq!(
                render(&rgba, scale(width), scale(height)),
                naive(&rgba, width, height),
                "{width}x{height}"
            );
        }
    }

    #[test]
    fn run_of_three_repeats_and_run_of_four_compresses() {
        for (width, expected) in [(3usize, "#215~~~"), (4, "#215!4~")] {
            let rgba = vec![255u8; width * 6 * 4];
            let text = String::from_utf8_lossy(&render(&rgba, scale(width), 6)).into_owned();
            assert!(
                text.contains(expected),
                "width {width}: tail {:?}",
                &text[text.len() - 20..]
            );
        }
    }

    #[test]
    fn separators_and_terminator_follow_the_band_rules() {
        let rgba = paint(3, 7, &[(0, 0, 3, 3, 255), (0, 3, 3, 7, 20)]);
        let ours = render(&rgba, 3, 7);
        let text = String::from_utf8_lossy(&ours).into_owned();
        assert!(
            text.starts_with("\x1bP7;0;0q\"1;1;3;7"),
            "separators_and_terminator_follow_the_band_rules: expected {} to hold (observed false)",
            stringify!(text.starts_with("\x1bP7;0;0q\"1;1;3;7"))
        );
        assert!(
            text.ends_with("\x1b\\"),
            "separators_and_terminator_follow_the_band_rules: expected {} to hold (observed false)",
            stringify!(text.ends_with("\x1b\\"))
        );
        assert_eq!(ours, naive(&rgba, 3, 7));
        let data = text
            .split_once("\"1;1;3;7")
            .map(|(_, rest)| rest)
            .unwrap_or("");
        assert_eq!(
            data.matches('$').count(),
            1,
            "two registers share the first band"
        );
        assert_eq!(
            data.matches('-').count(),
            1,
            "the first band ends with a dash"
        );
        let single_band = render(&paint(1, 1, &[]), 1, 1);
        let flat = String::from_utf8_lossy(&single_band).into_owned();
        assert_eq!(flat.matches('$').count(), 0);
        assert_eq!(flat.matches('-').count(), 0);
    }

    #[test]
    fn money_bands_separated_by_dash_and_registers_by_dollar() {
        let mut pixels = Vec::new();
        for y in 0..12usize {
            for x in 0..3usize {
                let tone = if (x + y) % 2 == 0 { 255 } else { 0 };
                pixels.extend_from_slice(&[tone, tone, tone, 255]);
            }
        }
        let text = String::from_utf8_lossy(&render(&pixels, 3, 12)).into_owned();
        assert_eq!(text.matches('-').count(), 1);
        assert_eq!(text.matches('$').count(), 2);
    }

    #[test]
    fn short_buffer_and_bad_dimensions_are_rejected_before_any_byte() {
        let mut out = Vec::new();
        assert!(
            encode(&[0u8; 15], 2, 2, &mut out).is_err(),
            "short_buffer_and_bad_dimensions_are_rejected_before_any_byte: expected {} to hold (observed false)",
            stringify!(encode(&[0u8; 15], 2, 2, &mut out).is_err())
        );
        assert!(
            encode(&[0u8; 16], -1, 4, &mut out).is_err(),
            "short_buffer_and_bad_dimensions_are_rejected_before_any_byte: expected {} to hold (observed false)",
            stringify!(encode(&[0u8; 16], -1, 4, &mut out).is_err())
        );
        assert!(
            encode(&[0u8; 16], 4, -1, &mut out).is_err(),
            "short_buffer_and_bad_dimensions_are_rejected_before_any_byte: expected {} to hold (observed false)",
            stringify!(encode(&[0u8; 16], 4, -1, &mut out).is_err())
        );
        assert!(
            out.is_empty(),
            "short_buffer_and_bad_dimensions_are_rejected_before_any_byte: expected {} to hold (observed false)",
            stringify!(out.is_empty())
        );
        assert!(
            encode(&[0u8; 16], 0, 2, &mut out).is_ok(),
            "short_buffer_and_bad_dimensions_are_rejected_before_any_byte: expected {} to hold (observed false)",
            stringify!(encode(&[0u8; 16], 0, 2, &mut out).is_ok())
        );
        assert!(
            !out.is_empty(),
            "short_buffer_and_bad_dimensions_are_rejected_before_any_byte: expected {} to hold (observed false)",
            stringify!(!out.is_empty())
        );
    }

    #[test]
    fn alpha_is_ignored_and_registers_span_the_cube() {
        let mut out = Vec::new();
        let rgba = [200u8, 10, 40, 0, 200, 10, 40, 128];
        assert!(
            encode(&rgba, 2, 1, &mut out).is_ok(),
            "alpha_is_ignored_and_registers_span_the_cube: expected {} to hold (observed false)",
            stringify!(encode(&rgba, 2, 1, &mut out).is_ok())
        );
        let text = String::from_utf8_lossy(&out).into_owned();
        let register = naive_register(200, 10, 40);
        assert!(
            text.contains(&format!("#{register}")),
            "alpha_is_ignored_and_registers_span_the_cube: expected {} to hold (observed false)",
            stringify!(text.contains(&format!("#{register}")))
        );
        assert_eq!(REGISTERS, 216);
    }
}
