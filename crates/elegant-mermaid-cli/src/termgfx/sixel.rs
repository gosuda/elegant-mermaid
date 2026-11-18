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
#[path = "sixel_tests.rs"]
mod tests;
