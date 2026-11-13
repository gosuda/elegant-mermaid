pub mod class;
pub mod config_value;
pub mod detect;
pub mod flowchart;
pub mod preprocess;
pub mod state;

pub(crate) fn eol_len(b: &[u8], i: usize) -> usize {
    match b.get(i) {
        Some(b'\n') => 1,
        Some(b'\r') => {
            if b.get(i + 1) == Some(&b'\n') {
                2
            } else {
                1
            }
        }
        _ => 0,
    }
}

pub(crate) fn line_content_end(b: &[u8], from: usize, to: usize) -> usize {
    let mut j = from;
    while j < to {
        match b.get(j) {
            Some(b'\r') | Some(b'\n') => break,
            _ => j += 1,
        }
    }
    j
}

pub(crate) fn is_ws_byte(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\r' | b'\n')
}
