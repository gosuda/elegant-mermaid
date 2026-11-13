use base64::Engine;

use super::{BEL, ESC, write_decimal};

pub fn encode(png: &[u8], width: u32, height: u32, out: &mut Vec<u8>) {
    out.extend_from_slice(&[ESC, b']']);
    out.extend_from_slice(b"1337;File=inline=1;size=");
    write_decimal(out, u32::try_from(png.len()).unwrap_or(u32::MAX));
    out.extend_from_slice(b";width=");
    write_decimal(out, width);
    out.extend_from_slice(b"px;height=");
    write_decimal(out, height);
    out.extend_from_slice(b"px;preserveAspectRatio=0:");
    let payload = base64::engine::general_purpose::STANDARD.encode(png);
    out.extend_from_slice(payload.as_bytes());
    out.push(BEL);
}

#[cfg(test)]
mod tests {
    use super::encode;

    fn naive(png: &[u8], width: u32, height: u32) -> Vec<u8> {
        let alphabet = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let mut payload = Vec::new();
        for block in png.chunks(3) {
            let b0 = u32::from(*block.first().unwrap_or(&0));
            let b1 = u32::from(*block.get(1).unwrap_or(&0));
            let b2 = u32::from(*block.get(2).unwrap_or(&0));
            let triple = (b0 << 16) | (b1 << 8) | b2;
            payload.push(alphabet[usize::try_from((triple >> 18) & 63).unwrap_or(0)]);
            payload.push(alphabet[usize::try_from((triple >> 12) & 63).unwrap_or(0)]);
            if block.len() > 1 {
                payload.push(alphabet[usize::try_from((triple >> 6) & 63).unwrap_or(0)]);
            } else {
                payload.push(b'=');
            }
            if block.len() > 2 {
                payload.push(alphabet[usize::try_from(triple & 63).unwrap_or(0)]);
            } else {
                payload.push(b'=');
            }
        }
        let mut out = b"\x1b]1337;File=inline=1;size=".to_vec();
        out.extend_from_slice(png.len().to_string().as_bytes());
        out.extend_from_slice(b";width=");
        out.extend_from_slice(width.to_string().as_bytes());
        out.extend_from_slice(b"px;height=");
        out.extend_from_slice(height.to_string().as_bytes());
        out.extend_from_slice(b"px;preserveAspectRatio=0:");
        out.extend_from_slice(&payload);
        out.push(0x07);
        out
    }

    #[test]
    fn three_byte_payload_bytes() {
        let mut out = Vec::new();
        encode(&[0, 1, 2], 10, 7, &mut out);
        assert_eq!(
            out,
            b"\x1b]1337;File=inline=1;size=3;width=10px;height=7px;preserveAspectRatio=0:AAEC\x07"
        );
    }

    #[test]
    fn payloads_of_every_remaining_length_match_the_naive_reference() {
        for (png, width, height) in [
            (vec![], 0u32, 0u32),
            (vec![0x00], 1, 1),
            (vec![0xFF, 0x10], 3, 5),
            (vec![0x12, 0x34, 0x56, 0x78], 640, 480),
            (vec![0xA5; 1000], 1200, 901),
        ] {
            let mut out = Vec::new();
            encode(&png, width, height, &mut out);
            assert_eq!(out, naive(&png, width, height), "{} bytes", png.len());
        }
    }

    #[test]
    fn output_is_one_sequence_on_one_line() {
        let mut out = Vec::new();
        encode(&[0u8; 900], 64, 32, &mut out);
        assert_eq!(out.iter().filter(|b| **b == 0x07).count(), 1);
        assert!(
            !out.contains(&b'\n'),
            "output_is_one_sequence_on_one_line: expected {} to hold (observed false)",
            stringify!(!out.contains(&b'\n'))
        );
        assert!(
            out.starts_with(b"\x1b]1337;File="),
            "output_is_one_sequence_on_one_line: expected {} to hold (observed false)",
            stringify!(out.starts_with(b"\x1b]1337;File="))
        );
        assert!(
            out.ends_with(&[0x07]),
            "output_is_one_sequence_on_one_line: expected {} to hold (observed false)",
            stringify!(out.ends_with(&[0x07]))
        );
    }
}
