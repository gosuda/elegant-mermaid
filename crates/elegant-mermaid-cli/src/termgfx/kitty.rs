use super::{ESC, ST};

const CHUNK: usize = 4096;
const DELETE: &[u8] = b"\x1b_Ga=d,d=A,q=2\x1b\\";

pub fn encode(png: &[u8], out: &mut Vec<u8>) {
    out.extend_from_slice(DELETE);
    encode_chunks(&encode_payload(png), out);
}

pub fn encode_payload(png: &[u8]) -> String {
    base64::engine::Engine::encode(&base64::engine::general_purpose::STANDARD, png)
}

pub fn encode_chunks(payload: &str, out: &mut Vec<u8>) {
    let bytes = payload.as_bytes();
    let count = bytes.len().div_ceil(CHUNK).max(1);
    for index in 0..count {
        let start = index * CHUNK;
        let stop = usize::min(start + CHUNK, bytes.len());
        out.extend_from_slice(&[ESC, b'_', b'G']);
        if index == 0 {
            out.extend_from_slice(b"a=T,f=100,i=1,q=2,");
        }
        out.extend_from_slice(b"m=");
        out.push(if index + 1 < count { b'1' } else { b'0' });
        out.push(b';');
        out.extend_from_slice(bytes.get(start..stop).unwrap_or(&[]));
        out.extend_from_slice(&ST);
    }
}

#[cfg(test)]
mod tests {
    use super::{encode, encode_chunks, encode_payload};

    fn naive_chunks(payload: &str) -> Vec<u8> {
        let bytes = payload.as_bytes();
        let count = bytes.len().div_ceil(4096).max(1);
        let mut out = Vec::new();
        for index in 0..count {
            let start = index * 4096;
            let stop = usize::min(start + 4096, bytes.len());
            out.extend_from_slice(b"\x1b_G");
            if index == 0 {
                out.extend_from_slice(b"a=T,f=100,i=1,q=2,");
            }
            out.extend_from_slice(b"m=");
            out.push(if index + 1 < count { b'1' } else { b'0' });
            out.push(b';');
            out.extend_from_slice(&bytes[start..stop]);
            out.extend_from_slice(b"\x1b\\");
        }
        out
    }

    #[test]
    fn chunking_matches_naive_reference_at_every_boundary() {
        for length in [0usize, 1, 4095, 4096, 4097, 8191, 8192, 8193, 12_289] {
            let payload = "A".repeat(length);
            let mut out = Vec::new();
            encode_chunks(&payload, &mut out);
            let expected = naive_chunks(&payload);
            assert_eq!(out, expected, "payload of {length} characters");
            let chunks = length.div_ceil(4096).max(1);
            let text = String::from_utf8_lossy(&out).into_owned();
            assert_eq!(text.matches("a=T,f=100,i=1,q=2,m=").count(), 1, "{length}");
            assert_eq!(text.matches("m=1;").count(), chunks - 1, "{length}");
            assert_eq!(text.matches("m=0;").count(), 1, "{length}");
        }
    }

    #[test]
    fn payload_is_standard_base64_with_padding() {
        assert_eq!(encode_payload(&[0, 1, 2]), "AAEC");
        assert_eq!(encode_payload(&[0]), "AA==");
        assert_eq!(encode_payload(&[0, 0]), "AAA=");
        assert_eq!(encode_payload(&[]), "");
        assert_eq!(encode_payload(b"hi"), "aGk=");
    }

    #[test]
    fn encode_deletes_previous_images_then_transmits_one_chunk() {
        let mut out = Vec::new();
        encode(&[0, 1, 2], &mut out);
        let mut expected = b"\x1b_Ga=d,d=A,q=2\x1b\\".to_vec();
        expected.extend_from_slice(b"\x1b_Ga=T,f=100,i=1,q=2,m=0;AAEC\x1b\\");
        assert_eq!(out, expected);
    }

    #[test]
    fn encode_of_a_large_png_splits_into_numbered_chunks() {
        let png = vec![0x5Au8; 3072];
        let mut out = Vec::new();
        encode(&png, &mut out);
        let payload = encode_payload(&png);
        assert_eq!(payload.len(), 4096);
        let mut expected = b"\x1b_Ga=d,d=A,q=2\x1b\\".to_vec();
        expected.extend_from_slice(&naive_chunks(&payload));
        assert_eq!(out, expected);
    }
}
