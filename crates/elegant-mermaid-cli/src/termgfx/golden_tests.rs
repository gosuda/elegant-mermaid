use std::path::{Path, PathBuf};

use tiny_skia::Pixmap;

use super::{iterm, kitty, sixel};

struct Image {
    width: u32,
    height: u32,
    rgba: Vec<u8>,
}

fn decode(png: &[u8]) -> Result<Image, String> {
    let pixmap = Pixmap::decode_png(png).map_err(|e| e.to_string())?;
    Ok(Image {
        width: pixmap.width(),
        height: pixmap.height(),
        rgba: pixmap.data().to_vec(),
    })
}

const FIXTURES: [&str; 3] = ["tiny", "tall", "wide"];

struct Encoder {
    extension: &'static str,
    encode: fn(&[u8], &Image) -> Result<Vec<u8>, String>,
}

const ENCODERS: [Encoder; 3] = [
    Encoder {
        extension: "kitty",
        encode: encode_kitty,
    },
    Encoder {
        extension: "iterm",
        encode: encode_iterm,
    },
    Encoder {
        extension: "sixel",
        encode: encode_sixel,
    },
];

fn encode_kitty(png: &[u8], _: &Image) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    kitty::encode(png, &mut out);
    Ok(out)
}

fn encode_iterm(png: &[u8], image: &Image) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    iterm::encode(png, image.width, image.height, &mut out);
    Ok(out)
}

fn encode_sixel(_: &[u8], image: &Image) -> Result<Vec<u8>, String> {
    let width = i32::try_from(image.width).map_err(|e| e.to_string())?;
    let height = i32::try_from(image.height).map_err(|e| e.to_string())?;
    let mut out = Vec::new();
    sixel::encode(&image.rgba, width, height, &mut out).map_err(|e| e.to_string())?;
    Ok(out)
}

fn golden_path(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/termgfx")
        .join(name)
}

fn read_golden(name: &str) -> Result<Vec<u8>, String> {
    std::fs::read(golden_path(name)).map_err(|e| format!("{name}: {e}"))
}

fn first_difference(got: &[u8], want: &[u8]) -> String {
    let offset = got.iter().zip(want).take_while(|(a, b)| a == b).count();
    let from = offset.saturating_sub(16);
    let excerpt = |bytes: &[u8]| {
        let stop = usize::min(offset + 16, bytes.len());
        String::from_utf8_lossy(bytes.get(from..stop).unwrap_or(&[])).into_owned()
    };
    format!(
        "got {} bytes, want {} bytes, first difference at offset {offset}\n got ...{:?}\nwant ...{:?}",
        got.len(),
        want.len(),
        excerpt(got),
        excerpt(want),
    )
}

fn check(fixture: &str, encoder: &Encoder, png: &[u8], image: &Image) -> Result<(), String> {
    let got = (encoder.encode)(png, image)?;
    let want = read_golden(&format!("{fixture}.{}", encoder.extension))?;
    if got == want {
        return Ok(());
    }
    Err(first_difference(&got, &want))
}

fn failures(fixture: &str) -> Vec<String> {
    let loaded = read_golden(&format!("{fixture}.png")).and_then(|png| {
        let image = decode(&png)?;
        Ok((png, image))
    });
    let (png, image) = match loaded {
        Ok(pair) => pair,
        Err(message) => return vec![format!("{fixture}.png: {message}")],
    };
    ENCODERS
        .iter()
        .filter_map(|encoder| {
            check(fixture, encoder, &png, &image)
                .err()
                .map(|message| format!("{fixture}.{}: {message}", encoder.extension))
        })
        .collect()
}

#[test]
fn encoder_golden() {
    let failed: Vec<String> = FIXTURES.iter().flat_map(|name| failures(name)).collect();
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

fn contains(bytes: &[u8], marker: &[u8]) -> bool {
    bytes.windows(marker.len()).any(|window| window == marker)
}

#[test]
fn encoder_golden_exercises_every_byte_rule() {
    let rules: [(&str, &str, &[u8]); 9] = [
        (
            "kitty",
            "delete before transmit",
            b"\x1b_Ga=d,d=A,q=2\x1b\\\x1b_Ga=T,f=100,i=1,q=2,m=",
        ),
        ("kitty", "continuation chunk", b"\x1b_Gm=0;"),
        (
            "iterm",
            "inline file header",
            b"\x1b]1337;File=inline=1;size=",
        ),
        ("iterm", "bell terminator", b"\x07"),
        ("sixel", "raster attributes", b"\x1bP7;0;0q\"1;1;"),
        ("sixel", "repeat introducer", b"!"),
        ("sixel", "register separator", b"$#"),
        ("sixel", "band separator", b"-#"),
        ("sixel", "string terminator", b"\x1b\\"),
    ];
    for (extension, name, marker) in rules {
        let present = FIXTURES.iter().any(|fixture| {
            read_golden(&format!("{fixture}.{extension}"))
                .is_ok_and(|bytes| contains(&bytes, marker))
        });
        assert!(present, "no {extension} golden exercises {name}");
    }
}

#[test]
fn sixel_quantisation_boundaries() {
    let boundaries: [(u8, usize); 12] = [
        (0, 0),
        (25, 0),
        (26, 1),
        (76, 1),
        (77, 2),
        (127, 2),
        (128, 3),
        (178, 3),
        (179, 4),
        (229, 4),
        (230, 5),
        (255, 5),
    ];
    for (value, level) in boundaries {
        let mut out = Vec::new();
        assert!(sixel::encode(&[value, 0, 0, 255], 1, 1, &mut out).is_ok());
        let want = format!("#{}@\x1b\\", 36 * level);
        assert!(
            out.ends_with(want.as_bytes()),
            "red {value}: tail {:?}, want register {} and {want:?}",
            &out[out.len() - 12..],
            36 * level,
        );
    }
}
