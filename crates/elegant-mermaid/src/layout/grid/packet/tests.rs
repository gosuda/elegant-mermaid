use super::{PacketInput, PacketParams, PacketPiece, packet};
use crate::geom::{self, GeomError, Rect, Size};

fn vector_params() -> PacketParams {
    PacketParams {
        bits_per_row: 32,
        bit_width: 2048,
        row_height: 2048,
        padding_x: 320,
        padding_y: 320,
        show_bits_pad: 1024,
        margin_x: 64,
        line_height: 1280,
        show_bits: true,
        descending: false,
    }
}

fn cell_params() -> PacketParams {
    PacketParams {
        bits_per_row: 32,
        bit_width: 2,
        row_height: 3,
        padding_x: 1,
        padding_y: 1,
        show_bits_pad: 0,
        margin_x: 0,
        line_height: 1,
        show_bits: true,
        descending: false,
    }
}

fn piece(start: i64, end: i64, lead: i32, trail: i32) -> PacketPiece {
    PacketPiece {
        start,
        end,
        lead: Size { w: lead, h: 1 },
        trail: Size { w: trail, h: 1 },
    }
}

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn input(pieces: Vec<PacketPiece>, has_title: bool) -> PacketInput {
    PacketInput { pieces, has_title }
}

#[test]
fn vector_geometry() {
    let out = packet(
        &input(
            vec![
                piece(0, 15, 500, 900),
                piece(16, 31, 900, 900),
                piece(32, 32, 500, 0),
            ],
            true,
        ),
        vector_params(),
    )
    .unwrap();
    assert_eq!(
        out.rects,
        vec![
            rect(64, 1344, 32448, 2048),
            rect(32832, 1344, 32448, 2048),
            rect(64, 4736, 1728, 2048),
        ]
    );
    assert_eq!(out.lead[0], rect(64, 64, 500, 1280));
    assert_eq!(out.trail[0], rect(64 + 32448 - 900, 64, 900, 1280));
    assert_eq!(out.lead[2], rect(64 + 864 - 250, 3456, 500, 1280));
    assert_eq!(out.trail[2], rect(0, 0, 0, 0));
    assert_eq!(out.title, rect(64, 2 * 3392 + 1344, 65536, 2048));
    assert_eq!(
        out.canvas,
        Size {
            w: 65664,
            h: 2 * 3392 + 1344 + 2048
        }
    );
    assert_eq!(out.rows, 2);
}

#[test]
fn cell_geometry() {
    let out = packet(
        &input(
            vec![piece(0, 3, 1, 1), piece(4, 4, 1, 0), piece(106, 106, 3, 0)],
            false,
        ),
        cell_params(),
    )
    .unwrap();
    assert_eq!(out.rects[0], rect(0, 1, 7, 3));
    assert_eq!(out.rects[1], rect(8, 1, 1, 3));
    assert_eq!(out.rects[2], rect(20, 13, 1, 3));
    assert_eq!(out.lead[0], rect(0, 0, 1, 1));
    assert_eq!(out.trail[0], rect(6, 0, 1, 1));
    assert_eq!(out.lead[2], rect(19, 12, 3, 1));
    assert_eq!(out.canvas, Size { w: 64, h: 17 });
    assert_eq!(out.rows, 4);
}

#[test]
fn descending_mirrors_the_row() {
    let mut params = vector_params();
    params.bits_per_row = 16;
    params.descending = true;
    let out = packet(
        &input(
            vec![
                piece(0, 7, 100, 100),
                piece(8, 11, 100, 100),
                piece(12, 12, 100, 0),
                piece(13, 15, 100, 100),
            ],
            false,
        ),
        params,
    )
    .unwrap();
    let xs: Vec<i32> = out.rects.iter().map(|r| r.x).collect();
    assert_eq!(xs, vec![64 + 8 * 2048, 64 + 4 * 2048, 64 + 3 * 2048, 64]);
    assert_eq!(out.canvas.w, 64 + 16 * 2048 + 64);
}

#[test]
fn without_bit_numbers() {
    let mut params = vector_params();
    params.show_bits = false;
    let out = packet(
        &input(vec![piece(0, 3, 500, 500), piece(32, 33, 500, 500)], false),
        params,
    )
    .unwrap();
    assert_eq!(out.rects[0].y, 320);
    assert_eq!(out.rects[1].y, 320 + 2048 + 320);
    assert_eq!(out.lead, vec![rect(0, 0, 0, 0); 2]);
    assert_eq!(out.trail, vec![rect(0, 0, 0, 0); 2]);
    assert_eq!(out.canvas.h, 2 * (2048 + 320) + 320);
}

#[test]
fn empty_input() {
    let out = packet(&input(Vec::new(), false), vector_params()).unwrap();
    assert_eq!(out.canvas, Size { w: 65664, h: 1344 });
    let titled = packet(&input(Vec::new(), true), vector_params()).unwrap();
    assert_eq!(titled.title, rect(64, 1344, 65536, 2048));
    assert_eq!(
        titled.canvas,
        Size {
            w: 65664,
            h: 1344 + 2048
        }
    );
}

#[test]
fn narrow_fields_clamp_to_zero_width() {
    let mut params = vector_params();
    params.bit_width = 1;
    params.padding_x = 5;
    let out = packet(
        &input(vec![piece(0, 2, 10, 10), piece(3, 8, 10, 10)], false),
        params,
    )
    .unwrap();
    assert_eq!(out.rects[0].w, 0);
    assert_eq!(out.rects[1].w, 1);
}

#[test]
fn label_band_never_exceeds_the_padding() {
    let mut params = vector_params();
    params.padding_y = 0;
    params.show_bits_pad = 640;
    let out = packet(&input(vec![piece(0, 3, 100, 100)], false), params).unwrap();
    assert_eq!(out.lead[0], rect(64, 0, 100, 640));
    assert_eq!(out.rects[0].y, 640);
}

#[test]
fn labels_never_start_left_of_the_canvas() {
    let out = packet(
        &input(vec![piece(64, 64, 3, 0), piece(65, 65, 3, 0)], false),
        cell_params(),
    )
    .unwrap();
    assert_eq!(out.lead[0].x, 0);
    assert_eq!(out.lead[1].x, 1);
}

#[test]
fn rejects_invalid_pieces() {
    let negative_label = PacketPiece {
        start: 0,
        end: 1,
        lead: Size { w: -1, h: 0 },
        trail: Size { w: 0, h: 0 },
    };
    for (name, piece) in [
        ("crosses a row", piece(30, 33, 1, 1)),
        ("reversed", piece(4, 3, 1, 1)),
        ("negative start", piece(-1, 3, 1, 1)),
        ("negative label", negative_label),
    ] {
        assert_eq!(
            packet(&input(vec![piece], false), vector_params()).unwrap_err(),
            GeomError::Domain,
            "{name}"
        );
    }
}

#[test]
fn rejects_invalid_params() {
    type Tweak = fn(&mut PacketParams);
    let tweaks: [(&str, Tweak); 5] = [
        ("zero bits", |p| p.bits_per_row = 0),
        ("zero bit width", |p| p.bit_width = 0),
        ("zero row height", |p| p.row_height = 0),
        ("negative padding", |p| p.padding_x = -1),
        ("negative margin", |p| p.margin_x = -1),
    ];
    for (name, tweak) in tweaks {
        let mut params = vector_params();
        tweak(&mut params);
        assert_eq!(
            packet(&input(Vec::new(), false), params).unwrap_err(),
            GeomError::Domain,
            "{name}"
        );
    }
}

#[test]
fn overflow() {
    let mut params = vector_params();
    params.row_height = 1 << 28;
    params.padding_y = 1 << 28;
    assert_eq!(
        packet(&input(vec![piece(32, 32, 1, 0)], false), params).unwrap_err(),
        GeomError::Overflow
    );
    let mut wide = vector_params();
    wide.bits_per_row = 1 << 20;
    wide.bit_width = 1 << 20;
    assert_eq!(
        packet(&input(Vec::new(), false), wide).unwrap_err(),
        GeomError::Overflow
    );
    assert_eq!(
        packet(
            &input(vec![piece(1 << 40, 1 << 40, 1, 0)], false),
            vector_params()
        )
        .unwrap_err(),
        GeomError::Overflow
    );
}

#[test]
fn rows_are_contiguous_and_disjoint() {
    let mut pieces = Vec::new();
    let mut start = 0i64;
    while start < 200 {
        let end = (start + start % 7).min(199).min((start / 32 + 1) * 32 - 1);
        pieces.push(piece(start, end, 40, 40));
        start = end + 1;
    }
    for params in [vector_params(), cell_params()] {
        let out = packet(&input(pieces.clone(), true), params).unwrap();
        for (i, a) in out.rects.iter().enumerate() {
            assert!(a.x >= params.margin_x);
            assert!(a.x + a.w <= out.canvas.w - params.margin_x);
            assert!(a.y + a.h <= out.title.y);
            for (j, b) in out.rects.iter().enumerate().skip(i + 1) {
                assert!(!geom::intersects(*a, *b).unwrap(), "{i} {j}");
            }
            for label in [out.lead[i], out.trail[i]] {
                for (j, b) in out.rects.iter().enumerate() {
                    assert!(!geom::intersects(label, *b).unwrap(), "label {i} box {j}");
                }
            }
        }
    }
}
