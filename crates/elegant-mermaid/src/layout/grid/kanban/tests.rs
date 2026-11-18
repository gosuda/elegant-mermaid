use super::{KanbanCard, KanbanInput, KanbanParams, KanbanSection, kanban};
use crate::geom::{COORD_LIMIT, GeomError, Rect, Size, contains, intersects};

const VECTOR: KanbanParams = KanbanParams {
    section_width: 12800,
    gutter: 640,
    section_gap: 320,
    card_gap: 320,
    padding: 512,
    border: 0,
    label_band_min: 1600,
    section_min_height: 3200,
};

const CELL: KanbanParams = KanbanParams {
    section_width: 25,
    gutter: 1,
    section_gap: 1,
    card_gap: 1,
    padding: 1,
    border: 1,
    label_band_min: 1,
    section_min_height: 4,
};

fn r(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn sections(heights: &[i32]) -> Vec<KanbanSection> {
    heights
        .iter()
        .map(|&label_height| KanbanSection { label_height })
        .collect()
}

fn cards(rows: &[(usize, i32)]) -> Vec<KanbanCard> {
    rows.iter()
        .map(|&(section, height)| KanbanCard { section, height })
        .collect()
}

fn input(label_heights: &[i32], rows: &[(usize, i32)]) -> KanbanInput {
    KanbanInput {
        sections: sections(label_heights),
        cards: cards(rows),
    }
}

#[test]
fn vector_columns_and_cards() -> Result<(), GeomError> {
    let out = kanban(&input(&[1280, 1280], &[(0, 2560), (0, 3840)]), VECTOR)?;
    assert_eq!(
        out.sections,
        [r(512, 512, 12800, 8960), r(13632, 512, 12800, 3200)]
    );
    assert_eq!(
        out.cards,
        [r(992, 2112, 11840, 2560), r(992, 4992, 11840, 3840)]
    );
    assert_eq!(out.labels[0], r(512, 672, 12800, 1280));
    assert_eq!(out.canvas, Size { w: 26944, h: 9984 });
    Ok(())
}

#[test]
fn cell_columns_and_cards() -> Result<(), GeomError> {
    let out = kanban(&input(&[1, 1], &[(0, 3), (0, 4)]), CELL)?;
    assert_eq!(out.sections, [r(1, 1, 25, 12), r(27, 1, 25, 5)]);
    assert_eq!(out.cards, [r(1, 3, 24, 3), r(1, 7, 24, 4)]);
    assert_eq!(out.labels[0], r(1, 2, 25, 1));
    assert_eq!(out.canvas, Size { w: 53, h: 14 });
    Ok(())
}

#[test]
fn header_band_grows_with_tallest_label() -> Result<(), GeomError> {
    let out = kanban(&input(&[2560, 1280], &[(1, 2560)]), VECTOR)?;
    assert_eq!(out.cards[0].y, 512 + 2560);
    assert_eq!(out.sections[1], r(13632, 512, 12800, 5760));
    assert_eq!(out.labels[1], r(13632, 512 + 640, 12800, 1280));
    Ok(())
}

#[test]
fn interleaved_cards_keep_declaration_order_per_section() -> Result<(), GeomError> {
    let out = kanban(
        &input(&[1280, 1280], &[(1, 640), (0, 640), (1, 640)]),
        VECTOR,
    )?;
    assert_eq!(out.cards[1].y, out.cards[0].y);
    assert_eq!(out.cards[2].y, out.cards[0].y + out.cards[0].h + 320);
    assert!(out.cards[0].x > out.cards[1].x);
    Ok(())
}

#[test]
fn empty_diagram_is_a_margin() -> Result<(), GeomError> {
    let out = kanban(&KanbanInput::default(), VECTOR)?;
    assert_eq!(out.canvas, Size { w: 1024, h: 1024 });
    assert!(out.sections.is_empty());
    Ok(())
}

#[test]
fn empty_section_has_minimum_height() -> Result<(), GeomError> {
    assert_eq!(kanban(&input(&[1280], &[]), VECTOR)?.sections[0].h, 3200);
    assert_eq!(kanban(&input(&[1], &[]), CELL)?.sections[0].h, 5);
    Ok(())
}

#[test]
fn cards_stay_inside_their_section_and_apart() -> Result<(), GeomError> {
    for (params, label, height) in [(VECTOR, 1280, 1920), (CELL, 1, 3)] {
        let out = kanban(&input(&[label], &[(0, height); 7]), params)?;
        for (i, card) in out.cards.iter().enumerate() {
            assert!(contains(out.sections[0], *card)?);
            if i > 0 {
                assert!(!intersects(out.cards[i - 1], *card)?);
            }
        }
    }
    Ok(())
}

#[test]
fn rejects_invalid_input() {
    let section = [1];
    let negative_param = KanbanParams {
        card_gap: -1,
        ..CELL
    };
    let narrow = KanbanParams {
        section_width: 1,
        ..CELL
    };
    let cases = [
        ("section out of range", input(&section, &[(1, 1)]), CELL),
        ("negative height", input(&section, &[(0, -1)]), CELL),
        ("negative label", input(&[-1], &[]), CELL),
        ("negative parameter", input(&section, &[]), negative_param),
        ("card as wide as nothing", input(&section, &[]), narrow),
    ];
    for (name, case, params) in cases {
        assert_eq!(
            kanban(&case, params).err(),
            Some(GeomError::Domain),
            "{name}"
        );
    }
}

#[test]
fn overflow_is_an_error() {
    let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
    let tall = input(&[1], &[(0, limit), (0, limit)]);
    assert_eq!(kanban(&tall, VECTOR).err(), Some(GeomError::Overflow));
    let wide = KanbanParams {
        section_width: limit,
        ..VECTOR
    };
    assert_eq!(
        kanban(&input(&[0, 0], &[]), wide).err(),
        Some(GeomError::Overflow)
    );
}
