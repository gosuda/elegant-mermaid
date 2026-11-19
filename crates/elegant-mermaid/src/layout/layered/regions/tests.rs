use super::*;

const MINIMA: Minima = Minima {
    border: 1,
    padding: 2,
    title: 1,
};

fn oracle(
    constraints: &Constraints,
    sets: &[RegionSet<'_>],
    reservations: &[Reservation],
) -> Result<(), String> {
    for set in sets {
        let bands = set
            .regions
            .iter()
            .map(|g| {
                constraints
                    .bands
                    .iter()
                    .find(|b| b.group == *g)
                    .ok_or_else(|| {
                        format!(
                            "region {g} has no reserved band; observed {:?}",
                            constraints.bands
                        )
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (index, band) in bands.iter().enumerate() {
            assert!(
                band.left < band.right,
                "region {} must reserve positive width",
                band.group
            );
            assert!(
                band.left >= 0 && band.right <= constraints.widths[set.parent],
                "region {} escapes parent {}",
                band.group,
                set.parent
            );
            assert_eq!(
                band.span, bands[0].span,
                "set {} lacks a common span",
                set.parent
            );
            if index > 0 {
                assert!(
                    bands[index - 1].right <= band.left,
                    "declared regions {} and {} overlap or reverse",
                    bands[index - 1].group,
                    band.group
                );
            }
            for r in reservations.iter().filter(|r| r.group == band.group) {
                let origin = i64::from(constraints.origins[r.group]);
                assert!(
                    i64::from(r.left) + origin >= 0
                        && i64::from(r.right) + origin <= i64::from(band.right - band.left),
                    "algorithmic footprint escapes region {}",
                    r.group
                );
                assert!(
                    band.span.first <= r.span.first && r.span.last <= band.span.last,
                    "rank footprint escapes region {}",
                    r.group
                );
            }
        }
    }
    Ok(())
}

#[test]
fn empty_bands_and_nonuniform_footprints() -> Result<(), String> {
    let parents = [None, Some(0), Some(0), Some(0), Some(0), Some(0)];
    let sets = [RegionSet {
        parent: 0,
        regions: &[1, 2, 3, 4, 5],
    }];
    let reservations = [
        Reservation {
            group: 2,
            left: -17,
            right: 43,
            span: Span { first: 2, last: 9 },
        },
        Reservation {
            group: 4,
            left: 800,
            right: 803,
            span: Span { first: 0, last: 1 },
        },
    ];
    let c = solve(&parents, &sets, &reservations, MINIMA)
        .map_err(|error| format!("valid nonuniform region reservations failed: {error:?}"))?;
    oracle(&c, &sets, &reservations)?;
    assert_eq!(
        c.widths[1], 7,
        "leading empty band keeps border/title minima"
    );
    assert_eq!(c.widths[3], 7, "middle empty band remains visible");
    assert_eq!(c.widths[5], 7, "trailing empty band remains visible");
    assert_eq!(
        c.bands[0].span,
        Span { first: 0, last: 9 },
        "every sibling band must cover the union of member rank spans; observed {:?}",
        c.bands
    );
    Ok(())
}

#[test]
fn nested_sets_use_subtree_widths_and_declared_order() -> Result<(), String> {
    let parents = [None, Some(0), Some(0), Some(1), Some(1)];
    let sets = [
        RegionSet {
            parent: 0,
            regions: &[2, 1],
        },
        RegionSet {
            parent: 1,
            regions: &[4, 3],
        },
    ];
    for reverse in [false, true] {
        let reservations: Vec<_> = [(3usize, 3i32, -9, 80), (4, 4, 200, 204)]
            .into_iter()
            .map(|(group, rank, left, right)| {
                let (left, right) = if reverse {
                    (-right, -left)
                } else {
                    (left, right)
                };
                Reservation {
                    group,
                    left,
                    right,
                    span: Span {
                        first: rank,
                        last: rank + 2,
                    },
                }
            })
            .collect();
        let c = solve(&parents, &sets, &reservations, MINIMA).map_err(|error| {
            format!("valid nested reservations failed with reverse={reverse}: {error:?}")
        })?;
        oracle(&c, &sets, &reservations)?;
        assert_eq!(
            c.bands.iter().map(|b| b.group).collect::<Vec<_>>(),
            [2, 1, 4, 3],
            "input cross positions must not override declaration-pinned bands"
        );
        assert!(
            c.widths[1] >= c.widths[3] + c.widths[4] + 6,
            "outer reservation must include the entire nested set"
        );
    }
    Ok(())
}

#[test]
fn rejects_invalid_forests_and_overlapping_sets() {
    for parents in [vec![Some(1), Some(0)], vec![Some(9)], vec![Some(0)]] {
        assert!(
            matches!(solve(&parents, &[], &[], MINIMA), Err(LayoutError::Domain)),
            "invalid parent forest accepted: {parents:?}"
        );
    }
    let parents = [None, Some(0), Some(0), Some(1)];
    for regions in [&[1, 1][..], &[1, 3][..], &[9][..], &[][..]] {
        assert!(
            matches!(
                solve(&parents, &[RegionSet { parent: 0, regions }], &[], MINIMA),
                Err(LayoutError::Domain)
            ),
            "invalid child membership accepted: {regions:?}"
        );
    }
    let overlapping = [
        RegionSet {
            parent: 0,
            regions: &[1],
        },
        RegionSet {
            parent: 0,
            regions: &[2],
        },
    ];
    let observed = solve(&parents, &overlapping, &[], MINIMA);
    assert!(
        matches!(&observed, Err(LayoutError::Domain)),
        "two sets sharing parent 0 must be rejected as Domain; observed {observed:?}"
    );
}

#[test]
fn checked_dimensions_and_reservation_domain() {
    let parents = [None, Some(0)];
    let sets = [RegionSet {
        parent: 0,
        regions: &[1],
    }];
    let r = Reservation {
        group: 1,
        left: i32::MIN,
        right: i32::MAX,
        span: Span { first: 0, last: 0 },
    };
    let observed = solve(&parents, &sets, &[r], MINIMA);
    assert!(
        matches!(&observed, Err(LayoutError::Overflow)),
        "a reservation spanning the entire i32 range must return Overflow; observed {observed:?}"
    );
    let invalid = Reservation {
        left: 2,
        right: 1,
        ..r
    };
    let observed = solve(&parents, &sets, &[invalid], MINIMA);
    assert!(
        matches!(&observed, Err(LayoutError::Domain)),
        "an inverted reservation interval must return Domain; observed {observed:?}"
    );
    let minima = Minima {
        border: i32::MAX,
        ..MINIMA
    };
    let observed = solve(&parents, &sets, &[], minima);
    assert!(
        matches!(&observed, Err(LayoutError::Overflow)),
        "border plus padding exceeding i32 must return Overflow; observed {observed:?}"
    );
}
