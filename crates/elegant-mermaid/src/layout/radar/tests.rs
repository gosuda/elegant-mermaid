use std::path::Path;

use super::{chart_of, from_radar, layout, payload, unzigzag, zigzag};
use crate::layout::input::Input;
use crate::model::radar as mr;
use crate::scene::{DumpOptions, Profile};
use crate::syntax::preprocess::preprocess;
use crate::syntax::radar::parse;

type Check = Result<(), String>;

#[test]
fn zigzag_round_trips_signed_values() {
    for value in [
        0,
        1,
        -1,
        2,
        -2,
        2_147_483_647,
        -2_147_483_647,
        1 << 40,
        -(1 << 40),
    ] {
        assert_eq!(unzigzag(zigzag(value)), value);
    }
}

fn model_of(source: &str) -> Option<mr::Model> {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    if !parsed.diagnostics.is_empty() {
        return None;
    }
    let (model, diagnostics) = mr::resolve(source, &parsed.document);
    diagnostics.is_empty().then_some(model)
}

fn input_of(source: &str, profile: Profile) -> Result<Input, String> {
    let model = model_of(source).ok_or("rejected source")?;
    from_radar(&model, profile, DumpOptions::default()).map_err(|e| e.to_string())
}

fn assert_input_carries_the_payload(source: &str) -> Check {
    let Some(model) = model_of(source) else {
        return Ok(());
    };
    let input =
        from_radar(&model, Profile::Vector, DumpOptions::default()).map_err(|e| e.to_string())?;
    let want = payload(&model);
    let got = chart_of(&input);
    assert_eq!(want.title, got.title, "{source:?}");
    assert_eq!(want.radar, got.radar, "{source:?}");
    for (key, value) in &want.config {
        assert_eq!(got.config.get(key), Some(value), "{source:?}");
    }
    Ok(())
}

#[test]
fn input_carries_the_whole_payload() -> Check {
    let sources = [
        "radar-beta\naxis A, B, C\ncurve c{1, 2, 3}\n",
        "radar-beta\ntitle T\naxis a[\"Alpha\"], b, c\ncurve x[\"X\"]{1, 2, 3}, y{3, 2, 1}\nmax 5\nmin 1\nticks 3\ngraticule polygon\nshowLegend false\n",
        "radar-beta\naxis A, B\ncurve k{B: 3, A: 1}\ncurve ragged{1}\n",
        "---\nconfig:\n  radar:\n    width: 400\n    curveTension: 0.5\n---\nradar-beta\naxis A, B, C\ncurve c{1, 2, 3}\n",
    ];
    for source in sources {
        assert_input_carries_the_payload(source)?;
    }
    Ok(())
}

#[test]
fn corpus_inputs_carry_their_payloads() -> Check {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/radar");
    let mut count = 0;
    for dir in std::fs::read_dir(root).map_err(|e| e.to_string())? {
        let dir = dir.map_err(|e| e.to_string())?.path();
        for file in std::fs::read_dir(dir).map_err(|e| e.to_string())? {
            let path = file.map_err(|e| e.to_string())?.path();
            let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
            assert_input_carries_the_payload(&source)?;
            count += 1;
        }
    }
    assert!(count > 0);
    Ok(())
}

#[test]
fn model_dump_carries_the_regions() -> Check {
    let input = input_of(
        "radar-beta\naxis A, B\ncurve c{1, 2}\nmax 4\nticks 3\ngraticule polygon\n",
        Profile::Vector,
    )?;
    assert_eq!(input.region_sets.len(), 2);
    assert_eq!(input.region_sets[0].regions, [0, 1, 1, 3000, 1, 8000, 0]);
    assert_eq!(input.region_sets[1].regions, [1, 2, 2000, 4000]);
    Ok(())
}

#[test]
fn every_profile_gives_the_vector_input() -> Check {
    let source = "radar-beta\naxis A, B, C\ncurve c{1, 2, 3}\n";
    let cell = input_of(source, Profile::Cell)?;
    let vector = input_of(source, Profile::Vector)?;
    assert_eq!(cell.profile, Profile::Vector);
    assert_eq!(cell.options.profile, Profile::Vector);
    let regions = |input: &Input| -> Vec<Vec<usize>> {
        input
            .region_sets
            .iter()
            .map(|s| s.regions.clone())
            .collect()
    };
    assert_eq!(regions(&cell), regions(&vector));
    Ok(())
}

#[test]
fn layout_satisfies_the_hard_constraints() -> Check {
    for source in [
        "radar-beta\naxis A, B, C\ncurve c{1, 2, 3}\n",
        "radar-beta\ntitle Skills\naxis m[\"Math\"], s[\"Sci\"], e[\"Eng\"], a[\"Art\"]\ncurve a{4, 3, 2, 1}, b{1, 2, 3, 4}\nmax 5\ngraticule polygon\n",
        "radar-beta\naxis A, B\ncurve c{1, 2}\nticks 0\nshowLegend false\n",
        "radar-beta\naxis A\ncurve c{3}\nmin 1\n",
        "radar-beta\ncurve c{1}\n",
    ] {
        let input = input_of(source, Profile::Vector)?;
        let (scene, _) = layout(&input).map_err(|e| e.to_string())?;
        let verdict = scene.validate().map_err(|e| format!("{e:?}"))?;
        assert!(verdict.is_none(), "{source:?}: {verdict:?}");
    }
    Ok(())
}
