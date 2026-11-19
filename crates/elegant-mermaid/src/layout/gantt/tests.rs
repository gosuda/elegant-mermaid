use std::path::Path;

use super::{chart_of, from_gantt, payload, unzigzag, zigzag};
use crate::layout::input::Input;
use crate::model::gantt as mg;
use crate::scene::{DumpOptions, Profile};
use crate::syntax::gantt::parse;
use crate::syntax::preprocess::preprocess;

type Check = Result<(), String>;

const SAMPLE: &str = "gantt\ntitle Plan\ndateFormat YYYY-MM-DD\nexcludes weekends\nsection Build\nCompile :crit, c1, 2014-01-03, 3d\nShip :milestone, m1, 2014-01-10, 0d\nclick c1 href \"https://example.com/c1\"\nclick m1 href \"javascript:void(0)\"\n";

#[test]
fn zigzag_round_trips_signed_values() {
    for value in [
        0,
        1,
        -1,
        2_777_414_400,
        -62_135_596_800,
        8_640_000_000_000,
        -8_640_000_000_000,
    ] {
        assert_eq!(unzigzag(zigzag(value)), value);
    }
}

fn model_of(source: &str) -> Option<mg::Model> {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    if !parsed.diagnostics.is_empty() {
        return None;
    }
    Some(mg::resolve(source, &parsed.document).0)
}

fn input_of(source: &str, profile: Profile) -> Result<Input, String> {
    let model = model_of(source).ok_or("rejected source")?;
    from_gantt(&model, profile, DumpOptions::default()).map_err(|e| e.to_string())
}

fn assert_input_carries_the_payload(source: &str) -> Check {
    let Some(model) = model_of(source) else {
        return Ok(());
    };
    let input =
        from_gantt(&model, Profile::Vector, DumpOptions::default()).map_err(|e| e.to_string())?;
    let want = payload(&model);
    let got = chart_of(&input);
    assert_eq!(want.title, got.title, "{source:?}");
    assert_eq!(want.gantt, got.gantt, "{source:?}");
    assert_eq!(want.config, got.config, "{source:?}");
    Ok(())
}

#[test]
fn input_carries_the_whole_payload() -> Check {
    let sources = [
        SAMPLE,
        "gantt\nsection A\nT :a1, 2014-01-01, 2014-01-05\nsection B\nU :after a1, 3d\n",
        "gantt\ntopAxis\ntickInterval 2week\nweekday monday\naxisFormat %d/%b\nexcludes weekends, monday\nincludes 2014-01-04\nV :vert, v1, 2014-01-02, 1d\nW :2014-01-01, 4d\n",
        "---\nconfig:\n  gantt:\n    barHeight: 30\n    topPadding: 60\n---\ngantt\ndateFormat YYYY-MM-DD\nT :2014-01-01, 1d\n",
    ];
    for source in sources {
        assert_input_carries_the_payload(source)?;
    }
    Ok(())
}

#[test]
fn corpus_inputs_carry_their_payloads() -> Check {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/gantt");
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
fn model_dump_carries_task_regions_and_effective_options() -> Check {
    let input = input_of(SAMPLE, Profile::Vector)?;
    assert_eq!(input.region_sets.len(), 2);
    let first = &input.region_sets[0].regions;
    assert_eq!(first[0], 4);
    assert_eq!(first[1], 1);
    assert_eq!(unzigzag(first[2]), 1_388_707_200);
    assert_eq!(input.region_sets[1].regions[0], 1);
    let keys: Vec<&str> = input.options.config.keys().map(String::as_str).collect();
    assert_eq!(keys, ["axisFormat", "excludes", "weekday", "weekend"]);
    let ids: Vec<&str> = input.boxes.iter().map(|b| b.id.as_str()).collect();
    assert_eq!(ids, ["plot", "s0", "t0", "t1"]);
    Ok(())
}

#[test]
fn links_own_the_task_boxes() -> Check {
    let model = model_of(SAMPLE).ok_or("rejected source")?;
    let resolved = crate::model::Resolved::Gantt(model);
    let links = resolved.links();
    assert_eq!(links.len(), 1);
    assert_eq!(links[0].owner, "t0");
    Ok(())
}
