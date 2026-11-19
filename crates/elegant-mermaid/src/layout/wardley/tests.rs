use std::path::Path;

use super::{DEFAULT_STAGES, from_input, from_wardley, payload};
use crate::model::wardley as mw;
use crate::scene::{DumpOptions, Profile};
use crate::syntax::preprocess::preprocess;
use crate::syntax::wardley::parse;

type Check = Result<(), String>;

fn model_of(source: &str) -> Option<mw::Model> {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    if !parsed.diagnostics.is_empty() {
        return None;
    }
    Some(mw::resolve(source, &parsed.document).0)
}

fn assert_input_carries_the_payload(source: &str) -> Check {
    let Some(model) = model_of(source) else {
        return Ok(());
    };
    for profile in [Profile::Vector, Profile::Cell] {
        let input =
            from_wardley(&model, profile, DumpOptions::default()).map_err(|e| format!("{e:?}"))?;
        let got = from_input(&input).map_err(|e| format!("{e:?}"))?;
        assert_eq!(payload(&model), got, "{source:?}");
    }
    Ok(())
}

#[test]
fn input_carries_the_payload_for_every_corpus_file() -> Check {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/wardley");
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
fn four_default_stages_when_evolution_is_absent() -> Check {
    let model = model_of("wardley-beta\ncomponent A [0.5, 0.5]\n").ok_or("rejected")?;
    let w = payload(&model);
    assert_eq!(w.stages, DEFAULT_STAGES);
    assert!(w.boundaries.is_empty());
    Ok(())
}

#[test]
fn only_resolved_links_that_are_not_pipeline_spokes_remain() -> Check {
    let source = "wardley-beta\ncomponent Kettle [0.5, 0.5]\ncomponent Pot [0.2, 0.2]\npipeline Kettle {\ncomponent Fire [0.3]\ncomponent Gas [0.6]\n}\nFire -> Kettle\nKettle -> Gas\nPot -> Missing\nPot -> Fire\n";
    let model = model_of(source).ok_or("rejected")?;
    let w = payload(&model);
    assert_eq!(w.links.len(), 1);
    assert_eq!(Some(w.links[0].from), model.node_index("Pot"));
    assert_eq!(Some(w.links[0].to), model.node_index("Kettle_Fire"));
    assert_eq!(w.pipelines.len(), 1);
    assert_eq!(Some(w.pipelines[0].parent), model.node_index("Kettle"));
    Ok(())
}

#[test]
fn model_dump_carries_the_region_sets() -> Check {
    let model = model_of("wardley-beta\ncomponent A [0.5, 0.25] (buy)\n").ok_or("rejected")?;
    let input = from_wardley(&model, Profile::Vector, DumpOptions::default())
        .map_err(|e| format!("{e:?}"))?;
    let dump = crate::layout::modeldump::model_dump(&input);
    assert!(
        dump.contains("\"regions\":[[0,0,4,0],\n[0,1,0,2,25000,50000,0,0]]"),
        "{dump}"
    );
    assert!(dump.contains("\"kind\":\"wardley\""));
    Ok(())
}
