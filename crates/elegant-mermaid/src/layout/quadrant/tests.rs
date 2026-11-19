use std::path::{Path, PathBuf};

use super::{payload, quadrant_of};
use crate::DiagramKind;
use crate::model::Resolved;
use crate::scene::{DumpOptions, Profile};

type Check = Result<(), String>;

fn assert_input_carries_the_payload(source: &str) -> Check {
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    let (resolved, diagnostics) = Resolved::parse(DiagramKind::Quadrant, source, &removed);
    if !diagnostics.is_empty() {
        return Ok(());
    }
    let Some(Resolved::Quadrant(model)) = &resolved else {
        return Err("not a quadrant model".into());
    };
    for profile in [Profile::Vector, Profile::Cell] {
        let input = Resolved::Quadrant(model.clone())
            .input(profile, DumpOptions::default())
            .map_err(|e| e.to_string())?;
        assert_eq!(
            format!("{:?}", payload(model)),
            format!("{:?}", quadrant_of(&input)),
            "{source:?}"
        );
    }
    Ok(())
}

#[test]
fn input_carries_the_whole_payload() -> Check {
    for source in [
        "quadrantChart\n",
        "quadrantChart\n  title T\n  x-axis A --> B\n  y-axis C\n  quadrant-1 one\n  quadrant-4 four\n  P: [0.25, 0.75]\n  Q:::hot: [1, 0] radius: 12\n  classDef hot radius: 3\n",
        "%%{init: {\"quadrantChart\": {\"chartWidth\": 800, \"pointRadius\": 9, \"titlePadding\": 0}}}%%\nquadrantChart\n  title #amp; T\n  P: [0.5, 0.5]\n",
    ] {
        assert_input_carries_the_payload(source)?;
    }
    Ok(())
}

#[test]
fn corpus_inputs_carry_their_payloads() -> Check {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/quadrant");
    let mut paths: Vec<PathBuf> = Vec::new();
    for source in std::fs::read_dir(root).map_err(|e| e.to_string())? {
        for file in std::fs::read_dir(source.map_err(|e| e.to_string())?.path())
            .map_err(|e| e.to_string())?
        {
            paths.push(file.map_err(|e| e.to_string())?.path());
        }
    }
    paths.sort();
    assert!(!paths.is_empty());
    for path in paths {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        assert_input_carries_the_payload(&source)?;
    }
    Ok(())
}

#[test]
fn model_regions_list_every_point() -> Check {
    let source = "quadrantChart\n  A: [0.1, 0.2]\n  B: [0.3, 0.4] radius: 7\n";
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    let (resolved, _) = Resolved::parse(DiagramKind::Quadrant, source, &removed);
    let input = resolved
        .ok_or("no model")?
        .input(Profile::Vector, DumpOptions::default())
        .map_err(|e| e.to_string())?;
    let sets: Vec<(usize, Vec<usize>)> = input
        .region_sets
        .iter()
        .map(|set| (set.parent, set.regions.clone()))
        .collect();
    assert_eq!(sets, [(5, vec![100, 200, 0]), (6, vec![300, 400, 8])]);
    Ok(())
}
