use std::path::Path;

use super::{chart_of, from_xychart, payload, unzigzag, zigzag};
use crate::layout::chart::series_title;
use crate::layout::input::Input;
use crate::model::chart::Chart;
use crate::model::xychart as mx;
use crate::scene::{DumpOptions, Profile};
use crate::syntax::preprocess::preprocess;
use crate::syntax::xychart::parse;

type Check = Result<(), String>;

#[test]
fn zigzag_round_trips_signed_values() {
    let values = [
        0,
        1,
        -1,
        2,
        -2,
        2_147_483_647,
        -2_147_483_647,
        1 << 40,
        -(1 << 40),
    ];
    for value in values {
        assert_eq!(unzigzag(zigzag(value)), value);
    }
}

fn model_of(source: &str) -> Option<mx::Model> {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    if !parsed.diagnostics.is_empty() {
        return None;
    }
    Some(mx::resolve(source, &parsed.document).0)
}

fn titled(mut chart: Chart) -> Chart {
    if let Some(xy) = chart.xy.as_mut() {
        for (i, plot) in xy.plots.iter_mut().enumerate() {
            plot.title = series_title(i, &plot.title);
        }
    }
    chart
}

fn assert_input_carries_the_payload(source: &str) -> Check {
    let Some(model) = model_of(source) else {
        return Ok(());
    };
    let input =
        from_xychart(&model, Profile::Vector, DumpOptions::default()).map_err(|e| e.to_string())?;
    let want = titled(payload(&model));
    let got = chart_of(&input);
    assert_eq!(want.title, got.title, "{source:?}");
    assert_eq!(want.xy, got.xy, "{source:?}");
    for (key, value) in &want.config {
        assert_eq!(got.config.get(key), Some(value), "{source:?}");
    }
    Ok(())
}

#[test]
fn input_carries_the_whole_payload() -> Check {
    let sources = [
        "xychart\nbar [1, -2.5, 3]\n",
        "xychart horizontal\ntitle T\nx-axis X [a, b, c, a]\ny-axis \"Y\" -5 --> 5\nbar \"B\" [1, 2]\nline [4 \"p\", -4, 3]\n",
        "xychart\nx-axis 0 --> 10\nline \"L\" [1, 2, 3]\nbar [3]\n",
        "---\nconfig:\n  xyChart:\n    width: 900\n    xAxis:\n      showLabel: false\n---\nxychart\nx-axis [a]\nbar [1]\nx-axis 1 --> 2\n",
    ];
    for source in sources {
        assert_input_carries_the_payload(source)?;
    }
    Ok(())
}

#[test]
fn corpus_inputs_carry_their_payloads() -> Check {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/xychart");
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

fn input_of(source: &str, profile: Profile) -> Result<Input, String> {
    let model = model_of(source).ok_or("rejected source")?;
    from_xychart(&model, profile, DumpOptions::default()).map_err(|e| e.to_string())
}

#[test]
fn model_dump_carries_the_regions() -> Check {
    let input = input_of("xychart\nx-axis [a, b]\nbar [1, 2]\n", Profile::Vector)?;
    assert_eq!(input.region_sets.len(), 2);
    assert_eq!(
        input.region_sets[0].regions[..7],
        [0, 0, 1, 0, 0, 2000, 4000]
    );
    Ok(())
}
