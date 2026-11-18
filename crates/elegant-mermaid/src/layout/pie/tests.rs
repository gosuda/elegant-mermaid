use super::{from_pie, layout, payload, payload_of};
use crate::layout::input::Input;
use crate::model::pie as mp;
use crate::scene::{DumpOptions, Profile};
use crate::syntax::pie::parse;
use crate::syntax::preprocess::preprocess;

type Check = Result<(), String>;

fn model_of(source: &str) -> Option<mp::Model> {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    if !parsed.diagnostics.is_empty() {
        return None;
    }
    let (model, diagnostics) = mp::resolve(source, &parsed.document);
    diagnostics.is_empty().then_some(model)
}

fn input_of(source: &str, profile: Profile) -> Result<Input, String> {
    let model = model_of(source).ok_or("rejected source")?;
    from_pie(&model, profile, DumpOptions::default()).map_err(|e| e.to_string())
}

#[test]
fn input_carries_the_whole_payload() -> Check {
    let sources = [
        "pie\n\"A\" : 1\n\"B\" : 2\n",
        "pie showData\ntitle T\n\"A [x]\" : 1.5\n\"B\" : 0\n\"C\" : 10\n",
        "---\nconfig:\n  pie:\n    donutHole: 0.4\n    textPosition: 0.5\n---\npie\n\"A\" : 1\n\"B\" : 3\n",
        "pie showData\n\"A [1]\" : 1\n",
    ];
    for source in sources {
        let model = model_of(source).ok_or(format!("rejected {source:?}"))?;
        let input =
            from_pie(&model, Profile::Vector, DumpOptions::default()).map_err(|e| e.to_string())?;
        let want = payload(&model);
        let got = payload_of(&input);
        assert_eq!(want, got, "{source:?}");
    }
    Ok(())
}

#[test]
fn both_profiles_give_the_vector_input() -> Check {
    let source = "pie title T\n\"A\" : 1\n\"B\" : 2\n";
    let vector = input_of(source, Profile::Vector)?;
    let cell = input_of(source, Profile::Cell)?;
    assert_eq!(vector.profile, Profile::Vector);
    assert_eq!(cell.profile, Profile::Vector);
    assert_eq!(vector.boxes.len(), cell.boxes.len());
    assert_eq!(vector.labels.len(), cell.labels.len());
    Ok(())
}

#[test]
fn layout_reproduces_the_scene_of_the_model_input() -> Check {
    let source = "pie showData\ntitle Pets\n\"Dogs\" : 386\n\"Cats\" : 85\n\"Rats\" : 15\n";
    let input = input_of(source, Profile::Vector)?;
    let (scene, capped) = layout(&input).map_err(|e| e.to_string())?;
    assert!(!capped);
    let dump = scene.dump_part();
    let ids: Vec<&str> = dump.boxes.iter().map(|b| b.id.as_str()).collect();
    assert_eq!(ids, ["plot", "s0", "s1", "s2"]);
    let labels: Vec<&str> = dump.labels.iter().map(|l| l.id.as_str()).collect();
    assert_eq!(
        labels,
        [
            "title", "s0.pct", "s1.pct", "s2.pct", "legend.0", "legend.1", "legend.2"
        ]
    );
    Ok(())
}
