use std::path::Path;

use super::layout;
use crate::DiagramKind;
use crate::cells::{self, Options};
use crate::model::Resolved;
use crate::scene::{DumpOptions, Profile, Scene};

type Check = Result<(), String>;

fn scene_of(source: &str, profile: Profile) -> Result<Scene, String> {
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    let (model, diagnostics) = Resolved::parse(DiagramKind::Info, source, &removed);
    if !diagnostics.is_empty() {
        return Err(format!("rejected source: {diagnostics:?}"));
    }
    let input = model
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|e| e.to_string())?;
    let (scene, _) = layout(&input).map_err(|e| e.to_string())?;
    Ok(scene)
}

#[test]
fn scene_shows_the_version_in_both_profiles() -> Check {
    let vector = scene_of("info\n", Profile::Vector)?;
    assert_eq!((vector.canvas().w, vector.canvas().h), (400 * 64, 100 * 64));
    assert_eq!(vector.labels()[0].lines, ["v0.1.0"]);
    let cell = scene_of("info showInfo\n", Profile::Cell)?;
    assert_eq!((cell.canvas().w, cell.canvas().h), (6, 1));
    assert_eq!(cell.boxes()[0].id, "info");
    assert_eq!(cell.labels()[0].lines, ["v0.1.0"]);
    Ok(())
}

#[test]
fn corpus_scenes_are_valid() -> Check {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let paths = [
        root.join("info/mermaid/info~pr-check~should-handle-an-info-definition.mmd"),
        root.join("info/mermaid/info~pr-check~should-handle-an-info-definition-with-showinfo.mmd"),
        root.join(
            "state/mermaid/state-diagram-v2~nightly-check~v2-should-render-a-simple-info.mmd",
        ),
    ];
    for path in paths {
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        for profile in [Profile::Vector, Profile::Cell] {
            let scene = scene_of(&source, profile)?;
            assert_eq!(scene.check(), Ok(true), "{path:?} {profile:?}");
            if profile == Profile::Cell {
                let result =
                    cells::render(&scene, &Options::default()).map_err(|e| e.to_string())?;
                assert_eq!(result.refused_clusters, 0);
                assert_eq!(result.text, "v0.1.0\n");
            }
        }
    }
    Ok(())
}
