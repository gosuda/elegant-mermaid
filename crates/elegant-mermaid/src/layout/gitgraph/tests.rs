use super::*;
use crate::diag::Severity;
use crate::model::Resolved;
use crate::scene::{GroupRole, Item};
use crate::syntax::preprocess::preprocess;

const SAMPLE: &str = "gitGraph\n\
    commit id: \"A\"\n\
    commit id: \"B\" tag: \"v1\" tag: \"rc\" type: HIGHLIGHT\n\
    branch develop order: 2\n\
    commit type: REVERSE\n\
    checkout main\n\
    commit\n\
    merge develop tag: \"m\" type: REVERSE\n\
    cherry-pick id: \"develop-2\"\n";

fn input(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let removed = preprocess(source).removed;
    let (model, diagnostics) = Resolved::parse(crate::DiagramKind::Gitgraph, source, &removed);
    if diagnostics.iter().any(|d| d.severity == Severity::Error) {
        return Err("source has errors");
    }
    model
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|_| "input failed")
}

fn boxes(input: &Input) -> Vec<String> {
    input
        .boxes
        .iter()
        .map(|b| format!("{}|{}|{}|{}", b.id, b.role.as_str(), b.shape, b.parent))
        .collect()
}

fn all_ids(input: &Input) -> Vec<&str> {
    let boxes = input.boxes.iter().map(|b| b.id.as_str());
    let routes = input.routes.iter().map(|r| r.id.as_str());
    let labels = input.labels.iter().map(|l| l.id.as_str());
    boxes.chain(routes).chain(labels).collect()
}

#[test]
fn input_encodes_the_model() -> Result<(), &'static str> {
    let input = input(SAMPLE, Profile::Vector)?;
    assert_eq!(input.direction, Direction::Lr);
    assert_eq!(
        boxes(&input),
        [
            "lane0|group|branch|",
            "lane1|group|branch:2|",
            "A|node|commit|lane0",
            "B|node|highlight|lane0",
            "develop-2|node|reverse|lane1",
            "main-3|node|commit|lane0",
            "main-4|node|merge-reverse|lane0",
            "main-5|node|cherry-pick|lane0",
        ]
    );
    let routes: Vec<String> = input
        .routes
        .iter()
        .map(|r| format!("{}|{}>{}|{}", r.id, r.from, r.to, r.line))
        .collect();
    assert_eq!(
        routes,
        [
            "e0|A>B|normal",
            "e1|B>develop-2|normal",
            "e2|B>main-3|normal",
            "e3|main-3>main-4|normal",
            "e4|develop-2>main-4|normal",
            "e5|main-4>main-5|normal",
            "e6|develop-2>main-5|dotted",
        ]
    );
    let labels: Vec<String> = input
        .labels
        .iter()
        .map(|l| format!("{}|{}|{}|{}", l.id, l.owner, l.text, l.role.as_str()))
        .collect();
    assert_eq!(
        labels,
        [
            "lane0.label|lane0|main|label",
            "lane1.label|lane1|develop|label",
            "A.label|A|A|body",
            "B.label|B|B|body",
            "B.tag0|B|v1|body",
            "B.tag1|B|rc|body",
            "develop-2.label|develop-2|develop-2|body",
            "main-3.label|main-3|main-3|body",
            "main-4.label|main-4|main-4|body",
            "main-4.tag0|main-4|m|body",
            "main-5.label|main-5|main-5|body",
            "main-5.tag0|main-5|cherry-pick:develop-2|body",
        ]
    );
    Ok(())
}

#[test]
fn ids_stay_unique() -> Result<(), &'static str> {
    let input = input(
        "gitGraph\ncommit id: \"lane0\"\ncommit id: \"e0\"\ncommit id: \"e0.label\"\ncommit id: \"lane0.label\"\n",
        Profile::Cell,
    )?;
    let ids = all_ids(&input);
    let unique: BTreeSet<&str> = ids.iter().copied().collect();
    assert_eq!(unique.len(), ids.len(), "{ids:?}");
    Ok(())
}

#[test]
fn config_toggles_labels() -> Result<(), &'static str> {
    let source = "%%{init: {'gitGraph': {'showBranches': false, 'showCommitLabel': false}}}%%\ngitGraph\ncommit id: \"A\" tag: \"t\"\n";
    let mut input = input(source, Profile::Vector)?;
    assert_eq!(
        input
            .labels
            .iter()
            .map(|l| l.id.as_str())
            .collect::<Vec<_>>(),
        ["A.tag0"]
    );
    for profile in [Profile::Vector, Profile::Cell] {
        input.profile = profile;
        let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
        assert_eq!(scene.labels().len(), 1);
        assert_eq!(scene.labels()[0].lines, ["t"]);
        for group in scene.items() {
            if group.role == GroupRole::Group {
                assert!(group.items.is_empty());
            }
        }
    }
    Ok(())
}

#[test]
fn layout_satisfies_the_hard_constraints() -> Result<(), &'static str> {
    let body = SAMPLE.trim_start_matches("gitGraph\n");
    for source in [
        SAMPLE.to_owned(),
        format!("gitGraph TB:\n{body}"),
        format!("gitGraph BT:\n{body}"),
        "gitGraph\n".to_owned(),
        "gitGraph\nbranch a\nbranch b order: 1\n".to_owned(),
        "gitGraph BT:\ncommit id: \"x\"\ncommit id: \"x\" tag: \"dup\"\n".to_owned(),
    ] {
        for profile in [Profile::Vector, Profile::Cell] {
            let (scene, _) = layout(&input(&source, profile)?).map_err(|_| "layout failed")?;
            let clause = scene.validate().map_err(|_| "validate failed")?;
            assert!(clause.is_none(), "{source} {profile:?}: {clause:?}");
        }
    }
    Ok(())
}

#[test]
fn rejects_foreign_route_endpoints() {
    let mut foreign = input("gitGraph\ncommit id: \"A\"\n", Profile::Cell).unwrap();
    foreign.routes.push(InputRoute {
        id: "e".to_owned(),
        from: "A".to_owned(),
        to: "nowhere".to_owned(),
        orthogonal: true,
        marker_start: String::new(),
        marker_end: String::new(),
        line: "normal".to_owned(),
        min_length: 1,
        from_side: None,
        to_side: None,
    });
    assert!(matches!(layout(&foreign), Err(LayoutError::Domain)));
}

#[test]
fn cell_markers_follow_commit_kinds() -> Result<(), &'static str> {
    let (scene, _) = layout(&input(SAMPLE, Profile::Cell)?).map_err(|_| "layout failed")?;
    let symbols: Vec<&str> = scene
        .items()
        .iter()
        .filter(|group| group.role == GroupRole::Node)
        .flat_map(|group| group.items.iter())
        .filter_map(|item| match item {
            Item::SymbolRef(symbol) => Some(symbol.symbol.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(
        symbols,
        [
            "disc",
            "diamond",
            "ring",
            "disc",
            "bullseye",
            "diamond-hollow"
        ]
    );
    Ok(())
}

fn assert_cell_text(scene: &Scene, texts: &[&str]) {
    let rendered = crate::cells::render(scene, &crate::cells::Options::default()).expect("render");
    assert_eq!(
        rendered.refused_clusters, 0,
        "refused clusters:\n{}",
        rendered.text
    );
    for text in texts {
        assert!(
            rendered.text.contains(text),
            "missing {text:?}:\n{}",
            rendered.text
        );
    }
}

#[test]
fn cell_labels_are_never_overwritten() -> Result<(), &'static str> {
    let body = SAMPLE.trim_start_matches("gitGraph\n");
    for header in ["gitGraph\n", "gitGraph TB:\n", "gitGraph BT:\n"] {
        let source = format!("{header}{body}");
        let (scene, _) = layout(&input(&source, Profile::Cell)?).map_err(|_| "layout failed")?;
        assert_cell_text(
            &scene,
            &[
                "main",
                "develop",
                "develop-2",
                "main-3",
                "main-4",
                "main-5",
                "cherry-pick:develop-2",
                "v1",
                "rc",
            ],
        );
    }
    Ok(())
}

const DUPLICATE_IDS: &str = "commit id: \"alpha\"\n\
    commit id: \"bravo\"\n\
    branch dev\n\
    commit id: \"xray\"\n\
    commit id: \"yankee\"\n\
    checkout main\n\
    commit id: \"charlie\"\n\
    merge dev\n\
    commit id: \"yankee\"\n";

#[test]
fn duplicate_ids_keep_cell_labels_apart() -> Result<(), &'static str> {
    for header in ["gitGraph\n", "gitGraph TB:\n", "gitGraph BT:\n"] {
        let source = format!("{header}{DUPLICATE_IDS}");
        let (scene, _) = layout(&input(&source, Profile::Cell)?).map_err(|_| "layout failed")?;
        assert_cell_text(&scene, &["alpha", "bravo", "xray", "yankee", "charlie"]);
    }
    Ok(())
}
#[test]
fn corpus_cell_text_is_never_overwritten() -> Result<(), std::boxed::Box<dyn std::error::Error>> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/gitgraph");
    let mut paths = Vec::new();
    collect_corpus(&root, &mut paths)?;
    paths.sort();
    assert!(!paths.is_empty());
    for path in paths {
        let source = std::fs::read_to_string(&path)?;
        let Ok(input) = input(&source, Profile::Cell) else {
            continue;
        };
        let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
        let rendered = crate::cells::render(&scene, &crate::cells::Options::default())?;
        assert_eq!(rendered.refused_clusters, 0, "{}", path.display());
    }
    Ok(())
}

fn collect_corpus(
    root: &std::path::Path,
    paths: &mut Vec<std::path::PathBuf>,
) -> std::io::Result<()> {
    for entry in std::fs::read_dir(root)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_corpus(&path, paths)?;
        } else if path.extension().is_some_and(|extension| extension == "mmd") {
            paths.push(path);
        }
    }
    Ok(())
}

#[test]
fn direction_names_are_exact() {
    assert_eq!(direction_of("LR"), Direction::Lr);
    assert_eq!(direction_of("TB"), Direction::Tb);
    assert_eq!(direction_of("BT"), Direction::Bt);
    assert_eq!(direction_of("RL"), Direction::Rl);
    assert_eq!(direction_of("sideways"), Direction::Rl);
}

#[test]
fn header_right_to_left_is_a_syntax_error() {
    assert!(matches!(
        input("gitGraph RL:\ncommit\n", Profile::Vector),
        Err("source has errors")
    ));
}

#[test]
fn right_to_left_model_is_rejected() -> Result<(), &'static str> {
    for profile in [Profile::Vector, Profile::Cell] {
        let mut model = input(SAMPLE, profile)?;
        model.direction = Direction::Rl;
        assert!(
            matches!(layout(&model), Err(LayoutError::Domain)),
            "{profile:?}"
        );
    }
    Ok(())
}
