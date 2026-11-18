use super::*;
fn input(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let parsed = crate::syntax::usecase::parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 0);
    let (model, diagnostics) = crate::model::usecase::resolve(source, &parsed.document);
    assert_eq!(diagnostics.len(), 0);
    from_usecase(&model, profile, DumpOptions::default()).map_err(|_| "layout input failed")
}
#[test]
fn ellipses_wrap_and_take_kind_minimum() -> Result<(), &'static str> {
    for (profile, minimum) in [(Profile::Cell, 15), (Profile::Vector, 7680)] {
        let input = input("usecase-beta\nU(short)\n", profile)?;
        let node = input.boxes.first().ok_or("missing usecase")?;
        assert_eq!((&*node.id, &*node.shape), ("U", "usecaseEllipse"));
        let size = input.sizes.first().ok_or("missing size")?;
        assert!(
            matches!(size, SizeRule::Content(Size { w, .. }) if *w == minimum),
            "ellipse content width must use the {profile:?} minimum {minimum}; observed size: {size:?}"
        );
        assert_eq!(input.spacing, Spacing::for_kind(profile, "usecase"));
    }
    let input = input(
        "usecase-beta\nU(abcdefghijklmno pqrstuvwxyz)\n",
        Profile::Cell,
    )?;
    let SizeRule::Content(size) = input.sizes.first().ok_or("missing size")? else {
        return Err("expected content size");
    };
    assert_eq!(
        (size.w, size.h),
        (19, 4),
        "the kind wrap target 15 cells must give lines 15 and 11, plus 2*2 pad on x and 2*1 pad on y; observed {size:?}"
    );
    Ok(())
}
#[test]
fn actors_and_boundaries_select_shapes() -> Result<(), &'static str> {
    let source = "usecase-beta\nactor A\nactor B@{type:hollow}\nactor C@{type:awesome}\nactor D@{icon:person}\nactor E@{business:true}\nsystemBoundary S@{type:package}\nU@{business:true}\nend\n";
    let input = input(source, Profile::Cell)?;
    assert_eq!(
        input
            .boxes
            .iter()
            .map(|node| node.shape.as_str())
            .collect::<Vec<_>>(),
        [
            "usecaseActor",
            "usecaseActorHollow",
            "usecaseActorAwesome",
            "usecaseActorIcon:icon:person",
            "usecaseActor:business",
            "rect:package",
            "usecaseBusiness"
        ]
    );
    assert!(
        matches!(
            input.sizes.first(),
            Some(SizeRule::Exact(Size { w: 9, h: 9 }))
        ),
        "a one-line cell actor must retain its intrinsic 9 by 9 glyph-caption box; observed sizes: {:?}",
        input.sizes
    );
    assert_eq!(input.groups.len(), 1);
    assert_eq!(input.boxes.last().ok_or("missing child")?.parent, "S");
    Ok(())
}
#[test]
fn routes_keep_direction_markers_and_stereotype_style() -> Result<(), &'static str> {
    let input = input(
        "usecase-beta\ne0\nA <-- B\nB --o C\nC --x D\nD ..>:include E\n",
        Profile::Cell,
    )?;
    assert_eq!(
        input
            .routes
            .iter()
            .map(|edge| edge.id.as_str())
            .collect::<Vec<_>>(),
        ["e1", "e2", "e3", "e4"]
    );
    assert_eq!(
        input
            .routes
            .iter()
            .map(|edge| (
                edge.marker_start.as_str(),
                edge.marker_end.as_str(),
                edge.line.as_str()
            ))
            .collect::<Vec<_>>(),
        [
            ("point", "none", "normal"),
            ("none", "circle", "normal"),
            ("none", "cross", "normal"),
            ("none", "point", "dotted")
        ]
    );
    assert!(
        input.labels.iter().any(|label| label.owner == "e4"),
        "the include relation must own its route label"
    );
    Ok(())
}
#[test]
fn scene_contains_actor_glyph_caption_and_usecase_ellipse() -> Result<(), &'static str> {
    for profile in [Profile::Cell, Profile::Vector] {
        let input = input("usecase-beta\nactor A(User)\nU(Task)\n", profile)?;
        let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
        let actor = scene
            .items()
            .iter()
            .find(|group| group.owner == "A")
            .ok_or("missing actor group")?;
        assert!(
            actor
                .items
                .iter()
                .any(|item| matches!(item, scene::Item::Ellipse(_))),
            "the {profile:?} actor must contain a head ellipse; observed items: {:?}",
            actor.items
        );
        assert!(
            actor
                .items
                .iter()
                .any(|item| matches!(item, scene::Item::Polyline(_))),
            "the {profile:?} actor must contain figure strokes; observed items: {:?}",
            actor.items
        );
        let usecase = scene
            .items()
            .iter()
            .find(|group| group.owner == "U")
            .ok_or("missing usecase group")?;
        assert!(
            matches!(usecase.items.first(), Some(scene::Item::Ellipse(_))),
            "the {profile:?} use case must start with its ellipse outline; observed items: {:?}",
            usecase.items
        );
    }
    Ok(())
}

#[test]
fn actor_intrinsic_size_has_no_ellipse_minimum() -> Result<(), &'static str> {
    let parsed = crate::syntax::usecase::parse("usecase-beta\nactor A\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 0);
    let (model, diagnostics) =
        crate::model::usecase::resolve("usecase-beta\nactor A\n", &parsed.document);
    assert_eq!(diagnostics.len(), 0);
    for (profile, expected) in [
        (Profile::Vector, Size { w: 4608, h: 7424 }),
        (Profile::Cell, Size { w: 9, h: 9 }),
    ] {
        let input =
            from_usecase(&model, profile, DumpOptions::default()).map_err(|_| "input failed")?;
        assert!(
            matches!(input.sizes.first(), Some(SizeRule::Exact(size)) if *size == expected),
            "the {profile:?} actor must use intrinsic size {expected:?}, not the ellipse minimum; observed sizes: {:?}",
            input.sizes
        );
    }
    Ok(())
}

#[test]
fn notes_merge_into_box_declaration_order() -> Result<(), &'static str> {
    let source = "usecase-beta\nA\nnote for A \"detail\"\nB\n";
    let parsed = crate::syntax::usecase::parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 0);
    let (model, diagnostics) = crate::model::usecase::resolve(source, &parsed.document);
    assert_eq!(diagnostics.len(), 0);
    let input =
        from_usecase(&model, Profile::Cell, DumpOptions::default()).map_err(|_| "input failed")?;
    assert_eq!(
        input
            .boxes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["A", "note-0", "B"]
    );
    assert_eq!(input.boxes.get(1).ok_or("missing note")?.shape, "note");
    assert_eq!(input.routes.first().ok_or("missing note relation")?.to, "A");
    Ok(())
}

fn caption_texts<'a>(scene: &'a scene::Scene, owner: &str) -> Vec<&'a scene::TextItem> {
    let groups = scene.items().iter().filter(|group| group.owner == owner);
    let mut texts = Vec::new();
    for item in groups.flat_map(|group| &group.items) {
        if let scene::Item::Text(text) = item {
            texts.push(text);
        }
    }
    texts
}

fn caption_runs(scene: &scene::Scene, owner: &str) -> Vec<scene::Run> {
    let mut runs = Vec::new();
    for text in caption_texts(scene, owner) {
        for line in &text.lines {
            runs.extend(line.iter().cloned());
        }
    }
    runs
}

fn caption_lines(scene: &scene::Scene, owner: &str) -> Vec<String> {
    let mut lines = Vec::new();
    for text in caption_texts(scene, owner) {
        for line in &text.lines {
            lines.push(line.iter().map(|run| run.text.as_str()).collect());
        }
    }
    lines
}

#[test]
fn emphasis_crossing_a_wrap_boundary_stays_bold_without_delimiters() -> Result<(), &'static str> {
    let label = "**abcdefghijklmnopqrstuvwxyz abcdefghijklmnopqrstuvwxyz**";
    let input = input(&format!("usecase-beta\nU({label})\n"), Profile::Cell)?;
    let SizeRule::Content(size) = input.sizes.first().ok_or("missing size")? else {
        return Err("expected content size");
    };
    assert_eq!(
        (size.w, size.h),
        (19, 6),
        "cell widths ignore style, so the kind target 15 must wrap into lines 15/11/15/11 plus 2*2 pad on x and 2*1 pad on y; observed {size:?}"
    );
    let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
    let runs = caption_runs(&scene, "U");
    assert!(
        runs.iter().any(|run| run.bold),
        "the emphasized run must arrive bold even though the wrap falls inside it: {runs:?}"
    );
    assert!(
        runs.iter().all(|run| !run.text.contains("**")),
        "delimiters must never appear as scene text: {runs:?}"
    );
    assert_eq!(
        caption_lines(&scene, "U"),
        [
            "abcdefghijklmno".to_string(),
            "pqrstuvwxyz".to_string(),
            "abcdefghijklmno".to_string(),
            "pqrstuvwxyz".to_string(),
        ],
        "both halves of the split emphasis must wrap at the kind target; observed {:?}",
        caption_lines(&scene, "U")
    );
    Ok(())
}

#[test]
fn escaped_punctuation_resolves_in_scene_without_backslashes() -> Result<(), &'static str> {
    let input = input("usecase-beta\nU(a\\*b \\_c\\\\d)\n", Profile::Cell)?;
    let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
    let runs = caption_runs(&scene, "U");
    assert_eq!(
        runs.iter().map(|run| run.text.as_str()).collect::<String>(),
        "a*b _c\\d",
        "the scene must show the resolved punctuation with no backslashes: {runs:?}"
    );
    assert!(
        runs.iter().all(|run| !run.bold && !run.italic),
        "escaped delimiters must not create styled runs: {runs:?}"
    );
    Ok(())
}

#[test]
fn forced_breaks_keep_empty_rows_and_scene_lines() -> Result<(), &'static str> {
    let input = input("usecase-beta\nU(x<br/><br/>y)\n", Profile::Cell)?;
    let SizeRule::Content(size) = input.sizes.first().ok_or("missing size")? else {
        return Err("expected content size");
    };
    assert_eq!(
        (size.w, size.h),
        (15, 5),
        "three forced regions render rows x/empty/y: height 3 plus 2*1 pad, width 1 plus 2*2 pad against the 15 minimum; observed {size:?}"
    );
    let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
    assert_eq!(
        caption_lines(&scene, "U"),
        ["x".to_string(), String::new(), "y".to_string()],
        "the empty forced region must stay an empty row; observed {:?}",
        caption_lines(&scene, "U")
    );
    Ok(())
}

#[test]
fn unsupported_markup_and_math_stay_literal_and_unstyled() -> Result<(), &'static str> {
    let input = input("usecase-beta\nB(a * b _c_d)\nC($$x$$)\n", Profile::Cell)?;
    let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
    for (owner, expected) in [("B", "a * b _c_d"), ("C", "$$x$$")] {
        let runs = caption_runs(&scene, owner);
        assert_eq!(
            runs.iter().map(|run| run.text.as_str()).collect::<String>(),
            expected,
            "{owner} must render its literal text unchanged: {runs:?}"
        );
        assert!(
            runs.iter().all(|run| !run.bold && !run.italic),
            "{owner} must not gain style from unsupported markup or math dollars: {runs:?}"
        );
    }
    Ok(())
}
