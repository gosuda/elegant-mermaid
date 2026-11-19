use super::*;
use crate::{
    geom::Size,
    outlines::{Command, Contours, GlyphOutlines},
};

fn outlines() -> GlyphOutlines {
    let font = || {
        let mut glyphs = Contours::new();
        for cp in 33..127 {
            glyphs.insert(
                cp,
                vec![
                    Command::Move(0, 0),
                    Command::Line(1000, 0),
                    Command::Line(1000, 1000),
                    Command::Close,
                ],
            );
        }
        (2048, glyphs)
    };
    GlyphOutlines::new([font(), font()])
}

fn scene(text: &str) -> Scene {
    Scene::new(
        Size { w: 6400, h: 3200 },
        Dump::new("flowchart", DumpOptions::default()),
        vec![
            Group::new(GroupRole::Node, "").with_items(vec![Item::Text(TextItem {
                rect: Rect {
                    x: 640,
                    y: 640,
                    w: 3840,
                    h: 1280,
                },
                role: TextRole::Body,
                size: 16,
                align: Align::Start,
                style: TextStyle::Text,
                series: 0,
                lines: vec![vec![Run::plain(text)]],
            })]),
        ],
    )
}

fn render(
    text: &str,
    mode: TextMode,
    outlines: Option<&GlyphOutlines>,
) -> Result<String, ConfigError> {
    let mut out = String::new();
    write(
        &mut out,
        &scene(text),
        &Options {
            text: mode,
            outlines,
            ..Options::default()
        },
    )?;
    Ok(out)
}

#[test]
fn paths_replace_text_elements_with_glyph_paths() -> Result<(), ConfigError> {
    let outlines = outlines();
    let svg = render("A", TextMode::Paths, Some(&outlines))?;
    assert!(
        svg.contains("<path class='emd-s-text' d='M10 25.59 L17.81 25.59 L17.81 17.78 Z'/>\n"),
        "{svg}"
    );
    assert!(svg.contains(".emd-s-text{fill:#"), "{svg}");
    assert!(!svg.contains("<text"), "{svg}");
    assert!(!svg.contains("<tspan"), "{svg}");
    Ok(())
}

#[test]
fn text_without_outlines_emits_no_element() -> Result<(), ConfigError> {
    let outlines = outlines();
    let svg = render("   ", TextMode::Paths, Some(&outlines))?;
    assert!(!svg.contains("emd-s-text"), "{svg}");
    assert!(!svg.contains("<text"), "{svg}");
    Ok(())
}

#[test]
fn font_mode_ignores_supplied_outlines() -> Result<(), ConfigError> {
    let outlines = outlines();
    let svg = render("A", TextMode::Font, Some(&outlines))?;
    assert!(svg.contains("<text class='emd-t-body emd-s-text'"), "{svg}");
    assert!(!svg.contains("<path class='emd-s-text'"), "{svg}");
    Ok(())
}

#[test]
fn paths_without_outlines_are_rejected() {
    let error = render("A", TextMode::Paths, None);
    assert!(
        matches!(&error, Err(ConfigError::Invalid(message)) if message.contains("glyph outlines")),
        "{error:?}"
    );
}
