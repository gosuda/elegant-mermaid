use super::*;
use crate::{
    geom::{Rect, Size},
    scene::{Dump, DumpOptions, Group, GroupRole, RectItem},
};
use std::{
    error::Error,
    path::{Path, PathBuf},
};
fn fixture_files(path: &Path) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let mut out = Vec::new();
    for entry in std::fs::read_dir(path)? {
        let p = entry?.path();
        if p.is_dir() {
            out.extend(fixture_files(&p)?);
        } else if p.extension().is_some_and(|e| e == "mmd") {
            out.push(p);
        }
    }
    out.sort();
    Ok(out)
}
fn fixture(kind: &str) -> Result<Scene, Box<dyn Error>> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus")
        .join(kind);
    let paths = fixture_files(&root)?;
    let path = paths.first().ok_or("missing corpus fixture")?;
    let src = std::fs::read_to_string(path)?;
    Ok(crate::layout(
        &crate::parse(&src),
        &crate::options::LayoutOptions::default(),
    )?)
}
fn accepted_fixture(kind: &str) -> Result<Scene, Box<dyn Error>> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus")
        .join(kind);
    for path in fixture_files(&root)? {
        let src = String::from_utf8_lossy(&std::fs::read(&path)?).into_owned();
        let document = crate::parse(&src);
        if !document.has_errors() {
            return Ok(crate::layout(
                &document,
                &crate::options::LayoutOptions::default(),
            )?);
        }
    }
    Err(format!("no accepted corpus fixture for {kind}").into())
}
#[test]
fn png_kinds() -> Result<(), Box<dyn Error>> {
    let kinds: Vec<_> = crate::layout::families::FAMILIES
        .iter()
        .map(|family| family.kind)
        .collect();
    assert!(kinds.len() >= 3, "implemented kinds: {kinds:?}");
    for kind in kinds {
        let scene = accepted_fixture(kind)?;
        for scale in [1u32, 2] {
            let bytes = png(
                &scene,
                &PngOptions {
                    scale,
                    ..PngOptions::default()
                },
            )?;
            let image = Pixmap::decode_png(&bytes)?;
            let side = |units: i32| u32::try_from((i64::from(units) * i64::from(scale) + 63) / 64);
            assert_eq!(image.width(), side(scene.canvas().w)?, "{kind} @{scale}");
            assert_eq!(image.height(), side(scene.canvas().h)?, "{kind} @{scale}");
            let first = image.pixels().first().ok_or("empty PNG")?;
            assert!(
                image.pixels().iter().any(|p| p != first),
                "png_kinds: {kind} @{scale} is a single colour"
            );
        }
    }
    Ok(())
}
#[test]
fn png_svg_text_paths_use_the_embedded_inter_outlines() -> Result<(), Box<dyn Error>> {
    let source = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n";
    let font = crate::render_svg_str(source, &crate::SvgOptions::default())?;
    let paths = crate::render_svg_str(
        source,
        &crate::SvgOptions {
            text: crate::TextMode::Paths,
            outlines: Some(inter_outlines()),
            ..crate::SvgOptions::default()
        },
    )?;
    assert!(font.contains("<text"), "{font}");
    assert!(paths.contains("<path class='emd-s-text' d='M"), "{paths}");
    assert!(
        !paths.contains("<text") && !paths.contains("<tspan"),
        "{paths}"
    );
    assert_eq!(
        paths.matches("<path class='emd-s-text'").count(),
        font.matches("<text").count()
    );
    let missing = crate::render_svg_str(
        source,
        &crate::SvgOptions {
            text: crate::TextMode::Paths,
            ..crate::SvgOptions::default()
        },
    );
    assert!(matches!(
        missing,
        Err(crate::RenderError::InvalidConfig { errors: 1 })
    ));
    Ok(())
}
fn scene(size: Size) -> Scene {
    Scene::new(
        size,
        Dump::new("flowchart", DumpOptions::default()),
        Vec::new(),
    )
}
#[test]
fn png_errors() -> Result<(), Box<dyn Error>> {
    let s = scene(Size { w: 64, h: 64 });
    for scale in [0, 9] {
        assert!(
            matches!(
                png(
                    &s,
                    &PngOptions {
                        scale,
                        ..PngOptions::default()
                    }
                ),
                Err(RasterError::InvalidConfig { errors: 1 })
            ),
            "png_errors: expected {} to hold (observed false)",
            stringify!(matches!(
                png(
                    &s,
                    &PngOptions {
                        scale,
                        ..PngOptions::default()
                    }
                ),
                Err(RasterError::InvalidConfig { errors: 1 })
            ))
        );
    }
    assert!(
        matches!(
            png(
                &scene(Size {
                    w: 16385 * 64,
                    h: 64
                }),
                &PngOptions {
                    scale: 1,
                    ..PngOptions::default()
                }
            ),
            Err(RasterError::PixelsTooLarge { .. })
        ),
        "png_errors: expected {} to hold (observed false)",
        stringify!(matches!(
            png(
                &scene(Size {
                    w: 16385 * 64,
                    h: 64
                }),
                &PngOptions {
                    scale: 1,
                    ..PngOptions::default()
                }
            ),
            Err(RasterError::PixelsTooLarge { .. })
        ))
    );
    Ok(())
}
#[test]
fn png_scanline_oracle() -> Result<(), Box<dyn Error>> {
    for kind in ["flowchart", "class"] {
        let original = fixture(kind)?;
        let groups = original
            .items()
            .iter()
            .map(|g| {
                Group::new(g.role, &g.owner)
                    .with_items(g.items.iter().filter_map(fill_only).collect())
            })
            .collect();
        let s = Scene::new(original.canvas(), original.dump_part().clone(), groups);
        let image = render(&s, &PngOptions::default())?;
        let bg = image.pixel(0, 0).ok_or("empty image")?;
        for y in 0..image.height() {
            let expected = oracle_row(&s, y)?;
            let actual: Vec<_> = (0..image.width())
                .filter(|&x| image.pixel(x, y).is_some_and(|p| p != bg))
                .collect();
            for (a, b) in [
                actual.first().zip(expected.first()),
                actual.last().zip(expected.last()),
            ]
            .into_iter()
            .flatten()
            {
                assert!(a.abs_diff(*b) <= 1, "{kind} row {y}: {a} vs {b}");
            }
            assert_eq!(actual.is_empty(), expected.is_empty(), "{kind} row {y}");
        }
    }
    Ok(())
}
fn fill_only(item: &Item) -> Option<Item> {
    let mut item = item.clone();
    let shape = match &mut item {
        Item::Rect(v) => &mut v.shape,
        Item::RoundRect(v) => &mut v.shape,
        Item::Polygon(v) => &mut v.shape,
        Item::Path(v) => &mut v.shape,
        _ => return None,
    };
    shape.width = Width::Units(0);
    Some(item)
}
fn oracle_row(s: &Scene, y: u32) -> Result<Vec<u32>, Box<dyn Error>> {
    let polygons = s
        .items()
        .iter()
        .flat_map(|g| &g.items)
        .map(oracle_polygons)
        .collect::<Result<Vec<_>, _>>()?;
    let mut row = Vec::new();
    for x in 0..u32::try_from((i64::from(s.canvas().w) * 2 + 63) / 64)? {
        if polygons.iter().any(|contours| {
            contours
                .iter()
                .filter(|ps| inside(ps, i64::from(x) * 32 + 16, i64::from(y) * 32 + 16))
                .count()
                % 2
                == 1
        }) {
            row.push(x);
        }
    }
    Ok(row)
}
fn rect_points(r: Rect) -> Vec<Point> {
    vec![
        Point { x: r.x, y: r.y },
        Point {
            x: r.x + r.w,
            y: r.y,
        },
        Point {
            x: r.x + r.w,
            y: r.y + r.h,
        },
        Point {
            x: r.x,
            y: r.y + r.h,
        },
    ]
}
fn oracle_polygons(item: &Item) -> Result<Vec<Vec<Point>>, Box<dyn Error>> {
    match item {
        Item::Rect(v) if v.shape.style != ShapeStyle::Group => Ok(vec![rect_points(v.rect)]),
        Item::RoundRect(v) => {
            let r = v.r.min(v.rect.w / 2).min(v.rect.h / 2).max(0);
            let mut ps = Vec::new();
            for (x, y, a) in [
                (v.rect.x + v.rect.w - r, v.rect.y + r, -16384),
                (v.rect.x + v.rect.w - r, v.rect.y + v.rect.h - r, 0),
                (v.rect.x + r, v.rect.y + v.rect.h - r, 16384),
                (v.rect.x + r, v.rect.y + r, 32768),
            ] {
                ps.extend(crate::cells::braille::arc(Point { x, y }, r, a, 16384)?);
            }
            Ok(vec![ps])
        }
        Item::Polygon(v) => Ok(vec![v.points.clone()]),
        Item::Path(v) => oracle_path(&v.commands),
        _ => Ok(Vec::new()),
    }
}
fn oracle_path(cs: &[PathCommand]) -> Result<Vec<Vec<Point>>, Box<dyn Error>> {
    let mut contours = vec![Vec::new()];
    let mut at = Point { x: 0, y: 0 };
    for c in cs {
        let ps = match *c {
            PathCommand::Move(p) => {
                contours.push(Vec::new());
                vec![p]
            }
            PathCommand::Line(p) => vec![p],
            PathCommand::Curve { c1, c2, to } => crate::cells::braille::cubic([at, c1, c2, to])?,
            PathCommand::Arc {
                centre,
                r,
                start,
                sweep,
            } => crate::cells::braille::arc(centre, r, start, sweep)?,
            PathCommand::Close => Vec::new(),
        };
        if let Some(p) = ps.last() {
            at = *p;
        }
        if let Some(contour) = contours.last_mut() {
            contour.extend(ps);
        }
    }
    Ok(contours)
}
fn inside(ps: &[Point], x: i64, y: i64) -> bool {
    let mut hits = 0;
    for (a, b) in ps.iter().zip(ps.iter().cycle().skip(1)).take(ps.len()) {
        let (ax, ay, bx, by) = (
            i64::from(a.x),
            i64::from(a.y),
            i64::from(b.x),
            i64::from(b.y),
        );
        if (ay <= y && y < by) || (by <= y && y < ay) {
            let cross = (bx - ax) * (y - ay) + (ax - x) * (by - ay);
            if cross.signum() == (by - ay).signum() {
                hits += 1;
            }
        }
    }
    hits % 2 == 1
}
#[test]
fn png_rectangle_oracle() -> Result<(), Box<dyn Error>> {
    let s = Scene::new(
        Size { w: 6400, h: 6400 },
        Dump::new("flowchart", DumpOptions::default()),
        vec![
            Group::new(GroupRole::Node, "A").with_items(vec![Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Ink),
                rect: Rect {
                    x: 640,
                    y: 640,
                    w: 1280,
                    h: 1280,
                },
            })]),
        ],
    );
    let image = render(&s, &PngOptions::default())?;
    assert_ne!(image.pixel(30, 30), image.pixel(0, 0));
    Ok(())
}

#[test]
fn owned_rgba_encoder_preserves_opaque_channels() -> Result<(), Box<dyn Error>> {
    let pixels = vec![17, 91, 203, 255, 222, 54, 7, 255];
    let png = encode_rgba(2, 1, pixels.clone())?;
    let decoded = Pixmap::decode_png(&png)?;
    assert_eq!(decoded.width(), 2);
    assert_eq!(decoded.height(), 1);
    assert_eq!(decoded.data(), pixels);
    assert!(
        encode_rgba(2, 1, vec![0; 7]).is_err(),
        "owned_rgba_encoder_preserves_opaque_channels: expected {} to hold (observed false)",
        stringify!(encode_rgba(2, 1, vec![0; 7]).is_err())
    );
    Ok(())
}
