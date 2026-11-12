use super::*;
#[test]
#[expect(
    clippy::unwrap_used,
    reason = "test fixtures and render results must exist"
)]
fn svg_primitives_styles() {
    let mut r = Renderer {
        theme: theme::resolve("").unwrap(),
        used: BTreeSet::new(),
    };
    for style in [
        ShapeStyle::Node,
        ShapeStyle::Group,
        ShapeStyle::Band,
        ShapeStyle::Note,
        ShapeStyle::Edge,
        ShapeStyle::Rule,
        ShapeStyle::Mark,
        ShapeStyle::MarkHollow,
        ShapeStyle::Ink,
        ShapeStyle::InkLine,
        ShapeStyle::Series,
        ShapeStyle::SeriesLine,
        ShapeStyle::SeriesTint,
        ShapeStyle::SeriesFlow,
        ShapeStyle::Error,
        ShapeStyle::Warning,
        ShapeStyle::Success,
        ShapeStyle::Plate,
    ] {
        let item = Item::Ellipse(EllipseItem {
            shape: Shape::plain(style).with_line(Line::Dotted),
            cx: 640,
            cy: 640,
            rx: 64,
            ry: 64,
        });
        assert!(r.primitive(&item).unwrap().starts_with("<ellipse "));
    }
    let shape = Shape::plain(ShapeStyle::Edge);
    let p = Point { x: 64, y: 0 };
    let polygon = Item::Polygon(PolygonItem {
        shape,
        points: vec![Point { x: 0, y: 0 }, p, Point { x: 0, y: 64 }],
    });
    assert!(
        r.primitive(&polygon)
            .unwrap()
            .contains("points='0,0 1,0 0,1'")
    );
    let path = Item::Path(PathItem {
        shape,
        commands: vec![
            PathCommand::Move(p),
            PathCommand::Line(p),
            PathCommand::Curve {
                c1: p,
                c2: p,
                to: p,
            },
            PathCommand::Arc {
                centre: Point { x: 0, y: 0 },
                r: 64,
                start: 0,
                sweep: 16384,
            },
            PathCommand::Close,
        ],
    });
    assert!(
        r.primitive(&path)
            .unwrap()
            .contains("d='M 1 0 L 1 0 C 1 0 1 0 1 0 A 1 1 0 0 1 0 1 Z'")
    );
    let symbol = Item::SymbolRef(SymbolRefItem {
        symbol: SymbolName::new("disc").unwrap(),
        at: p,
        style: ShapeStyle::Ink,
    });
    assert!(matches!(r.primitive(&symbol), Err(ConfigError::Invalid(_))));
}
#[test]
#[expect(
    clippy::unwrap_used,
    reason = "fixed scene and built-in theme are valid"
)]
fn svg_styled_lines_and_alignment() {
    let mut r = Renderer {
        theme: theme::resolve("").unwrap(),
        used: BTreeSet::new(),
    };
    let text = TextItem {
        rect: Rect {
            x: 640,
            y: 640,
            w: 1280,
            h: 2560,
        },
        role: TextRole::Body,
        size: 14,
        align: Align::End,
        style: TextStyle::Text,
        series: 0,
        lines: vec![
            vec![Run {
                text: "<&".into(),
                bold: true,
                italic: true,
            }],
            vec![Run::plain("next")],
        ],
    };
    assert_eq!(
        r.text(&text).unwrap(),
        "<text class='emd-t-body emd-s-text' x='30' font-size='14' xml:space='preserve' text-anchor='end'><tspan x='30' y='24.89'><tspan font-weight='600'><tspan font-style='italic'>&lt;&amp;</tspan></tspan></tspan><tspan x='30' y='44.89'>next</tspan></text>\n"
    );
}
