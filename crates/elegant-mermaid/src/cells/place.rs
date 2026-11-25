use super::{Canvas, Token, colour};
use crate::{
    geom::{GeomError, Rect},
    measure,
    scene::{Align, TextItem},
    theme::Theme,
};

pub fn line_start(align: Align, x: i32, w: i32, line_w: i32) -> Result<i32, GeomError> {
    let gap = i64::from(w) - i64::from(line_w);
    let offset = match align {
        Align::Start => 0,
        Align::Middle => gap.div_euclid(2),
        Align::End => gap,
    };
    i32::try_from(i64::from(x) + offset).map_err(|_| GeomError::Overflow)
}

pub(crate) struct PositionedLine {
    pub(crate) text: String,
    pub(crate) rect: Rect,
}

/// The renderer's occupied cells, after joining styled runs and replacing
/// control characters. Every authored line is positioned, even beyond rect.h.
pub(crate) fn positioned_lines(
    label: &TextItem,
) -> impl Iterator<Item = Result<PositionedLine, GeomError>> + '_ {
    label.lines.iter().enumerate().map(move |(row, runs)| {
        let text: String = runs
            .iter()
            .flat_map(|run| run.text.chars())
            .map(super::serialise::printable)
            .collect();
        let w = measure::cell_width(&text)?;
        let x = line_start(label.align, label.rect.x, label.rect.w, w)?;
        let row = i32::try_from(row).map_err(|_| GeomError::Overflow)?;
        let y = label.rect.y.checked_add(row).ok_or(GeomError::Overflow)?;
        Ok(PositionedLine {
            text,
            rect: Rect { x, y, w, h: 1 },
        })
    })
}

impl Canvas {
    pub fn place_all(&mut self, labels: &[&TextItem], theme: &Theme) -> Result<usize, GeomError> {
        let mut refused = 0usize;
        for label in labels {
            let ink = colour::text_token(theme.name(), label.style.name(), label.series);
            for line in positioned_lines(label) {
                let line = line?;
                refused = refused
                    .checked_add(self.place_clusters(&line.text, line.rect.x, line.rect.y, ink)?)
                    .ok_or(GeomError::Overflow)?;
            }
        }
        Ok(refused)
    }
    pub(super) fn place_clusters(
        &mut self,
        text: &str,
        mut col: i32,
        y: i32,
        ink: Token,
    ) -> Result<usize, GeomError> {
        let mut refused = 0;
        for cluster in measure::segment(text) {
            let width =
                u8::try_from(measure::cluster_width(cluster)).map_err(|_| GeomError::Overflow)?;
            if !self.put_label(col, y, cluster.text, width, ink) {
                refused += 1;
            }
            col = col
                .checked_add(i32::from(width))
                .ok_or(GeomError::Overflow)?;
        }
        Ok(refused)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cells::{Charset, ColorMode, Rgb};
    use crate::geom::Rect;
    use crate::scene::{Run, TextRole, TextStyle};

    #[test]
    fn label_lines_replace_controls_before_segmentation_and_alignment()
    -> Result<(), Box<dyn std::error::Error>> {
        let theme = crate::theme::resolve("")?;
        for text in ["a\r\nb", "a\u{1}\u{301}b", "世é"] {
            let (expected, width) = match text {
                "a\r\nb" => (" a��b\n", 4),
                "a\u{1}\u{301}b" => (" a�\u{301}b\n", 3),
                _ => (" 世é\n", 3),
            };
            let label = TextItem {
                rect: Rect {
                    x: 0,
                    y: 0,
                    w: width + 2,
                    h: 1,
                },
                role: TextRole::Label,
                size: 14,
                align: Align::Middle,
                style: TextStyle::Text,
                series: 0,
                lines: vec![vec![Run::plain(text)]],
            };
            let mut canvas = Canvas::new(width + 2, 1)?;
            assert_eq!(canvas.place_all(&[&label], &theme)?, 0);
            assert_eq!(
                canvas.serialise(Charset::Unicode, ColorMode::None, |_| Rgb {
                    r: 0,
                    g: 0,
                    b: 0
                }),
                expected
            );
        }
        Ok(())
    }

    #[test]
    fn positioned_lines_share_sanitized_graphemes_alignment_and_unclipped_rows()
    -> Result<(), GeomError> {
        let label = TextItem {
            rect: Rect {
                x: 10,
                y: 5,
                w: 20,
                h: 0,
            },
            role: TextRole::Label,
            size: 14,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: vec![
                vec![Run::plain("A"), Run::plain("\u{301}")],
                vec![Run::plain("\u{1}\u{301}"), Run::plain("B")],
                Vec::new(),
                vec![Run::plain(" ")],
            ],
        };
        let lines = positioned_lines(&label)
            .map(|line| line.map(|line| (line.text, line.rect)))
            .collect::<Result<Vec<_>, _>>()?;
        assert_eq!(
            lines,
            [
                (
                    "A\u{301}".into(),
                    Rect {
                        x: 19,
                        y: 5,
                        w: 1,
                        h: 1
                    }
                ),
                (
                    "\u{fffd}\u{301}B".into(),
                    Rect {
                        x: 19,
                        y: 6,
                        w: 2,
                        h: 1
                    }
                ),
                (
                    String::new(),
                    Rect {
                        x: 20,
                        y: 7,
                        w: 0,
                        h: 1
                    }
                ),
                (
                    " ".into(),
                    Rect {
                        x: 19,
                        y: 8,
                        w: 1,
                        h: 1
                    }
                ),
            ]
        );
        Ok(())
    }

    #[test]
    fn positioned_lines_preserve_floor_alignment_and_checked_coordinates() {
        let mut label = TextItem {
            rect: Rect {
                x: 10,
                y: 5,
                w: 0,
                h: 1,
            },
            role: TextRole::Label,
            size: 14,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: vec![vec![Run::plain("A")]],
        };
        assert_eq!(
            positioned_lines(&label)
                .next()
                .map(|line| line.map(|line| line.rect)),
            Some(Ok(Rect {
                x: 9,
                y: 5,
                w: 1,
                h: 1
            }))
        );
        label.align = Align::End;
        label.rect.x = i32::MAX;
        label.rect.w = 2;
        assert_eq!(
            positioned_lines(&label).next().map(|line| line.map(|_| ())),
            Some(Err(GeomError::Overflow))
        );
        label.rect.x = 0;
        label.rect.y = i32::MAX;
        label.lines.push(vec![Run::plain("B")]);
        assert_eq!(
            positioned_lines(&label).nth(1).map(|line| line.map(|_| ())),
            Some(Err(GeomError::Overflow))
        );
    }
}
