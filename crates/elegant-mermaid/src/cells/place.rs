use super::{Canvas, Token, colour};
use crate::{
    geom::GeomError,
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
impl Canvas {
    pub fn place_all(&mut self, labels: &[&TextItem], theme: &Theme) -> Result<usize, GeomError> {
        let mut refused = 0usize;
        for label in labels {
            let ink = colour::text_token(theme.name(), label.style.name(), label.series);
            for (row, runs) in label.lines.iter().enumerate() {
                let text: String = runs
                    .iter()
                    .flat_map(|run| run.text.chars())
                    .map(super::serialise::printable)
                    .collect();
                refused = refused
                    .checked_add(self.place_line(label, &text, row, ink)?)
                    .ok_or(GeomError::Overflow)?;
            }
        }
        Ok(refused)
    }
    fn place_line(
        &mut self,
        label: &TextItem,
        text: &str,
        row: usize,
        ink: Token,
    ) -> Result<usize, GeomError> {
        let mut col = line_start(
            label.align,
            label.rect.x,
            label.rect.w,
            measure::cell_width(text)?,
        )?;
        let row = i32::try_from(row).map_err(|_| GeomError::Overflow)?;
        let y = label.rect.y.checked_add(row).ok_or(GeomError::Overflow)?;
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
}
