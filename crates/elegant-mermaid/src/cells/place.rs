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
                let text: String = runs.iter().map(|run| run.text.as_str()).collect();
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
