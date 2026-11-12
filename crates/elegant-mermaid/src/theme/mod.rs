pub mod colour;
pub mod contrast;
pub use colour::{
    Colour, ColourError, Delta, Hsl, adjust, darken, invert, lighten, mk_border_dark,
    mk_border_light,
};
pub use contrast::{contrast, is_dark, luminance};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Token {
    Background,
    Foreground,
    Line,
    Accent,
    Muted,
    Surface,
    Border,
    Series0,
    Series1,
    Series2,
    Series3,
    Series4,
    Series5,
    Series6,
    Series7,
    Series8,
    Series9,
    Series10,
    Series11,
    Error,
    Warning,
    Success,
}
impl Token {
    pub const ALL: [Self; 22] = [
        Self::Background,
        Self::Foreground,
        Self::Line,
        Self::Accent,
        Self::Muted,
        Self::Surface,
        Self::Border,
        Self::Series0,
        Self::Series1,
        Self::Series2,
        Self::Series3,
        Self::Series4,
        Self::Series5,
        Self::Series6,
        Self::Series7,
        Self::Series8,
        Self::Series9,
        Self::Series10,
        Self::Series11,
        Self::Error,
        Self::Warning,
        Self::Success,
    ];
    pub fn id(self) -> &'static str {
        [
            "bg", "fg", "line", "accent", "muted", "surface", "border", "series0", "series1",
            "series2", "series3", "series4", "series5", "series6", "series7", "series8", "series9",
            "series10", "series11", "error", "warning", "success",
        ][self as usize]
    }
}
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("unknown theme: {name}")]
pub struct UnknownThemeError {
    pub name: String,
}
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ThemeError {
    #[error(transparent)]
    Unknown(#[from] UnknownThemeError),
    #[error(transparent)]
    Colour(#[from] ColourError),
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TextChoice {
    #[default]
    Foreground,
    Background,
    Plate,
}
#[derive(Clone, Debug)]
pub struct Theme {
    name: &'static str,
    colours: [Colour; 22],
}
pub fn resolve(name: &str) -> Result<Theme, ThemeError> {
    let name = if name.is_empty() {
        "elegant-light"
    } else {
        name
    };
    let row = crate::r#gen::themes::THEMES
        .iter()
        .find(|row| row.name == name)
        .ok_or_else(|| UnknownThemeError {
            name: name.to_owned(),
        })?;
    let mut colours = [Colour::default(); 22];
    for token in Token::ALL {
        if let Some(value) = row.tokens.iter().find(|value| value.token == token.id()) {
            colours[token as usize] = Colour::parse_hex(value.value)?;
        }
    }
    Ok(Theme {
        name: row.name,
        colours,
    })
}
impl Theme {
    pub fn name(&self) -> &'static str {
        self.name
    }
    pub fn colour(&self, token: Token) -> Colour {
        self.colours[token as usize]
    }
    pub fn stroke(&self, token: Token) -> Token {
        if crate::r#gen::strokeok::STROKE_OK
            .iter()
            .any(|row| row.theme == self.name && row.token == token.id() && row.ok == 0)
        {
            Token::Line
        } else {
            token
        }
    }
    pub fn series_text(&self, index: u8) -> TextChoice {
        match crate::r#gen::seriestext::SERIES_TEXT
            .iter()
            .find(|row| row.theme == self.name && row.series == index % 12)
            .map(|row| row.choice)
        {
            Some(1) => TextChoice::Background,
            Some(2) => TextChoice::Plate,
            _ => TextChoice::Foreground,
        }
    }
}
#[cfg(test)]
mod tests;
