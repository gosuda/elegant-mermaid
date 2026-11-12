use super::{Style, Token};
use crate::geom::{GeomError, Point};
pub const MASK_N: u8 = 1;
pub const MASK_E: u8 = 2;
pub const MASK_S: u8 = 4;
pub const MASK_W: u8 = 8;
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum Label {
    #[default]
    None,
    Cluster {
        text: String,
        width: u8,
    },
    Continuation,
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Cell {
    pub mask: u8,
    pub style: Style,
    pub dots: u8,
    pub label: Label,
    pub symbol: u32,
    pub token: Option<Token>,
    pub label_token: Option<Token>,
}
impl Cell {
    pub fn empty() -> Self {
        Self::default()
    }
}
pub fn max_token(a: Option<Token>, b: Option<Token>) -> Option<Token> {
    a.into_iter().chain(b).max_by_key(|t| t.rank())
}
pub fn merge_cell(a: &Cell, b: &Cell) -> Cell {
    Cell {
        mask: a.mask | b.mask,
        style: a.style.max(b.style),
        dots: a.dots | b.dots,
        label: a.label.clone(),
        symbol: a.symbol.max(b.symbol),
        token: max_token(a.token, b.token),
        label_token: a.label_token,
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Canvas {
    width: i32,
    height: i32,
    cells: Vec<Cell>,
}
impl Canvas {
    pub fn new(width: i32, height: i32) -> Result<Self, GeomError> {
        if width < 0 || height < 0 {
            return Err(GeomError::Domain);
        }
        let len = usize::try_from(i64::from(width) * i64::from(height))
            .map_err(|_| GeomError::Overflow)?;
        let mut cells = Vec::new();
        cells
            .try_reserve_exact(len)
            .map_err(|_| GeomError::Overflow)?;
        cells.resize(len, Cell::default());
        Ok(Self {
            width,
            height,
            cells,
        })
    }
    pub fn width(&self) -> i32 {
        self.width
    }
    pub fn height(&self) -> i32 {
        self.height
    }
    pub fn cells(&self) -> &[Cell] {
        &self.cells
    }
    fn index(&self, x: i32, y: i32) -> Option<usize> {
        if x < 0 || y < 0 || x >= self.width || y >= self.height {
            return None;
        }
        usize::try_from(i64::from(y) * i64::from(self.width) + i64::from(x)).ok()
    }
    pub fn cell(&self, x: i32, y: i32) -> Option<&Cell> {
        self.index(x, y).and_then(|i| self.cells.get(i))
    }
    pub fn put(&mut self, x: i32, y: i32, f: impl FnOnce(&mut Cell)) {
        if let Some(i) = self.index(x, y) {
            f(&mut self.cells[i])
        }
    }
    pub fn put_symbol(&mut self, x: i32, y: i32, s: u32) {
        self.put(x, y, |c| c.symbol = c.symbol.max(s))
    }
    pub fn merge_into(&mut self, x: i32, y: i32, c: &Cell) {
        self.put(x, y, |v| *v = merge_cell(v, c))
    }
    pub fn attach(&mut self, x: i32, y: i32, mask: u8, style: Style, token: Token) {
        self.put(x, y, |c| {
            c.mask |= mask;
            c.style = c.style.max(style);
            c.token = max_token(c.token, Some(token));
        })
    }
    pub fn put_segment(&mut self, a: Point, b: Point, style: Style, token: Token) {
        if a.y == b.y {
            for x in a.x.min(b.x)..a.x.max(b.x) {
                self.attach(x, a.y, MASK_E, style, token);
                self.attach(x + 1, a.y, MASK_W, style, token)
            }
        } else if a.x == b.x {
            for y in a.y.min(b.y)..a.y.max(b.y) {
                self.attach(a.x, y, MASK_S, style, token);
                self.attach(a.x, y + 1, MASK_N, style, token)
            }
        }
    }
    pub fn put_label(&mut self, x: i32, y: i32, text: &str, width: u8, token: Token) -> bool {
        if !(1..=2).contains(&width) || text.is_empty() {
            return false;
        }
        let Some(end) = x.checked_add(i32::from(width)) else {
            return false;
        };
        if x < 0
            || end > self.width
            || !(x..end).all(|c| {
                self.cell(c, y)
                    .is_some_and(|v| v.mask == 0 && v.symbol == 0 && v.label == Label::None)
            })
        {
            return false;
        }
        self.put(x, y, |c| {
            c.label = Label::Cluster {
                text: text.to_owned(),
                width,
            };
            c.label_token = Some(token)
        });
        if width == 2 {
            self.put(x + 1, y, |c| c.label = Label::Continuation)
        }
        true
    }
}
