//! Iconify icon packs and icon placement. Only `<path d>` bodies with the commands
//! `MLHVCSQTZ` are drawn; every other body is unsupported and draws `unknown`.

mod architecture;
mod body;
mod json;
mod path;
mod unknown;

use std::collections::BTreeMap;

use crate::diag::{Diagnostic, Severity};
use crate::error::IconPackError;
use crate::geom::{Point, Rect};
use crate::scene::{
    Group, GroupRole, Item, ItemClass, PathItem, Profile, Scene, Shape, ShapeStyle, SymbolName,
    SymbolRefItem,
};
use crate::source::Span;
use json::Json;

const BOX: i32 = 1536;
const HALF_BOX: i32 = BOX / 2;
const UNKNOWN_NAME: &str = "unknown";
const BUILTIN_NAMES: [&str; 5] = ["cloud", "database", "disk", "internet", "server"];
const DEFAULT_SIZE: i64 = 16;
const MAX_DIMENSION_DIGITS: usize = 6;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Icon {
    body: String,
    left: i64,
    top: i64,
    width: i64,
    height: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IconPack {
    prefix: String,
    icons: BTreeMap<String, Icon>,
}

impl IconPack {
    pub fn prefix(&self) -> &str {
        &self.prefix
    }

    pub fn contains(&self, name: &str) -> bool {
        self.icons.contains_key(name)
    }

    fn find(&self, reference: &str) -> Option<&Icon> {
        let (prefix, name) = reference.split_once(':')?;
        if prefix != self.prefix {
            return None;
        }
        self.icons.get(name)
    }
}

fn malformed(reason: impl Into<String>) -> IconPackError {
    IconPackError::Malformed {
        reason: reason.into(),
    }
}

fn dimension(value: Option<&Json>, key: &str) -> Result<Option<i64>, IconPackError> {
    match value {
        None => Ok(None),
        Some(Json::Number(text)) => Some(text.as_str())
            .filter(|text| has_plain_dimension_digits(text))
            .and_then(path::fixed)
            .map(Some)
            .ok_or_else(|| malformed(format!("{key} is out of range"))),
        Some(_) => Err(malformed(format!("{key} must be a number"))),
    }
}

fn has_plain_dimension_digits(text: &str) -> bool {
    let unsigned = text.strip_prefix('-').unwrap_or(text);
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    !text.contains(['e', 'E'])
        && whole.len() <= MAX_DIMENSION_DIGITS
        && fraction.len() <= MAX_DIMENSION_DIGITS
}

struct Defaults {
    left: i64,
    top: i64,
    width: i64,
    height: i64,
}

fn read_icon(name: &str, value: &Json, defaults: &Defaults) -> Result<Icon, IconPackError> {
    if !matches!(value, Json::Object(_)) {
        return Err(malformed(format!("icon {name} must be an object")));
    }
    let Some(Json::String(body)) = value.member("body") else {
        return Err(malformed(format!("icon {name} needs a string body")));
    };
    let member = |key: &str, fallback: i64| -> Result<i64, IconPackError> {
        Ok(dimension(value.member(key), key)?.unwrap_or(fallback))
    };
    let width = member("width", defaults.width)?;
    let height = member("height", defaults.height)?;
    if width <= 0 || height <= 0 {
        return Err(malformed(format!("icon {name} needs a positive size")));
    }
    Ok(Icon {
        body: body.clone(),
        left: member("left", defaults.left)?,
        top: member("top", defaults.top)?,
        width,
        height,
    })
}

pub fn parse_icon_pack(source: &str) -> Result<IconPack, IconPackError> {
    let root = json::parse(source).map_err(|error| malformed(error.to_string()))?;
    if !matches!(root, Json::Object(_)) {
        return Err(malformed("the root must be an object"));
    }
    let Some(Json::String(prefix)) = root.member("prefix") else {
        return Err(malformed("missing string prefix"));
    };
    if prefix.is_empty() {
        return Err(malformed("the prefix must not be empty"));
    }
    let Some(Json::Object(icons)) = root.member("icons") else {
        return Err(malformed("missing icons object"));
    };
    let defaults = Defaults {
        left: dimension(root.member("left"), "left")?.unwrap_or(0),
        top: dimension(root.member("top"), "top")?.unwrap_or(0),
        width: dimension(root.member("width"), "width")?.unwrap_or(DEFAULT_SIZE * path::SCALE),
        height: dimension(root.member("height"), "height")?.unwrap_or(DEFAULT_SIZE * path::SCALE),
    };
    if defaults.width <= 0 || defaults.height <= 0 {
        return Err(malformed("the default size must be positive"));
    }
    let mut table = BTreeMap::new();
    for (name, value) in icons {
        table.insert(name.clone(), read_icon(name, value, &defaults)?);
    }
    Ok(IconPack {
        prefix: prefix.clone(),
        icons: table,
    })
}

/// Where a reference draws its icon, and which names it resolves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Placement {
    /// Centred on the top edge of the owner's box; only qualified pack names resolve.
    Edge,
    /// Centred in the outline of the owner's node; built-in names resolve too.
    Service,
    /// Inset at the top left of the owner's group frame; built-in names resolve too.
    Badge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IconRef<'a> {
    pub owner: &'a str,
    pub name: &'a str,
    pub span: Span,
    pub placement: Placement,
}

fn drawn(icon: &Icon, origin: Point) -> Option<Vec<Item>> {
    if icon.width.max(icon.height) < path::SCALE {
        return None;
    }
    let frame = path::Frame {
        left: icon.left,
        top: icon.top,
        width: icon.width,
        height: icon.height,
        origin,
    };
    body::path_data(&icon.body)?
        .iter()
        .map(|data| {
            path::convert(data, &frame).map(|commands| {
                Item::Path(PathItem {
                    shape: Shape::plain(ShapeStyle::Ink),
                    commands,
                })
            })
        })
        .collect()
}

fn symbol_cell(symbol: &'static str, at: Point, style: ShapeStyle) -> Vec<Item> {
    SymbolName::new(symbol)
        .map(|symbol| vec![Item::SymbolRef(SymbolRefItem { symbol, at, style })])
        .unwrap_or_default()
}

fn missing(reference: &IconRef<'_>) -> Diagnostic {
    Diagnostic {
        code: "icon/pack-missing",
        severity: Severity::Info,
        message: format!("icon {} is not available", reference.name),
        span: reference.span,
        related: Vec::new(),
        help: "The diagram draws the unknown icon in its place.".into(),
        fixes: Vec::new(),
    }
}

/// The two places one icon can start: the top-left corner of its 24 px box in the vector
/// profile, and its cell in the cell profile.
#[derive(Debug, Clone, Copy)]
struct Origins {
    vector: Point,
    cell: Point,
}

fn centred(rect: Rect) -> Origins {
    let cell = Point {
        x: rect.x + rect.w / 2,
        y: rect.y + rect.h / 2,
    };
    Origins {
        vector: Point {
            x: cell.x - HALF_BOX,
            y: cell.y - HALF_BOX,
        },
        cell,
    }
}

fn above(rect: Rect) -> Origins {
    let cell = Point {
        x: rect.x + rect.w / 2,
        y: rect.y,
    };
    Origins {
        vector: Point {
            x: cell.x - HALF_BOX,
            y: cell.y - HALF_BOX,
        },
        cell,
    }
}

fn inset(rect: Rect, profile: Profile) -> Origins {
    let key = format!("{}.architecture.title_inset", profile.as_str());
    let inset = crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map_or(0, |row| row.value);
    let corner = Point {
        x: rect.x + inset,
        y: rect.y + inset,
    };
    Origins {
        vector: corner,
        cell: corner,
    }
}

fn outline_rect(group: &Group) -> Option<Rect> {
    group.items.iter().find_map(|item| match item {
        Item::RoundRect(shape) => Some(shape.rect),
        Item::Rect(shape) => Some(shape.rect),
        _ => None,
    })
}

impl IconRef<'_> {
    /// The name that resolves: a flowchart icon resolves only as a qualified pack name.
    fn draw_name(&self) -> &str {
        match self.placement {
            Placement::Edge if !self.name.contains(':') => "",
            _ => self.name,
        }
    }

    fn role(&self) -> GroupRole {
        match self.placement {
            Placement::Badge => GroupRole::Group,
            Placement::Edge | Placement::Service => GroupRole::Node,
        }
    }

    fn origins(&self, rect: Rect, group: Option<&Group>, profile: Profile) -> Origins {
        match self.placement {
            Placement::Edge => above(rect),
            Placement::Service => centred(group.and_then(outline_rect).unwrap_or(rect)),
            Placement::Badge => inset(rect, profile),
        }
    }
}

/// Draws a built-in icon, or none when one of its coordinates leaves the int32 range.
fn built_in(name: &str, origins: Origins, profile: Profile) -> Option<Vec<Item>> {
    if profile == Profile::Cell {
        let symbol = BUILTIN_NAMES.iter().find(|known| **known == name)?;
        return Some(symbol_cell(symbol, origins.cell, ShapeStyle::InkLine));
    }
    let pieces = architecture::shapes(name)?;
    architecture::draw(&pieces, origins.vector)
}

pub(crate) fn items_for(
    reference: &IconRef<'_>,
    rect: Rect,
    profile: Profile,
    packs: &[IconPack],
) -> (Vec<Item>, Option<Diagnostic>) {
    items_at(reference, above(rect), profile, packs)
}

fn items_at(
    reference: &IconRef<'_>,
    origins: Origins,
    profile: Profile,
    packs: &[IconPack],
) -> (Vec<Item>, Option<Diagnostic>) {
    let name = reference.draw_name();
    if let Some(items) = built_in(name, origins, profile) {
        return (items, None);
    }
    let found = packs.iter().find_map(|pack| pack.find(name));
    if name == UNKNOWN_NAME {
        return (unknown_items(origins, profile), None);
    }
    let supported = found.and_then(|icon| drawn(icon, origins.vector));
    match (profile, supported) {
        (Profile::Vector, Some(items)) => (items, None),
        (Profile::Vector, None) => (unknown::glyph(origins.vector), Some(missing(reference))),
        (Profile::Cell, supported) => {
            let note = supported.is_none().then(|| missing(reference));
            (unknown_items(origins, profile), note)
        }
    }
}

fn unknown_items(origins: Origins, profile: Profile) -> Vec<Item> {
    match profile {
        Profile::Vector => unknown::glyph(origins.vector),
        Profile::Cell => symbol_cell(UNKNOWN_NAME, origins.cell, ShapeStyle::Ink),
    }
}

pub(crate) fn place(
    scene: &mut Scene,
    references: &[IconRef<'_>],
    packs: &[IconPack],
) -> Vec<Diagnostic> {
    let profile = scene.profile();
    let mut diagnostics = Vec::new();
    for reference in references {
        let Some(rect) = scene
            .boxes()
            .iter()
            .find(|b| b.id == reference.owner)
            .map(|b| b.rect)
        else {
            continue;
        };
        let role = reference.role();
        let group = scene
            .items_mut()
            .iter_mut()
            .find(|g| g.role == role && g.owner == reference.owner);
        let origins = reference.origins(rect, group.as_deref(), profile);
        let (items, diagnostic) = items_at(reference, origins, profile, packs);
        diagnostics.extend(diagnostic);
        let Some(group) = group else {
            continue;
        };
        let at = group
            .items
            .iter()
            .position(|item| item.class() != ItemClass::Shape)
            .unwrap_or(group.items.len());
        group.items.splice(at..at, items);
    }
    diagnostics
}

#[cfg(test)]
mod tests;
