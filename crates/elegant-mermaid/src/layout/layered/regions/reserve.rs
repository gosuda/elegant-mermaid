//! The reservation solver: group extents, rank spans, and region bands.
//! One `solve` run folds reservations into owning groups, resolves nested
//! extents bottom-up, shares spans top-down, and lays out every declared
//! region in order, leading and trailing empty ones included.

use super::LayoutError;

#[derive(Clone, Copy, Debug)]
pub struct RegionSet<'a> {
    pub parent: usize,
    pub regions: &'a [usize],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub first: i32,
    pub last: i32,
}

#[derive(Clone, Copy, Debug)]
pub struct Reservation {
    pub group: usize,
    pub left: i32,
    pub right: i32,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub struct Minima {
    pub border: i32,
    pub padding: i32,
    pub title: i32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Band {
    pub group: usize,
    pub left: i32,
    pub right: i32,
    pub span: Span,
}

/// Offsets are relative to the containing group's content origin. All ranks are
/// inclusive. A region's full width must constrain every rank in its span.
#[derive(Debug, PartialEq, Eq)]
pub struct Constraints {
    pub widths: Vec<i32>,
    pub spans: Vec<Option<Span>>,
    pub bands: Vec<Band>,
    pub origins: Vec<i32>,
}

pub(super) fn add(a: i32, b: i32) -> Result<i32, LayoutError> {
    a.checked_add(b).ok_or(LayoutError::Overflow)
}

fn merge(a: Option<Span>, b: Option<Span>) -> Option<Span> {
    match (a, b) {
        (Some(a), Some(b)) => Some(Span {
            first: a.first.min(b.first),
            last: a.last.max(b.last),
        }),
        (a, b) => a.or(b),
    }
}

pub(super) struct IndexedGroups {
    pub(super) children: Vec<Vec<usize>>,
    pub(super) order: Vec<usize>,
    by_parent: Vec<Option<usize>>,
    band_count: usize,
}

/// Child adjacency in declaration order, plus a preorder that reaches every
/// group exactly once. A parent outside the forest, a cycle, or an
/// unreachable group is Domain.
fn child_forest(parents: &[Option<usize>]) -> Result<(Vec<Vec<usize>>, Vec<usize>), LayoutError> {
    let n = parents.len();
    let mut children = vec![Vec::new(); n];
    let mut roots = Vec::new();
    for (child, parent) in parents.iter().enumerate() {
        match *parent {
            Some(parent) => {
                if parent >= n || parent == child {
                    return Err(LayoutError::Domain);
                }
                children[parent].push(child);
            }
            None => roots.push(child),
        }
    }
    let order = preorder(&children, roots, n)?;
    Ok((children, order))
}

fn preorder(
    children: &[Vec<usize>],
    roots: Vec<usize>,
    n: usize,
) -> Result<Vec<usize>, LayoutError> {
    let mut order = Vec::with_capacity(n);
    let mut stack = roots;
    while let Some(group) = stack.pop() {
        order.push(group);
        stack.extend(children[group].iter().copied());
    }
    if order.len() != n {
        return Err(LayoutError::Domain);
    }
    Ok(order)
}

/// At most one set per parent, and every region is a child of its set's
/// parent, owned by that set alone.
fn index_sets(
    parents: &[Option<usize>],
    sets: &[RegionSet<'_>],
) -> Result<(Vec<Option<usize>>, usize), LayoutError> {
    let n = parents.len();
    let mut owner = vec![None; n];
    let mut by_parent = vec![None; n];
    for (index, set) in sets.iter().enumerate() {
        if set.parent >= n || set.regions.is_empty() || by_parent[set.parent].is_some() {
            return Err(LayoutError::Domain);
        }
        by_parent[set.parent] = Some(index);
        for &region in set.regions {
            if region >= n || parents[region] != Some(set.parent) || owner[region].is_some() {
                return Err(LayoutError::Domain);
            }
            owner[region] = Some(index);
        }
    }
    let band_count = owner.iter().filter(|x| x.is_some()).count();
    Ok((by_parent, band_count))
}

pub(super) fn index_groups(
    parents: &[Option<usize>],
    sets: &[RegionSet<'_>],
) -> Result<IndexedGroups, LayoutError> {
    let (children, order) = child_forest(parents)?;
    let (by_parent, band_count) = index_sets(parents, sets)?;
    Ok(IndexedGroups {
        children,
        order,
        by_parent,
        band_count,
    })
}

/// Scratch buffers of one `solve` run. Each buffer is mutated only inside the
/// phase method that owns its invariant.
struct Workbook {
    children: Vec<Vec<usize>>,
    order: Vec<usize>,
    by_parent: Vec<Option<usize>>,
    band_count: usize,
    inset: i32,
    widths: Vec<i32>,
    spans: Vec<Option<Span>>,
    lefts: Vec<Option<i32>>,
    rights: Vec<Option<i32>>,
    origins: Vec<i32>,
    offsets: Vec<i32>,
}

impl Workbook {
    fn new(n: usize, indexed: IndexedGroups, inset: i32, minimum: i32) -> Self {
        let IndexedGroups {
            children,
            order,
            by_parent,
            band_count,
        } = indexed;
        Self {
            children,
            order,
            by_parent,
            band_count,
            inset,
            widths: vec![minimum; n],
            spans: vec![None; n],
            lefts: vec![None; n],
            rights: vec![None; n],
            origins: vec![inset; n],
            offsets: vec![0; n],
        }
    }

    /// Every reservation footprint folds into its owning group's extent. A
    /// reservation outside the forest, with an inverted interval, or with a
    /// rank span below zero is Domain, checked before any buffer changes.
    fn fold_reservations(&mut self, reservations: &[Reservation]) -> Result<(), LayoutError> {
        for reservation in reservations {
            self.validate_reservation(reservation)?;
            let g = reservation.group;
            self.lefts[g] =
                Some(self.lefts[g].map_or(reservation.left, |x| x.min(reservation.left)));
            self.rights[g] =
                Some(self.rights[g].map_or(reservation.right, |x| x.max(reservation.right)));
            self.spans[g] = merge(self.spans[g], Some(reservation.span));
        }
        Ok(())
    }

    fn validate_reservation(&self, reservation: &Reservation) -> Result<(), LayoutError> {
        let n = self.widths.len();
        if reservation.group >= n
            || reservation.left > reservation.right
            || reservation.span.first < 0
            || reservation.span.first > reservation.span.last
        {
            return Err(LayoutError::Domain);
        }
        Ok(())
    }

    /// Bottom-up over the preorder: each group absorbs its own reservation
    /// footprint, then its children's extents, then lays out its regions.
    fn resolve_nested_extents(&mut self, sets: &[RegionSet<'_>]) -> Result<(), LayoutError> {
        for position in (0..self.order.len()).rev() {
            let g = self.order[position];
            self.absorb_footprint(g)?;
            self.absorb_children(g)?;
            self.lay_out_regions(g, sets)?;
        }
        Ok(())
    }

    /// A group with reservations widens to its reservation footprint and
    /// re-anchors its content origin so the reserved interval lands at `inset`.
    fn absorb_footprint(&mut self, g: usize) -> Result<(), LayoutError> {
        if let (Some(left), Some(right)) = (self.lefts[g], self.rights[g]) {
            let width = right.checked_sub(left).ok_or(LayoutError::Overflow)?;
            self.widths[g] = self.widths[g].max(add(add(width, self.inset)?, self.inset)?);
            self.origins[g] = self.inset.checked_sub(left).ok_or(LayoutError::Overflow)?;
        }
        Ok(())
    }

    /// A parent covers each child on both sides and joins their rank spans.
    fn absorb_children(&mut self, g: usize) -> Result<(), LayoutError> {
        let mut span = self.spans[g];
        let mut width = self.widths[g];
        for &child in &self.children[g] {
            span = merge(span, self.spans[child]);
            width = width.max(add(add(self.widths[child], self.inset)?, self.inset)?);
        }
        self.spans[g] = span;
        self.widths[g] = width;
        Ok(())
    }

    /// Sibling regions run left to right after the leading inset with no gaps
    /// of their own; the row widens the parent.
    fn lay_out_regions(&mut self, g: usize, sets: &[RegionSet<'_>]) -> Result<(), LayoutError> {
        let Some(index) = self.by_parent[g] else {
            return Ok(());
        };
        let mut cursor = self.inset;
        for &region in sets[index].regions {
            self.offsets[region] = cursor;
            cursor = add(cursor, self.widths[region])?;
        }
        self.widths[g] = self.widths[g].max(add(cursor, self.inset)?);
        Ok(())
    }

    /// Top-down: all regions of one set share one rank span, the union of
    /// their own spans, falling back to the parent's, then to rank zero.
    fn share_common_spans(&mut self, sets: &[RegionSet<'_>]) {
        for &g in &self.order {
            let Some(index) = self.by_parent[g] else {
                continue;
            };
            let mut span = None;
            for &region in sets[index].regions {
                span = merge(span, self.spans[region]);
            }
            let common = span.or(self.spans[g]).unwrap_or(Span { first: 0, last: 0 });
            for &region in sets[index].regions {
                self.spans[region] = Some(common);
            }
        }
    }

    /// Bands are emitted in set and region declaration order; a region with
    /// no footprint of its own still appears, at its minimum width.
    fn bands(&self, sets: &[RegionSet<'_>]) -> Result<Vec<Band>, LayoutError> {
        let mut bands = Vec::with_capacity(self.band_count);
        for set in sets {
            for &region in set.regions {
                bands.push(Band {
                    group: region,
                    left: self.offsets[region],
                    right: add(self.offsets[region], self.widths[region])?,
                    span: self.spans[region].ok_or(LayoutError::Domain)?,
                });
            }
        }
        Ok(bands)
    }
}

/// The shared frame inset and the smallest legal frame width. A negative
/// minimum is Domain; the width never drops below one unit.
fn frame_minimum(minima: Minima) -> Result<(i32, i32), LayoutError> {
    if minima.border < 0 || minima.padding < 0 || minima.title < 0 {
        return Err(LayoutError::Domain);
    }
    let inset = add(minima.border, minima.padding)?;
    let minimum = add(add(inset, inset)?, minima.title)?.max(1);
    Ok((inset, minimum))
}

/// Validates the complete group forest, indexes reservations once, and solves
/// nested sets bottom-up. Empty metadata preserves the ordinary pipeline: the
/// caller must not apply this module's reservations when `sets` is empty.
pub fn solve(
    parents: &[Option<usize>],
    sets: &[RegionSet<'_>],
    reservations: &[Reservation],
    minima: Minima,
) -> Result<Constraints, LayoutError> {
    let (inset, minimum) = frame_minimum(minima)?;
    let mut book = Workbook::new(parents.len(), index_groups(parents, sets)?, inset, minimum);
    book.fold_reservations(reservations)?;
    book.resolve_nested_extents(sets)?;
    book.share_common_spans(sets);
    let bands = book.bands(sets)?;
    Ok(Constraints {
        widths: book.widths,
        spans: book.spans,
        bands,
        origins: book.origins,
    })
}
