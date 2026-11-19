import Elegant.GridArchitectureCellContracts
import Elegant.GridArchitectureRouteClearanceFacts

set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Kinds.Architecture

open Polyline
open Elegant
open Elegant.Grid.Architecture
open Elegant.Grid.Architecture.ClearanceAux

/-! ### Route segment clearance facts

The following lemmas are the route-side half of clause 6: every consecutive segment of
a master-computed `Grid.Architecture.path` misses the tile-fitted rectangle of every node whose resolved
cell differs from the cells of both route endpoints, and streets miss every
tile-fitted rectangle unconditionally. -/

/-- Rectangle of a span in raw geometry coordinates. -/
def RouteClearance.spanRect (s : Grid.Architecture.Span) : Rect := ⟨s.x0, s.y0, s.x1 - s.x0, s.y1 - s.y0⟩

private theorem RouteClearance.point_ne_of_xy (u v : Point) (h : u.x ≠ v.x ∨ u.y ≠ v.y) : u ≠ v := by
  intro heq
  rw [Point.mk.injEq] at heq
  rcases h with h | h
  · exact h heq.1
  · exact h heq.2

private theorem RouteClearance.xy_ne_of_point_ne (u v : Point) (h : u ≠ v) :
    u.x ≠ v.x ∨ u.y ≠ v.y := by
  by_cases hx : u.x = v.x
  · refine Or.inr fun hyy => h ?_
    cases u <;> cases v <;> rw [Point.mk.injEq]
    exact ⟨hx, hyy⟩
  · exact Or.inl fun hxx => hx hxx

/-- A `RouteClearance.HasSeg` pair of a list is a consecutive pair. -/
theorem RouteClearance.segMisses_of_allSegsMiss : ∀ (xs : List Point) (r : Rect),
    Polyline.allSegsMiss xs r → ∀ u v, RouteClearance.HasSeg xs u v → u ≠ v →
    Polyline.segMisses u v r := by
  intro xs
  induction xs with
  | nil => intro r _ u v h; cases h
  | cons a rest ih =>
    intro r hall u v hmem huv
    cases rest with
    | nil => nomatch hmem
    | cons b more =>
      obtain ⟨hhead, htail⟩ := hall
      cases hmem with
      | here _ _ _ => exact hhead
      | cons _ _ _ _ h' => exact ih r htail u v h' huv

/-- What the master proof needs from an assigned Grid.Architecture.port. The gutter lies on a street of
the Grid.Architecture.port node's own tile edge (`cell` or `cell + 1`), the stub is perpendicular to the
street, and both the Grid.Architecture.port point and the gutter point stay inside the tile expanded by
the gutter on every side. -/
structure RouteClearance.PortFacts (px py g : Int) (e : Grid.Architecture.PortEnd) : Prop where
  streetV : e.vertical = true →
    e.gutter.x = e.line ∧ (e.line = e.cell.x * px - g ∨ e.line = (e.cell.x + 1) * px - g)
  streetH : e.vertical = false →
    e.gutter.y = e.line ∧ (e.line = e.cell.y * py - g ∨ e.line = (e.cell.y + 1) * py - g)
  gutX : e.cell.x * px - g ≤ e.gutter.x ∧ e.gutter.x ≤ (e.cell.x + 1) * px - g
  gutY : e.cell.y * py - g ≤ e.gutter.y ∧ e.gutter.y ≤ (e.cell.y + 1) * py - g
  stubV : e.vertical = true → e.point.y = e.gutter.y
  stubH : e.vertical = false → e.point.x = e.gutter.x
  inX : e.cell.x * px - g ≤ e.point.x ∧ e.point.x ≤ (e.cell.x + 1) * px - g
  inY : e.cell.y * py - g ≤ e.point.y ∧ e.point.y ≤ (e.cell.y + 1) * py - g

/-- Two distinct cells differ in some coordinate. -/
private theorem RouteClearance.cell_xy_ne (u v : Grid.Architecture.Cell) (h : u ≠ v) :
    u.x ≠ v.x ∨ u.y ≠ v.y := by
  by_cases hx : u.x = v.x
  · refine Or.inr fun hy => h ?_
    cases u <;> cases v <;> simp_all
  · exact Or.inl hx

/-- Both stub segments of a vertical port miss every foreign tile-bounded box. -/
private theorem RouteClearance.stubHseg_clear (px py g : Int) (u : Grid.Architecture.PortEnd)
    (rect : Rect) (colF rowF : Int)
    (uv : u.vertical = true) (hu : RouteClearance.PortFacts px py g u)
    (hdiff : colF ≠ u.cell.x ∨ rowF ≠ u.cell.y)
    (hb : RouteClearance.BoxBounds px py g rect colF rowF) :
    Polyline.segMisses u.point u.gutter rect ∧
      Polyline.segMisses u.gutter u.point rect := by
  obtain ⟨hX1, hX2⟩ := RouteClearance.PortFacts.inX hu
  obtain ⟨hY1, hY2⟩ := RouteClearance.PortFacts.inY hu
  obtain ⟨hgX1, hgX2⟩ := RouteClearance.PortFacts.gutX hu
  obtain ⟨hgY1, hgY2⟩ := RouteClearance.PortFacts.gutY hu
  have hstub := RouteClearance.PortFacts.stubV hu uv
  constructor
  · refine RouteClearance.tile_hseg_misses px py g u.cell.x u.cell.y u.point u.gutter
      rect colF rowF hstub (by omega) (by omega) ?_ ?_ hdiff hb
    · simp only [Int.min_def]; split <;> omega
    · simp only [Int.max_def]; split <;> omega
  · refine RouteClearance.tile_hseg_misses px py g u.cell.x u.cell.y u.gutter u.point
      rect colF rowF hstub.symm (by omega) (by omega) ?_ ?_ hdiff hb
    · simp only [Int.min_def]; split <;> omega
    · simp only [Int.max_def]; split <;> omega

/-- Both stub segments of a horizontal port miss every foreign tile-bounded box. -/
private theorem RouteClearance.stubVseg_clear (px py g : Int) (u : Grid.Architecture.PortEnd)
    (rect : Rect) (colF rowF : Int)
    (uv : u.vertical = false) (hu : RouteClearance.PortFacts px py g u)
    (hdiff : colF ≠ u.cell.x ∨ rowF ≠ u.cell.y)
    (hb : RouteClearance.BoxBounds px py g rect colF rowF) :
    Polyline.segMisses u.point u.gutter rect ∧
      Polyline.segMisses u.gutter u.point rect := by
  obtain ⟨hX1, hX2⟩ := RouteClearance.PortFacts.inX hu
  obtain ⟨hY1, hY2⟩ := RouteClearance.PortFacts.inY hu
  obtain ⟨hgX1, hgX2⟩ := RouteClearance.PortFacts.gutX hu
  obtain ⟨hgY1, hgY2⟩ := RouteClearance.PortFacts.gutY hu
  have hstub := RouteClearance.PortFacts.stubH hu uv
  constructor
  · refine RouteClearance.tile_vseg_misses px py g u.cell.x u.cell.y u.point u.gutter
      rect colF rowF hstub (by omega) (by omega) ?_ ?_ hdiff hb
    · simp only [Int.min_def]; split <;> omega
    · simp only [Int.max_def]; split <;> omega
  · refine RouteClearance.tile_vseg_misses px py g u.cell.x u.cell.y u.gutter u.point
      rect colF rowF hstub.symm (by omega) (by omega) ?_ ?_ hdiff hb
    · simp only [Int.min_def]; split <;> omega
    · simp only [Int.max_def]; split <;> omega
/-- A vertical segment on `u`'s tile street misses every foreign tile-bounded box. -/
private theorem RouteClearance.vstreetAt_clear (px py g : Int) (u : Grid.Architecture.PortEnd)
    (p q : Point) (rect : Rect) (colF rowF : Int)
    (hX : p.x = u.cell.x * px - g ∨ p.x = (u.cell.x + 1) * px - g)
    (hx : p.x = q.x)
    (hb : RouteClearance.BoxBounds px py g rect colF rowF) :
    Polyline.segMisses p q rect := by
  rcases hX with h | h
  · exact RouteClearance.vstreet_misses px py g u.cell.x p q rect colF rowF hx h hb
  · exact RouteClearance.vstreet_misses px py g (u.cell.x + 1) p q rect colF rowF hx h hb

/-- A horizontal segment on `u`'s tile street misses every foreign tile-bounded box. -/
private theorem RouteClearance.hstreetAt_clear (px py g : Int) (u : Grid.Architecture.PortEnd)
    (p q : Point) (rect : Rect) (colF rowF : Int)
    (hY : p.y = u.cell.y * py - g ∨ p.y = (u.cell.y + 1) * py - g)
    (hy : p.y = q.y)
    (hb : RouteClearance.BoxBounds px py g rect colF rowF) :
    Polyline.segMisses p q rect := by
  rcases hY with h | h
  · exact RouteClearance.hstreet_misses px py g u.cell.y p q rect colF rowF hy h hb
  · exact RouteClearance.hstreet_misses px py g (u.cell.y + 1) p q rect colF rowF hy h hb

/-- Every Grid.Architecture.port satisfies the Grid.Architecture.port facts relative to its node's tile-bounded box. -/
theorem RouteClearance.port_facts (p : Grid.Architecture.GeometryParams) (pitch : Grid.Architecture.Pitch) (node : Grid.Architecture.Node) (box icon : Grid.Architecture.Span)
    (position : Grid.Architecture.Cell) (s : Grid.Architecture.Side) (i k : Nat)
    (hb : RouteClearance.BoxBounds pitch.x pitch.y p.gutter (RouteClearance.spanRect box) position.x position.y)
    (boundary : Grid.Architecture.SpanBoundary (Grid.Architecture.port p pitch node box icon position s i k).point box) :
    RouteClearance.PortFacts pitch.x pitch.y p.gutter
      (Grid.Architecture.port p pitch node box icon position s i k) := by
  have gnn := RouteClearance.BoxBounds.gNonneg hb
  have pxp := RouteClearance.BoxBounds.pxPos hb
  have pyp := RouteClearance.BoxBounds.pyPos hb
  have bx := RouteClearance.BoxBounds.x0ge hb
  have bx1 := RouteClearance.BoxBounds.x1le hb
  have by_ := RouteClearance.BoxBounds.y0ge hb
  have by1 := RouteClearance.BoxBounds.y1le hb
  simp only [RouteClearance.spanRect] at bx bx1 by_ by1
  have h0 := boundary.1
  have h1 := boundary.2.1
  have h2 := boundary.2.2.1
  have h3 := boundary.2.2.2.1
  revert h0 h1 h2 h3
  cases s with
  | top =>
    intro h0 h1 h2 h3
    simp only [Grid.Architecture.port] at h0 h1 h2 h3 ⊢
    refine ⟨fun h => Bool.noConfusion h, fun _ => ⟨rfl, Or.inl rfl⟩, ?_, ?_,
      fun h => Bool.noConfusion h, fun _ => rfl, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
  | bottom =>
    intro h0 h1 h2 h3
    simp only [Grid.Architecture.port] at h0 h1 h2 h3 ⊢
    refine ⟨fun h => Bool.noConfusion h, fun _ => ⟨rfl, Or.inr rfl⟩, ?_, ?_,
      fun h => Bool.noConfusion h, fun _ => rfl, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
  | left =>
    intro h0 h1 h2 h3
    simp only [Grid.Architecture.port] at h0 h1 h2 h3 ⊢
    refine ⟨fun _ => ⟨rfl, Or.inl rfl⟩, fun h => Bool.noConfusion h, ?_, ?_,
      fun _ => rfl, fun h => Bool.noConfusion h, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
  | right =>
    intro h0 h1 h2 h3
    simp only [Grid.Architecture.port] at h0 h1 h2 h3 ⊢
    refine ⟨fun _ => ⟨rfl, Or.inr rfl⟩, fun h => Bool.noConfusion h, ?_, ?_,
      fun _ => rfl, fun h => Bool.noConfusion h, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
/-- Every consecutive segment of a route misses the tile-fitted rectangle of every node
whose resolved cell differs from the cells of both route endpoints. Streets miss every
tile-fitted rectangle unconditionally. -/
theorem RouteClearance.route_misses_foreign_box
    (p : Grid.Architecture.GeometryParams) (pitch : Grid.Architecture.Pitch)
    (resolved : Grid.Architecture.Resolved) (nodes : List Grid.Architecture.Node)
    (geo : Grid.Architecture.Geometry)
    (f : Nat) (_fbound : f < nodes.length)
    (hfb : RouteClearance.BoxBounds pitch.x pitch.y p.gutter
      (RouteClearance.spanRect (geo.boxes.getD f default))
      (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y)
    (fdistinct : ∀ n, n < nodes.length → n ≠ f →
      resolved.nodes.getD n default ≠ resolved.nodes.getD f default)
    (a b : Grid.Architecture.PortEnd)
    (haF : RouteClearance.PortFacts pitch.x pitch.y p.gutter a)
    (haIdx : ∃ n, n < nodes.length ∧ n ≠ f ∧ a.cell = resolved.nodes.getD n default)
    (hbF : RouteClearance.PortFacts pitch.x pitch.y p.gutter b)
    (hbIdx : ∃ n, n < nodes.length ∧ n ≠ f ∧ b.cell = resolved.nodes.getD n default) :
    Polyline.allSegsMiss (Grid.Architecture.path p pitch a b) (RouteClearance.spanRect (geo.boxes.getD f default)) := by
  obtain ⟨aN, aNb, aNf, haCell⟩ := haIdx
  obtain ⟨bN, bNb, bNf, hbCell⟩ := hbIdx
  have hdA : resolved.nodes.getD f default ≠ a.cell := by
    rw [haCell]; exact Ne.symm (fdistinct aN aNb aNf)
  have hdB : resolved.nodes.getD f default ≠ b.cell := by
    rw [hbCell]; exact Ne.symm (fdistinct bN bNb bNf)
  have hdiffA := RouteClearance.cell_xy_ne _ _ hdA
  have hdiffB := RouteClearance.cell_xy_ne _ _ hdB
  obtain ⟨haX1, haX2⟩ := RouteClearance.PortFacts.inX haF
  obtain ⟨haY1, haY2⟩ := RouteClearance.PortFacts.inY haF
  obtain ⟨hbX1, hbX2⟩ := RouteClearance.PortFacts.inX hbF
  obtain ⟨hbY1, hbY2⟩ := RouteClearance.PortFacts.inY hbF
  obtain ⟨hgaX1, hgaX2⟩ := RouteClearance.PortFacts.gutX haF
  obtain ⟨hgaY1, hgaY2⟩ := RouteClearance.PortFacts.gutY haF
  obtain ⟨hgbX1, hgbX2⟩ := RouteClearance.PortFacts.gutX hbF
  obtain ⟨hgbY1, hgbY2⟩ := RouteClearance.PortFacts.gutY hbF
  refine RouteClearance.allSegsMiss_of_hasSeg _ _ (RouteClearance.compactPoints_adjNe _) ?_
  simp only [Grid.Architecture.path]
  intro u v hmem huv
  have hraw := RouteClearance.hasSeg_compact _ _ _ hmem huv
  by_cases h1 : (decide (a.vertical = b.vertical) && (a.line == b.line)) = true
  · simp only [h1, ↓reduceIte] at hraw
    simp only [Bool.and_eq_true] at h1
    have haeq : a.vertical = b.vertical := of_decide_eq_true h1.1
    have hle : a.line = b.line := by simpa using h1.2
    cases ha : a.vertical
    · have hbv : b.vertical = false := by rw [← haeq]; exact ha
      have gA := RouteClearance.PortFacts.streetH haF ha
      have gB := RouteClearance.PortFacts.streetH hbF hbv
      have haye : a.gutter.y = b.gutter.y := by rw [gA.1, gB.1]; exact hle
      refine RouteClearance.segMisses_of_allSegsMiss
        [a.point, a.gutter, b.gutter, b.point]
        (RouteClearance.spanRect (geo.boxes.getD f default))
        ⟨(RouteClearance.stubVseg_clear pitch.x pitch.y p.gutter a
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          ha haF hdiffA hfb).1,
        RouteClearance.hstreetAt_clear pitch.x pitch.y p.gutter a a.gutter b.gutter
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          (by rw [gA.1]; exact gA.2) haye hfb,
        (RouteClearance.stubVseg_clear pitch.x pitch.y p.gutter b
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          hbv hbF hdiffB hfb).2,
        trivial⟩ u v hraw huv
    · have hbv : b.vertical = true := by rw [← haeq]; exact ha
      have gA := RouteClearance.PortFacts.streetV haF ha
      have gB := RouteClearance.PortFacts.streetV hbF hbv
      have haxe : a.gutter.x = b.gutter.x := by rw [gA.1, gB.1]; exact hle
      refine RouteClearance.segMisses_of_allSegsMiss
        [a.point, a.gutter, b.gutter, b.point]
        (RouteClearance.spanRect (geo.boxes.getD f default))
        ⟨(RouteClearance.stubHseg_clear pitch.x pitch.y p.gutter a
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          ha haF hdiffA hfb).1,
        RouteClearance.vstreetAt_clear pitch.x pitch.y p.gutter a a.gutter b.gutter
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          (by rw [gA.1]; exact gA.2) haxe hfb,
        (RouteClearance.stubHseg_clear pitch.x pitch.y p.gutter b
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          hbv hbF hdiffB hfb).2,
        trivial⟩ u v hraw huv
  · simp only [h1, ↓reduceIte] at hraw
    by_cases h2 : (a.vertical && b.vertical) = true
    · simp only [h2, ↓reduceIte] at hraw
      simp only [Bool.and_eq_true] at h2
      obtain ⟨hav, hbv⟩ := h2
      have gA := RouteClearance.PortFacts.streetV haF hav
      have gB := RouteClearance.PortFacts.streetV hbF hbv
      refine RouteClearance.segMisses_of_allSegsMiss
        [a.point, a.gutter, ⟨a.line, a.cell.y * pitch.y - p.gutter⟩,
          ⟨b.line, a.cell.y * pitch.y - p.gutter⟩, b.gutter, b.point]
        (RouteClearance.spanRect (geo.boxes.getD f default))
        ⟨(RouteClearance.stubHseg_clear pitch.x pitch.y p.gutter a
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          hav haF hdiffA hfb).1,
        RouteClearance.vstreetAt_clear pitch.x pitch.y p.gutter a a.gutter
          ⟨a.line, a.cell.y * pitch.y - p.gutter⟩
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          (by rw [gA.1]; exact gA.2) gA.1 hfb,
        RouteClearance.hstreetAt_clear pitch.x pitch.y p.gutter a
          ⟨a.line, a.cell.y * pitch.y - p.gutter⟩
          ⟨b.line, a.cell.y * pitch.y - p.gutter⟩
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          (Or.inl rfl) rfl hfb,
        RouteClearance.vstreetAt_clear pitch.x pitch.y p.gutter b
          ⟨b.line, a.cell.y * pitch.y - p.gutter⟩ b.gutter
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          (by show b.line = b.cell.x * pitch.x - p.gutter ∨
            b.line = (b.cell.x + 1) * pitch.x - p.gutter; exact gB.2)
          (by rw [gB.1]) hfb,
        (RouteClearance.stubHseg_clear pitch.x pitch.y p.gutter b
          (RouteClearance.spanRect (geo.boxes.getD f default))
          (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
          hbv hbF hdiffB hfb).2,
        trivial⟩ u v hraw huv
    · simp only [h2, ↓reduceIte] at hraw
      by_cases h3 : (!a.vertical && !b.vertical) = true
      · simp only [h3, ↓reduceIte] at hraw
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h3
        obtain ⟨hav, hbv⟩ := h3
        have gA := RouteClearance.PortFacts.streetH haF hav
        have gB := RouteClearance.PortFacts.streetH hbF hbv
        refine RouteClearance.segMisses_of_allSegsMiss
          [a.point, a.gutter, ⟨a.cell.x * pitch.x - p.gutter, a.line⟩,
            ⟨a.cell.x * pitch.x - p.gutter, b.line⟩, b.gutter, b.point]
          (RouteClearance.spanRect (geo.boxes.getD f default))
          ⟨(RouteClearance.stubVseg_clear pitch.x pitch.y p.gutter a
            (RouteClearance.spanRect (geo.boxes.getD f default))
            (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
            hav haF hdiffA hfb).1,
          RouteClearance.hstreetAt_clear pitch.x pitch.y p.gutter a a.gutter
            ⟨a.cell.x * pitch.x - p.gutter, a.line⟩
            (RouteClearance.spanRect (geo.boxes.getD f default))
            (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
            (by rw [gA.1]; exact gA.2) gA.1 hfb,
          RouteClearance.vstreetAt_clear pitch.x pitch.y p.gutter a
            ⟨a.cell.x * pitch.x - p.gutter, a.line⟩
            ⟨a.cell.x * pitch.x - p.gutter, b.line⟩
            (RouteClearance.spanRect (geo.boxes.getD f default))
            (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
            (Or.inl rfl) rfl hfb,
          RouteClearance.hstreetAt_clear pitch.x pitch.y p.gutter b
            ⟨a.cell.x * pitch.x - p.gutter, b.line⟩ b.gutter
            (RouteClearance.spanRect (geo.boxes.getD f default))
            (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
            (by show b.line = b.cell.y * pitch.y - p.gutter ∨
              b.line = (b.cell.y + 1) * pitch.y - p.gutter; exact gB.2)
            (by rw [gB.1]) hfb,
          (RouteClearance.stubVseg_clear pitch.x pitch.y p.gutter b
            (RouteClearance.spanRect (geo.boxes.getD f default))
            (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
            hbv hbF hdiffB hfb).2,
          trivial⟩ u v hraw huv
      · simp only [h3, ↓reduceIte] at hraw
        by_cases h4 : a.vertical = true
        · simp only [h4, ↓reduceIte] at hraw
          have hav : a.vertical = true := h4
          have hbv : b.vertical = false := by
            cases hb : b.vertical
            · rfl
            · exfalso
              rw [hav, hb] at h2
              exact h2 rfl
          have gA := RouteClearance.PortFacts.streetV haF hav
          have gB := RouteClearance.PortFacts.streetH hbF hbv
          refine RouteClearance.segMisses_of_allSegsMiss
            [a.point, a.gutter, ⟨a.line, b.line⟩, b.gutter, b.point]
            (RouteClearance.spanRect (geo.boxes.getD f default))
            ⟨(RouteClearance.stubHseg_clear pitch.x pitch.y p.gutter a
              (RouteClearance.spanRect (geo.boxes.getD f default))
              (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
              hav haF hdiffA hfb).1,
            RouteClearance.vstreetAt_clear pitch.x pitch.y p.gutter a a.gutter
              ⟨a.line, b.line⟩
              (RouteClearance.spanRect (geo.boxes.getD f default))
              (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
              (by rw [gA.1]; exact gA.2) gA.1 hfb,
            RouteClearance.hstreetAt_clear pitch.x pitch.y p.gutter b
              ⟨a.line, b.line⟩ b.gutter
              (RouteClearance.spanRect (geo.boxes.getD f default))
              (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
              (by show b.line = b.cell.y * pitch.y - p.gutter ∨
                b.line = (b.cell.y + 1) * pitch.y - p.gutter; exact gB.2)
              (by rw [gB.1]) hfb,
            (RouteClearance.stubVseg_clear pitch.x pitch.y p.gutter b
              (RouteClearance.spanRect (geo.boxes.getD f default))
              (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
              hbv hbF hdiffB hfb).2,
            trivial⟩ u v hraw huv
        · simp only [h4, ↓reduceIte] at hraw
          have hav : a.vertical = false := by
            cases ha2 : a.vertical
            · rfl
            · exfalso; exact h4 ha2
          have hbv : b.vertical = true := by
            cases hb2 : b.vertical
            · exfalso
              rw [hav, hb2] at h3
              exact h3 rfl
            · rfl
          have gA := RouteClearance.PortFacts.streetH haF hav
          have gB := RouteClearance.PortFacts.streetV hbF hbv
          refine RouteClearance.segMisses_of_allSegsMiss
            [a.point, a.gutter, ⟨b.line, a.line⟩, b.gutter, b.point]
            (RouteClearance.spanRect (geo.boxes.getD f default))
            ⟨(RouteClearance.stubVseg_clear pitch.x pitch.y p.gutter a
              (RouteClearance.spanRect (geo.boxes.getD f default))
              (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
              hav haF hdiffA hfb).1,
            RouteClearance.hstreetAt_clear pitch.x pitch.y p.gutter a a.gutter
              ⟨b.line, a.line⟩
              (RouteClearance.spanRect (geo.boxes.getD f default))
              (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
              (by rw [gA.1]; exact gA.2) gA.1 hfb,
            RouteClearance.vstreetAt_clear pitch.x pitch.y p.gutter b
              ⟨b.line, a.line⟩ b.gutter
              (RouteClearance.spanRect (geo.boxes.getD f default))
              (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
              (by show b.line = b.cell.x * pitch.x - p.gutter ∨
                b.line = (b.cell.x + 1) * pitch.x - p.gutter; exact gB.2)
              (by rw [gB.1]) hfb,
            (RouteClearance.stubHseg_clear pitch.x pitch.y p.gutter b
              (RouteClearance.spanRect (geo.boxes.getD f default))
              (resolved.nodes.getD f default).x (resolved.nodes.getD f default).y
              hbv hbF hdiffB hfb).2,
            trivial⟩ u v hraw huv

/-- `mapM` point lookup: the `i`-th output is the image of the `i`-th input. -/
private theorem mapM_at {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    (i : Nat) (hi : i < xs.length) :
    ∃ hy : i < ys.length, f xs[i] = .ok ys[i] := by
  obtain ⟨hlen, hpairs⟩ := Elegant.Grid.mapM_ok_pairs xs ys h
  have hy : i < ys.length := by omega
  exact ⟨hy, hpairs xs[i] ys[i] (by
    apply List.mem_iff_getElem.mpr
    refine ⟨i, ?_, ?_⟩
    · simp only [List.length_zip]
      omega
    · simp only [List.getElem_zip])⟩

/-- A successfully translated route list is the pointwise translation image. -/
private theorem translatePoint_map (dx dy : Int) (xs ys : List Point)
    (h : xs.mapM (Grid.Architecture.translatePoint dx dy) = .ok ys) :
    ys = xs.map (fun v => (⟨v.x + dx, v.y + dy⟩ : Point)) := by
  have hlen := (Elegant.Grid.mapM_ok_pairs xs ys h).1
  apply List.ext_getElem
  · simp only [List.length_map]
    exact hlen.symm
  · intro _i _hi hj
    have hx : _i < xs.length := by simpa only [List.length_map] using hj
    obtain ⟨_hy, hpoint⟩ := mapM_at h _i hx
    obtain ⟨hxadd, hyadd⟩ :=
      Grid.Architecture.translatePoint_add dx dy xs[_i] ys[_i] hpoint
    simp only [List.getElem_map]
    rw [← hxadd, ← hyadd]

/-- The computed pitch never drops below the base pitch on either axis. -/
private theorem pitch_x_lower (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    p.pitchX ≤ (Grid.Architecture.pitch p nodes edgeLabels).x := by
  simp only [Grid.Architecture.pitch]
  split <;> omega

private theorem pitch_y_lower (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    p.pitchY ≤ (Grid.Architecture.pitch p nodes edgeLabels).y := by
  simp only [Grid.Architecture.pitch]
  omega

/-- The computed pitch's top inset is never negative. -/
private theorem pitch_top_nonneg (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    0 ≤ (Grid.Architecture.pitch p nodes edgeLabels).top := by
  simp only [Grid.Architecture.pitch]
  split <;> omega

/-- A tile-fitting node's dump rectangle stays inside its own pitch tile with gutter
clearance on the sides, which is exactly `RouteClearance.BoxBounds`. -/
private theorem node_box_bounds (p : Grid.Architecture.GeometryParams)
    (pitch : Grid.Architecture.Pitch) (nodeInput : List Grid.Architecture.Node)
    (groupInput : List Grid.Architecture.Group) (resolved : Grid.Architecture.Resolved)
    (n : Nat) (hn : n < nodeInput.length)
    (pxpos : 0 < pitch.x) (pypos : 0 < pitch.y) (g0 : 0 ≤ p.gutter)
    (_pth : 0 ≤ p.thickness)
    (fits : nodeTileFits p pitch (nodeInput.getD n default) = true)
    (jq : (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2)
    (ptop : 0 ≤ pitch.top) :
    RouteClearance.BoxBounds pitch.x pitch.y p.gutter
      (RouteClearance.spanRect
        ((Grid.Architecture.geometry p pitch nodeInput groupInput resolved).boxes.getD n default))
      (resolved.nodes.getD n default).x (resolved.nodes.getD n default).y := by
  have icon := Grid.Architecture.geometry_icon_at p pitch nodeInput groupInput resolved n hn
  have hbox := Grid.Architecture.geometry_box_at p pitch nodeInput groupInput resolved n hn
  rw [icon] at hbox
  simp only [Grid.Architecture.sized] at hbox
  unfold nodeTileFits at fits
  have hright : (resolved.nodes.getD n default).x * pitch.x + pitch.x =
      ((resolved.nodes.getD n default).x + 1) * pitch.x := by
    rw [Int.add_mul, Int.one_mul]
  have hrightY : (resolved.nodes.getD n default).y * pitch.y + pitch.y =
      ((resolved.nodes.getD n default).y + 1) * pitch.y := by
    rw [Int.add_mul, Int.one_mul]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
  obtain ⟨fits1, fits2⟩ := fits
  have hdecomp := Int.mul_fdiv_add_fmod (pitch.x - (nodeInput.getD n default).icon.w) 2
  have hmodnn := Int.fmod_nonneg_of_pos (pitch.x - (nodeInput.getD n default).icon.w)
    (show (0 : Int) < 2 by decide)
  have hmodlt := Int.fmod_lt_of_pos (pitch.x - (nodeInput.getD n default).icon.w)
    (show (0 : Int) < 2 by decide)
  rw [hbox]
  simp only [RouteClearance.spanRect]
  by_cases hj : (nodeInput.getD n default).junction = true
  · have hjq := jq hj
    simp only [hj, ↓reduceIte] at fits2 ⊢
    refine ⟨pxpos, pypos, g0, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
  · simp only [hj, Bool.false_eq_true, ↓reduceIte] at fits2 ⊢
    refine ⟨pxpos, pypos, g0, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega

/-- A port carries its endpoint node's resolved cell. -/
private theorem port_cell (p : Grid.Architecture.GeometryParams)
    (pitch : Grid.Architecture.Pitch) (node : Grid.Architecture.Node)
    (box icon : Grid.Architecture.Span) (position : Grid.Architecture.Cell)
    (s : Grid.Architecture.Side) (i k : Nat) :
    (Grid.Architecture.port p pitch node box icon position s i k).cell = position := by
  unfold Grid.Architecture.port
  cases s <;> rfl

/-- The head of a duplicate-free list differs from every tail element. -/
private theorem nodup_head_ne {α : Type} (x : α) (rest : List α)
    (hnd : (x :: rest).Nodup) (k : Nat) (hk : k < rest.length) :
    x ≠ rest.get ⟨k, hk⟩ :=
  fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ List.get_mem _ _)

/-- Distinct indices of a duplicate-free list hold distinct values. -/
private theorem nodup_getElem_ne {α : Type} {xs : List α} (hnd : xs.Nodup) :
    ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) (_hij : i < j),
      xs.get ⟨i, hi⟩ ≠ xs.get ⟨j, hj⟩ := by
  intro i j hi hj _hij
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x rest ih =>
      cases j with
      | zero => omega
      | succ l =>
          cases i with
          | zero => exact nodup_head_ne x rest hnd l (by simpa using hj)
          | succ k =>
              exact ih (List.nodup_cons.mp hnd).2 k l (by simpa using hi)
                (by simpa using hj) (by omega)

/-- The dot product is equivariant under a common translation. -/
private theorem dot_shift (nx ny dx dy x y : Int) :
    Polyline.dot nx ny ⟨x + dx, y + dy⟩ =
      Polyline.dot nx ny ⟨x, y⟩ + nx * dx + ny * dy := by
  simp only [Polyline.dot, Point.x, Point.y, Int.mul_add]
  omega

private theorem minCorner_shift (nx ny dx dy : Int) (r : Rect) :
    Polyline.minCorner nx ny ⟨r.x + dx, r.y + dy, r.w, r.h⟩ =
      Polyline.minCorner nx ny r + nx * dx + ny * dy := by
  unfold Polyline.minCorner
  simp only [Polyline.dot, Point.x, Point.y, Int.mul_add, Int.min_def, Int.max_def]
  omega

private theorem maxCorner_shift (nx ny dx dy : Int) (r : Rect) :
    Polyline.maxCorner nx ny ⟨r.x + dx, r.y + dy, r.w, r.h⟩ =
      Polyline.maxCorner nx ny r + nx * dx + ny * dy := by
  unfold Polyline.maxCorner
  simp only [Polyline.dot, Point.x, Point.y, Int.mul_add, Int.max_def, Int.min_def]
  omega

/-- `segMisses` is invariant under translating the segment and the rectangle by the
same offset. -/
private theorem segMisses_trans (dx dy : Int) (p q : Point) (r : Rect) :
    Polyline.segMisses p q r →
      Polyline.segMisses ⟨p.x + dx, p.y + dy⟩ ⟨q.x + dx, q.y + dy⟩
        ⟨r.x + dx, r.y + dy, r.w, r.h⟩ := by
  intro h
  unfold Polyline.segMisses at h ⊢
  simp only [Point.x, Point.y, Int.min_def, Int.max_def] at h ⊢
  rcases h with h | h | h | h | ⟨hne, hcmp⟩
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))
    · intro heq
      rw [Point.mk.injEq] at heq
      have hpq : p = q := by
        rw [Point.mk.injEq]
        constructor <;> omega
      exact hne hpq
    · rw [minCorner_shift, maxCorner_shift]
      have hnorm : ((p.y + dy) - (q.y + dy) : Int) = p.y - q.y := by omega
      have hnorm2 : ((q.x + dx) - (p.x + dx) : Int) = q.x - p.x := by omega
      rw [hnorm, hnorm2]
      have hpx : Polyline.dot (p.y - q.y) (q.x - p.x) ⟨p.x + dx, p.y + dy⟩ =
          Polyline.dot (p.y - q.y) (q.x - p.x) p +
            (p.y - q.y) * dx + (q.x - p.x) * dy :=
        dot_shift _ _ _ _ _ _
      rw [hpx]
      rcases hcmp with hcmp | hcmp
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)

/-- Segment-missing is preserved by translating a whole polyline and its rectangle. -/
private theorem allSegsMiss_translate (dx dy : Int) : ∀ (ps : List Point) (r : Rect),
    Polyline.allSegsMiss ps r →
      Polyline.allSegsMiss (ps.map (fun v => (⟨v.x + dx, v.y + dy⟩ : Point)))
        ⟨r.x + dx, r.y + dy, r.w, r.h⟩ := by
  intro ps r
  induction ps with
  | nil => intro _; simp [Polyline.allSegsMiss]
  | cons p rest ih =>
      cases rest with
      | nil => intro _; simp [Polyline.allSegsMiss]
      | cons q rest' =>
          intro h
          simp only [List.map_cons, Polyline.allSegsMiss]
          refine ⟨?_, ?_⟩
          · exact segMisses_trans dx dy p q r h.1
          · exact ih h.2

private theorem route_index_ports (p : Grid.Architecture.GeometryParams)
    (pitch : Grid.Architecture.Pitch) (nodeInput : List Grid.Architecture.Node)
    (edges : List Grid.Architecture.Edge) (resolved : Grid.Architecture.Resolved)
    (geo : Grid.Architecture.Geometry) (i : Nat) (hi : i < edges.length) :
    ∃ (iA kA iB kB : Nat) (a b : Grid.Architecture.PortEnd),
      a = Grid.Architecture.port p pitch (nodeInput.getD edges[i].a default)
        (geo.boxes.getD edges[i].a default) (geo.icons.getD edges[i].a default)
        (resolved.nodes.getD edges[i].a default) edges[i].sideA iA kA ∧
      b = Grid.Architecture.port p pitch (nodeInput.getD edges[i].b default)
        (geo.boxes.getD edges[i].b default) (geo.icons.getD edges[i].b default)
        (resolved.nodes.getD edges[i].b default) edges[i].sideB iB kB ∧
      (Grid.Architecture.routes p pitch nodeInput edges resolved geo).getD i [] =
        Grid.Architecture.path p pitch a b ∧
      iA ≤ kA ∧ iB ≤ kB := by
  have actual : edges[i]?.getD default = edges[i] := by
    rw [List.getElem?_eq_getElem hi, Option.getD_some]
  simp only [Grid.Architecture.routes, Grid.Architecture.assignPorts,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some,
    Nat.zero_add, actual, ↓reduceIte]
  exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, Grid.Architecture.assigned_slot_le_length _ _,
    Grid.Architecture.assigned_slot_le_length _ _⟩

/-- A rectangle is determined by its four components. -/
private theorem rect_eq_of_components (r : Rect) (x y w h : Int)
    (hx : r.x = x) (hy : r.y = y) (hw : r.w = w) (hh : r.h = h) :
    r = ⟨x, y, w, h⟩ := by
  cases r
  simp only at hx hy hw hh
  rw [hx, hy, hw, hh]
/-- A successful `parentIndex` lookup admits only the root or an in-range group
index, the parent evidence required by `hierarchy_final_cells_unique`. -/
private theorem parentIndex_ok_admitted {groups : List ModelBox} {id : String}
    {p : Int} (h : parentIndex groups id = .ok p) :
    p = -1 ∨ ∃ i, i < groups.length ∧ p = Int.ofNat i := by
  unfold parentIndex at h
  by_cases he : id.isEmpty = true
  · simp only [he, ↓reduceIte, Except.ok.injEq] at h
    exact Or.inl h.symm
  · simp only [he, ↓reduceIte] at h
    cases hf : groups.findIdx? (fun b => b.id == id) with
    | none => rw [hf] at h; simp at h
    | some i =>
        rw [hf] at h
        simp at h
        have hi : i < groups.length :=
          (List.findIdx?_eq_some_iff_findIdx_eq.mp hf).1
        exact Or.inr ⟨i, hi, h.symm⟩

/-- `configInt` only returns integers that passed the nonnegative config guard. -/
private theorem configInt_value_nonneg (m : Model) (key : String) (v : Int)
    (h : configInt m key = some v) : 0 ≤ v := by
  unfold configInt at h
  cases hsrc : m.options.config.find? (fun q => q.1 == key) with
  | none => rw [hsrc] at h; cases h
  | some pair =>
      obtain ⟨k, cv⟩ := pair
      cases cv with
      | string s => rw [hsrc] at h; cases h
      | boolean b => rw [hsrc] at h; cases h
      | integer val =>
          rw [hsrc] at h
          change (if 0 ≤ val ∧ val ≤ I32_MAX then some val else none) = some v at h
          by_cases valid : 0 ≤ val ∧ val ≤ I32_MAX
          · rw [ite_eq_left valid] at h
            have same := Option.some.inj h
            rw [← same]
            exact valid.1
          · rw [ite_eq_right valid] at h
            cases h

/-- Residual executed-build facts for clause 6: for geometry parameters, a computed
pitch, a node input, and a resolved hierarchy, every node passes the tile-fit admission,
measured node extents are nonnegative, junction icons leave a nonnegative vertical
remainder in their tile, and the resolved cells are pairwise distinct with at least one
slot per node. These package the `archParams`/`archPitch` equality, the `nodeTileFits`
admission guard, the node-input decode, and `hierarchy_final_cells_unique` — executed
facts of the build pipeline, not clearance conclusions. -/
def ArchC6BuildFacts (p : Grid.Architecture.GeometryParams) (pitch : Grid.Architecture.Pitch)
    (nodeInput : List Grid.Architecture.Node) (resolved : Grid.Architecture.Resolved) :
    Prop :=
  (∀ n, n < nodeInput.length → nodeTileFits p pitch (nodeInput.getD n default) = true) ∧
    (∀ n, n < nodeInput.length →
      0 ≤ (nodeInput.getD n default).icon.w ∧
      0 ≤ (nodeInput.getD n default).icon.h ∧
      0 ≤ (nodeInput.getD n default).label.h) ∧
    (∀ n, n < nodeInput.length → (nodeInput.getD n default).junction = true →
      0 ≤ pitch.y - (nodeInput.getD n default).icon.h) ∧
    resolved.nodes.Nodup ∧ nodeInput.length ≤ resolved.nodes.length

/-- Clause 6: every route misses the interior of every exclusive box outside its scope.
Routes run through streets between pitch tiles, every exclusive box is a node box inside
its own tile, and a route only enters the tiles of its two endpoint nodes, whose ids
belong to the route scope. The residual executed-build
facts of `ArchC6BuildFacts` are derived from the `build_success` equations. -/
theorem architecture_c6 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : layout m = .ok result) :
    _root_.Validator.C6 result.scene.layoutDump := by
  obtain ⟨scene, capped, built, dump⟩ := public_layout_dump m result h
  rw [dump]
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := build_success m scene capped built
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  have hrole : ∀ b ∈ m.boxes, (b.role != .group || !b.exclusive) = true := by
    have hmw : modelWellFormed m = true := hwf
    simp only [modelWellFormed, Bool.and_eq_true] at hmw
    exact List.all_eq_true.mp hmw.2
  have hboxEq : scene.layoutDump.boxes = dumpBoxes := by rw [hscene]; rfl
  have hrouteEq : scene.layoutDump.routes = dumpRoutes := by rw [hscene]; rfl
  have hedgesLen : m.routes.length = edges.length :=
    (Elegant.Grid.mapM_ok_pairs _ _ hedges).1
  have hnodeLen : nodeInput.length = nodes.length := by
    have hc := (Elegant.Grid.mapM_ok_pairs _ _ hcaptions).1
    have hn := (Elegant.Grid.mapM_ok_pairs _ _ hnodeInput).1
    simp only [List.length_zip] at hn
    omega
  have hrawLen : rawRoutes.length = edges.length := by
    rw [hrawRoutes]
    simp only [Grid.Architecture.routes, Grid.Architecture.assignPorts,
      List.length_map, List.length_zipIdx]
  have hpxBase : 0 < LayoutConst.architecture_pitch_x.get profile := by
    cases profile <;> decide
  have hpyBase : 0 < LayoutConst.architecture_pitch_y.get profile := by
    cases profile <;> decide
  have hpPitchX : p.pitchX = LayoutConst.architecture_pitch_x.get profile := by rw [hp]
  have hpPitchY : p.pitchY = LayoutConst.architecture_pitch_y.get profile := by rw [hp]
  have hpxpos : 0 < pitch.x := by
    rw [hpitch]
    have hx := pitch_x_lower p nodeInput sizes
    rw [hpPitchX] at hx
    have hbase : 0 < p.pitchX := by rw [hpPitchX]; exact hpxBase
    omega
  have hpypos : 0 < pitch.y := by
    rw [hpitch]
    have hy := pitch_y_lower p nodeInput sizes
    rw [hpPitchY] at hy
    have hbase : 0 < p.pitchY := by rw [hpPitchY]; exact hpyBase
    omega
  have hptop : 0 ≤ pitch.top := by
    rw [hpitch]
    exact pitch_top_nonneg p nodeInput sizes
  have hgut : 0 ≤ p.gutter := by
    rw [hp]
    show 0 ≤ (if cell then (1 : Int) else 0)
    split <;> omega
  have hpth : 0 ≤ p.thickness := by
    rw [hp]
    show 0 ≤ thickness
    rw [hthickness]
    cases profile <;> decide
  have hp_eq : p = archParams m := by
    rw [hp]
    simp only [archParams, archIconWidth, archIconHeight,
      GeometryParams.mk.injEq]
    rw [← hprofile, ← hcell]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | rfl
        | exact hiw
        | exact hih
        | exact hlh
        | exact hinset
        | exact hthickness
  have hpitch_eq : pitch = archPitch m nodeInput edgeLines := by
    rw [hpitch, hsizes]
    simp only [archPitch, archLineHeight]
    rw [← hp_eq, ← hprofile, ← hlh]
  rw [← hp_eq, ← hpitch_eq] at hguard
  have hlh0 : 0 ≤ lh := by rw [hlh]; cases profile <;> decide
  have hiw0 : 0 < iw := by
    rw [hiw]
    cases hcfg : configInt m "iconSize" with
    | none =>
        show 0 < LayoutConst.architecture_icon_width.get profile
        cases profile <;> decide
    | some px =>
        have hpx0 : 0 ≤ px := configInt_value_nonneg m "iconSize" px hcfg
        show 0 < (if px > 0 then
          (if cell then max 1 (Int.fdiv (14*px+80) 160) else px*64)
          else LayoutConst.architecture_icon_width.get profile)
        split
        · rename_i hpx
          split
          · exact Int.lt_of_lt_of_le (by decide : (0 : Int) < 1)
              (Int.le_max_left _ _)
          · exact Int.mul_pos hpx (by decide)
        · cases profile <;> decide
  have hih0 : 0 < ih := by
    rw [hih]
    cases hcfg : configInt m "iconSize" with
    | none =>
        show 0 < LayoutConst.architecture_icon_height.get profile
        cases profile <;> decide
    | some px =>
        have hpx0 : 0 ≤ px := configInt_value_nonneg m "iconSize" px hcfg
        show 0 < (if px > 0 then
          (if cell then max 1 (Int.fdiv (6*px+80) 160) else px*64)
          else LayoutConst.architecture_icon_height.get profile)
        split
        · rename_i hpx
          split
          · exact Int.lt_of_lt_of_le (by decide : (0 : Int) < 1)
              (Int.le_max_left _ _)
          · exact Int.mul_pos hpx (by decide)
        · cases profile <;> decide
  have hjs0 : 0 < LayoutConst.architecture_junction_size.get profile := by
    cases profile <;> decide
  have hfits : ∀ n, n < nodeInput.length →
      nodeTileFits p pitch (nodeInput.getD n default) = true := by
    intro n hn
    have hmem : nodeInput.getD n default ∈ nodeInput := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
        Option.getD_some] using List.getElem_mem hn
    by_cases hfit : nodeTileFits p pitch (nodeInput.getD n default) = true
    · exact hfit
    · have hfalse : nodeTileFits p pitch (nodeInput.getD n default) = false :=
        Bool.eq_false_iff.mpr hfit
      have hany : nodeInput.any (fun n => !(nodeTileFits p pitch n)) = true :=
        List.any_eq_true.mpr ⟨nodeInput.getD n default, hmem, by rw [hfalse]; decide⟩
      exact absurd hany hguard
  have node_decode : ∀ n, n < nodeInput.length →
      (0 < (nodeInput.getD n default).icon.w) ∧
      (0 < (nodeInput.getD n default).icon.h) ∧
      (0 ≤ (nodeInput.getD n default).label.h) ∧
      ((nodeInput.getD n default).junction = true →
        (nodeInput.getD n default).icon.h =
          LayoutConst.architecture_junction_size.get profile) ∧
      ((nodeInput.getD n default).parent = -1 ∨
        ∃ i, i < groups.length ∧
          (nodeInput.getD n default).parent = Int.ofNat i) := by
    intro n hn
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hnodeInput).1
    have hxs : n < (nodes.zip captions).length := by rw [hnl]; exact hn
    have hzip : (nodes.zip captions).length =
        min nodes.length captions.length := by simp only [List.length_zip]
    have hnn : n < nodes.length := by omega
    have hnc : n < captions.length := by omega
    have hdec := mapM_pointwise hnodeInput n hxs hn
    simp only [List.getElem_zip] at hdec
    cases hp : parentIndex groups nodes[n].parent with
    | error err =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok parent =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        have hget : nodeInput.getD n default = nodeInput[n] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
            Option.getD_some]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hget, ← hdec]
          dsimp only
          split <;> first | exact hjs0 | exact hiw0
        · rw [hget, ← hdec]
          dsimp only
          split <;> first | exact hjs0 | exact hih0 | exact hiw0
        · rw [hget, ← hdec]
          show 0 ≤ min COORD_LIMIT (((captions[n]).length : Int) * lh)
          exact Int.le_min.mpr
            ⟨by decide, Int.mul_nonneg (Int.natCast_nonneg _) hlh0⟩
        · intro hj
          rw [hget, ← hdec] at hj ⊢
          dsimp only at hj ⊢
          simp only [hj, ↓reduceIte]
        · rw [hget, ← hdec]
          dsimp only
          exact parentIndex_ok_admitted hp
  have groupLen : groupInput.length = groups.length := by
    have hgl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have htit := (Elegant.Grid.mapM_ok_pairs _ _ htitles).1
    have hzl : (groups.zip titles).length =
        min groups.length titles.length := by simp only [List.length_zip]
    rw [htit] at hzl
    simp only [Nat.min_self] at hzl
    exact (hgl.symm.trans hzl).trans htit.symm
  have group_decode : ∀ g, g < groupInput.length →
      (groupInput.getD g default).parent = -1 ∨
        ∃ i, i < groups.length ∧
          (groupInput.getD g default).parent = Int.ofNat i := by
    intro g hg
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have hxs : g < (groups.zip titles).length := by rw [hnl]; exact hg
    have hzip : (groups.zip titles).length =
        min groups.length titles.length := by simp only [List.length_zip]
    have hgg : g < groups.length := by omega
    have hgt : g < titles.length := by omega
    have hdec := mapM_pointwise hgroupInput g hxs hg
    simp only [List.getElem_zip] at hdec
    cases hp : parentIndex groups groups[g].parent with
    | error err =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok parent =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        have hget : groupInput.getD g default = groupInput[g] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg,
            Option.getD_some]
        rw [hget, ← hdec]
        dsimp only
        exact parentIndex_ok_admitted hp
  have hg_eq : input.groups = groupInput := by rw [hinput]
  have hpar : input.parents = nodeInput.map (·.parent) := by rw [hinput]
  have ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k := by
    rw [hinput]
    intro k hk
    change (groupInput.getD k default).parent < Int.ofNat k
    apply Classical.byContradiction
    intro notEarlier
    have indexed : (groupInput.getD k default, k) ∈ groupInput.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        Option.getD_some]
    have hany : groupInput.zipIdx.any
        (fun q => decide (q.1.parent ≥ Int.ofNat q.2)) = true := by
      apply List.any_eq_true.mpr
      refine ⟨(groupInput.getD k default, k), indexed, ?_⟩
      simp only [decide_eq_true_eq]
      omega
    exact absurd hany hgroupOrder
  have groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent := by
    intro g hg
    have hg' : g < groupInput.length := by rw [← hg_eq]; exact hg
    rw [hg_eq]
    rcases group_decode g hg' with h | ⟨i, hi, heq⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, by rw [groupLen]; exact hi, heq⟩
  have hpad : 0 ≤ padding := by
    rw [hpadding]
    let value : Option Int :=
      match m.options.config.find? (fun q => q.1 == "padding") with
      | some (_, .integer v) =>
        if 0 ≤ v ∧ v ≤ I32_MAX then some v else none
      | _ => none
    change 0 ≤ (match value with
      | some px => if cell then Int.fdiv (2 * px + 20) 40 else px * 64
      | none => LayoutConst.architecture_padding.get profile)
    cases actual : value with
    | none =>
        change 0 ≤ LayoutConst.architecture_padding.get profile
        cases profile <;> decide
    | some px =>
        have hcfg : configInt m "padding" = some px := actual
        have hpx0 : 0 ≤ px := configInt_value_nonneg m "padding" px hcfg
        change 0 ≤ (if cell then Int.fdiv (2 * px + 20) 40 else px * 64)
        cases cell with
        | false =>
            change 0 ≤ px * 64
            exact Int.mul_nonneg hpx0 (by decide)
        | true =>
            change 0 ≤ Int.fdiv (2 * px + 20) 40
            rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
            exact Int.ediv_nonneg (by omega) (by decide)
  have hfpad : 0 ≤ frameParams.padding := by rw [hframeParams]; exact hpad
  have hfline : 0 ≤ frameParams.lineHeight := by rw [hframeParams]; exact hlh0
  have hpX : 0 < params.pitchX := by rw [hparams]; exact hpxpos
  have hpY : 0 < params.pitchY := by rw [hparams]; exact hpypos
  have parents_adm : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g := by
    intro parent hmem
    rw [hpar] at hmem
    obtain ⟨a, ha, hfa⟩ := List.mem_map.mp hmem
    obtain ⟨k, hk, hka⟩ := List.mem_iff_getElem.mp ha
    have hkp : nodeInput[k].parent = parent := by
      have h1 := congrArg (fun x : Node => x.parent) hka
      exact h1.trans hfa
    have hkd : nodeInput.getD k default = nodeInput[k] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        Option.getD_some]
    obtain ⟨hw, hh, hl, hjc, hE⟩ := node_decode k hk
    rw [hkd] at hE
    rcases hE with h | ⟨i, hi, heq⟩
    · left
      rw [hkp] at h
      exact h
    · right
      refine ⟨i, ?_, ?_⟩
      · rw [hg_eq, groupLen]; exact hi
      · rw [hkp] at heq
        exact heq
  have hfacts : ArchC6BuildFacts p pitch nodeInput resolved := by
    refine ⟨hfits, ?_, ?_, ?_, ?_⟩
    · intro n hn
      obtain ⟨hw, hh, hl, hjc, hE⟩ := node_decode n hn
      exact ⟨Int.le_of_lt hw, Int.le_of_lt hh, hl⟩
    · intro n hn hj
      obtain ⟨hw, hh, hl, hjc, hE⟩ := node_decode n hn
      have hij : (nodeInput.getD n default).icon.h =
          LayoutConst.architecture_junction_size.get profile := hjc hj
      rw [hij]
      have hpy' : p.pitchY ≤ pitch.y := by
        have h := pitch_y_lower p nodeInput sizes
        rw [← hpitch] at h
        exact h
      have hjsle : LayoutConst.architecture_junction_size.get profile ≤
          LayoutConst.architecture_pitch_y.get profile := by
        cases profile <;> decide
      omega
    · have huniq := CellContracts.hierarchy_final_cells_unique input params
        frameParams (LayoutConst.architecture_bfs_cap.get profile).toNat
        ordered groupParents parents_adm hpX hpY hfpad hfline
      rw [← hplaced, ← hresolved] at huniq
      exact huniq
    · have hlen := (resolveHierarchy_storage_lengths input params frameParams
        (LayoutConst.architecture_bfs_cap.get profile).toNat).1
      rw [← hplaced, ← hresolved] at hlen
      have hparLen : input.parents.length = nodeInput.length := by
        rw [hpar, List.length_map]
      have hge : input.parents.length ≤ (virtualParents input).length := by
        simp only [virtualParents, List.length_append, List.length_map]
        omega
      rw [hlen, ← hparLen]
      exact hge
  obtain ⟨hfitsR, hsizesR, hjqR, hnodup, hresLen⟩ := hfacts
  have hjqAt : ∀ n, n < nodeInput.length → (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2 := by
    intro n hn hj
    have hpitchDiff := hjqR n hn hj
    exact Int.fdiv_nonneg (by omega) (by decide)
  have hboxBoundsAt : ∀ n, n < nodeInput.length →
      RouteClearance.BoxBounds pitch.x pitch.y p.gutter
        (RouteClearance.spanRect (geometry.boxes.getD n default))
        (resolved.nodes.getD n default).x (resolved.nodes.getD n default).y := by
    intro n hn
    have h := node_box_bounds p pitch nodeInput groupInput resolved n hn
      hpxpos hpypos hgut hpth (hfitsR n hn) (hjqAt n hn) hptop
    rw [← hgeometry] at h
    exact h
  have hboundaryAt : ∀ n, n < nodeInput.length → ∀ (s : Grid.Architecture.Side)
      (i k : Nat), i ≤ k →
      Grid.Architecture.SpanBoundary
        (Grid.Architecture.port p pitch (nodeInput.getD n default)
          (geometry.boxes.getD n default) (geometry.icons.getD n default)
          (resolved.nodes.getD n default) s i k).point (geometry.boxes.getD n default) := by
    intro n hn s i k hslot
    have h := Grid.Architecture.geometry_port_on_boundary p pitch nodeInput groupInput
      resolved n hn s i k hslot (hsizesR n hn).1 (hsizesR n hn).2.1 (hsizesR n hn).2.2 hpth
    rw [← hgeometry] at h
    exact h
  intro r hr b hb hexclusive hscope
  rw [hrouteEq, hdumpRoutes] at hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hi, hget⟩ :=
    List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)
  rw [hboxEq] at hb
  obtain ⟨mb, hmb, hrec⟩ := mapM_output_origin hdumpBoxes hb
  simp only at hrec
  by_cases hgroup : (mb.role == BoxRole.group) = true
  · exfalso
    simp only [hgroup, ↓reduceIte] at hrec
    cases hfound : groups.findIdx? (fun g => g.id == mb.id) with
    | none =>
        simp only [hfound, pure, Except.pure, Bind.bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at hrec
        cases hrec
    | some i =>
        simp only [hfound, pure, Except.pure, Bind.bind, Except.bind] at hrec
        cases hrec
        have hne : (mb.role != BoxRole.group) = false := by
          cases hrole2 : mb.role <;> simp_all
        have hfalse : mb.exclusive = false := by
          have hsafe := hrole mb hmb
          rw [hne] at hsafe
          simpa using hsafe
        have htrue : mb.exclusive = true := hexclusive
        rw [hfalse] at htrue
        cases htrue
  · have hgroupF : (mb.role == BoxRole.group) = false := by simp [hgroup]
    simp only [hgroupF, ↓reduceIte] at hrec
    cases hfind : nodes.findIdx? (fun g => g.id == mb.id) with
    | none =>
        simp only [hfind, pure, Except.pure, Bind.bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at hrec
        cases hrec
    | some f =>
        simp only [hfind, pure, Except.pure, Bind.bind, Except.bind] at hrec
        cases hrec
        dsimp only at hscope ⊢
        have hfLen : f < nodes.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
        have hfId : nodes[f].id = mb.id := by
          have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
          simpa using hbeq
        have hidxE : q.2 < edges.length := by omega
        obtain ⟨_edgeLength, decodedEdges⟩ :=
          decoded_edges_lookup nodes m.routes edges _ hedges
        obtain ⟨_he, _hfindA, _hfindB, haL, hbL, hidA, hidB⟩ := decodedEdges q.2 hi
        have haL' : edges[q.2].a < nodeInput.length := by rw [hnodeLen]; exact haL
        have hbL' : edges[q.2].b < nodeInput.length := by rw [hnodeLen]; exact hbL
        have hrawL : q.2 < rawRoutes.length := by omega
        obtain ⟨hroutesL, htrans⟩ := mapM_at hroutes q.2 hrawL
        have htransPt : routes[q.2] =
            rawRoutes[q.2].map (fun v => (⟨v.x + dx, v.y + dy⟩ : Point)) :=
          translatePoint_map dx dy rawRoutes[q.2] routes[q.2] htrans
        have hroutesGetD : routes.getD q.2 [] = routes[q.2] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hroutesL,
            Option.getD_some]
        have hrawGetD : rawRoutes.getD q.2 [] = rawRoutes[q.2] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrawL,
            Option.getD_some]
        obtain ⟨iA, kA, iB, kB, aP, bP, hpa, hpb, hpathEq, hslotA, hslotB⟩ :=
          route_index_ports p pitch nodeInput edges resolved geometry q.2 hidxE
        have hrawPath : rawRoutes.getD q.2 [] =
            Grid.Architecture.path p pitch aP bP := by
          rw [hrawRoutes]
          exact hpathEq
        have haneq : edges[q.2].a ≠ f := by
          intro hfe
          apply hscope
          have hidA' := hidA
          simp only [hfe] at hidA'
          rw [hget] at hidA'
          have h1 : mb.id = q.1.fromId := hfId.symm.trans hidA'
          rw [h1]
          unfold LayoutDump.routeScope
          exact List.mem_append_left _ List.mem_cons_self
        have hbneq : edges[q.2].b ≠ f := by
          intro hfe
          apply hscope
          have hidB' := hidB
          simp only [hfe] at hidB'
          rw [hget] at hidB'
          have h1 : mb.id = q.1.toId := hfId.symm.trans hidB'
          rw [h1]
          unfold LayoutDump.routeScope
          exact List.mem_append_left _
            (List.mem_cons_of_mem _ List.mem_cons_self)
        have haF : RouteClearance.PortFacts pitch.x pitch.y p.gutter aP := by
          rw [hpa]
          exact RouteClearance.port_facts p pitch (nodeInput.getD edges[q.2].a default)
            (geometry.boxes.getD edges[q.2].a default)
            (geometry.icons.getD edges[q.2].a default)
            (resolved.nodes.getD edges[q.2].a default) edges[q.2].sideA iA kA
            (hboxBoundsAt edges[q.2].a haL')
            (hboundaryAt edges[q.2].a haL' edges[q.2].sideA iA kA hslotA)
        have hbF : RouteClearance.PortFacts pitch.x pitch.y p.gutter bP := by
          rw [hpb]
          exact RouteClearance.port_facts p pitch (nodeInput.getD edges[q.2].b default)
            (geometry.boxes.getD edges[q.2].b default)
            (geometry.icons.getD edges[q.2].b default)
            (resolved.nodes.getD edges[q.2].b default) edges[q.2].sideB iB kB
            (hboxBoundsAt edges[q.2].b hbL')
            (hboundaryAt edges[q.2].b hbL' edges[q.2].sideB iB kB hslotB)
        have hfInput : f < nodeInput.length := by omega
        have hfdistinct : ∀ n, n < nodeInput.length → n ≠ f →
            resolved.nodes.getD n default ≠ resolved.nodes.getD f default := by
          intro n hn hne heq
          have hnn : n < resolved.nodes.length := by omega
          have hfn : f < resolved.nodes.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnn, Option.getD_some,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfn, Option.getD_some] at heq
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · exact nodup_getElem_ne hnodup n f hnn hfn hlt heq
          · exact nodup_getElem_ne hnodup f n hfn hnn hlt heq.symm
        have hmiss : Polyline.allSegsMiss (Grid.Architecture.path p pitch aP bP)
            (RouteClearance.spanRect (geometry.boxes.getD f default)) :=
          RouteClearance.route_misses_foreign_box p pitch resolved nodeInput geometry f
            hfInput (hboxBoundsAt f hfInput) hfdistinct aP bP haF
            ⟨edges[q.2].a, haL', haneq, by
              rw [hpa]
              exact port_cell p pitch (nodeInput.getD edges[q.2].a default)
                (geometry.boxes.getD edges[q.2].a default)
                (geometry.icons.getD edges[q.2].a default)
                (resolved.nodes.getD edges[q.2].a default) edges[q.2].sideA iA kA⟩
            hbF ⟨edges[q.2].b, hbL', hbneq, by
              rw [hpb]
              exact port_cell p pitch (nodeInput.getD edges[q.2].b default)
                (geometry.boxes.getD edges[q.2].b default)
                (geometry.icons.getD edges[q.2].b default)
                (resolved.nodes.getD edges[q.2].b default) edges[q.2].sideB iB kB⟩
        have hfGeom : f < geometry.boxes.length := by
          rw [hgeometry]
          simp only [Grid.Architecture.geometry, List.length_map, List.length_zipIdx]
          omega
        obtain ⟨hboxesL, hboxAt⟩ := mapM_at hboxes f hfGeom
        have hspanD : geometry.boxes.getD f default = geometry.boxes[f] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfGeom,
            Option.getD_some]
        have hboxGetD : boxes.getD f ⟨0, 0, 0, 0⟩ = boxes[f] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hboxesL,
            Option.getD_some]
        have hrectTrans : Grid.Architecture.translateRect dx dy
            (geometry.boxes.getD f default) = .ok (boxes.getD f ⟨0, 0, 0, 0⟩) := by
          rw [hspanD, hboxGetD]
          exact hboxAt
        rcases Grid.Architecture.translateRect_shape dx dy
            (geometry.boxes.getD f default) (boxes.getD f ⟨0, 0, 0, 0⟩) hrectTrans
          with degen | shape
        · intro hhit
          obtain ⟨hw, -, -⟩ := hhit
          rw [degen.2.2] at hw
          simp at hw
        · intro hhit
          obtain ⟨-, -, hnm⟩ := hhit
          apply hnm
          obtain ⟨s1, s2, s3, s4⟩ := shape
          have hall : Polyline.allSegsMiss
              (List.map (fun v => (⟨v.x + dx, v.y + dy⟩ : Point)) (rawRoutes.getD q.2 []))
              ⟨(RouteClearance.spanRect (geometry.boxes.getD f default)).x + dx,
               (RouteClearance.spanRect (geometry.boxes.getD f default)).y + dy,
               (RouteClearance.spanRect (geometry.boxes.getD f default)).w,
               (RouteClearance.spanRect (geometry.boxes.getD f default)).h⟩ := by
            have h2 := allSegsMiss_translate dx dy (Grid.Architecture.path p pitch aP bP)
              (RouteClearance.spanRect (geometry.boxes.getD f default)) hmiss
            rw [hrawPath]
            exact h2
          rw [hroutesGetD, htransPt, ← hrawGetD,
            rect_eq_of_components (boxes.getD f ⟨0, 0, 0, 0⟩) _ _ _ _ s1 s2 s3 s4]
          exact hall
end Elegant.Kinds.Architecture
