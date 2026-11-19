import Elegant.SequenceHdr

set_option autoImplicit false

/-! The dump of a sequence layout: the shifted boxes, labels, and routes that `mkPainter` writes,
their lookup by id, the extent that sizes the canvas, and the points of a route
(`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

def rr (w : Walk) (i : Nat) : Rect := w.boxRects.getD i rectZero

def shiftR (sx sy : Int) (r : Rect) : Rect := ⟨r.x + sx, r.y + sy, r.w, r.h⟩

theorem disjoint_shift (sx sy : Int) (a b : Rect) :
    Disjoint (shiftR sx sy a) (shiftR sx sy b) ↔ Disjoint a b := by
  unfold Disjoint shiftR Rect.meetsInterior
  constructor <;> intro h hh <;> apply h <;> (try dsimp only at *) <;> omega

theorem contained_shift (sx sy : Int) (a b : Rect) :
    Rect.Contained (shiftR sx sy a) (shiftR sx sy b) ↔ Rect.Contained a b := by
  unfold Rect.Contained shiftR
  constructor <;> intro h <;> (try dsimp only at *) <;> omega

theorem strictInside_shift (sx sy : Int) (a b : Rect) :
    Rect.StrictInside (shiftR sx sy a) (shiftR sx sy b) ↔ Rect.StrictInside a b := by
  unfold Rect.StrictInside shiftR
  constructor <;> intro h <;> (try dsimp only at *) <;> omega

theorem disjoint_comm' {a b : Rect} (h : Disjoint a b) : Disjoint b a := by
  unfold Disjoint at *
  intro hh
  exact h ((Rect.meetsInterior_comm a b).mpr hh)

theorem disjoint_of_zero {a b : Rect} (h : a.w ≤ 0 ∨ a.h ≤ 0) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  intro hh
  omega

theorem disjoint_of_strictInside {o i g : Rect} (h : Rect.StrictInside o i) (hg : Disjoint g o) :
    Disjoint g i := by
  unfold Disjoint Rect.meetsInterior at *
  unfold Rect.StrictInside at h
  intro hh
  apply hg
  omega

theorem strictInside_trans {a b c : Rect} (h1 : Rect.StrictInside a b) (h2 : Rect.StrictInside b c) :
    Rect.StrictInside a c := by
  unfold Rect.StrictInside at *
  omega

theorem contained_of_strictInside {a b : Rect} (h : Rect.StrictInside a b) : Rect.Contained a b := by
  unfold Rect.StrictInside at h
  unfold Rect.Contained
  omega

/-- The dump of the walk `w`. -/
def dumpOf (pl : Plan) (cs : List Int) (w : Walk) : LayoutDump :=
  let p := mkPainter pl cs w
  ⟨p.canvas, p.boxes, p.routes, p.labels.map (·.toLabel)⟩

def sxOf (pl : Plan) (w : Walk) : Int := pl.c.diagramMarginX - (extentOf w).1

def dbox (pl : Plan) (w : Walk) (b : ModelBox) (i : Nat) : Box :=
  ⟨b.id, b.role.id, shiftR (sxOf pl w) pl.c.diagramMarginY (rr w i), b.parent, b.exclusive⟩

theorem dump_boxes (pl : Plan) (cs : List Int) (w : Walk) :
    (dumpOf pl cs w).boxes = pl.m.boxes.zipIdx.map fun (b, i) => dbox pl w b i := rfl

theorem mem_dump_boxes {pl : Plan} {cs : List Int} {w : Walk} {x : Box} :
    x ∈ (dumpOf pl cs w).boxes ↔ ∃ i b, pl.m.boxes[i]? = some b ∧ x = dbox pl w b i := by
  rw [dump_boxes, List.mem_map]
  constructor
  · rintro ⟨⟨b, i⟩, hx, rfl⟩
    exact ⟨i, b, List.mk_mem_zipIdx_iff_getElem?.mp hx, rfl⟩
  · rintro ⟨i, b, hb, rfl⟩
    exact ⟨(b, i), List.mk_mem_zipIdx_iff_getElem?.mpr hb, rfl⟩

theorem find_eq_of_nodup {α : Type} (f : α → String) :
    ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, l.find? (fun y => f y == f x) = some x := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a t ih =>
    intro hnd x hx
    have hnd' := List.nodup_cons.mp (by simpa using hnd : (f a :: t.map f).Nodup)
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : (f a == f x) = false := by
        have : f a ≠ f x := fun h => hnd'.1 (h ▸ List.mem_map_of_mem hx)
        simpa using this
      simp only [List.find?_cons, hne]
      exact ih (by simpa using hnd'.2) x hx

theorem dump_ids_nodup {pl : Plan} (cs : List Int) (w : Walk) (hfm : ModelFacts pl.m) :
    ((dumpOf pl cs w).boxes.map (·.id)).Nodup := by
  rw [dump_boxes]
  have : (List.map (fun x => x.id) (List.map (fun (x : ModelBox × Nat) => dbox pl w x.1 x.2)
      pl.m.boxes.zipIdx)) = pl.m.boxes.map (·.id) := by
    rw [List.map_map]
    have h := List.zipIdx_map_fst 0 pl.m.boxes
    calc _ = (pl.m.boxes.zipIdx.map Prod.fst).map (·.id) := by rw [List.map_map]; rfl
      _ = pl.m.boxes.map (·.id) := by rw [h]
  rw [this]
  exact hfm.nodup

theorem box?_of_mem {pl : Plan} {cs : List Int} {w : Walk} (hfm : ModelFacts pl.m) {x : Box}
    (hx : x ∈ (dumpOf pl cs w).boxes) : (dumpOf pl cs w).box? x.id = some x :=
  find_eq_of_nodup (fun b : Box => b.id) _ (dump_ids_nodup cs w hfm) x hx

theorem box?_dbox {pl : Plan} {cs : List Int} {w : Walk} (hfm : ModelFacts pl.m) {i : Nat}
    {b : ModelBox} (hb : pl.m.boxes[i]? = some b) :
    (dumpOf pl cs w).box? b.id = some (dbox pl w b i) :=
  box?_of_mem hfm (mem_dump_boxes.mpr ⟨i, b, hb, rfl⟩)

/-! ### The extent -/

def Tle (a b : Int × Int × Int) : Prop := b.1 ≤ a.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2

theorem Tle.trans' {a b c : Int × Int × Int} (h1 : Tle a b) (h2 : Tle b c) : Tle a c := by
  unfold Tle at *
  omega

theorem foldl_tle {α : Type} (F : Int × Int × Int → α → Int × Int × Int)
    (hF : ∀ a x, Tle a (F a x)) :
    ∀ (l : List α) (a : Int × Int × Int), Tle a (l.foldl F a) := by
  intro l
  induction l with
  | nil => intro a; exact ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _⟩
  | cons x t ih =>
    intro a
    simp only [List.foldl_cons]
    exact Tle.trans' (hF a x) (ih (F a x))

def growT (a : Int × Int × Int) (r : Rect) : Int × Int × Int :=
  (min a.1 r.x, max a.2.1 (r.x + r.w), max a.2.2 (r.y + r.h))

theorem growT_tle (a : Int × Int × Int) (r : Rect) : Tle a (growT a r) := by
  unfold Tle growT
  dsimp only
  omega

def Qb (r : Rect) (t : Int × Int × Int) : Prop := t.1 ≤ r.x ∧ r.x + r.w ≤ t.2.1 ∧ r.y + r.h ≤ t.2.2

theorem Qb.mono {r : Rect} {t t' : Int × Int × Int} (h : Qb r t) (ht : Tle t t') : Qb r t' := by
  unfold Qb Tle at *
  omega

theorem foldl_growT_mem :
    ∀ (l : List Rect) (a : Int × Int × Int) (r : Rect), r ∈ l → Qb r (l.foldl growT a) := by
  intro l
  induction l with
  | nil => intro a r h; simp at h
  | cons x t ih =>
    intro a r hr
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr
    · refine Qb.mono ?_ (foldl_tle growT growT_tle t _)
      unfold Qb growT
      dsimp only
      omega
    · exact ih _ r hr

theorem extentOf_boxRect (w : Walk) (r : Rect) (hr : r ∈ w.boxRects) : Qb r (extentOf w) := by
  have h1 : Qb r (w.boxRects.foldl growT (0, 0, w.bottom)) := foldl_growT_mem _ _ r hr
  have h2 : Tle (w.boxRects.foldl growT (0, 0, w.bottom))
      (w.routeRuns.foldl (fun acc run => run.points.foldl
        (fun (a : Int × Int × Int) p => (min a.1 p.x, max a.2.1 p.x, max a.2.2 p.y)) acc)
        (w.boxRects.foldl growT (0, 0, w.bottom))) := by
    refine foldl_tle _ (fun a run => ?_) _ _
    refine foldl_tle _ (fun a p => ?_) _ _
    unfold Tle
    dsimp only
    omega
  have h3 := foldl_tle growT growT_tle w.bars
    (w.routeRuns.foldl (fun acc run => run.points.foldl
        (fun (a : Int × Int × Int) p => (min a.1 p.x, max a.2.1 p.x, max a.2.2 p.y)) acc)
        (w.boxRects.foldl growT (0, 0, w.bottom)))
  have h4 := foldl_tle (fun (a : Int × Int × Int) (r : Rect) => if r.w != 0 ∨ r.h != 0 then growT a r else a)
    (fun a x => by
      by_cases hc : x.w != 0 ∨ x.h != 0
      · simp only [hc, ↓reduceIte]
        exact growT_tle a x
      · simp only [hc, ↓reduceIte]
        exact ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _⟩) w.labelRects
    (w.bars.foldl growT
      (w.routeRuns.foldl (fun acc run => run.points.foldl
        (fun (a : Int × Int × Int) p => (min a.1 p.x, max a.2.1 p.x, max a.2.2 p.y)) acc)
        (w.boxRects.foldl growT (0, 0, w.bottom))))
  exact Qb.mono h1 (Tle.trans' h2 (Tle.trans' h3 h4))

/-! ### Routes and labels -/

theorem findIdx_eq_of_nodup (l : List ModelBox) (hnd : (l.map (·.id)).Nodup) :
    ∀ (i : Nat) (h : i < l.length), l.findIdx? (fun b => b.id == l[i].id) = some i := by
  induction l with
  | nil => intro i h; simp at h
  | cons a t ih =>
    intro i h
    have hnd' := List.nodup_cons.mp (by simpa using hnd : (a.id :: t.map (·.id)).Nodup)
    cases i with
    | zero => simp [List.findIdx?_cons]
    | succ k =>
      have hk : k < t.length := by simpa using h
      have hne : (a.id == t[k].id) = false := by
        have : a.id ≠ t[k].id := fun hh => hnd'.1 (hh ▸ List.mem_map_of_mem (List.getElem_mem hk))
        simpa using this
      simp only [List.findIdx?_cons, List.getElem_cons_succ, hne]
      simp [ih (by simpa using hnd'.2) k hk]

theorem findIdx_boxId {m : Model} (hfm : ModelFacts m) {i : Nat} (hi : i < m.boxes.length) :
    m.boxes.findIdx? (fun b => b.id == boxId m i) = some i := by
  have h := findIdx_eq_of_nodup m.boxes hfm.nodup i hi
  have e : boxId m i = m.boxes[i].id := by simp [boxId, List.getElem?_eq_getElem hi]
  rw [e]
  exact h

theorem routePoints_four (pl : Plan) (w : Walk) (sx sy : Int) (r : ModelRoute) (run : RouteRun)
    (xs xd a b y : Int) (bs bt : Nat)
    (hrun : run.points = [⟨xs, a⟩, ⟨xs, y⟩, ⟨xd, y⟩, ⟨xd, b⟩])
    (hf : pl.m.boxes.findIdx? (fun x => x.id == r.fromId) = some bs)
    (ht : pl.m.boxes.findIdx? (fun x => x.id == r.toId) = some bt) :
    routePoints pl w sx sy r run =
      [⟨xs + sx, (rr w bs).y + (rr w bs).h + sy⟩, ⟨xs + sx, y + sy⟩, ⟨xd + sx, y + sy⟩,
        ⟨xd + sx, (rr w bt).y + (rr w bt).h + sy⟩] := by
  unfold routePoints
  simp [hrun, hf, ht, rr]

theorem routePoints_six (pl : Plan) (w : Walk) (sx sy : Int) (r : ModelRoute) (run : RouteRun)
    (xs dx a y d : Int) (bs bt : Nat)
    (hrun : run.points = [⟨xs, a⟩, ⟨xs, y⟩, ⟨xs + dx, y⟩, ⟨xs + dx, y + d⟩, ⟨xs, y + d⟩, ⟨xs, a⟩])
    (hf : pl.m.boxes.findIdx? (fun x => x.id == r.fromId) = some bs)
    (ht : pl.m.boxes.findIdx? (fun x => x.id == r.toId) = some bt) :
    routePoints pl w sx sy r run =
      [⟨xs + sx, (rr w bs).y + (rr w bs).h + sy⟩, ⟨xs + sx, y + sy⟩, ⟨xs + dx + sx, y + sy⟩,
        ⟨xs + dx + sx, y + d + sy⟩, ⟨xs + sx, y + d + sy⟩,
        ⟨xs + sx, (rr w bt).y + (rr w bt).h + sy⟩] := by
  unfold routePoints
  simp [hrun, hf, ht, rr]

def droute (pl : Plan) (w : Walk) (r : ModelRoute) (i : Nat) : Route :=
  ⟨r.id, r.fromId, r.toId, r.orthogonal,
    match w.routeRuns[i]? with
    | some run => routePoints pl w (sxOf pl w) pl.c.diagramMarginY r run
    | none => []⟩

theorem dump_routes (pl : Plan) (cs : List Int) (w : Walk) :
    (dumpOf pl cs w).routes = pl.m.routes.zipIdx.map fun (r, i) => droute pl w r i := rfl

theorem mem_dump_routes {pl : Plan} {cs : List Int} {w : Walk} {x : Route} :
    x ∈ (dumpOf pl cs w).routes ↔ ∃ i r, pl.m.routes[i]? = some r ∧ x = droute pl w r i := by
  rw [dump_routes, List.mem_map]
  constructor
  · rintro ⟨⟨r, i⟩, hx, rfl⟩
    exact ⟨i, r, List.mk_mem_zipIdx_iff_getElem?.mp hx, rfl⟩
  · rintro ⟨i, r, hr, rfl⟩
    exact ⟨(r, i), List.mk_mem_zipIdx_iff_getElem?.mpr hr, rfl⟩

def dlabel (pl : Plan) (w : Walk) (l : ModelLabel) (i : Nat) : Label :=
  ⟨l.id, l.owner, shiftR (sxOf pl w) pl.c.diagramMarginY (w.labelRects.getD i rectZero),
    lineTexts (pl.labelLines.getD i [])⟩

theorem dump_labels (pl : Plan) (cs : List Int) (w : Walk) :
    (dumpOf pl cs w).labels = pl.m.labels.zipIdx.map fun (l, i) => dlabel pl w l i := by
  show List.map _ (List.map _ _) = _
  rw [List.map_map]
  rfl

theorem mem_dump_labels {pl : Plan} {cs : List Int} {w : Walk} {x : Label} :
    x ∈ (dumpOf pl cs w).labels ↔ ∃ i l, pl.m.labels[i]? = some l ∧ x = dlabel pl w l i := by
  rw [dump_labels, List.mem_map]
  constructor
  · rintro ⟨⟨l, i⟩, hx, rfl⟩
    exact ⟨i, l, List.mk_mem_zipIdx_iff_getElem?.mp hx, rfl⟩
  · rintro ⟨i, l, hl, rfl⟩
    exact ⟨(l, i), List.mk_mem_zipIdx_iff_getElem?.mpr hl, rfl⟩

theorem dump_canvas (pl : Plan) (cs : List Int) (w : Walk) :
    (dumpOf pl cs w).canvas =
      ⟨(extentOf w).2.1 - (extentOf w).1 + 2 * pl.c.diagramMarginX,
        (extentOf w).2.2 + 2 * pl.c.diagramMarginY⟩ := rfl

end Sequence
end Elegant
