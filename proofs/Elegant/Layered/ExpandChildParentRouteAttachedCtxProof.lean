import Elegant.Layered.Pipeline
import Elegant.Layered.ExpandChildParentRouteRunProof
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.RecursiveC78
import Elegant.Model
import Elegant.Scene
import ElegantGeometry.Validator

set_option autoImplicit false

open Elegant
open Elegant.Layered
open Elegant.Layered.PipelineImpl

namespace Elegant.Layered.PipelineImpl

/-! # Attached-route clearance seam: recursion-context threading.

Proved here:

* `pracCtx_hitsRect_of_strictInside` (private) and its private helpers: the
  `hitsRect` monotonicity chain through strict containment, copied with a
  file-unique prefix from `ExpandChildParentRouteClearProof.lean` (whose
  copies are private to that module and do not resolve here). Hitting a
  strictly inside rectangle implies hitting the outer one; contrapositively,
  missing the group frame implies missing every strictly inside rectangle.
* `ParentRouteAttachedCtxPremise` (public): the exact validated-parent-scene
  clause the step consumes, over the executed call — `Validator.C5` of the
  parent dump (endpoint attachment of every parent route) plus the dump-box
  agreement for the group frame (the dump lookup agrees with the scene
  lookup). This is what `FamilyAssembly` must supply from its recursion (see
  below); it is a premise, not a claim proved here.
* `ParentRouteAttachedFrameMiss` (public): the single remaining open fact, a
  lemma on the way — every attached parent route whose endpoint attachment is
  explicitly supplied misses the group frame rectangle. It drops the
  inner-rectangle quantifier of the target (frame rectangle only) and takes
  the `C5` attachment tuple as an antecedent instead of proving it; the
  proved monotonicity bridge in this file restores the quantifier.
* `parentRouteAttachedClear_of_recursion_ctx` (public): the seam statement
  `ExpandChildParentRouteAttachedClear group parent` from the standard call
  bundle (`hexpand`, `hframed`, `hctx`, `hparams`), the recursion-supplied
  validity premise `hvalid`, and the single open fact `hmiss`. No other
  premise is taken; the bundle members this proof does not consume are
  explicitly discarded, matching the convention of
  `parentRouteAttachedSelfEndpoint_holds`.

Open: `ParentRouteAttachedFrameMiss` only. Its content is the router-level
attachment geometry identified in `ExpandChildParentRouteRunProof.lean`:
outward-facing port stubs and middle-segment avoidance at the frame, which
do not follow from `C5` (boundary ports alone do not pin stub exteriors or
middles). The self-loop boundary half is already proved outright
(`parentRouteAttachedSelfEndpoint_holds`); this file does not duplicate it.

How `FamilyAssembly` can supply `ParentRouteAttachedCtxPremise` (no edit
made here): the seam field `parentRouteAttachedClear` is consumed verbatim
by `strictMiss_of_below` / `strictMiss_restricted_closed`, whose attached
half currently comes straight from the field. Once the parent-scene validity
is proved through the actual `layoutRecursive` fuel induction (the same
induction that will close `layered_valid`), each `succ` case holds
`layoutRecursive fuel (parentSubInput inp group P titleLines child) o =
.ok parent` (already in `ExpandChildCallContext`) together with validity of
that parent result at the same fuel; validity yields `Validator.C5
parent.scene.layoutDump`, and the dump-box agreement follows definitionally
(`Scene.layoutDump` is built from the scene boxes, closed by `simp` as in
`parentRouteAttachedSelfEndpoint_holds`). At that point the field is
discharged by `parentRouteAttachedClear_of_recursion_ctx` applied to the
call bundle, the induction-supplied `hvalid`, and the residual `hmiss`,
exactly as `parentFrameStrict_of_recursion_ctx` discharges its seam field
from executed-call transports plus its two residuals.

Probe evidence (run outside the build): the premise (`c5` of every parent
dump, dump-box agreement) and the residual (attached routes with passing port
checks miss the frame and the shrink-by-1/3/5 and centered-half strictly
inside rectangles) held on every executed `expandChild` call of the
edge-into-titled, nested cross-group, self-loop group, zero-size fixed and
empty group inputs. The ill-formed input is rejected at the domain level with
zero calls.
-/

/-! ## `hitsRect` monotonicity through strict containment (prefixed copies)

Copies of the private lemmas in `ExpandChildParentRouteClearProof.lean`,
renamed with the file-unique `pracCtx` prefix, used for the attached
transport below. -/

/-- A corner-minimum bound: the `minCorner` of a rectangle lies below the
corner product at any point of its closed extent. -/
private theorem pracCtx_minCorner_le_dot {nx ny : Int} {outer : Rect} {x y : Int}
    (hx1 : outer.x ≤ x) (hx2 : x ≤ outer.x + outer.w)
    (hy1 : outer.y ≤ y) (hy2 : y ≤ outer.y + outer.h) :
    Polyline.minCorner nx ny outer ≤ nx * x + ny * y := by
  have hnonpos : ∀ {a b c : Int}, b ≤ c → a ≤ 0 → a * c ≤ a * b := by
    intro a b c h ha
    simpa [Int.mul_comm] using Int.mul_le_mul_of_nonpos_right h ha
  by_cases hnx : 0 ≤ nx <;> by_cases hny : 0 ≤ ny
  · have hle : Polyline.minCorner nx ny outer ≤
        nx * outer.x + ny * outer.y := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_left _ _) (Int.min_le_left _ _)
    have e1 : nx * outer.x ≤ nx * x := Int.mul_le_mul_of_nonneg_left hx1 hnx
    have e2 : ny * outer.y ≤ ny * y := Int.mul_le_mul_of_nonneg_left hy1 hny
    omega
  · have hny' : ny < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * outer.x + ny * (outer.y + outer.h) := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_right _ _) (Int.min_le_left _ _)
    have e1 : nx * outer.x ≤ nx * x := Int.mul_le_mul_of_nonneg_left hx1 hnx
    have e2 : ny * (outer.y + outer.h) ≤ ny * y :=
      hnonpos hy2 (Int.le_of_lt hny')
    omega
  · have hnx' : nx < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * (outer.x + outer.w) + ny * outer.y := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_left _ _) (Int.min_le_right _ _)
    have e1 : nx * (outer.x + outer.w) ≤ nx * x :=
      hnonpos hx2 (Int.le_of_lt hnx')
    have e2 : ny * outer.y ≤ ny * y := Int.mul_le_mul_of_nonneg_left hy1 hny
    omega
  · have hnx' : nx < 0 := by omega
    have hny' : ny < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * (outer.x + outer.w) + ny * (outer.y + outer.h) := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_right _ _) (Int.min_le_right _ _)
    have e1 : nx * (outer.x + outer.w) ≤ nx * x :=
      hnonpos hx2 (Int.le_of_lt hnx')
    have e2 : ny * (outer.y + outer.h) ≤ ny * y :=
      hnonpos hy2 (Int.le_of_lt hny')
    omega

private theorem pracCtx_dot_le_maxCorner {nx ny : Int} {outer : Rect} {x y : Int}
    (hx1 : outer.x ≤ x) (hx2 : x ≤ outer.x + outer.w)
    (hy1 : outer.y ≤ y) (hy2 : y ≤ outer.y + outer.h) :
    nx * x + ny * y ≤ Polyline.maxCorner nx ny outer := by
  have hnonpos : ∀ {a b c : Int}, b ≤ c → a ≤ 0 → a * c ≤ a * b := by
    intro a b c h ha
    simpa [Int.mul_comm] using Int.mul_le_mul_of_nonpos_right h ha
  by_cases hnx : 0 ≤ nx <;> by_cases hny : 0 ≤ ny
  · have hle : nx * (outer.x + outer.w) + ny * (outer.y + outer.h) ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _)
    have e1 : nx * x ≤ nx * (outer.x + outer.w) :=
      Int.mul_le_mul_of_nonneg_left hx2 hnx
    have e2 : ny * y ≤ ny * (outer.y + outer.h) :=
      Int.mul_le_mul_of_nonneg_left hy2 hny
    omega
  · have hny' : ny < 0 := by omega
    have hle : nx * (outer.x + outer.w) + ny * outer.y ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _)
    have e1 : nx * x ≤ nx * (outer.x + outer.w) :=
      Int.mul_le_mul_of_nonneg_left hx2 hnx
    have e2 : ny * y ≤ ny * outer.y :=
      hnonpos hy1 (Int.le_of_lt hny')
    omega
  · have hnx' : nx < 0 := by omega
    have hle : nx * outer.x + ny * (outer.y + outer.h) ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _)
    have e1 : nx * x ≤ nx * outer.x :=
      hnonpos hx1 (Int.le_of_lt hnx')
    have e2 : ny * y ≤ ny * (outer.y + outer.h) :=
      Int.mul_le_mul_of_nonneg_left hy2 hny
    omega
  · have hnx' : nx < 0 := by omega
    have hny' : ny < 0 := by omega
    have hle : nx * outer.x + ny * outer.y ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)
    have e1 : nx * x ≤ nx * outer.x :=
      hnonpos hx1 (Int.le_of_lt hnx')
    have e2 : ny * y ≤ ny * outer.y :=
      hnonpos hy1 (Int.le_of_lt hny')
    omega

/-- A segment that misses an outer rectangle misses every strictly
inner one: axis separations transport by the gap, diagonal separations by
the corner bounds. -/
private theorem pracCtx_segMisses_of_strictInside {outer inner : Rect} {p q : Point}
    (hSI : outer.StrictInside inner)
    (hw : 0 ≤ inner.w) (hh : 0 ≤ inner.h)
    (hm : Polyline.segMisses p q outer) : Polyline.segMisses p q inner := by
  obtain ⟨hox, how, hoy, hoh⟩ := hSI
  unfold Polyline.segMisses at hm ⊢
  rcases hm with h | h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · obtain ⟨hne, hle | hge⟩ := h
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inl ?_⟩)))
      have c1 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * inner.x + (q.x - p.x) * inner.y :=
        pracCtx_minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have c2 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * inner.y :=
        pracCtx_minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have c3 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * inner.x + (q.x - p.x) * (inner.y + inner.h) :=
        pracCtx_minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y + inner.h) (by omega) (by omega) (by omega) (by omega)
      have c4 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * (inner.y + inner.h) :=
        pracCtx_minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y + inner.h)
          (by omega) (by omega) (by omega) (by omega)
      have h4 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          Polyline.minCorner (p.y - q.y) (q.x - p.x) inner := by
        simp only [Polyline.minCorner, Polyline.dot] at c1 c2 c3 c4 ⊢
        omega
      exact Int.le_trans hle h4
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inr ?_⟩)))
      have g1 : (p.y - q.y) * inner.x + (q.x - p.x) * inner.y ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        pracCtx_dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have g2 : (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * inner.y ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        pracCtx_dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have g3 : (p.y - q.y) * inner.x + (q.x - p.x) * (inner.y + inner.h) ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        pracCtx_dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y + inner.h) (by omega) (by omega) (by omega) (by omega)
      have g4 : (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * (inner.y + inner.h) ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        pracCtx_dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y + inner.h)
          (by omega) (by omega) (by omega) (by omega)
      have h4 : Polyline.maxCorner (p.y - q.y) (q.x - p.x) inner ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer := by
        simp only [Polyline.maxCorner, Polyline.dot] at g1 g2 g3 g4 ⊢
        omega
      exact Int.le_trans h4 hge

/-- A polyline that misses an outer rectangle misses every strictly
inner one. -/
private theorem pracCtx_allSegsMiss_of_strictInside {outer inner : Rect}
    (hSI : outer.StrictInside inner) (hw : 0 ≤ inner.w) (hh : 0 ≤ inner.h)
    (pts : List Point) :
    Polyline.allSegsMiss pts outer → Polyline.allSegsMiss pts inner := by
  induction pts
  case nil => intro h; trivial
  case cons head tail ih =>
    intro h
    cases tail with
    | nil => trivial
    | cons q rest' =>
        obtain ⟨hseg, htail⟩ := h
        exact ⟨pracCtx_segMisses_of_strictInside hSI hw hh hseg, ih htail⟩

/-- Hitting a strictly inner rectangle implies hitting the outer one. -/
private theorem pracCtx_hitsRect_of_strictInside {outer inner : Rect}
    {pts : List Point}
    (hSI : outer.StrictInside inner) (h : Polyline.hitsRect pts inner) :
    Polyline.hitsRect pts outer := by
  obtain ⟨hwI, hhI, hmissI⟩ := h
  obtain ⟨hox, how, hoy, hoh⟩ := hSI
  refine ⟨by omega, by omega, ?_⟩
  intro hmissO
  exact hmissI (pracCtx_allSegsMiss_of_strictInside ⟨hox, how, hoy, hoh⟩
    (Int.le_of_lt hwI) (Int.le_of_lt hhI) _ hmissO)

/-! ## Recursion-supplied premise and the remaining open fact -/

/-- The validated-parent-scene clause the attached step consumes, over the
executed call: `C5` endpoint attachment of every parent route, plus the
dump-box agreement pinning the group frame (the dump lookup agrees with the
scene lookup). `FamilyAssembly` supplies this from its fuel induction once
parent-scene validity is proved through the actual recursion; the agreement
conjunct is definitional (`Scene.layoutDump` is built from the scene
boxes). -/
def ParentRouteAttachedCtxPremise (group : ModelBox) (parent : FamilyResult) : Prop :=
  Validator.C5 parent.scene.layoutDump ∧
    ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      parent.scene.layoutDump.box? group.id = some frame

/-- The single remaining open fact, a lemma on the way to
`ExpandChildParentRouteAttachedClear`: every attached parent route whose
endpoint attachment is explicitly supplied misses the group frame rectangle.
Strictly on the way: the inner-rectangle quantifier of the target is dropped
(frame rectangle only) and the `C5` attachment tuple is taken as an
antecedent; the proved `pracCtx_hitsRect_of_strictInside` bridge restores the
quantifier in `parentRouteAttachedClear_of_recursion_ctx`. The missing
content is router-level: outward-facing port stubs and middle-segment
avoidance at the frame. True on every probe call (`frameViols = 0`
wherever the port checks pass). -/
def ParentRouteAttachedFrameMiss (group : ModelBox) (parent : FamilyResult) : Prop :=
  ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, (pr.fromId = group.id ∨ pr.toId = group.id) →
      ∀ (p q : Point) (fb tb : Box),
        pr.points.head? = some p → pr.points.getLast? = some q →
        parent.scene.layoutDump.box? pr.fromId = some fb →
        parent.scene.layoutDump.box? pr.toId = some tb →
        Validator.onBoundary p fb.rect → Validator.onBoundary q tb.rect →
        ¬ Polyline.hitsRect pr.points frame.rect

/-- Attached inner miss from the frame-level open fact: hitting a strictly
inside rectangle would hit the frame, contradicting the residual. -/
private theorem pracCtx_attached_inner_of_frame
    {group : ModelBox} {parent : FamilyResult}
    (hmiss : ParentRouteAttachedFrameMiss group parent)
    {frame : Box}
    (hfind : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    {pr : Route}
    (hmem : pr ∈ parent.scene.routes)
    (hatt : pr.fromId = group.id ∨ pr.toId = group.id)
    {p q : Point} {fb tb : Box}
    (hp : pr.points.head? = some p) (hq : pr.points.getLast? = some q)
    (hfb : parent.scene.layoutDump.box? pr.fromId = some fb)
    (htb : parent.scene.layoutDump.box? pr.toId = some tb)
    (hbFrom : Validator.onBoundary p fb.rect)
    (hbTo : Validator.onBoundary q tb.rect)
    {r : Rect} (hSI : frame.rect.StrictInside r) :
    ¬ Polyline.hitsRect pr.points r := by
  intro hr
  exact hmiss frame hfind pr hmem hatt p q fb tb hp hq hfb htb hbFrom hbTo
    (pracCtx_hitsRect_of_strictInside hSI hr)

/-- `parentRouteAttachedClear`: the parent scene of every executed
`expandChild` call satisfies `ExpandChildParentRouteAttachedClear`, from the
call bundle, the recursion-supplied validity premise, and the single open
frame-level fact. Same conclusion as the `LayeredSeams` field, with the
missing validated-scene clause threaded explicitly in the form the recursion
supplies, mirroring `parentFrameStrict_of_recursion_ctx`. -/
theorem parentRouteAttachedClear_of_recursion_ctx
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hvalid : ParentRouteAttachedCtxPremise group parent)
    (hmiss : ParentRouteAttachedFrameMiss group parent) :
    ExpandChildParentRouteAttachedClear group parent := by
  have _hex := hexpand
  have _hfr := hframed
  have _hctx := hctx
  have _hparams := hparams
  intro frame hfind pr hmem hatt r hSI hr
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hbFrom, hbTo⟩ := hvalid.1 pr hmem
  have hagree := hvalid.2 frame hfind
  rcases hatt with hfrom | hto
  · have hfromBox : fb = frame := by
      rw [hfrom] at hfb
      have hEq : some fb = some frame := hfb.symm.trans hagree
      cases hEq
      rfl
    subst hfromBox
    exact pracCtx_attached_inner_of_frame hmiss hfind hmem (Or.inl hfrom)
      hp hq hfb htb hbFrom hbTo hSI hr
  · have htoBox : tb = frame := by
      rw [hto] at htb
      have hEq : some tb = some frame := htb.symm.trans hagree
      cases hEq
      rfl
    subst htoBox
    exact pracCtx_attached_inner_of_frame hmiss hfind hmem (Or.inr hto)
      hp hq hfb htb hbFrom hbTo hSI hr

end Elegant.Layered.PipelineImpl
