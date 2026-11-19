import Elegant.SequenceValid5

set_option autoImplicit false

/-! Clause 6 of the validator: no route meets the interior of an exclusive actor header outside its
scope (`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem seg_vx {x y1 y2 : Int} {r : Rect} (h : x ≤ r.x ∨ r.x + r.w ≤ x) :
    Polyline.segMisses ⟨x, y1⟩ ⟨x, y2⟩ r := by
  rcases h with h | h
  · exact Or.inl (by dsimp only; omega)
  · exact Or.inr (Or.inl (by dsimp only; omega))

theorem seg_hy {x1 x2 y : Int} {r : Rect} (h : r.y + r.h ≤ y) :
    Polyline.segMisses ⟨x1, y⟩ ⟨x2, y⟩ r :=
  Or.inr (Or.inr (Or.inr (Or.inl (by dsimp only; omega))))

theorem seg_vy {x y1 y2 : Int} {r : Rect} (h1 : r.y + r.h ≤ y1) (h2 : r.y + r.h ≤ y2) :
    Polyline.segMisses ⟨x, y1⟩ ⟨x, y2⟩ r :=
  Or.inr (Or.inr (Or.inr (Or.inl (by dsimp only; omega))))

theorem lifeline_outside {pl : Plan} {cs : List Int} {steps : List Step} (hwf : pl.Wf)
    (hcs : cs = columns pl steps) {o s : Nat} (hne : o ≠ s) (ho : o < pl.widths.length)
    (hs : s < pl.widths.length) :
    cs.getD s 0 ≤ cs.getD o 0 - half (pl.widths.getD o 0) ∨
      cs.getD o 0 - half (pl.widths.getD o 0) + pl.widths.getD o 0 ≤ cs.getD s 0 := by
  subst hcs
  have h1 := hwf.widths o
  have h2 := hwf.widths s
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · right
    have := actor_headers_disjoint pl hwf steps o s hlt hs
    have := half_nonneg h2
    omega
  · left
    have := actor_headers_disjoint pl hwf steps s o hgt ho
    have := half_le h2
    omega

theorem route_clear_actor {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk}
    {ck : CheckState} {E : List Ent} (F : FinFacts pl cs steps w ck E) {r : ModelRoute}
    {pts : List Point} {sx sy : Int} (hf : RouteForm pl cs w sx sy r pts) {o j : Nat}
    (ho : o < pl.actorBoxes.length) (hj : pl.actorBoxes[o]? = some j)
    (h1 : boxId pl.m j ≠ r.fromId) (h2 : boxId pl.m j ≠ r.toId) :
    Polyline.allSegsMiss pts (shiftR sx sy (actorRect pl cs o)) := by
  obtain ⟨src, dst, bs, bt, y, hsrc, hdst, hbs, hbt, hfr, hto, hy, hsh⟩ := hf
  have hos : o ≠ src := by
    intro h
    subst h
    rw [hbs] at hj
    have := Option.some.inj hj
    subst this
    exact h1 hfr.symm
  have hod : o ≠ dst := by
    intro h
    subst h
    rw [hbt] at hj
    have := Option.some.inj hj
    subst this
    exact h2 hto.symm
  have hlo : o < pl.widths.length := by rw [F.pf.lenW]; exact ho
  have hls : src < pl.widths.length := by rw [F.pf.lenW]; exact hsrc
  have hld : dst < pl.widths.length := by rw [F.pf.lenW]; exact hdst
  have hs := lifeline_outside F.wf F.hcs hos hlo hls
  have hd := lifeline_outside F.wf F.hcs hod hlo hld
  have hbh := F.pf.bandH o
  have hbm := F.wf.pos.boxMargin
  have hbH0 := F.pf.bandH0
  have hdepth := F.wf.pos.selfLoopDepth
  have hyy : pl.bandTop + pl.heights.getD o 0 ≤ y := by unfold B0 at hy; omega
  have hvs : cs.getD src 0 + sx ≤ (shiftR sx sy (actorRect pl cs o)).x ∨
      (shiftR sx sy (actorRect pl cs o)).x + (shiftR sx sy (actorRect pl cs o)).w ≤
        cs.getD src 0 + sx := by
    unfold shiftR actorRect; dsimp only; omega
  have hvd : cs.getD dst 0 + sx ≤ (shiftR sx sy (actorRect pl cs o)).x ∨
      (shiftR sx sy (actorRect pl cs o)).x + (shiftR sx sy (actorRect pl cs o)).w ≤
        cs.getD dst 0 + sx := by
    unfold shiftR actorRect; dsimp only; omega
  have hhy : (shiftR sx sy (actorRect pl cs o)).y + (shiftR sx sy (actorRect pl cs o)).h ≤ y + sy := by
    unfold shiftR actorRect; dsimp only; omega
  have hhy2 : (shiftR sx sy (actorRect pl cs o)).y + (shiftR sx sy (actorRect pl cs o)).h ≤
      y + pl.c.selfLoopDepth + sy := by
    unfold shiftR actorRect; dsimp only; omega
  rcases hsh with ⟨-, hp⟩ | ⟨-, dx, -, hp⟩
  · rw [hp]
    exact ⟨seg_vx hvs, seg_hy hhy, seg_vx hvd, trivial⟩
  · rw [hp]
    exact ⟨seg_vx hvs, seg_hy hhy, seg_vy hhy hhy2, seg_hy hhy2, seg_vx hvs, trivial⟩

theorem dump_c6 {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C6 (dumpOf pl cs w) := by
  intro r hr b hb hex hnot
  obtain ⟨i, rm, hrm, rfl⟩ := mem_dump_routes.mp hr
  obtain ⟨j, bm, hbm, rfl⟩ := mem_dump_boxes.mp hb
  have hform := droute_form F hrm
  have hid : boxId pl.m j = bm.id := boxId_of_getElem pl.m j bm hbm
  have n1 : bm.id ≠ rm.fromId := fun h => hnot (by simp [LayoutDump.routeScope, droute, dbox, h])
  have n2 : bm.id ≠ rm.toId := fun h => hnot (by simp [LayoutDump.routeScope, droute, dbox, h])
  rcases box_cls F hbm with ⟨o, ho, hao, hnp, hact, hex', hr', hpar⟩ | ⟨-, -, hex', -, -⟩ |
      ⟨-, hex', -⟩
  · have hall := route_clear_actor F hform ho (j := j) hao (by rw [hid]; exact n1)
      (by rw [hid]; exact n2)
    have hrect : (dbox pl w bm j).rect = shiftR (sxOf pl w) pl.c.diagramMarginY (actorRect pl cs o) := by
      show shiftR _ _ (rr w j) = _
      rw [hr']
    show ¬ Polyline.hitsRect (droute pl w rm i).points (dbox pl w bm j).rect
    rw [hrect]
    exact Polyline.not_hits_of_allMiss hall
  · exact absurd hex (by simp [dbox, hex'])
  · exact absurd hex (by simp [dbox, hex'])

end Sequence
end Elegant
