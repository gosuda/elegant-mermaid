import Elegant.SequenceValid4

set_option autoImplicit false

/-! The routes of the dump: their points, and clauses 4, 5, and 6 of the validator
(`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem routeEndsOk_spec {pl : Plan} {route src dst : Nat} {r : ModelRoute}
    (h : routeEndsOk pl route src dst = true) (hr : pl.m.routes[route]? = some r) :
    ∃ bs bt, pl.actorBoxes[src]? = some bs ∧ pl.actorBoxes[dst]? = some bt ∧
      r.fromId = boxId pl.m bs ∧ r.toId = boxId pl.m bt := by
  unfold routeEndsOk at h
  rw [hr] at h
  cases hs : pl.actorBoxes[src]? with
  | none => simp [hs] at h
  | some bs =>
    cases hd : pl.actorBoxes[dst]? with
    | none => simp [hs, hd] at h
    | some bt =>
      simp only [hs, hd, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨bs, bt, rfl, rfl, h.1, h.2⟩

/-- The points of a route of the dump: a message between two lifelines, or a self message. -/
def RouteForm (pl : Plan) (cs : List Int) (w : Walk) (sx sy : Int) (r : ModelRoute)
    (pts : List Point) : Prop :=
  ∃ (src dst bs bt : Nat) (y : Int), src < pl.actorBoxes.length ∧ dst < pl.actorBoxes.length ∧
    pl.actorBoxes[src]? = some bs ∧ pl.actorBoxes[dst]? = some bt ∧
    r.fromId = boxId pl.m bs ∧ r.toId = boxId pl.m bt ∧ B0 pl ≤ y ∧
    ((src ≠ dst ∧ pts =
        [⟨cs.getD src 0 + sx, (rr w bs).y + (rr w bs).h + sy⟩, ⟨cs.getD src 0 + sx, y + sy⟩,
         ⟨cs.getD dst 0 + sx, y + sy⟩, ⟨cs.getD dst 0 + sx, (rr w bt).y + (rr w bt).h + sy⟩]) ∨
      (src = dst ∧ ∃ dx : Int, 0 ≤ dx ∧ pts =
        [⟨cs.getD src 0 + sx, (rr w bs).y + (rr w bs).h + sy⟩, ⟨cs.getD src 0 + sx, y + sy⟩,
         ⟨cs.getD src 0 + dx + sx, y + sy⟩, ⟨cs.getD src 0 + dx + sx, y + pl.c.selfLoopDepth + sy⟩,
         ⟨cs.getD src 0 + sx, y + pl.c.selfLoopDepth + sy⟩,
         ⟨cs.getD src 0 + sx, (rr w bt).y + (rr w bt).h + sy⟩]))

theorem actorBox_lt {pl : Plan} (hpf : PlanFacts pl) {o bs : Nat} (ho : o < pl.actorBoxes.length)
    (hbs : pl.actorBoxes[o]? = some bs) : bs < pl.m.boxes.length := by
  obtain ⟨b, hb, -⟩ := hpf.ab_actor o ho
  have e : pl.actorBoxes[o] = bs := by
    simp [List.getElem?_eq_getElem ho] at hbs
    exact hbs
  rw [e] at hb
  exact (List.getElem?_eq_some_iff.mp hb).1

theorem droute_form {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {i : Nat} {r : ModelRoute}
    (hr : pl.m.routes[i]? = some r) :
    RouteForm pl cs w (sxOf pl w) pl.c.diagramMarginY r (droute pl w r i).points := by
  have hlen : w.routeRuns.length = pl.m.routes.length := by
    rw [F.rinv.runs_len]
    exact finalOk_routes F.fin
  have hi : i < pl.m.routes.length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨run, hrun⟩ : ∃ run, w.routeRuns[i]? = some run :=
    ⟨w.routeRuns[i]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨src, dst, hsrc, hdst, hends, y, hy, hsh⟩ := F.rinv.runs_ok i run hrun
  obtain ⟨bs, bt, hbs, hbt, hf, ht⟩ := routeEndsOk_spec hends hr
  have hfi : pl.m.boxes.findIdx? (fun x => x.id == r.fromId) = some bs := by
    rw [hf]
    exact findIdx_boxId F.fm (actorBox_lt F.pf hsrc hbs)
  have hti : pl.m.boxes.findIdx? (fun x => x.id == r.toId) = some bt := by
    rw [ht]
    exact findIdx_boxId F.fm (actorBox_lt F.pf hdst hbt)
  have hd : (droute pl w r i).points = routePoints pl w (sxOf pl w) pl.c.diagramMarginY r run := by
    unfold droute
    simp only [hrun]
  rw [hd]
  refine ⟨src, dst, bs, bt, y, hsrc, hdst, hbs, hbt, hf, ht, hy, ?_⟩
  rcases hsh with ⟨hne, a, b, hp⟩ | ⟨heq, a, dx, hdx, hp⟩
  · left
    exact ⟨hne, routePoints_four pl w _ _ r run _ _ a b y bs bt hp hfi hti⟩
  · right
    refine ⟨heq, dx, hdx, ?_⟩
    exact routePoints_six pl w _ _ r run _ dx a y _ bs bt hp hfi hti

theorem actor_rect {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {o bs : Nat} (ho : o < pl.actorBoxes.length)
    (hbs : pl.actorBoxes[o]? = some bs) :
    ∃ y, rr w bs = ⟨cs.getD o 0 - half (pl.widths.getD o 0), y, pl.widths.getD o 0,
      pl.heights.getD o 0⟩ := by
  obtain ⟨y, hy⟩ := F.rinv.actor_form o ho
  have e : pl.actorBoxes.getD o 0 = bs := by simp [List.getD_eq_getElem?_getD, hbs]
  rw [e] at hy
  exact ⟨y, hy⟩

theorem dump_c4 {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C4 (dumpOf pl cs w) := by
  intro r hr _
  obtain ⟨i, rm, hrm, rfl⟩ := mem_dump_routes.mp hr
  obtain ⟨src, dst, bs, bt, y, -, -, -, -, -, -, -, hsh⟩ := droute_form F hrm
  rcases hsh with ⟨-, hp⟩ | ⟨-, dx, -, hp⟩
  · show Polyline.isOrthogonal (droute pl w rm i).points = true
    rw [hp]
    simp [Polyline.isOrthogonal]
  · show Polyline.isOrthogonal (droute pl w rm i).points = true
    rw [hp]
    simp [Polyline.isOrthogonal]

theorem box?_of_actor {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {bs : Nat} (hbs : bs < pl.m.boxes.length) :
    ∃ b, pl.m.boxes[bs]? = some b ∧ (dumpOf pl cs w).box? (boxId pl.m bs) = some (dbox pl w b bs) := by
  obtain ⟨b, hb⟩ : ∃ b, pl.m.boxes[bs]? = some b := ⟨pl.m.boxes[bs], List.getElem?_eq_getElem hbs⟩
  refine ⟨b, hb, ?_⟩
  rw [boxId_of_getElem pl.m bs b hb]
  exact box?_dbox F.fm hb

theorem onBoundary_foot {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {o bs : Nat} (ho : o < pl.actorBoxes.length)
    (hbs : pl.actorBoxes[o]? = some bs) (sx sy : Int) :
    Validator.onBoundary
      ⟨cs.getD o 0 + sx, (rr w bs).y + (rr w bs).h + sy⟩ (shiftR sx sy (rr w bs)) := by
  obtain ⟨y, hy⟩ := actor_rect F ho hbs
  have h1 := F.wf.widths o
  have h2 := F.wf.heights o
  have h3 := half_nonneg h1
  have h4 := half_le h1
  unfold Validator.onBoundary shiftR
  rw [hy]
  refine ⟨?_, ?_, ?_, ?_, Or.inr (Or.inr (Or.inr ?_))⟩ <;> dsimp only <;> omega

theorem dump_c5 {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C5 (dumpOf pl cs w) := by
  intro r hr
  obtain ⟨i, rm, hrm, rfl⟩ := mem_dump_routes.mp hr
  obtain ⟨src, dst, bs, bt, y, hsrc, hdst, hbs, hbt, hf, ht, hy, hsh⟩ := droute_form F hrm
  obtain ⟨fb, hfb, hfbox⟩ := box?_of_actor F (actorBox_lt F.pf hsrc hbs)
  obtain ⟨tb, htb, htbox⟩ := box?_of_actor F (actorBox_lt F.pf hdst hbt)
  have e1 : (droute pl w rm i).fromId = boxId pl.m bs := hf
  have e2 : (droute pl w rm i).toId = boxId pl.m bt := ht
  have hfo := onBoundary_foot F hsrc hbs (sxOf pl w) pl.c.diagramMarginY
  have hto := onBoundary_foot F hdst hbt (sxOf pl w) pl.c.diagramMarginY
  rcases hsh with ⟨-, hp⟩ | ⟨hs, dx, -, hp⟩
  · refine ⟨⟨cs.getD src 0 + sxOf pl w, (rr w bs).y + (rr w bs).h + pl.c.diagramMarginY⟩,
      ⟨cs.getD dst 0 + sxOf pl w, (rr w bt).y + (rr w bt).h + pl.c.diagramMarginY⟩,
      dbox pl w fb bs, dbox pl w tb bt, ?_, ?_, ?_, ?_, hfo, hto⟩
    · show (droute pl w rm i).points.head? = _
      rw [hp]; rfl
    · show (droute pl w rm i).points.getLast? = _
      rw [hp]; rfl
    · rw [e1]; exact hfbox
    · rw [e2]; exact htbox
  · subst hs
    have hbb : bt = bs := by
      rw [hbs] at hbt
      exact (Option.some.inj hbt).symm
    subst hbb
    refine ⟨⟨cs.getD src 0 + sxOf pl w, (rr w bt).y + (rr w bt).h + pl.c.diagramMarginY⟩,
      ⟨cs.getD src 0 + sxOf pl w, (rr w bt).y + (rr w bt).h + pl.c.diagramMarginY⟩,
      dbox pl w fb bt, dbox pl w tb bt, ?_, ?_, ?_, ?_, hfo, hto⟩
    · show (droute pl w rm i).points.head? = _
      rw [hp]; rfl
    · show (droute pl w rm i).points.getLast? = _
      rw [hp]; rfl
    · rw [e1]; exact hfbox
    · rw [e2]; exact htbox

end Sequence
end Elegant
