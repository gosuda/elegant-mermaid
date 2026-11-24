import Elegant.Kinds.IshikawaPlaceDrawnBound

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-!
# Birth-index route bound for Ishikawa ribs.

Target `(1)`: `ishikawaBoundaryRouteXNonpos'` proves the residual
`IshikawaBoundaryRouteXNonpos` with no odd-bone hypothesis. The induction runs
over the executed `place` loop (`Elegant.forIn_processed`), carrying for every
loop bone together: its `IndexedBoneGenealogy` derivation, its drawn counter
equal to `processedOddDraws done`, and the bounds `x1 ≤ x0 ∧ x0 ≤ 0`; plus the
route bound for every accumulated piece. Odd-born bones close through
`accounted_odd_born_x0_nonpos_of_prefix` (drawn half from the loop invariant
`place_drawn_le_count`); even-born bones interpolate inside the parent slot
(the slot gaps `generated_entry_parent_slot_gaps`); cause pieces are direct.

Probe (same replay as `IshikawaPlaceDrawnBound`, 10 layouts, 16 ribs):
`drawBad = 0` (78 bones), `oddBad = 0` (28 odd-born), `upBad = 0` (156 route
points). The pure-genealogy odd-bone statement stays false (overdrawn witness
`s06b` vector `x0 = 1180`); the induction below threads accounted draws only,
so ancestor overdraw never enters.
-/

/-- Split helper for the `place` bind chain (cf. `clearance_bind_ok`). -/
private theorem place_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Lookup preserved under point update (cf. `indexed_lookup_set`). -/
private theorem place_lookup_set {α : Type} (P : Nat → α → Prop)
    (xs : List α) (i : Nat) (replacement : α)
    (hold : ∀ j value, xs[j]? = some value → P j value)
    (hnew : P i replacement) :
    ∀ j value, (xs.set i replacement)[j]? = some value → P j value := by
  intro j value hvalue
  by_cases heq : i = j
  · subst j
    have hlt : i < xs.length := by
      simpa only [List.length_set] using (List.getElem?_eq_some_iff.mp hvalue).1
    rw [List.getElem?_set_self hlt] at hvalue
    cases hvalue
    exact hnew
  · rw [List.getElem?_set_ne heq] at hvalue
    exact hold j value hvalue

/-- Lookup preserved under append (cf. `indexed_lookup_append_one`). -/
private theorem place_lookup_append_one {α : Type} (P : Nat → α → Prop)
    (xs : List α) (new : α)
    (hold : ∀ j value, xs[j]? = some value → P j value)
    (hnew : P xs.length new) :
    ∀ j value, (xs ++ [new])[j]? = some value → P j value := by
  intro j value hvalue
  by_cases hlt : j < xs.length
  · rw [List.getElem?_append_left hlt] at hvalue
    exact hold j value hvalue
  · have hbound := (List.getElem?_eq_some_iff.mp hvalue).1
    have heq : j = xs.length := by
      simp only [List.length_append, List.length_singleton] at hbound
      omega
    subst j
    rw [List.getElem?_append_right (Nat.le_refl xs.length)] at hvalue
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hvalue
    subst value
    exact hnew

/-- Successful layouts validate every numeric parameter used below. -/
private theorem place_param_facts (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hne : ns ≠ []) (hrun : Elegant.Ishikawa.layout ns p = .ok raw) :
    0 ≤ p.cos ∧ 1 ≤ p.sin ∧ 1 ≤ p.base ∧ 1 ≤ p.stub ∧ 0 ≤ p.perChild := by
  cases ns with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
    unfold Elegant.Ishikawa.layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    split at hrun
    · simp only [bind, Except.bind] at hrun
      cases hrun
    · split at hrun
      · simp only [bind, Except.bind] at hrun
        cases hrun
      · rename_i hparameters
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hparameters
        omega

/-- The `place` loop keeps every bone and every piece route at nonpositive x.
The fold carries genealogy, drawn accounting, bone bounds, and piece-route
bounds together; the conclusion is the piece-route conjunct. -/
theorem place_loop_route_x_nonpos
    (ns : List Tree.Node) (p : Params) (spine : Int)
    (_gen : Rib) (cause k : Nat) (ribs : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (hcos : 0 ≤ p.cos) (hsin : 1 ≤ p.sin)
    (_hbase : 1 ≤ p.base) (_hstub : 1 ≤ p.stub) (_hper : 0 ≤ p.perChild)
    (hlength : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).length)
    (hheights : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).heights)
    (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed) :
    ∀ (i : Nat) (rect : Rect) (points : List Point),
      (i, rect, points) ∈ placed.pieces → ∀ q ∈ points, q.x ≤ 0 := by
  let R := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  have hR : R = effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k)) := rfl
  have hheightsR : 0 ≤ R.heights := hheights
  have hrun0 : 0 ≤ run p R.length :=
    Int.fdiv_nonneg (Int.mul_nonneg hlength hcos) (by omega)
  simp only [place, ← hR] at hplace
  cases hcauseN : ns[R.cause]? with
  | none => simp only [hcauseN] at hplace; cases hplace
  | some causeNode =>
    simp only [hcauseN] at hplace
    obtain ⟨mid, hloop, hret⟩ := place_bind_ok hplace
    let P := fun (done : List (Entry × Nat))
        (st : List (Nat × Rect × List Point) × List Bone) =>
      st.2.length = done.length + 1 ∧
      (∀ (j : Nat) (b : Bone), st.2[j]? = some b →
        IndexedBoneGenealogy ns p R j b) ∧
      (∀ (owner : Nat) (b : Bone), st.2[owner]? = some b →
        b.drawn = processedOddDraws done owner) ∧
      (∀ source ∈ done, (source.1.parent + 1).toNat < st.2.length) ∧
      (∀ (j : Nat) (b : Bone), st.2[j]? = some b →
        Bone.x1 b ≤ Bone.x0 b ∧ Bone.x0 b ≤ 0) ∧
      ∀ i rect points, (i, rect, points) ∈ st.1 → ∀ q ∈ points, q.x ≤ 0
    have hinv : P ([] ++ R.entries.zipIdx) mid := by
      refine Elegant.forIn_processed [] _ _ _ _ P ?_ ?_ hloop
      · constructor
        · rfl
        · constructor
          · intro j b hb
            cases j with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
              subst b
              exact IndexedBoneGenealogy.root
            | succ j => simp at hb
          · constructor
            · intro owner b hb
              cases owner with
              | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
                subst b
                rfl
              | succ owner => simp at hb
            · constructor
              · intro source hs
                cases hs
              · constructor
                · intro j b hb
                  cases j with
                  | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
                    subst b
                    have hx : -run p R.length ≤ (0 : Int) := by
                      have h := hrun0
                      omega
                    exact ⟨hx, Int.le_refl 0⟩
                  | succ j => simp at hb
                · intro i rect points hmem
                  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨rfl, rfl, rfl⟩
                  intro q hq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                  rcases hq with rfl | rfl
                  · exact Int.le_refl 0
                  · have hx : -run p R.length ≤ (0 : Int) := by
                      have h := hrun0
                      omega
                    exact hx
      · intro done entry rest state next heq hi hstep
        obtain ⟨hlenIH, hgeneIH, haccIH, hfrontIH, hbndIH, hpieceIH⟩ := hi
        obtain ⟨e, idx⟩ := entry
        have he : (e, idx) ∈ R.entries.zipIdx := by
          simp only [List.nil_append] at heq
          rw [heq]
          simp
        have heG : (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx := he
        have hidx : idx = done.length := by
          have hz := zipIdx_processed_index R.entries 0 done rest e idx
            (by simpa only [List.nil_append] using heq)
          simpa only [Nat.zero_add] using hz
        have hprefix : (generatedRib ns (cause, k)).entries.zipIdx =
            done ++ (e, idx) :: rest := heq
        cases hpar : state.2[(e.parent + 1).toNat]? with
        | none => simp only [hpar, bind, Except.bind] at hstep; cases hstep
        | some par =>
          have hgene := hgeneIH _ _ hpar
          have hparB := hbndIH _ _ hpar
          have hpx0 : par.x0 ≤ 0 := hparB.2
          have hspan : par.x1 ≤ par.x0 := hparB.1
          have hpx1 : par.x1 ≤ 0 := by
            have h := hparB
            omega
          have hparentDraw := haccIH _ _ hpar
          have hparentBound := (List.getElem?_eq_some_iff.mp hpar).1
          have hdrawB := place_lookup_set (IndexedBoneGenealogy ns p R)
            state.2 ((e.parent + 1).toNat) { par with drawn := par.drawn + 1 }
            hgeneIH (IndexedBoneGenealogy.draw _ par hgene)
          cases hpos : R.order.zipIdx.find? (fun v => v.1 == idx) with
          | none => simp only [hpar, hpos, bind, Except.bind] at hstep; cases hstep
          | some pos =>
            have hposG : (generatedRib ns (cause, k)).order.zipIdx.find?
                (fun v => v.1 == idx) = some pos := hpos
            let newBone := depthBone p par e.depth
              (Int.fdiv (R.length * (pos.2 + 1 : Nat)) (R.entries.length + 1 : Nat))
              (children ns e.node).length (run p R.heights + 3)
            have hzero : newBone.drawn = 0 := by
              dsimp only [newBone]
              unfold depthBone
              split <;> rfl
            have haccountNext := processedOddDraws_actual_set_append done e idx
              state.2 par newBone hpar haccIH hfrontIH hzero
            have hgap := generated_entry_parent_slot_gaps ns p ribs hg cause k
              hsource hlink hcause e idx pos par heG hposG hgene
            have hmargin : 0 ≤ run p R.heights + 3 := by
              have h : 0 ≤ run p R.heights :=
                Int.fdiv_nonneg (Int.mul_nonneg hheights hcos) (by omega)
              omega
            have hbl : 0 ≤ boneLength p (children ns e.node).length
                (run p R.heights + 3) :=
              Int.le_trans
                (Int.mul_nonneg (by omega : (0 : Int) ≤
                  (children ns e.node).length + 1) hmargin)
                (Int.le_max_right _ _)
            have hbB : newBone.x1 ≤ newBone.x0 ∧ newBone.x0 ≤ 0 := by
              by_cases hd : e.depth % 2 = 0
              · have hgapE := hgap.2 hd
                have hslot1 : par.t0 + R.heights ≤
                    Int.fdiv (R.length * (pos.2 + 1 : Nat))
                      (R.entries.length + 1 : Nat) := hgapE.1
                have hslot2 : Int.fdiv (R.length * (pos.2 + 1 : Nat))
                    (R.entries.length + 1 : Nat) + R.heights ≤
                    par.t1 := hgapE.2
                have hm0 : 0 ≤ Int.fdiv (R.length * (pos.2 + 1 : Nat))
                    (R.entries.length + 1 : Nat) - par.t0 := by
                  have h1 := hslot1
                  omega
                have hmd : Int.fdiv (R.length * (pos.2 + 1 : Nat))
                    (R.entries.length + 1 : Nat) - par.t0 ≤
                    par.t1 - par.t0 := by
                  have h1 := hslot1
                  have h2 := hslot2
                  omega
                have hNB : newBone = depthBone p par e.depth
                    (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                      (R.entries.length + 1 : Nat))
                    (children ns e.node).length (run p R.heights + 3) := rfl
                have hx0e : newBone.x0 = par.x0 + Int.fdiv
                    ((par.x1 - par.x0) * (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                      (R.entries.length + 1 : Nat) - par.t0))
                    (par.t1 - par.t0) := by
                  rw [hNB]
                  simp [depthBone, hd]
                have hb0 : newBone.x0 ≤ 0 := by
                  rw [hx0e]
                  by_cases hd0 : par.t1 - par.t0 = 0
                  · have hmz : Int.fdiv (R.length * (pos.2 + 1 : Nat))
                        (R.entries.length + 1 : Nat) - par.t0 = 0 := by
                      omega
                    have hf : Int.fdiv
                        ((par.x1 - par.x0) * (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                          (R.entries.length + 1 : Nat) - par.t0))
                        (par.t1 - par.t0) = 0 := by
                      rw [hd0, hmz, Int.mul_zero]
                      rfl
                    omega
                  · have hd0' : 0 < par.t1 - par.t0 := by omega
                    by_cases hpa : par.x1 - par.x0 ≤ 0
                    · have hh : (par.x1 - par.x0) * (Int.fdiv
                          (R.length * (pos.2 + 1 : Nat))
                          (R.entries.length + 1 : Nat) - par.t0) ≤ 0 := by
                        have h := Int.mul_le_mul_of_nonneg_right
                          (show par.x1 - par.x0 ≤ 0 by omega) hm0
                        simpa only [Int.zero_mul] using h
                      have hf : Int.fdiv
                          ((par.x1 - par.x0) * (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                            (R.entries.length + 1 : Nat) - par.t0))
                          (par.t1 - par.t0) ≤ 0 :=
                        Elegant.Chart.fdiv_le_of_le_mul hd0' (by omega)
                      omega
                    · have hpa' : 0 < par.x1 - par.x0 := by omega
                      have hm1 : (par.x1 - par.x0) * (Int.fdiv
                          (R.length * (pos.2 + 1 : Nat))
                          (R.entries.length + 1 : Nat) - par.t0) ≤
                          (par.x1 - par.x0) * (par.t1 - par.t0) :=
                        Int.mul_le_mul_of_nonneg_left hmd (by omega)
                      have hm1' : (par.x1 - par.x0) * (Int.fdiv
                          (R.length * (pos.2 + 1 : Nat))
                          (R.entries.length + 1 : Nat) - par.t0) ≤
                          (par.t1 - par.t0) * (par.x1 - par.x0) := by
                        rw [Int.mul_comm (par.t1 - par.t0) (par.x1 - par.x0)]
                        exact hm1
                      have hf : Int.fdiv
                          ((par.x1 - par.x0) * (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                            (R.entries.length + 1 : Nat) - par.t0))
                          (par.t1 - par.t0) ≤ par.x1 - par.x0 :=
                        Elegant.Chart.fdiv_le_of_le_mul hd0' hm1'
                      omega
                have hends := depthBone_even_endpoints p par e.depth
                  (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                    (R.entries.length + 1 : Nat))
                  (children ns e.node).length (run p R.heights + 3) hd
                have hx1 : newBone.x1 = newBone.x0 - boneLength p
                    (children ns e.node).length (run p R.heights + 3) := hends.2.2
                exact ⟨by rw [hx1]; omega, hb0⟩
              · have hodd : e.depth % 2 ≠ 0 := hd
                have hgapO := hgap.1 hodd
                have hx0 : newBone.x0 ≤ 0 :=
                  accounted_odd_born_x0_nonpos_of_prefix ns p cause k
                    (measuredSideLength p ribs) hlink hcause _ par hgene
                    done ((e, idx) :: rest) hprefix hparentDraw e.depth
                    (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                      (R.entries.length + 1 : Nat))
                    (children ns e.node).length (run p R.heights + 3)
                    hodd hspan hpx0
                have hends := depthBone_odd_endpoints p par e.depth
                  (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                    (R.entries.length + 1 : Nat))
                  (children ns e.node).length (run p R.heights + 3) hodd
                have hx1 : newBone.x1 = newBone.x0 - run p
                    (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                      (R.entries.length + 1 : Nat) - par.t0) := hends.2.2.2
                have hrunS : 0 ≤ run p
                    (Int.fdiv (R.length * (pos.2 + 1 : Nat))
                      (R.entries.length + 1 : Nat) - par.t0) := by
                  have hrise : 0 ≤ Int.fdiv (R.length * (pos.2 + 1 : Nat))
                      (R.entries.length + 1 : Nat) - par.t0 := by
                    have h1 : par.t0 + R.heights ≤
                        Int.fdiv (R.length * (pos.2 + 1 : Nat))
                          (R.entries.length + 1 : Nat) := hgapO
                    omega
                  exact Int.fdiv_nonneg (Int.mul_nonneg hrise hcos) (by omega)
                exact ⟨by rw [hx1]; omega, hx0⟩
            have hbaseSet : ∀ (j : Nat) (v : Bone),
                (state.2.set ((e.parent + 1).toNat)
                { par with drawn := par.drawn + 1 })[j]? = some v →
                Bone.x1 v ≤ Bone.x0 v ∧ Bone.x0 v ≤ 0 :=
              place_lookup_set _ _ _ _ hbndIH ⟨hspan, hpx0⟩
            by_cases hg : ((e.depth % 2 == 0) && decide (par.t1 ≤ par.t0)) = true
            · simp only [hpar, hpos, hg, ite_true, bind, Except.bind] at hstep
              cases hstep
            · simp only [hpar, hpos, hg, Bool.false_eq_true, ↓reduceIte,
                bind, Except.bind] at hstep
              split at hstep <;> rename_i hodd
              all_goals
                cases hn : ns[e.node]? with
                | none => simp only [hn] at hstep; cases hstep
                | some n =>
                  have hpieceNext : ∀ i rect points,
                      (i, rect, points) ∈ state.1 ++ [(e.node,
                        (⟨newBone.x1 - n.width,
                          ordinate spine R.upper newBone.t1 -
                            Int.fdiv n.height 2,
                          n.width, n.height⟩ : Rect),
                        [⟨newBone.x0, ordinate spine R.upper newBone.t0⟩,
                          ⟨newBone.x1,
                            ordinate spine R.upper newBone.t1⟩])] →
                      ∀ q ∈ points, q.x ≤ 0 := by
                    intro i rect points hmem
                    simp only [List.mem_append, List.mem_singleton,
                      Prod.mk.injEq] at hmem
                    rcases hmem with hmem | ⟨rfl, rfl, rfl⟩
                    · exact hpieceIH i rect points hmem
                    · intro q hq
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                      rcases hq with rfl | rfl
                      · exact hbB.2
                      · exact Int.le_trans hbB.1 hbB.2
                  simp only [hn, pure, Except.pure, Except.ok.injEq] at hstep
                  subst next
                  refine ⟨_, rfl, ?_⟩
                  constructor
                  · simpa only [List.length_append, List.length_singleton,
                      List.length_set] using congrArg (fun n : Nat => n + 1) hlenIH
                  · constructor
                    · have hnew := IndexedBoneGenealogy.entry par e idx pos
                        hgene he hpos
                      first
                      | apply place_lookup_append_one
                          (IndexedBoneGenealogy ns p R) _ _ hdrawB
                        simpa only [List.length_set, hlenIH, hidx] using hnew
                      | apply place_lookup_append_one
                          (IndexedBoneGenealogy ns p R) _ _ hgeneIH
                        simpa only [hlenIH, hidx] using hnew
                    · constructor
                      · first
                        | simpa only [hodd, ↓reduceIte] using haccountNext
                        | simpa only [hodd, Bool.false_eq_true, ↓reduceIte]
                          using haccountNext
                      · constructor
                        · intro source hs
                          simp only [List.mem_append, List.mem_singleton] at hs
                          simp only [List.length_append, List.length_singleton,
                            List.length_set]
                          rcases hs with hs | rfl
                          · exact Nat.lt_trans (hfrontIH source hs)
                              (Nat.lt_succ_self state.2.length)
                          · exact Nat.lt_trans hparentBound
                              (Nat.lt_succ_self state.2.length)
                        · constructor
                          · first
                            | exact place_lookup_append_one
                                (fun _ (b : Bone) =>
                                  Bone.x1 b ≤ Bone.x0 b ∧ Bone.x0 b ≤ 0) _ _
                                hbaseSet hbB
                            | exact place_lookup_append_one
                                (fun _ (b : Bone) =>
                                  Bone.x1 b ≤ Bone.x0 b ∧ Bone.x0 b ≤ 0) _ _
                                hbndIH hbB
                          · exact hpieceNext
    simp only [pure, Except.pure, Except.ok.injEq] at hret
    subst placed
    intro i rect points hmem q hq
    exact (hinv.2.2.2.2.2 i rect points hmem) q hq

/-- Target (1): every placed rib-piece route point lies at nonpositive x, with
no odd-bone hypothesis. -/
theorem ishikawaBoundaryRouteXNonpos' (m : Model) :
    IshikawaBoundaryRouteXNonpos m := by
  intro e rib hrib piece hmem q hq
  obtain ⟨source, cause, k, hsource, hcauseIdx, heq, hplace⟩ :=
    placed_rib_source e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.ribs e.placed e.length e.spine e.hribs e.hplaced rib hrib
  have hcause : cause ∈ children e.input.nodes 0 :=
    List.fst_mem_of_mem_zipIdx hcauseIdx
  have hsourceG : generatedRib e.input.nodes (cause, k) ∈ e.ribs := by
    rw [← heq]
    exact hsource
  have hne : e.input.nodes ≠ [] := by
    intro hnil
    have hh := e.hhead
    rw [hnil] at hh
    simp at hh
  have hparam := place_param_facts e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout
  have hlink := Elegant.Kinds.IshikawaValid.successful_link _ _ _ e.hlayout
  have hL : 0 ≤ (effectivePlacedInput e.input.nodes
      (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
      (generatedRib e.input.nodes (cause, k))).length :=
    successful_nonempty_effective_length_nonnegative _ _ _ hne e.hlayout _ _
  have hH : 0 ≤ (effectivePlacedInput e.input.nodes
      (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
      (generatedRib e.input.nodes (cause, k))).heights := by
    have hh0 : 0 ≤ (generatedRib e.input.nodes (cause, k)).heights := by
      rw [(generated_rib_fields e.input.nodes cause k).2.2.2]
      exact entry_height_fold_initial _ _ 0
    exact hh0
  have hplace' : place e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.spine
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))) = .ok rib := by
    rw [e.hlength, heq] at hplace
    exact hplace
  exact place_loop_route_x_nonpos e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.spine
    (generatedRib e.input.nodes (cause, k)) cause k e.ribs e.hribs hsourceG
    hlink hcause hparam.1 hparam.2.1 hparam.2.2.1 hparam.2.2.2.1
    hparam.2.2.2.2 hL hH rib hplace' _ _ _ hmem q hq

/-- Target (2): boundary clearance from the unconditional route bound. -/
theorem ishikawaBoundaryPieceClearance''' (m : Model) (hwf : WellFormed m)
    (hlimits : WithinLimits m) :
    IshikawaBoundaryPieceClearance m :=
  ishikawaBoundaryPieceClearance m hwf hlimits (ishikawaBoundaryRouteXNonpos' m)

/-- Target (3): the envelope lower half. Each route point lies at or right of
the left edge of a piece rect of the same rib; the pair minimum sits left of
every member rect by `extent_piece_bounds`. -/
theorem ishikawaRouteXExtentLower (m : Model) : IshikawaRouteXExtentLower m := by
  intro e P r hr hsub piece hm q hq
  have hflat : piece ∈ P.flatMap (·.pieces) :=
    List.mem_flatMap.mpr ⟨r, hr, hm⟩
  have hbnd := (extent_piece_bounds P piece hflat).1
  obtain ⟨source, cause, k, hsource, hcauseIdx, heq, hplace⟩ :=
    placed_rib_source e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.ribs e.placed e.length e.spine e.hribs e.hplaced r (hsub hr)
  have hcause : cause ∈ children e.input.nodes 0 :=
    List.fst_mem_of_mem_zipIdx hcauseIdx
  have hne : e.input.nodes ≠ [] := by
    intro hnil
    have hh := e.hhead
    rw [hnil] at hh
    simp at hh
  have hparam := place_param_facts e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout
  have hcos := hparam.1
  have hsin := hparam.2.1
  have hlink := Elegant.Kinds.IshikawaValid.successful_link _ _ _ e.hlayout
  have hplace' : place e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.spine
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))) = .ok r := by
    rw [e.hlength, heq] at hplace
    exact hplace
  have hdim := successful_node_dimensions e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout
  have hsourceG : generatedRib e.input.nodes (cause, k) ∈ e.ribs := by
    rw [← heq]
    exact hsource
  have hg := place_piece_accounted_geometry e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.spine _ r hplace'
    piece.1 piece.2.1 piece.2.2 hm
  have hL : 0 ≤ (effectivePlacedInput e.input.nodes
      (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
      (generatedRib e.input.nodes (cause, k))).length :=
    successful_nonempty_effective_length_nonnegative _ _ _ hne e.hlayout _ _
  have hH : 0 ≤ (effectivePlacedInput e.input.nodes
      (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
      (generatedRib e.input.nodes (cause, k))).heights := by
    have hh0 : 0 ≤ (generatedRib e.input.nodes (cause, k)).heights := by
      rw [(generated_rib_fields e.input.nodes cause k).2.2.2]
      exact entry_height_fold_initial _ _ 0
    exact hh0
  have hrun0 : 0 ≤ run (Elegant.Kinds.Ishikawa.params m.profile)
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))).length :=
    Int.fdiv_nonneg (Int.mul_nonneg hL hcos) (by omega)
  rcases hg with ⟨n, hn, hi, hrect, hpoints⟩ |
    ⟨e', idx, pos, par, n, done, rest, he, hpos, hn, hi, hpar, hprefix,
      hdrawn, hrect, hpoints⟩
  · have hw : 0 ≤ n.width :=
      Int.le_trans (by omega : (0 : Int) ≤ 1) (hdim n (List.mem_of_getElem? hn)).1
    have hfw : 0 ≤ Int.fdiv n.width 2 :=
      Int.fdiv_nonneg hw (by decide)
    have hrx : piece.2.1.x ≤ (0 : Int) := by
      rw [hrect]
      show -run (Elegant.Kinds.Ishikawa.params m.profile)
          (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).length -
          Int.fdiv n.width 2 ≤ 0
      omega
    have hrxL : piece.2.1.x ≤ -run (Elegant.Kinds.Ishikawa.params m.profile)
        (effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).length := by
      rw [hrect]
      show -run (Elegant.Kinds.Ishikawa.params m.profile)
          (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).length -
          Int.fdiv n.width 2 ≤ -run (Elegant.Kinds.Ishikawa.params m.profile)
          (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).length
      omega
    rw [hpoints] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Int.le_trans hbnd hrx
    · exact Int.le_trans hbnd hrxL
  · have hw : 0 ≤ n.width :=
      Int.le_trans (by omega : (0 : Int) ≤ 1) (hdim n (List.mem_of_getElem? hn)).1
    have hgap := generated_entry_parent_slot_gaps e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.ribs e.hribs cause k
      hsourceG hlink hcause e' idx pos par he hpos hpar
    have hspan : (depthBone (Elegant.Kinds.Ishikawa.params m.profile) par
        e'.depth
        (Int.fdiv ((effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).length * (pos.2 + 1 : Nat))
          ((effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).entries.length + 1 : Nat))
        (children e.input.nodes e'.node).length
        (run (Elegant.Kinds.Ishikawa.params m.profile)
          (effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).heights + 3)).x1 ≤
        (depthBone (Elegant.Kinds.Ishikawa.params m.profile) par
        e'.depth
        (Int.fdiv ((effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).length * (pos.2 + 1 : Nat))
          ((effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).entries.length + 1 : Nat))
        (children e.input.nodes e'.node).length
        (run (Elegant.Kinds.Ishikawa.params m.profile)
          (effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).heights + 3)).x0 := by
      by_cases hd : e'.depth % 2 = 0
      · have hends := depthBone_even_endpoints
          (Elegant.Kinds.Ishikawa.params m.profile) par e'.depth
          (Int.fdiv ((effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).length * (pos.2 + 1 : Nat))
            ((effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).entries.length + 1 : Nat))
          (children e.input.nodes e'.node).length
          (run (Elegant.Kinds.Ishikawa.params m.profile)
            (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).heights + 3) hd
        have hmargin : 0 ≤ run (Elegant.Kinds.Ishikawa.params m.profile)
            (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).heights + 3 := by
          have h : 0 ≤ run (Elegant.Kinds.Ishikawa.params m.profile)
              (effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
                e.ribs)
              (generatedRib e.input.nodes (cause, k))).heights :=
            Int.fdiv_nonneg (Int.mul_nonneg hH hcos) (by omega)
          omega
        have hbl : 0 ≤ boneLength (Elegant.Kinds.Ishikawa.params m.profile)
            (children e.input.nodes e'.node).length
            (run (Elegant.Kinds.Ishikawa.params m.profile)
              (effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
                e.ribs)
              (generatedRib e.input.nodes (cause, k))).heights + 3) := by
          unfold boneLength
          exact Int.le_trans
            (Int.mul_nonneg (by omega : (0 : Int) ≤
              (children e.input.nodes e'.node).length + 1)
              (by have h := hmargin; omega))
            (Int.le_max_right _ _)
        have hx1 := hends.2.2
        omega
      · have hodd : e'.depth % 2 ≠ 0 := hd
        have hends := depthBone_odd_endpoints
          (Elegant.Kinds.Ishikawa.params m.profile) par e'.depth
          (Int.fdiv ((effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).length * (pos.2 + 1 : Nat))
            ((effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).entries.length + 1 : Nat))
          (children e.input.nodes e'.node).length
          (run (Elegant.Kinds.Ishikawa.params m.profile)
            (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
              e.ribs)
            (generatedRib e.input.nodes (cause, k))).heights + 3) hodd
        have hx1 := hends.2.2.2
        have hslot := hgap.1 hodd
        have hrunS : 0 ≤ run (Elegant.Kinds.Ishikawa.params m.profile)
            (Int.fdiv ((effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
                e.ribs)
              (generatedRib e.input.nodes (cause, k))).length * (pos.2 + 1 : Nat))
              ((effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
                e.ribs)
              (generatedRib e.input.nodes (cause, k))).entries.length + 1 : Nat) -
              par.t0) := by
          have hrise : 0 ≤ Int.fdiv ((effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
                e.ribs)
              (generatedRib e.input.nodes (cause, k))).length * (pos.2 + 1 : Nat))
              ((effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile)
                e.ribs)
              (generatedRib e.input.nodes (cause, k))).entries.length + 1 : Nat) -
              par.t0 := by
            have h1 := hslot
            omega
          exact Int.fdiv_nonneg (Int.mul_nonneg hrise hcos) (by omega)
        omega
    let B := depthBone (Elegant.Kinds.Ishikawa.params m.profile) par
        e'.depth
        (Int.fdiv ((effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).length * (pos.2 + 1 : Nat))
          ((effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).entries.length + 1 : Nat))
        (children e.input.nodes e'.node).length
        (run (Elegant.Kinds.Ishikawa.params m.profile)
          (effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).heights + 3)
    have hspanB : B.x1 ≤ B.x0 := hspan
    have eRect : piece.2.1.x = B.x1 - n.width := by rw [hrect]
    rw [hpoints] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · show (extent P).1 ≤ B.x0
      exact Int.le_trans hbnd (by rw [eRect]; have h := hspanB; omega)
    · show (extent P).1 ≤ B.x1
      exact Int.le_trans hbnd (by rw [eRect]; omega)

/-- Target (4): cross-rib clearance with no hypothesis. -/
theorem ishikawaCrossRibPieceClearance''' (m : Model) :
    IshikawaCrossRibPieceClearance m :=
  ishikawaCrossRibPieceClearance' m
    (ishikawaRouteXEnvelope_of_lower_upper m (ishikawaRouteXExtentLower m)
      (ishikawaBoundaryRouteXNonpos' m))

end Elegant.Kinds.IshikawaFinal
