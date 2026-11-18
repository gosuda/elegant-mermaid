import Elegant.Kinds.IshikawaRawClearance
import Elegant.IshikawaClearanceFacts
import Elegant.IshikawaLayoutProvenanceFacts
import Elegant.IshikawaEnvFramesFacts
import Elegant.IshikawaAssemblyBoxFacts
import Elegant.IshikawaFlattenParentFacts
import Elegant.Kinds.IshikawaValid
import Elegant.Kinds.GitgraphFacts

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-- Residual envelope configurations for same-rib clearance: the two pair
shapes whose miss needs the rib x-envelope (master-diagonal side), which no
closed per-rib theorem supplies.

* Cause route against an entry box: the cause route spans every slot
  ordinate, so no slot gap separates it from an entry box; the miss needs
  the entry bone's left end to sit at least `run p r.heights + 1` left of
  the master diagonal at its slot (the ENV bound over executed bones).
* Odd route against a strict-descendant box (entry index later, order
  position earlier: `idxI < idxJ` with `posJ.2 < posI.2`, which is exactly
  the descendant configuration): the descendant box sits inside the route's
  ordinate span, so the miss needs the descendant x-transport along the
  ancestor chain, again an envelope fact.

Both configurations hold on executed layouts (the raw route/box clearance
probe found the unshifted miss true on 32 executed layouts, 4668 pairs),
each is one syntactic pair-configuration hence strictly simpler than the
goal, and both disjuncts are used below. Stated over the executed assembly
`e : IshikawaRawExecution m`, like the other residuals. -/
def IshikawaSameRibEnvelopeClearance (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (rA : Rib) (dx : Int),
    AssemblyPairShift e.placed (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
      rA dx →
    ∀ (pieceR pieceB : Nat × Rect × List Point),
      pieceR ∈ rA.pieces → pieceB ∈ rA.pieces →
      pieceR.1 ≠ pieceB.1 →
      ((pieceR.1 = rA.cause ∧ pieceB.1 ≠ rA.cause) ∨
        (∃ (eI eJ : Entry) (idxI idxJ : Nat) (posI posJ : Nat × Nat),
          (eI, idxI) ∈ rA.entries.zipIdx ∧
          (eJ, idxJ) ∈ rA.entries.zipIdx ∧
          pieceR.1 = eI.node ∧ pieceB.1 = eJ.node ∧
          eI.depth % 2 ≠ 0 ∧
          rA.order.zipIdx.find? (fun v => v.1 == idxI) = some posI ∧
          rA.order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ ∧
          idxI < idxJ ∧ posJ.2 < posI.2)) →
      ¬ Polyline.hitsRect pieceR.2.2 pieceB.2.1
private theorem same_rib_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩


/-- `place` only attaches pieces: cause, entries and order are preserved. -/
private theorem place_rib_fields_eq (ns : List Tree.Node) (p : Params)
    (spine : Int) (input placed : Rib)
    (h : place ns p spine input = .ok placed) :
    placed.cause = input.cause ∧ placed.entries = input.entries ∧
      placed.order = input.order := by
  simp only [place] at h
  cases hcause : ns[input.cause]? with
  | none =>
    simp only [hcause] at h
    cases h
  | some _ =>
    simp only [hcause] at h
    obtain ⟨mid, _, hret⟩ := same_rib_bind_ok h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
    cases hret
    exact ⟨rfl, rfl, rfl⟩

/-- Distinct entry indices hold distinct nodes (contrapositive form). -/
private theorem zipIdx_index_ne_of_node_ne' {es : List Entry} {eI eJ : Entry}
    {idxI idxJ : Nat}
    (heI : (eI, idxI) ∈ es.zipIdx) (heJ : (eJ, idxJ) ∈ es.zipIdx)
    (hnode : eI.node ≠ eJ.node) : idxI ≠ idxJ := by
  intro hidx
  have gI := List.mem_zipIdx_iff_getElem?.mp heI
  have gJ := List.mem_zipIdx_iff_getElem?.mp heJ
  change es[idxI]? = some eI at gI
  change es[idxJ]? = some eJ at gJ
  rw [← hidx] at gJ
  have heq : eI = eJ := Option.some.inj (gI.symm.trans gJ)
  exact hnode (congrArg Entry.node heq)

/-- Order positions of distinct entries differ in their slot coordinate. -/
private theorem order_positions_ne' {order : List Nat} {idxI idxJ : Nat}
    {posI posJ : Nat × Nat}
    (hI : order.zipIdx.find? (fun v => v.1 == idxI) = some posI)
    (hJ : order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ)
    (hidx : idxI ≠ idxJ) : posI.2 ≠ posJ.2 := by
  intro hpos
  have hIeq := List.find?_some hI
  have hJeq := List.find?_some hJ
  have hImem : posI ∈ order.zipIdx := List.mem_of_find?_eq_some hI
  have hJmem : posJ ∈ order.zipIdx := List.mem_of_find?_eq_some hJ
  have hI1 : posI.1 = idxI := by simpa only [beq_iff_eq] using hIeq
  have hJ1 : posJ.1 = idxJ := by simpa only [beq_iff_eq] using hJeq
  have gI := List.mem_zipIdx_iff_getElem?.mp hImem
  have gJ := List.mem_zipIdx_iff_getElem?.mp hJmem
  change order[posI.2]? = some posI.1 at gI
  change order[posJ.2]? = some posJ.1 at gJ
  rw [← hpos] at gJ
  have : posI.1 = posJ.1 := Option.some.inj (gI.symm.trans gJ)
  omega

/-- Same node in two entry slots forces equal slots, via node nodup. -/
private theorem entry_idx_eq_of_node_eq (es : List Entry)
    (hnd : (es.map Entry.node).Nodup)
    (eI eJ : Entry) (idxI idxJ : Nat)
    (heI : (eI, idxI) ∈ es.zipIdx) (heJ : (eJ, idxJ) ∈ es.zipIdx)
    (hnode : eI.node = eJ.node) : idxI = idxJ := by
  have gI := List.mem_zipIdx_iff_getElem?.mp heI
  have gJ := List.mem_zipIdx_iff_getElem?.mp heJ
  change es[idxI]? = some eI at gI
  change es[idxJ]? = some eJ at gJ
  have mI : (es.map Entry.node)[idxI]? = some eI.node := by
    rw [List.getElem?_map]
    rw [gI]
    rfl
  have mJ : (es.map Entry.node)[idxJ]? = some eJ.node := by
    rw [List.getElem?_map]
    rw [gJ]
    rfl
  rw [hnode] at mI
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp mI
  exact (hnd.getElem?_inj hi).mp (mI.trans mJ.symm)

/-- Children of the root are duplicate-free (filter of a range). -/
private theorem same_rib_children_nodup (ns : List Tree.Node) :
    (children ns 0).Nodup := by
  unfold children
  exact List.Sublist.nodup List.filter_sublist List.nodup_range

/-- Membership in `zipIdx` bounds the index below by the start. -/
private theorem same_rib_mem_zipIdx_ge {α : Type} (l : List α) (n : Nat)
    (a : α) (m : Nat) (h : (a, m) ∈ List.zipIdx l n) : n ≤ m := by
  revert n a m h
  induction l with
  | nil => intro n a m h; simp at h
  | cons x xs ih =>
    intro n a m h
    rw [List.zipIdx_cons] at h
    simp only [List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨_, hm⟩ := Prod.mk.inj h
      omega
    · exact Nat.le_trans (Nat.le_succ n) (ih (n + 1) a m h)

/-- `zipIdx` preserves nodup. -/
private theorem same_rib_zipIdx_nodup {α : Type} (l : List α)
    (h : l.Nodup) (n : Nat) : (List.zipIdx l n).Nodup := by
  induction l generalizing n with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have hxs : xs.Nodup := (List.nodup_cons.mp h).2
    rw [List.zipIdx_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      have hge : n + 1 ≤ n := same_rib_mem_zipIdx_ge xs (n + 1) x n hmem
      omega
    · exact ih hxs _

/-- Placed ribs have duplicate-free causes, hence equal the children list. -/
private theorem same_rib_causes_eq (m : Model) (e : IshikawaRawExecution m) :
    e.placed.map Rib.cause = children e.input.nodes 0 := by
  have hrec := Elegant.Kinds.Gitgraph.mapM_index_record _ _ _ e.hplaced
  have hlen : e.placed.length = (children e.input.nodes 0).length := by
    have h1 := hrec.1
    rw [e.hribs] at h1
    simp only [List.length_map, List.length_zipIdx] at h1
    omega
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map]
  cases hpl : e.placed[j]? with
  | none =>
    have hj : e.placed.length ≤ j := List.getElem?_eq_none_iff.mp hpl
    have hjc : (children e.input.nodes 0).length ≤ j := by omega
    rw [Option.map_none, List.getElem?_eq_none_iff.mpr hjc]
  | some r =>
    obtain ⟨src, hsrc, hplace⟩ := hrec.2 j r hpl
    rw [e.hribs, List.getElem?_map, List.getElem?_zipIdx] at hsrc
    cases hck : (children e.input.nodes 0)[j]? with
    | none =>
      simp only [hck, Option.map_none] at hsrc
      cases hsrc
    | some cause =>
      simp only [hck, Option.map_some, Nat.zero_add, Option.some.injEq] at hsrc
      have hfields := generated_rib_fields e.input.nodes cause j
      have hsc : src.cause = cause :=
        (congrArg Rib.cause hsrc.symm).trans hfields.1
      have hrc : r.cause = src.cause :=
        (place_rib_fields_eq _ _ _ _ _ hplace).1
      simp only [Option.map_some, hrc, hsc]

/-- A cause-nodup rib list is nodup. -/
private theorem same_rib_placed_nodup_of_causes {l : List Rib}
    (h : (l.map Rib.cause).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    have hcons : (a.cause :: t.map Rib.cause).Nodup := h
    have h1 := (List.nodup_cons.mp hcons).1
    have h2 := (List.nodup_cons.mp hcons).2
    exact List.nodup_cons.mpr
      ⟨fun hm => h1 (List.mem_map.mpr ⟨_, hm, rfl⟩), ih h2⟩

/-- Membership in the current assembly pair gives a small index. -/
private theorem assemblyShift_mem_take_pair {a : Rib} {rest : List Rib} {r : Rib}
    (h : r ∈ a :: rest.take 1) : ∃ i, i < 2 ∧ (a :: rest)[i]? = some r := by
  rcases List.mem_cons.mp h with rfl | hmem
  · exact ⟨0, by omega, rfl⟩
  · cases rest with
    | nil => simp at hmem
    | cons b bs =>
      have hb : r = b := List.eq_of_mem_singleton (by simpa using hmem)
      subst hb
      exact ⟨1, by omega, rfl⟩

/-- The assembly shift of a rib in a cause-nodup list is unique. -/
private theorem assemblyShift_fun_aux (placed : List Rib)
    (hnd : (placed.map Rib.cause).Nodup) :
    ∀ (n : Nat) {rs : List Rib} {C P : Int} {r : Rib} {dxA : Int}
      (_hA : AssemblyPairShift rs C P r dxA),
      rs = placed.drop n →
      ∀ {dxB : Int}, AssemblyPairShift rs C P r dxB → dxA = dxB := by
  intro n rs C P r dxA hA
  revert n
  induction hA with
  | current a rest C P r hr =>
    intro n hsuf dxB hB
    cases hB with
    | current _ _ _ _ _ _ => rfl
    | later _ _ _ _ _ _ htail =>
      exfalso
      obtain ⟨i, hi2, hii⟩ := assemblyShift_mem_take_pair hr
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (assemblyPairShift_mem htail)
      have e1 : placed[n + i]? = some r := by
        have h1 : (placed.drop n)[i]? = some r := by
          rw [← hsuf]
          exact hii
        rwa [List.getElem?_drop] at h1
      have e2 : placed[n + (j + 2)]? = some r := by
        have h1 : (placed.drop n)[j + 2]? = some r := by
          rw [← hsuf, show j + 2 = (j + 1) + 1 from by omega,
            List.getElem?_cons_succ, show j + 1 = 1 + j from by omega,
            ← List.getElem?_drop]
          exact hj
        rwa [List.getElem?_drop] at h1
      have g1 : (placed.map Rib.cause)[n + i]? = some r.cause := by
        rw [List.getElem?_map, e1, Option.map_some]
      have g2 : (placed.map Rib.cause)[n + (j + 2)]? = some r.cause := by
        rw [List.getElem?_map, e2, Option.map_some]
      have hlt1 : n + i < (placed.map Rib.cause).length := by
        rw [List.length_map]
        obtain ⟨hil2, _⟩ := List.getElem?_eq_some_iff.mp hii
        have hdrop := List.length_drop (i := n) (l := placed)
        have hlen : (placed.drop n).length = (a :: rest).length := by rw [← hsuf]
        omega
      have heq := (hnd.getElem?_inj hlt1).mp (g1.trans g2.symm)
      omega
  | later a rest C P r dx htail ih =>
    intro n hsuf dxB hB
    cases hB with
    | current _ _ _ _ _ hrB =>
      exfalso
      obtain ⟨i, hi2, hii⟩ := assemblyShift_mem_take_pair hrB
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (assemblyPairShift_mem htail)
      have e1 : placed[n + i]? = some r := by
        have h1 : (placed.drop n)[i]? = some r := by
          rw [← hsuf]
          exact hii
        rwa [List.getElem?_drop] at h1
      have e2 : placed[n + (j + 2)]? = some r := by
        have h1 : (placed.drop n)[j + 2]? = some r := by
          rw [← hsuf, show j + 2 = (j + 1) + 1 from by omega,
            List.getElem?_cons_succ, show j + 1 = 1 + j from by omega,
            ← List.getElem?_drop]
          exact hj
        rwa [List.getElem?_drop] at h1
      have g1 : (placed.map Rib.cause)[n + i]? = some r.cause := by
        rw [List.getElem?_map, e1, Option.map_some]
      have g2 : (placed.map Rib.cause)[n + (j + 2)]? = some r.cause := by
        rw [List.getElem?_map, e2, Option.map_some]
      have hlt1 : n + i < (placed.map Rib.cause).length := by
        rw [List.length_map]
        obtain ⟨hil2, _⟩ := List.getElem?_eq_some_iff.mp hii
        have hdrop := List.length_drop (i := n) (l := placed)
        have hlen : (placed.drop n).length = (a :: rest).length := by rw [← hsuf]
        omega
      have heq := (hnd.getElem?_inj hlt1).mp (g1.trans g2.symm)
      omega
    | later _ _ _ _ _ _ htailB =>
      have hsufT : rest.drop 1 = placed.drop (n + 2) := by
        have h2 : (a :: rest).drop 2 = rest.drop 1 := rfl
        rw [← h2, hsuf, List.drop_drop]
      exact ih _ hsufT htailB




/-- Same-rib piece clearance from the per-rib chain, transported across the
assembly shift. The shift of the rib is unique (cause-nodup), so both pieces
move by one common translation and `hitsRect_translate` reduces the goal to
the unshifted miss; inside the unshifted placed rib every pair is closed by
the per-rib theorems except the two envelope configurations, which are
discharged by the residual hypothesis. -/
theorem ishikawaSameRibPieceClearance (m : Model)
    (henv : IshikawaSameRibEnvelopeClearance m) :
    IshikawaSameRibPieceClearance m := by
  intro e hd rA dxA dxB hshiftA hshiftB pieceR pieceB hmemR hmemB hne
  have hmemA : rA ∈ e.placed := assemblyPairShift_mem hshiftA
  obtain ⟨source, cause, k, hsource0, hcauseIdx, heq, hplace0⟩ :=
    placed_rib_source e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.ribs e.placed e.length e.spine e.hribs e.hplaced rA hmemA
  have hplace : place e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.spine
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))) = .ok rA := by
    have h := hplace0
    rw [e.hlength, heq] at h
    exact h
  have hsource : generatedRib e.input.nodes (cause, k) ∈ e.ribs := by
    rw [← heq]
    exact hsource0
  have hcauseMem : cause ∈ children e.input.nodes 0 :=
    List.fst_mem_of_mem_zipIdx hcauseIdx
  have hlink :=
    Elegant.Kinds.IshikawaValid.successful_link e.input.nodes _ e.raw e.hlayout
  have hnd : (e.placed.map Rib.cause).Nodup := by
    rw [same_rib_causes_eq m e]
    exact same_rib_children_nodup e.input.nodes
  have hdx : dxA = dxB :=
    assemblyShift_fun_aux e.placed hnd 0 hshiftA (by simp) hshiftB
  subst hdx
  have hfields := place_rib_fields_eq _ _ _ _ _ hplace
  have hndNodes :
      ((generatedRib e.input.nodes (cause, k)).entries.map Entry.node).Nodup :=
    generated_entry_nodes_nodup e.input.nodes cause k hlink
  obtain ⟨iR, rectR, pointsR⟩ := pieceR
  obtain ⟨iB, rectB, pointsB⟩ := pieceB
  have hR := generated_piece_strict_temporal_geometry e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
    cause k hsource hcauseMem e.spine rA hplace iR rectR pointsR hmemR
  have hB := generated_piece_strict_temporal_geometry e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
    cause k hsource hcauseMem e.spine rA hplace iB rectB pointsB hmemB
  have hne' : iR ≠ iB := hne
  have hmissU : ¬ Polyline.hitsRect pointsR rectB := by
    by_cases hRcause : iR = rA.cause
    · -- Cause-index route: residual left disjunct.
      have hBc : iB ≠ rA.cause := fun h => hne' (hRcause.trans h.symm)
      exact henv e rA dxA hshiftA _ _ hmemR hmemB hne
        (Or.inl ⟨hRcause, hBc⟩)
    · rcases hR with ⟨nR, hnR, hiR, hrectR, hptsR⟩ |
        ⟨eI, idxI, posI, parI, nI, heI, hposI, hnI, hiI, hgeneI, _, hrectR,
          hptsR, _, _⟩
      · -- Cause shape but non-cause index: impossible.
        have hIRc : iR = rA.cause := by
          rw [hfields.1]
          exact hiR
        exact absurd hIRc hRcause
      · rcases hB with ⟨nB, hnB, _, hrectB, _⟩ |
          ⟨eJ, idxJ, posJ, parJ, nJ, heJ, hposJ, hnJ, hiJ, hgeneJ, _,
            hrectB, hptsB, _, _⟩
        · -- Box piece is the cause box.
          have hcn : e.input.nodes[cause]? = some nB := hnB
          have hmiss := place_entry_route_misses_cause_box e.input.nodes
            (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs
            e.hribs cause k hsource hcauseMem e.spine rA hplace eI idxI posI
            parI nI heI hposI hnI hgeneI nB hcn
          rw [hptsR, hrectB]
          exact hmiss
        · have hnode : eI.node ≠ eJ.node := by
            rw [hiI, hiJ] at hne'
            exact hne'
          by_cases heven : eI.depth % 2 = 0
          · have hmiss := place_entry_route_misses_entry_box_even
              e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile) e.raw
              e.hlayout e.ribs e.hribs cause k hsource hcauseMem e.spine
              eI idxI posI parI nI heI hposI hgeneI hnI eJ idxJ posJ parJ
              nJ heJ hposJ hgeneJ hnJ hnode heven
            rw [hptsR, hrectB]
            exact hmiss
          · have hodd : eI.depth % 2 ≠ 0 := by omega
            by_cases hltIdx : idxJ < idxI
            · have hdeepI := hd e cause k hsource hcauseMem rA hplace
              obtain ⟨_, childBorn, jBorn, _, hcb, hjb, hmiss, hpieces'⟩ :=
                ishikawa_hard_b_real' e.input.nodes
                  (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout
                  e.ribs e.hribs cause k hsource hcauseMem e.spine rA hplace
                  hdeepI eI eJ idxI idxJ heI heJ hodd hltIdx nJ hnJ
              have hR' := hpieces' iR rectR pointsR hmemR
              have hB' := hpieces' iB rectB pointsB hmemB
              rcases hR' with ⟨_, _, hcontra, _, _⟩ |
                ⟨er, idxr, _, bornR, her, hiE, _, hbornR, hrectE, hptsE⟩
              · have hIRc : iR = rA.cause := by
                  rw [hfields.1]
                  exact hcontra
                exact absurd hIRc hRcause
              · rcases hB' with ⟨cnB, hcnB, _, hrectBc, _⟩ |
                  ⟨e', idx', n', bornB, he', hiE', hnE', hbornB, hrectE',
                    hptsE'⟩
                · -- Frames say the box is cause-shaped: lemma3.
                  have hmissB := place_entry_route_misses_cause_box
                    e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
                    e.raw e.hlayout e.ribs e.hribs cause k hsource hcauseMem
                    e.spine rA hplace eI idxI posI parI nI heI hposI hnI
                    hgeneI cnB hcnB
                  rw [hptsR, hrectBc]
                  exact hmissB
                · have hidxR : idxr = idxI :=
                    entry_idx_eq_of_node_eq _ hndNodes _ _ _ _ her heI
                      (hiE.symm.trans hiI)
                  have hbornR : bornR = childBorn :=
                    Option.some.inj
                      (by rw [hidxR] at hbornR; exact hbornR.symm.trans hcb)
                  have hidxB : idx' = idxJ :=
                    entry_idx_eq_of_node_eq _ hndNodes _ _ _ _ he' heJ
                      (hiE'.symm.trans hiJ)
                  have hbornB : bornB = jBorn :=
                    Option.some.inj
                      (by rw [hidxB] at hbornB; exact hbornB.symm.trans hjb)
                  have eEq' : e'.node = eJ.node := hiE'.symm.trans hiJ
                  have hnEq' : n' = nJ := by
                    rw [eEq'] at hnE'
                    exact Option.some.inj (hnE'.symm.trans hnJ)
                  rw [hbornR] at hptsE
                  rw [hbornB, hnEq'] at hrectE'
                  have hmissU' : ¬ Polyline.hitsRect pointsR rectB := by
                    rw [hptsE, hrectE']
                    exact hmiss
                  exact hmissU'
            · by_cases hltIdx2 : idxI < idxJ
              · rcases Nat.lt_trichotomy posI.2 posJ.2 with hlt | heqPos | hgt
                · have hmiss :=
                      place_entry_route_misses_entry_box_odd_later
                        e.input.nodes
                        (Elegant.Kinds.Ishikawa.params m.profile) e.raw
                        e.hlayout e.ribs e.hribs cause k hsource hlink
                        hcauseMem e.spine eI idxI posI parI nI heI hposI
                        hgeneI hnI eJ idxJ posJ parJ nJ heJ hposJ hgeneJ
                        hnJ hnode hodd hlt
                  rw [hptsR, hrectB]
                  exact hmiss
                · have hposNe : posI.2 ≠ posJ.2 :=
                    order_positions_ne' hposI hposJ
                      (zipIdx_index_ne_of_node_ne' heI heJ hnode)
                  omega
                · have heIRA : (eI, idxI) ∈ rA.entries.zipIdx := by
                    rw [hfields.2.1]
                    exact heI
                  have heJRA : (eJ, idxJ) ∈ rA.entries.zipIdx := by
                    rw [hfields.2.1]
                    exact heJ
                  have hposIRA : rA.order.zipIdx.find?
                      (fun v => v.1 == idxI) = some posI := by
                    rw [hfields.2.2]
                    exact hposI
                  have hposJRA : rA.order.zipIdx.find?
                      (fun v => v.1 == idxJ) = some posJ := by
                    rw [hfields.2.2]
                    exact hposJ
                  exact henv e rA dxA hshiftA _ _ hmemR hmemB hne
                    (Or.inr ⟨eI, eJ, idxI, idxJ, posI, posJ, heIRA, heJRA,
                      hiI, hiJ, hodd, hposIRA, hposJRA, hltIdx2, hgt⟩)
              · have hidxEq : idxI = idxJ := by omega
                have gI := List.mem_zipIdx_iff_getElem?.mp heI
                have gJ := List.mem_zipIdx_iff_getElem?.mp heJ
                change _ = some eI at gI
                rw [← hidxEq] at gJ
                have heqE : eI = eJ := Option.some.inj (gI.symm.trans gJ)
                exact absurd (congrArg Entry.node heqE) hnode
  -- Transport across the common shift.
  have e1 : pointsR.map (fun q => ({ x := q.x + dxA, y := q.y } : Point)) =
      pointsR.map fun p => ({ x := p.x + dxA, y := p.y + 0 } : Point) := by
    simp only [Int.add_zero]
  have e2 : ({ rectB with x := rectB.x + dxA } : Rect) =
      ⟨rectB.x + dxA, rectB.y + 0, rectB.w, rectB.h⟩ := by
    simp only [Int.add_zero]
  rw [e1, e2]
  exact mt (hitsRect_translate dxA 0 pointsR rectB).mp hmissU

end Elegant.Kinds.IshikawaFinal
