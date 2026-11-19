import Elegant.IshikawaDeeperRouteGapProof

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-- Residual R-desc: sibling-subtree envelope for born bones.

For the odd route `child` with earlier sibling `S` (same parent entry) and an
indexed descendant `j` of `S`, the descendant's born bone lies inside the
sibling's born time span and ends at or left of the sibling's interpolated
bone line at its own ordinate:
`sBorn.t0 ≤ jBorn.t1`, `jBorn.t1 ≤ sBorn.t1`, and
`jBorn.x1 ≤ sBorn.x0 + Int.fdiv ((sBorn.x1 - sBorn.x0) * (jBorn.t1 - sBorn.t0)) /
  (sBorn.t1 - sBorn.t0)`.
The third conjunct is the even-bone attachment equation shape
(`depthBone`): an even child attaches exactly on its parent's line, an odd
descendant further left.

Strictly simpler than the goal: pure born-bone inequalities about one rib's
executed frames, with no route interpolation of `child`, no reservation
arithmetic, and no attachment-rank facts. Probed with
`proofs/wip/Probe/IshikawaDeeperGapOnlyProbe.lean`: on all link-valid trees to
seven nodes there are 13 sibling-descendant premises (one at six nodes, twelve
at seven); all 13 satisfy the time containment, the sibling-line bound, and
the sibling attachment gap, and all 13 satisfy the final gap (gapViols=0). -/
def HardBDeeperDescEnvelope (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k)))) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  ∀ (child j : Entry) (childIdx jIdx : Nat) (nj : Tree.Node)
    (frames : List Bone) (childBorn jBorn sBorn : Bone) (sIdx : Nat) (S : Entry)
    (nS : Tree.Node),
    HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
      childBorn jBorn →
    HardBRealFrames ns p spine r placed hplace frames →
    (generatedRib ns (cause, k)).entries[sIdx]? = some S → sIdx ≠ jIdx →
    S.parent = ((child.parent).toNat : Int) →
    IndexedAncestor (generatedRib ns (cause, k)).entries sIdx jIdx →
    frames[sIdx + 1]? = some sBorn → ns[S.node]? = some nS →
    sBorn.t0 ≤ jBorn.t1 ∧ jBorn.t1 ≤ sBorn.t1 ∧ jBorn.x1 ≤ sBorn.x0 +
      Int.fdiv ((sBorn.x1 - sBorn.x0) * (jBorn.t1 - sBorn.t0))
        (sBorn.t1 - sBorn.t0)

/-- Numerator monotonicity of `Int.fdiv` (local copy of the private
`IshikawaClearanceHardB.fdiv_mono_num`). -/
private theorem gapOnly_fdiv_mono {A B s : Int} (hs : 0 < s) (hAB : A ≤ B) :
    Int.fdiv A s ≤ Int.fdiv B s := by
  by_cases hgt : Int.fdiv B s < Int.fdiv A s
  · exfalso
    have hlt : s * Int.fdiv B s < s * Int.fdiv A s :=
      Int.mul_lt_mul_of_pos_left hgt hs
    have hqA := Int.mul_fdiv_add_fmod A s
    have hqB := Int.mul_fdiv_add_fmod B s
    have hfA := Int.fmod_nonneg_of_pos A hs
    have hfB := Int.fmod_lt_of_pos B hs
    have hle : s * Int.fdiv A s ≤ s * (Int.fdiv B s + 1) := by
      have e : s * (Int.fdiv B s + 1) = s * Int.fdiv B s + s := by
        rw [Int.mul_add, Int.mul_one]
      rw [e]
      omega
    have hlt' : s * Int.fdiv B s + s < s * Int.fdiv A s := by
      have e : s * (Int.fdiv B s + 1) = s * Int.fdiv B s + s := by
        rw [Int.mul_add, Int.mul_one]
      have : s * (Int.fdiv B s + 1) < s * Int.fdiv A s := by
        have h1 : Int.fdiv B s + 1 ≤ Int.fdiv A s := by omega
        have h2 := Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt hs)
        omega
      rw [e] at this
      exact this
    omega
  · omega

/-- Floor gap (local copy of the private
`IshikawaClearanceHardBClose.bclose_floor_gap`). -/
private theorem gapOnly_floor_gap (a b denominator margin : Int)
    (hden : 0 < denominator) (hgap : a + denominator * margin ≤ b) :
    Int.fdiv a denominator + margin ≤ Int.fdiv b denominator := by
  have hq := Int.mul_fdiv_add_fmod a denominator
  have hr := Int.fmod_nonneg_of_pos a hden
  apply Chart.le_fdiv_of_mul_le hden
  rw [Int.mul_add]
  omega

/-- Native reservation of an even bone (local copy of the private
`IshikawaClearanceFacts.even_native_reservation`). -/
private theorem gapOnly_native_reservation (p : Params) (par : Bone) (depth : Nat)
    (t : Int) (count : Nat) (margin : Int) (hd : depth % 2 = 0) :
    let b := depthBone p par depth t count margin
    0 < b.count + 1 ∧ (b.count + 1) * margin ≤ b.x0 - b.x1 := by
  let b := depthBone p par depth t count margin
  have hc : b.count = (count : Int) := by
    unfold b depthBone
    split <;> rfl
  have he := (depthBone_even_endpoints p par depth t count margin hd).2.2
  have hr : ((count : Int) + 1) * margin ≤ boneLength p count margin :=
    Int.le_max_right _ _
  constructor
  · rw [hc]
    omega
  · rw [hc]
    change ((count : Int) + 1) * margin ≤ b.x0 - b.x1
    change b.x1 = b.x0 - boneLength p count margin at he
    omega

/-- Floor gaps add along a parent's bone (local copy of the private
`IshikawaClearanceHardBClose.bclose_counter_gap`). -/
private theorem gapOnly_counter_gap (left right count margin firstDraw secondDraw : Int)
    (hden : 0 < count + 1) (hmargin : 0 ≤ margin)
    (hreserve : (count + 1) * margin ≤ left - right)
    (hrank : firstDraw + 1 ≤ secondDraw) :
    left + Int.fdiv ((right - left) * (count - firstDraw)) (count + 1) + margin ≤
      left + Int.fdiv ((right - left) * (count - secondDraw)) (count + 1) := by
  have hnonnegative : 0 ≤ left - right :=
    Int.le_trans (Int.mul_nonneg (Int.le_of_lt hden) hmargin) hreserve
  have hmul := Int.mul_le_mul_of_nonneg_left
    (show (1 : Int) ≤ secondDraw - firstDraw by omega) hnonnegative
  simp only [Int.mul_one] at hmul
  have halgebra :
      (right - left) * (count - secondDraw) -
          (right - left) * (count - firstDraw) =
        (left - right) * (secondDraw - firstDraw) := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  have hgap := gapOnly_floor_gap
    ((right - left) * (count - firstDraw))
    ((right - left) * (count - secondDraw)) (count + 1) margin hden (by omega)
  omega

/-- Prefix decomposition of `zipIdx` forces the prefix length (local copy of
the private `IshikawaClearanceHardBClose.zipIdx_index_of_split`). -/
private theorem gapOnly_zipIdx_split {α : Type} {l : List α}
    {before after : List (α × Nat)} {x : α} {idx : Nat}
    (hsplit : l.zipIdx = before ++ [(x, idx)] ++ after) :
    before.length = idx := by
  have h2 : l.zipIdx[before.length]? = some (x, idx) := by
    rw [hsplit]
    rw [List.getElem?_append_left
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    rw [List.getElem?_append_right (Nat.le_refl before.length)]
    simp
  rw [List.getElem?_zipIdx] at h2
  cases hopt : l[before.length]? with
  | none => rw [hopt] at h2; exact absurd h2 (by simp)
  | some y =>
    rw [hopt] at h2
    simp only [Option.map_some] at h2
    have hsnd := congrArg Prod.snd (Option.some.inj h2)
    simpa using hsnd

/-- Flatten step (local copy of the private
`IshikawaHardBBranch5Facts.flattenStep`, also mirrored as `deeperFlattenStep`
in `IshikawaDeeperEarlierProof`). -/
private def gapOnlyFlattenStep (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (par : Int) (depth : Nat) (st : List Entry × List Nat) (node : Nat) :
    List Entry × List Nat :=
  let idx := st.1.length
  let es := st.1 ++ [(⟨node, par, depth⟩ : Entry)]
  let os := if depth % 2 == 0 then st.2 ++ [idx] else st.2
  let res := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
  (res.1, if depth % 2 == 0 then res.2 else res.2 ++ [idx])

private theorem gapOnly_flatten_succ_eq_foldl (ns : List Tree.Node) (up : Bool)
    (fuel : Nat) (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry)
    (os : List Nat) :
    flatten ns up (fuel + 1) ids par depth es os =
      (if up then ids.reverse else ids).foldl
        (gapOnlyFlattenStep ns up fuel par depth) (es, os) := by
  rfl

set_option maxHeartbeats 1000000 in
private theorem gapOnly_flatten_parent_back (ns : List Tree.Node) (up : Bool) :
    ∀ (fuel : Nat) (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry)
      (os : List Nat),
      ∃ (segE : List Entry),
        (flatten ns up fuel ids par depth es os).1 = es ++ segE ∧
        ∀ (i : Nat) (e : Entry), (es ++ segE)[i]? = some e → es.length ≤ i →
          e.parent = par ∨
          ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
            (es ++ segE)[p]? = some pe := by
  intro fuel
  induction fuel with
  | zero =>
    intro ids par depth es os
    refine ⟨[], by simp [flatten], ?_⟩
    intro i e hlook hle
    rw [List.getElem?_append_right hle, List.getElem?_nil] at hlook
    exact absurd hlook (by simp)
  | succ fuel ih =>
    intro ids par depth es os
    have inner :
        ∀ (ls : List Nat) (st : List Entry × List Nat),
          ∃ (segE : List Entry),
            (ls.foldl (gapOnlyFlattenStep ns up fuel par depth) st).1 =
              st.1 ++ segE ∧
            ∀ (i : Nat) (e : Entry), (st.1 ++ segE)[i]? = some e →
              st.1.length ≤ i →
              e.parent = par ∨
              ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
                (st.1 ++ segE)[p]? = some pe := by
      intro ls
      induction ls with
      | nil =>
        intro st
        refine ⟨[], by simp, ?_⟩
        intro i e hlook hle
        rw [List.getElem?_append_right hle, List.getElem?_nil] at hlook
        exact absurd hlook (by simp)
      | cons node rest ihrest =>
        intro st
        obtain ⟨dE, hdE, hdprop⟩ :=
          ih (children ns node) (st.1.length : Int) (depth + 1)
            (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
            (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)
        have hstep : (gapOnlyFlattenStep ns up fuel par depth st node).1
              = (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE := hdE
        obtain ⟨segE', hsegE', hprop'⟩ :=
          ihrest (gapOnlyFlattenStep ns up fuel par depth st node)
        rw [hstep] at hsegE' hprop'
        refine ⟨⟨node, par, depth⟩ :: (dE ++ segE'), ?_, ?_⟩
        · rw [List.foldl_cons, hsegE']
          simp [List.append_assoc]
        · intro i e hlook hle
          by_cases hi : i < st.1.length + 1
          · have hieq : i = st.1.length := by omega
            rw [List.getElem?_append_right hle, hieq, Nat.sub_self,
              List.getElem?_cons_zero, Option.some.injEq] at hlook
            exact Or.inl (by rw [← hlook])
          · have hlenA : ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE).length =
                (st.1.length + 1) + dE.length := by
              simp only [List.length_append, List.length_singleton]
            have happ : st.1 ++ (⟨node, par, depth⟩ :: (dE ++ segE'))
                = ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++ segE' := by
              simp [List.append_assoc]
            have hlook2 : (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++
                segE')[i]? = some e := by
              rw [happ] at hlook
              exact hlook
            by_cases hiA : i < (st.1.length + 1) + dE.length
            · have hltiA : i < ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++
                  dE).length := by
                rw [hlenA]; omega
              have hlookA : ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE)[i]? =
                  some e := by
                rw [List.getElem?_append_left hltiA] at hlook2
                exact hlook2
              have hcase := hdprop i e hlookA
                (by simp only [List.length_append, List.length_singleton]; omega)
              rcases hcase with hpar0 | ⟨p, pe, hpe, hplt, hplook⟩
              · have hlt0 : st.1.length < ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++
                    dE).length := by
                  rw [hlenA]; omega
                have hlt1 : st.1.length < (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length := by
                  simp only [List.length_append, List.length_singleton]; omega
                refine Or.inr ⟨st.1.length, ⟨node, par, depth⟩, hpar0, by omega, ?_⟩
                rw [happ, List.getElem?_append_left hlt0,
                  List.getElem?_append_left hlt1,
                  List.getElem?_append_right (Nat.le_refl st.1.length),
                  Nat.sub_self, List.getElem?_singleton]
                rfl
              · have hpltA : p < ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++
                    dE).length := by
                  rw [hlenA]; omega
                refine Or.inr ⟨p, pe, hpe, hplt, ?_⟩
                rw [happ, List.getElem?_append_left hpltA]
                exact hplook
            · have hcase := hprop' i e hlook2 (by rw [hlenA]; omega)
              rcases hcase with hpar0 | ⟨p, pe, hpe, hplt, hplook⟩
              · exact Or.inl hpar0
              · refine Or.inr ⟨p, pe, hpe, hplt, ?_⟩
                rw [happ]
                exact hplook
    obtain ⟨segE, hsegE, hprop⟩ := inner (if up then ids.reverse else ids) (es, os)
    rw [gapOnly_flatten_succ_eq_foldl]
    exact ⟨segE, hsegE, hprop⟩

/-- Generated rib entries are backwards-parented (local copy of the private
`IshikawaHardBBranch5Facts.rib_parent_back`, also mirrored as
`deeper_rib_parent_back` in `IshikawaDeeperEarlierProof`). -/
private theorem gapOnly_rib_parent_back (ns : List Tree.Node) (cause k : Nat) :
    ∀ (i : Nat) (e : Entry), (generatedRib ns (cause, k)).entries[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        (generatedRib ns (cause, k)).entries[p]? = some pe := by
  obtain ⟨segE, hEq, hProp⟩ :=
    gapOnly_flatten_parent_back ns (upper k) 64 (children ns cause) (-1) 2 [] []
  have hf2 : (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 :=
    congrArg Prod.fst (generated_rib_fields ns cause k).2.2.1
  have hgr : (generatedRib ns (cause, k)).entries = segE := by
    rw [hf2, hEq]
    exact List.nil_append segE
  intro i e hlook
  have hres := hProp i e (by rw [hgr] at hlook; exact hlook) (Nat.zero_le i)
  rw [hgr]
  simpa only [List.nil_append, List.length_nil, Nat.zero_le, true_and, and_true] using hres

/-- Indexed ancestor chains strictly increase. -/
private theorem gapOnly_chain_lt (E : List Entry)
    (hback : ∀ (i : Nat) (e : Entry), E[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        E[p]? = some pe) :
    ∀ (a c : Nat), IndexedAncestor E a c → a < c := by
  intro a c h
  induction h with
  | edge _ e he hp =>
    rcases hback _ e he with hr | ⟨p, pe, hpe, hplt, _⟩
    · rw [hr] at hp
      exact absurd hp (by omega)
    · omega
  | tail _ e he hp ih =>
    rcases hback _ e he with hr | ⟨p, pe, hpe, hplt, _⟩
    · rw [hr] at hp
      exact absurd hp (by omega)
    · omega

set_option maxHeartbeats 1000000 in
/-- The deeper gap from the sibling reservation plus the envelope residual.

The sibling pair `(child, S)` misses by the slot reservation
(`hard_b_route_reservation` applied to the executed birth records, mirroring
`hard_b_sibling_real`); the residual transports that gap from `S`'s ordinate
to the deeper descendant `j`'s ordinate by floor monotonicity. -/
theorem hardBDeeperGapOnly (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (henv : HardBDeeperDescEnvelope ns p raw _hrun ribs _hg cause k _hsource
      _hcause spine placed _hplace _env) :
    HardBDeeperGapOnly ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed _hplace _env := by
  intro child j childIdx jIdx nj frames childBorn jBorn sBorn sIdx S _nS
    hconfig hreal hS _hsne hSP hchain hsBorn _hnS
  have hres0 := henv child j childIdx jIdx nj frames childBorn jBorn sBorn sIdx S
    _nS hconfig hreal hS _hsne hSP hchain hsBorn _hnS
  have hfall0 := hardBDeeperFall ns p raw _hrun ribs _hg cause k _hsource _hcause
    spine placed _hplace _env child j childIdx jIdx nj frames childBorn jBorn
    hconfig hreal
  obtain ⟨hchild, _hj, hodd, hjlt, _hnj, _hlen, hchildBorn, _hjBorn, _hspan⟩ :=
    hconfig
  obtain ⟨frames0, hshape0, hsub⟩ := hreal
  obtain ⟨hlen0, _hroot0, hrecords0⟩ := hshape0
  have hframesEq : frames = frames0 := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < frames.length
    · have hfi : frames[i]? = some frames[i] := List.getElem?_eq_getElem hi
      have hb : frames0[i]? = some frames[i] := hsub i _ hfi
      have hio : i < frames0.length := by
        have := (List.getElem?_eq_some_iff.mp hb).choose_spec
        omega
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hio]
      have hb2 : frames0[i]? = some frames0[i] := List.getElem?_eq_getElem hio
      rw [hb2] at hb
      exact hb.symm
    · have hni : frames[i]? = none := by
        rw [List.getElem?_eq_none_iff.mpr (by omega : frames.length ≤ i)]
      have hni0 : frames0[i]? = none := by
        rw [List.getElem?_eq_none_iff.mpr (by omega : frames0.length ≤ i)]
      rw [hni, hni0]
  obtain ⟨hresT0, hresT1, hresX⟩ := hres0
  subst hframesEq
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  have hSmem : (S, sIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hS
  obtain ⟨sDone, sRest, sPrefix, _⟩ := List.eq_append_cons_of_mem hSmem
  change (generatedRib ns (cause, k)).entries.zipIdx =
      sDone ++ (S, sIdx) :: sRest at sPrefix
  obtain ⟨sPos, sPar, sBorn0, _hsPos, hsParLookup, hsBorn0, hsEq⟩ :=
    hrecords0 sDone S sIdx sRest sPrefix
  obtain ⟨childDone, childRest, hchildPrefix, _⟩ := List.eq_append_cons_of_mem hchild
  change (generatedRib ns (cause, k)).entries.zipIdx =
      childDone ++ (child, childIdx) :: childRest at hchildPrefix
  obtain ⟨childPos, cPar, childBorn0, hchildPos, hchildParLookup, hchildBorn0,
    hchildEq⟩ := hrecords0 childDone child childIdx childRest hchildPrefix
  have hsBornEq : sBorn0 = sBorn := Option.some.inj (hsBorn0.symm.trans hsBorn)
  have hchildBornEq : childBorn0 = childBorn :=
    Option.some.inj (hchildBorn0.symm.trans hchildBorn)
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw _hrun
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at _hcause
  have hparameters := successful_slope_parameters ns p raw hne _hrun
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hlb := generated_entry_parent_lower_bound ns cause k child childIdx hchild
  have hrootFalse : child.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink _hcause child childIdx hchild heq
    exact hodd (by omega)
  have hparIdx : child.parent = ((child.parent).toNat : Int) := by omega
  have hchildOwner : (child.parent + 1).toNat = (child.parent).toNat + 1 := by
    rw [hparIdx]
    omega
  rw [hchildOwner] at hchildParLookup hchildEq
  obtain ⟨hpb, _⟩ := List.getElem?_eq_some_iff.mp hchildParLookup
  rw [hlen0] at hpb
  have hparentBound : (child.parent).toNat < r.entries.length :=
    Nat.lt_of_succ_lt_succ hpb
  let parentEntry := (generatedRib ns (cause, k)).entries[(child.parent).toNat]'hparentBound
  have hparentLookup : (generatedRib ns (cause, k)).entries[(child.parent).toNat]? =
      some parentEntry := List.getElem?_eq_getElem hparentBound
  have hparentMem : (parentEntry, (child.parent).toNat) ∈
      (generatedRib ns (cause, k)).entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hparentLookup
  have hpar : child.parent = ((child.parent).toNat : Int) := hparIdx
  have hchildDepth := generated_parent_child_depth ns cause k hlink _hcause
    parentEntry child (child.parent).toNat childIdx hparentMem hchild hpar
  have hparentEven : parentEntry.depth % 2 = 0 :=
    parent_depth_even parentEntry.depth child.depth hchildDepth hodd
  have hsParentEq : S.parent = child.parent := hSP.trans hparIdx.symm
  have hsPar : S.parent = ((child.parent).toNat : Int) := hSP
  have hsDepth := generated_parent_child_depth ns cause k hlink _hcause
    parentEntry S (child.parent).toNat sIdx hparentMem hSmem hsPar
  have hsOdd : S.depth % 2 ≠ 0 := by
    rw [hsDepth]
    omega
  obtain ⟨parentDone, parentRest, hparentPrefix, _⟩ :=
    List.eq_append_cons_of_mem hparentMem
  change (generatedRib ns (cause, k)).entries.zipIdx =
      parentDone ++ (parentEntry, (child.parent).toNat) :: parentRest at hparentPrefix
  obtain ⟨parentPos, grandpar, parentBorn, _hparentPos, _hgpLookup, hparentBornLookup,
    hparentEquation⟩ :=
    hrecords0 parentDone parentEntry (child.parent).toNat parentRest hparentPrefix
  have hcPar : cPar = parentBorn := by
    have h1 : frames[(child.parent).toNat + 1]? = some cPar := hchildParLookup
    have h2 : frames[(child.parent).toNat + 1]? = some parentBorn := hparentBornLookup
    exact Option.some.inj (h1.symm.trans h2)
  rw [hcPar] at hchildEq
  have hchildT0 : childBorn.t0 = parentBorn.t0 := by
    rw [← hchildBornEq, hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).1
  have hchildX0 : childBorn.x0 = parentBorn.x0 +
      Int.fdiv ((parentBorn.x1 - parentBorn.x0) *
        (parentBorn.count - processedOddDraws childDone ((child.parent).toNat + 1)))
        (parentBorn.count + 1) := by
    rw [← hchildBornEq, hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.2.1
  have hsOwner : (S.parent + 1).toNat = (child.parent).toNat + 1 := by
    rw [hsParentEq]
    exact hchildOwner
  rw [hsOwner] at hsParLookup hsEq
  have hsParBone : sPar = parentBorn := by
    have h1 : frames[(child.parent).toNat + 1]? = some sPar := hsParLookup
    have h2 : frames[(child.parent).toNat + 1]? = some parentBorn := hparentBornLookup
    exact Option.some.inj (h1.symm.trans h2)
  have hsT0 : sBorn.t0 = parentBorn.t0 := by
    rw [← hsBornEq, hsEq, hsParBone]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws sDone ((child.parent).toNat + 1) }
      S.depth (Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns S.node).length (run p r.heights + 3) hsOdd).1
  have hsT1 : sBorn.t1 =
      Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [← hsBornEq, hsEq, hsParBone]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws sDone ((child.parent).toNat + 1) }
      S.depth (Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns S.node).length (run p r.heights + 3) hsOdd).2.1
  have hsX0 : sBorn.x0 = parentBorn.x0 +
      Int.fdiv ((parentBorn.x1 - parentBorn.x0) *
        (parentBorn.count - processedOddDraws sDone ((child.parent).toNat + 1)))
        (parentBorn.count + 1) := by
    rw [← hsBornEq, hsEq, hsParBone]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws sDone ((child.parent).toNat + 1) }
      S.depth (Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns S.node).length (run p r.heights + 3) hsOdd).2.2.1
  have hslt : sIdx < jIdx :=
    gapOnly_chain_lt _ (gapOnly_rib_parent_back ns cause k) sIdx jIdx hchain
  have hsclt : sIdx < childIdx := by omega
  have hmatchesS : ((S.depth % 2 != 0) &&
      ((S.parent + 1).toNat == (child.parent).toNat + 1)) = true := by
    have hoddT : (S.depth % 2 != 0) = true := by
      cases hmod : S.depth % 2 with
      | zero => rw [hmod] at hsOdd; exact absurd rfl hsOdd
      | succ n => rfl
    have hown : ((S.parent + 1).toNat == (child.parent).toNat + 1) = true := by
      rw [hsOwner]
      exact beq_self_eq_true _
    rw [hoddT, hown]
    rfl
  have hsLen : sDone.length = sIdx :=
    gapOnly_zipIdx_split (l := (generatedRib ns (cause, k)).entries) (after := sRest)
      (x := S) (idx := sIdx) (by rw [sPrefix]; simp)
  have hchildLen : childDone.length = childIdx :=
    gapOnly_zipIdx_split (l := (generatedRib ns (cause, k)).entries) (after := childRest)
      (x := child) (idx := childIdx) (by rw [hchildPrefix]; simp)
  have hprefixS : sDone ++ [(S, sIdx)] <+: childDone := by
    apply List.prefix_of_prefix_length_le
      (l₃ := (generatedRib ns (cause, k)).entries.zipIdx)
    · exact ⟨sRest, by rw [sPrefix]; simp⟩
    · exact ⟨(child, childIdx) :: childRest, hchildPrefix.symm⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have hstepS : processedOddDraws (sDone ++ [(S, sIdx)]) ((child.parent).toNat + 1) =
      processedOddDraws sDone ((child.parent).toNat + 1) + 1 := by
    rw [processedOddDraws_append_one sDone S sIdx ((child.parent).toNat + 1), hmatchesS]
    rfl
  have hrankS : processedOddDraws sDone ((child.parent).toNat + 1) + 1 ≤
      processedOddDraws childDone ((child.parent).toNat + 1) := by
    have hm := processedOddDraws_prefix (sDone ++ [(S, sIdx)]) childDone
      ((child.parent).toNat + 1) hprefixS
    rw [hstepS] at hm
    exact hm
  have hreserve := gapOnly_native_reservation p
    { grandpar with drawn := processedOddDraws parentDone (parentEntry.parent + 1).toNat }
    parentEntry.depth
    (Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
    (children ns parentEntry.node).length (run p r.heights + 3) hparentEven
  rw [← hparentEquation] at hreserve
  have hmargin : 0 ≤ run p r.heights + 3 := by
    have hrunHeight : 0 ≤ run p r.heights :=
      Int.fdiv_nonneg (Int.mul_nonneg hheight hparameters.1)
        (Int.le_of_lt hparameters.2)
    omega
  have hcounter := gapOnly_counter_gap parentBorn.x0 parentBorn.x1 parentBorn.count
      (run p r.heights + 3)
      (processedOddDraws sDone ((child.parent).toNat + 1))
      (processedOddDraws childDone ((child.parent).toNat + 1))
      hreserve.1 hmargin hreserve.2 hrankS
  have hatt : run p r.heights + 3 ≤ childBorn.x0 - sBorn.x0 := by
    rw [hsX0, hchildX0]
    omega
  have hsFall : sBorn.x1 = sBorn.x0 - run p (sBorn.t1 - childBorn.t0) := by
    rw [hsT1, hchildT0, ← hsBornEq, hsEq, hsParBone]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws sDone ((child.parent).toNat + 1) }
      S.depth (Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns S.node).length (run p r.heights + 3) hsOdd).2.2.2
  have hsin : 0 < p.sin := by
    have h1 := hparameters.2
    omega
  have hcos : 0 ≤ p.cos := hparameters.1
  have hctst : childBorn.t0 = sBorn.t0 := hchildT0.trans hsT0.symm
  have hfallI : childBorn.x1 - childBorn.x0 = -run p (childBorn.t1 - childBorn.t0) := by
    rw [hfall0]
    omega
  have hfallS : sBorn.x1 - sBorn.x0 = -run p (sBorn.t1 - sBorn.t0) := by
    rw [hsFall, hctst]
    omega
  show run p r.heights + 1 ≤
    (childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
      (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) - jBorn.x1)
  by_cases hSlt : sBorn.t0 < sBorn.t1
  · by_cases hlt : childBorn.t0 < childBorn.t1
    · have hpar := parallel_line_gap p childBorn.x0 childBorn.x1 childBorn.t0
        childBorn.t1 sBorn.x0 sBorn.x1 sBorn.t0 sBorn.t1 jBorn.t1
        (run p r.heights + 3) hsin hcos (by omega) (by omega) hfallI hfallS
        hctst (by omega) (by omega) (by omega)
      omega
    · have hzero : childBorn.t1 - childBorn.t0 = 0 := by omega
      have hfdiv0 : Int.fdiv ((childBorn.x1 - childBorn.x0) *
          (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) = 0 := by
        rw [hzero]
        simp
      have hSxle : sBorn.x0 + Int.fdiv ((sBorn.x1 - sBorn.x0) *
          (jBorn.t1 - sBorn.t0)) (sBorn.t1 - sBorn.t0) ≤ sBorn.x0 := by
        have hAs : sBorn.x1 - sBorn.x0 ≤ 0 := by
          have hrunNN : 0 ≤ run p (sBorn.t1 - sBorn.t0) :=
            Int.fdiv_nonneg (Int.mul_nonneg (by omega) hcos) (Int.le_of_lt hsin)
          omega
        have hNnn : 0 ≤ (-(sBorn.x1 - sBorn.x0)) * (jBorn.t1 - sBorn.t0) :=
          Int.mul_nonneg (by omega) (by omega)
        have hSle : (sBorn.x1 - sBorn.x0) * (jBorn.t1 - sBorn.t0) ≤ 0 := by
          have hneg : (-(sBorn.x1 - sBorn.x0)) * (jBorn.t1 - sBorn.t0) =
              -(((sBorn.x1 - sBorn.x0) * (jBorn.t1 - sBorn.t0))) := by
            rw [Int.neg_mul]
          omega
        have hSmono := gapOnly_fdiv_mono (show 0 < sBorn.t1 - sBorn.t0 by omega) hSle
        have hS0 : Int.fdiv (0 : Int) (sBorn.t1 - sBorn.t0) = 0 := by simp
        omega
      omega
  · have hsq : jBorn.t1 = sBorn.t0 := by omega
    have hDz : sBorn.t1 - sBorn.t0 = 0 := by omega
    have hSx : sBorn.x0 + Int.fdiv ((sBorn.x1 - sBorn.x0) *
        (jBorn.t1 - sBorn.t0)) (sBorn.t1 - sBorn.t0) = sBorn.x0 := by
      rw [hDz]
      simp
    have hIx : childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
        (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) = childBorn.x0 := by
      have hj0 : jBorn.t1 - childBorn.t0 = 0 := by omega
      rw [hj0]
      simp
    omega

/-- The route-gap conjunction from the envelope residual. -/
theorem hardBDeeperRouteGap'' (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (henv : HardBDeeperDescEnvelope ns p raw _hrun ribs _hg cause k _hsource
      _hcause spine placed hplace _env) :
    HardBDeeperRouteGap ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env :=
  hardBDeeperRouteGap ns p raw _hrun ribs _hg cause k _hsource _hcause
    spine placed hplace _env
    (hardBDeeperGapOnly ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env henv)

/-- The envelope transport from the envelope residual, with no gap-only
hypothesis remaining. -/
theorem hardBDeeperEnvTransport'' (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (henv : HardBDeeperDescEnvelope ns p raw _hrun ribs _hg cause k _hsource
      _hcause spine placed hplace _env) :
    HardBDeeperEnvTransport ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env :=
  hardBDeeperEnvTransport' ns p raw _hrun ribs _hg cause k _hsource _hcause
    spine placed hplace _env
    (hardBDeeperGapOnly ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env henv)

end Elegant.Ishikawa
