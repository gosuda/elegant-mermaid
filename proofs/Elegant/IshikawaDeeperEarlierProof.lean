import Elegant.IshikawaClearanceHardBClose
import Elegant.IshikawaHardBBranch5Facts

/-! # Deeper-earlier HARD B premise

Proves `HardBDeeperEarlierReal` (the open deeper-earlier obligation of
`ishikawa_hard_b_real`) conditional on two small single-rib residuals.

Case analysis over the corrected block classification `HardBBranch5Block`:
* sibling-descendant disjunct: the earlier entry `j` lies in the subtree of an
  earlier sibling of the odd route. The sibling pair itself misses by the
  proved `hard_b_sibling_real`; the envelope transport from the sibling box to
  `j`'s box is residual `HardBDeeperEnvTransport`.
* block-head disjunct, root-self subcase (`H = J`): the head position is `j`'s
  own position, strictly before the parent position; slot monotonicity
  contradicts the assumed negation. Proved.
* block-head disjunct, non-root chain subcase: when `j`'s order position
  precedes the parent position, slot monotonicity contradicts the assumed
  negation (proved); when the route end precedes `j`'s slot, the later-slot
  gap contradicts the assumed negation (proved); the remaining middle
  configuration funnels into the sibling case through the proved-in-spirit
  order fact `HardBDeeperOrdInterval` (a subtree slotted inside its
  even parent's span lies in that subtree), which yields the eldest sibling
  on `j`'s ancestor chain.

The middle configuration is real (it occurs on executed layouts, always with
sibling shape: exhaustive sweep over all link-valid trees to seven nodes
found zero middle pairs without it), so it funnels rather than contradicts.

Truth evidence: `proofs/wip/Probe/IshikawaDeeperProbe.lean` lays out the
refuted-placement witness, two further trees, and every link-valid tree with
up to seven nodes; checks the miss conclusion for every odd/earlier
non-parent non-sibling pair on executed `place` output (zero violations);
and checks the order-interval fact for every even-parent triple
(574 instances, zero violations).
-/

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-! ### Local parent-back induction (mirrors the private
`flatten_parent_back` chain of `IshikawaHardBBranch5Facts`, which this module
cannot import: needed to order a sibling ancestor strictly before its
descendant). -/

private def deeperFlattenStep (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (par : Int) (depth : Nat) (st : List Entry × List Nat) (node : Nat) :
    List Entry × List Nat :=
  let idx := st.1.length
  let es := st.1 ++ [(⟨node, par, depth⟩ : Entry)]
  let os := if depth % 2 == 0 then st.2 ++ [idx] else st.2
  let res := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
  (res.1, if depth % 2 == 0 then res.2 else res.2 ++ [idx])

private theorem deeper_flatten_succ_eq_foldl (ns : List Tree.Node) (up : Bool)
    (fuel : Nat) (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry)
    (os : List Nat) :
    flatten ns up (fuel + 1) ids par depth es os =
      (if up then ids.reverse else ids).foldl
        (deeperFlattenStep ns up fuel par depth) (es, os) := by
  rfl

set_option maxHeartbeats 1000000 in
private theorem deeper_flatten_parent_back (ns : List Tree.Node) (up : Bool) :
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
            (ls.foldl (deeperFlattenStep ns up fuel par depth) st).1 =
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
        have hstep : (deeperFlattenStep ns up fuel par depth st node).1
              = (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE := hdE
        obtain ⟨segE', hsegE', hprop'⟩ :=
          ihrest (deeperFlattenStep ns up fuel par depth st node)
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
    rw [deeper_flatten_succ_eq_foldl]
    exact ⟨segE, hsegE, hprop⟩

private theorem deeper_chain_lt (E : List Entry)
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
private theorem deeper_rib_parent_back (ns : List Tree.Node) (cause k : Nat) :
    ∀ (i : Nat) (e : Entry), (generatedRib ns (cause, k)).entries[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        (generatedRib ns (cause, k)).entries[p]? = some pe := by
  obtain ⟨segE, hEq, hProp⟩ :=
    deeper_flatten_parent_back ns (upper k) 64 (children ns cause) (-1) 2 [] []
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

/-- Eldest sibling-side entry on an ancestor chain below a fixed parent index:
if the chain's bottom entry does not attach directly to `p`, some strict
ancestor on the chain does. -/
private theorem deeper_chain_first_below (E : List Entry) (p : Nat)
    (hback : ∀ (i : Nat) (e : Entry), E[i]? = some e →
      e.parent = -1 ∨ ∃ (q : Nat) (pe : Entry), e.parent = (q : Int) ∧ q < i ∧
        E[q]? = some pe) :
    ∀ (c : Nat), IndexedAncestor E p c → ∀ (ce : Entry), E[c]? = some ce →
      ce.parent ≠ (p : Int) →
      ∃ (s : Nat) (S : Entry), E[s]? = some S ∧ S.parent = (p : Int) ∧
        IndexedAncestor E s c := by
   intro c h ce hce hne
   revert ce hce hne
   induction h with
  | edge _ e he hp =>
    intro ce hce hne
    have heq : e = ce := Option.some.inj (he.symm.trans hce)
    exact absurd (heq ▸ hp) hne
   | @tail b cc hab e he hp ih =>
     intro ce hce hne
     have hec : e = ce := Option.some.inj (he.symm.trans hce)
     rcases hback cc e he with hr | ⟨q, pe, hqe, _hqlt, hqlook⟩
     · rw [hr] at hp
       exact absurd hp (by omega)
     · have hqb : q = b := by omega
       have hqlook' : E[b]? = some pe := hqb ▸ hqlook
       rw [hec] at hp
       by_cases hbe : pe.parent = (p : Int)
       · exact ⟨b, pe, hqlook', hbe, IndexedAncestor.edge b cc ce hce hp⟩
       · obtain ⟨s, S, hS, hSP, hSb⟩ := ih pe hqlook' hbe
         exact ⟨s, S, hS, hSP, IndexedAncestor.tail hSb ce hce hp⟩

/-- Residual R-ord: subtree order interval for a single rib.

If an even entry `a` is the parent of `d` and `j`'s order position lies at or
after `a`'s and at or before `d`'s, then `j` is `a` itself or a descendant of
`a`. Strictly simpler than the goal: a pure order fact about one rib, no
birth frames, no slot arithmetic, no geometry. Probed true on 574 even-parent
triples over all link-valid trees to seven nodes. -/
def HardBDeeperOrdInterval (ns : List Tree.Node) (cause k : Nat) : Prop :=
  ∀ (a d j : Nat) (ae de J : Entry) (pa pd pj : Nat × Nat),
    (generatedRib ns (cause, k)).entries[a]? = some ae →
    (generatedRib ns (cause, k)).entries[d]? = some de →
    (generatedRib ns (cause, k)).entries[j]? = some J →
    de.parent = (a : Int) → ae.depth % 2 = 0 →
    (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == a) =
      some pa →
    (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == d) =
      some pd →
    (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == j) =
      some pj →
    pa.2 ≤ pj.2 → pj.2 ≤ pd.2 →
    (j = a ∨ IndexedAncestor (generatedRib ns (cause, k)).entries a j)

/-- Residual R-env: envelope transport from a sibling box to a deeper box.

If the odd route `child` already misses the box of the sibling entry `S` and
`j` descends from `S`, then `child`'s route misses `j`'s box. Strictly simpler
than the goal: a pure born-bone transport fact about one rib's executed
frames, taking the sibling miss as a hypothesis. Probed true on every
executed layout checked (the sibling miss holds by the proved sibling
theorem wherever the shape applies). -/
def HardBDeeperEnvTransport (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
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
     ¬ Polyline.hitsRect
       [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
        ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
       ⟨sBorn.x1 - nS.width, ordinate spine r.upper sBorn.t1 - Int.fdiv nS.height 2,
         nS.width, nS.height⟩ →
     ¬ Polyline.hitsRect
       [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
        ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
       ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
         nj.width, nj.height⟩

 /-- The deeper-earlier obligation over executed birth frames, conditional on
 the order-interval fact and the envelope transport. The root-self and
 slot-ordered chain configurations are closed by slot monotonicity against the
 assumed negations; the sibling-subtree and middle-slotted configurations go
 through the sibling box miss and the transport. -/
theorem hardBDeeperEarlierReal
     (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
     (hrun : layout ns p = .ok raw)
     (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
     (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
     (hplace : place ns p spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) = .ok placed)
     (henv : IshikawaEnvFrames ns p
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))))
     (hlink : Tree.link ns = true)
     (hgeomOrd : HardBDeeperOrdInterval ns cause k)
     (hgeomEnv : HardBDeeperEnvTransport ns p raw hrun ribs hg cause k hsource
       hcause spine placed hplace henv) :
     HardBDeeperEarlierReal ns p raw hrun ribs hg cause k hsource hcause
       spine placed hplace henv := by
  intro child j childIdx jIdx nj frames childBorn jBorn hconfig hreal hblock
    hparNe hsibN hnotearly hnotlater
  have hcfg := hconfig
  rcases hconfig with ⟨hchild, hj, hodd, hjlt, _hnj, hlen, hchildBorn, hjBorn, hspan⟩
  have hrl := hreal
  rcases hreal with ⟨frames0, hshape0, hsub⟩
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
  subst hframesEq
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  obtain ⟨jDone, jRest, hjPrefix, _⟩ := List.eq_append_cons_of_mem hj
  change (generatedRib ns (cause, k)).entries.zipIdx =
      jDone ++ (j, jIdx) :: jRest at hjPrefix
  obtain ⟨jPos, _jPar, jBorn0, hjPos, _hjParLookup, hjBorn0, hjEq⟩ :=
    hrecords0 jDone j jIdx jRest hjPrefix
  obtain ⟨childDone, childRest, hchildPrefix, _⟩ := List.eq_append_cons_of_mem hchild
  change (generatedRib ns (cause, k)).entries.zipIdx =
      childDone ++ (child, childIdx) :: childRest at hchildPrefix
  obtain ⟨childPos, cPar, childBorn0, hchildPos, hchildParLookup, hchildBorn0,
    hchildEq⟩ :=
    hrecords0 childDone child childIdx childRest hchildPrefix
  have hjBornEq : jBorn0 = jBorn := by
    have h1 : frames[jIdx + 1]? = some jBorn := hjBorn
    have h2 : frames[jIdx + 1]? = some jBorn0 := hjBorn0
    exact Option.some.inj (h2.symm.trans h1)
  have hchildBornEq : childBorn0 = childBorn := by
    have h1 : frames[childIdx + 1]? = some childBorn := hchildBorn
    have h2 : frames[childIdx + 1]? = some childBorn0 := hchildBorn0
    exact Option.some.inj (h2.symm.trans h1)
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hnonempty : (generatedRib ns (cause, k)).entries.isEmpty = false := by
    cases hentries : (generatedRib ns (cause, k)).entries with
    | nil =>
      change (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx at hchild
      rw [hentries] at hchild
      simp at hchild
    | cons first rest => rfl
  have hbudget := generated_reservation_budget ns p ribs hg
    (generatedRib ns (cause, k)) hsource hnonempty
  have hlb := generated_entry_parent_lower_bound ns cause k child childIdx hchild
  have hrootFalse : child.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink hcause child childIdx hchild heq
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
      some parentEntry :=
    List.getElem?_eq_getElem hparentBound
  have hparentMem : (parentEntry, (child.parent).toNat) ∈
      (generatedRib ns (cause, k)).entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hparentLookup
  have hpar : child.parent = ((child.parent).toNat : Int) := hparIdx
  have hchildDepth := generated_parent_child_depth ns cause k hlink hcause
    parentEntry child (child.parent).toNat childIdx hparentMem hchild hpar
  have hparentEven : parentEntry.depth % 2 = 0 :=
    parent_depth_even parentEntry.depth child.depth hchildDepth hodd
  obtain ⟨parentDone, parentRest, hparentPrefix, _⟩ :=
    List.eq_append_cons_of_mem hparentMem
  change (generatedRib ns (cause, k)).entries.zipIdx =
      parentDone ++ (parentEntry, (child.parent).toNat) :: parentRest
    at hparentPrefix
  obtain ⟨parentPos, grandpar, parentBorn, hparentPos, _hgpLookup,
    hparentBornLookup, hparentEquation⟩ :=
    hrecords0 parentDone parentEntry (child.parent).toNat parentRest hparentPrefix
  have hcPar : cPar = parentBorn := by
    have h1 : frames[(child.parent).toNat + 1]? = some cPar := hchildParLookup
    have h2 : frames[(child.parent).toNat + 1]? = some parentBorn :=
      hparentBornLookup
    exact Option.some.inj (h1.symm.trans h2)
  rw [hcPar] at hchildEq
  have hchildT0 : childBorn.t0 = parentBorn.t0 := by
    rw [← hchildBornEq, hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).1
  have hchildT1 : childBorn.t1 =
      Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [← hchildBornEq, hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.1
  have hjT1 : jBorn.t1 =
      Int.fdiv (r.length * (jPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [← hjBornEq, hjEq]
    exact depthBone_endpoint_slot _ _ _ _ _ _
  have hparentT0 : parentBorn.t0 =
      Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hparentEquation]
    exact (depthBone_even_endpoints p
      { grandpar with drawn := processedOddDraws parentDone (parentEntry.parent + 1).toNat }
      parentEntry.depth (Int.fdiv (r.length * (parentPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns parentEntry.node).length
      (run p r.heights + 3) hparentEven).1
  have hback := deeper_rib_parent_back ns cause k
  -- Shared sibling-subtree case: from the sibling shape data to the miss,
  -- through the proved sibling box miss and the envelope transport.
  have sib_case : ∀ (s : Nat) (S : Entry),
      (generatedRib ns (cause, k)).entries[s]? = some S → s ≠ jIdx →
      S.parent = ((child.parent).toNat : Int) →
      IndexedAncestor (generatedRib ns (cause, k)).entries s jIdx →
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩ := by
    intro s S hS hsne hSP hSchain
    have hslt : s < jIdx := deeper_chain_lt _ hback s jIdx hSchain
    have hsclt : s < childIdx := by omega
    have hSmem : (S, s) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hS
    have hSdepth := generated_parent_child_depth ns cause k hlink hcause
      parentEntry S (child.parent).toNat s hparentMem hSmem hSP
    have hSodd : S.depth % 2 ≠ 0 := by rw [hSdepth]; omega
    have hSnode : S.node ∈ children ns parentEntry.node :=
      generated_parent_child_membership ns cause k parentEntry S
        (child.parent).toNat s hparentMem hSmem hSP
    have hSnodeLt : S.node < ns.length := by
      have hm := (List.mem_filter.mp hSnode).1
      rw [List.mem_range] at hm
      exact hm
    obtain ⟨nS, hnS⟩ : ∃ n, ns[S.node]? = some n :=
      ⟨ns[S.node], List.getElem?_eq_getElem hSnodeLt⟩
    obtain ⟨sDone, sRest, sPrefix, _⟩ := List.eq_append_cons_of_mem hSmem
    change (generatedRib ns (cause, k)).entries.zipIdx =
        sDone ++ (S, s) :: sRest at sPrefix
    obtain ⟨sPos, _sPar, sBorn, hsPos, _hsParLook, hsBorn, _hsEq⟩ :=
      hrecords0 sDone S s sRest sPrefix
    have hcfgS : HardBCaseConfig ns p cause k spine r child S childIdx s nS
        frames childBorn sBorn :=
       ⟨hchild, hSmem, hodd, hsclt, hnS, hlen, hchildBorn, hsBorn, hspan⟩
    have hSmiss := hard_b_sibling_real ns p raw hrun ribs hg cause k hsource
      hcause spine placed hplace child S childIdx s nS frames childBorn sBorn
       hcfgS hrl (hSP.trans hpar.symm)
    exact hgeomEnv child j childIdx jIdx nj frames childBorn jBorn sBorn s S
       nS hcfg hrl hS hsne hSP hSchain hsBorn hnS hSmiss
  have hDlook : (generatedRib ns (cause, k)).entries[childIdx]? = some child :=
    List.mem_zipIdx_iff_getElem?.mp hchild
  have hJlook : (generatedRib ns (cause, k)).entries[jIdx]? = some j :=
    List.mem_zipIdx_iff_getElem?.mp hj
  rcases hblock with ⟨sIdx, S, hS, hsne, hSPar, hchain⟩ |
      ⟨hIdx, H, hH, hHroot, hHor, hord⟩
  · exact sib_case sIdx S hS hsne hSPar hchain
  · have hHmem : (H, hIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hH
    obtain ⟨hDone, hRest, hPrefix, _⟩ := List.eq_append_cons_of_mem hHmem
    change (generatedRib ns (cause, k)).entries.zipIdx =
        hDone ++ (H, hIdx) :: hRest at hPrefix
    obtain ⟨headPos, _headPar, _headBorn, hheadPos, _, _, _⟩ :=
      hrecords0 hDone H hIdx hRest hPrefix
    have hdisj := hord headPos parentPos hheadPos hparentPos
    rcases hdisj with hle | hheadLt
    · omega
    · rcases hHor with ⟨_hHJ, hIdxJ⟩ | hchain
      · have hjPos' : (generatedRib ns (cause, k)).order.zipIdx.find?
            (fun v => v.1 == hIdx) = some jPos := by
          rw [hIdxJ]
          exact hjPos
        have hdisj2 := hord jPos parentPos hjPos' hparentPos
        rcases hdisj2 with hle2 | hltpos
        · omega
        · have hslot := hard_b_slot_mono_of_pos_lt _ jBorn childBorn parentBorn
            jPos parentPos hjT1 hparentT0 hchildT0 hheight hbudget hltpos
          exact False.elim (hnotearly hslot)
      · by_cases hearly : jPos.2 < parentPos.2
        · have hslot := hard_b_slot_mono_of_pos_lt _ jBorn childBorn parentBorn
            jPos parentPos hjT1 hparentT0 hchildT0 hheight hbudget hearly
          exact False.elim (hnotearly hslot)
        · have heary' : parentPos.2 ≤ jPos.2 := by omega
          by_cases hlate : childPos.2 < jPos.2
          · have hgap := ordinal_slots_gap r.length
              (r.entries.length + 1 : Nat) r.heights ((childPos.2 + 1 : Nat))
              ((jPos.2 + 1 : Nat)) (by omega) hheight hbudget (by omega)
            have hlateIneq : childBorn.t1 + r.heights ≤ jBorn.t1 := by
              rw [hchildT1, hjT1]
              exact hgap
            exact False.elim (hnotlater hlateIneq)
          · have hlate' : jPos.2 ≤ childPos.2 := by omega
            have hordRes := hgeomOrd (child.parent).toNat childIdx jIdx
              parentEntry child j parentPos childPos jPos hparentLookup hDlook
              hJlook hpar hparentEven hparentPos hchildPos hjPos heary' hlate'
            rcases hordRes with hjeq | hchainP
            · exact absurd (by rw [hparIdx, hjeq]) hparNe
            · have hsibNp : j.parent ≠ (((child.parent).toNat : Nat) : Int) :=
                hpar ▸ hsibN
              obtain ⟨s, S, hS, hSP, hSchain⟩ :=
                deeper_chain_first_below _ _ hback jIdx hchainP j hJlook hsibNp
              have hsne : s ≠ jIdx := by
                intro heq
                subst heq
                have hSJ : S = j :=
                  Option.some.inj (hS.symm.trans hJlook)
                have h2 : j.parent = child.parent := by
                  rw [← hSJ]
                  exact hSP.trans hpar.symm
                exact hsibN h2
              exact sib_case s S hS hsne hSP hSchain

end Elegant.Ishikawa
