import Elegant.Kinds.IshikawaSameRibClearance
import Elegant.IshikawaDeeperEarlierProof
import Elegant.IshikawaDeeperRouteGapProof

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-! ### Same-rib envelope clearance: entry-level residuals

`ishikawaSameRibPieceClearance` proves that the shifted route of one piece of
a placed rib misses the shifted box of every other piece except the two
configurations collected in `IshikawaSameRibEnvelopeClearance`.  This module
discharges that residual from two entry-level hypotheses, one per
configuration:

* (A) `IshikawaCauseRouteEntryBoxClearance`: the cause route against an entry
  box.  No proved entry-level theorem covers this direction:
  `bone_route_misses_cause_box` is the dual (entry route vs cause box) and
  `cause_route_misses_right_box` needs the foreign box right of the route's
  right end.  The closest produced fact is the ENV invariant
  `ishikawa_env_invariant`, bounding every entry-born bone's left end
  `run p r.heights + 1` left of the master diagonal at its own `t1`; the
  missing step is transferring that own-slot bound across the bone's slot
  span.  That transfer is the hypothesis.
* (B) `IshikawaDescendantRouteBoxClearance`: an odd-depth entry's route
  against the box of a strict descendant configuration (`idxI < idxJ` with
  order position `posJ.2 < posI.2`).  The landed hard-B chain
  (`ishikawa_hard_b_real'`) covers only the mirror index order
  (`jIdx < childIdx` in `HardBCaseConfig`); the descendant transport
  (`HardBDeeperDescEnvelope`, `HardBDeeperGapOnly`,
  `hardBDeeperEnvTransport'`) shares that index premise, so it does not
  apply.  The hypothesis is the entry-level form of exactly that pair shape.

Both hypotheses are about the `place` phase of one rib: no pieces, no
assembly shift. -/

/-- (A) entry-level: the cause route of a successfully placed generated rib
misses every entry box, in the born-bone form of
`place_entry_route_misses_entry_box_odd_later`. -/
def IshikawaCauseRouteEntryBoxClearance (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
  ∀ (eJ : Entry) (idxJ : Nat) (posJ : Nat × Nat) (parJ : Bone) (nJ : Tree.Node),
    (eJ, idxJ) ∈ r.entries.zipIdx →
    r.order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ →
    ns[eJ.node]? = some nJ →
    IndexedBoneGenealogy ns p r (eJ.parent + 1).toNat parJ →
    let tJ := Int.fdiv (r.length * (posJ.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let bJ := depthBone p parJ eJ.depth tJ (children ns eJ.node).length (run p r.heights + 3)
    ¬ Polyline.hitsRect
      [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]
      ⟨bJ.x1 - nJ.width, ordinate spine r.upper bJ.t1 - Int.fdiv nJ.height 2,
        nJ.width, nJ.height⟩

/-- (B) entry-level: an odd-depth entry's born route misses the box of an
entry whose index is later but whose order position is earlier (the strict
descendant configuration), over one rib's `place` run. -/
def IshikawaDescendantRouteBoxClearance (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hlink : Tree.link ns = true) (_hcause : cause ∈ children ns 0)
    (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
  ∀ (eI eJ : Entry) (idxI idxJ : Nat) (posI posJ : Nat × Nat)
    (parI parJ : Bone) (nI nJ : Tree.Node),
    (eI, idxI) ∈ r.entries.zipIdx →
    (eJ, idxJ) ∈ r.entries.zipIdx →
    r.order.zipIdx.find? (fun v => v.1 == idxI) = some posI →
    r.order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ →
    ns[eI.node]? = some nI → ns[eJ.node]? = some nJ →
    IndexedBoneGenealogy ns p r (eI.parent + 1).toNat parI →
    IndexedBoneGenealogy ns p r (eJ.parent + 1).toNat parJ →
    eI.depth % 2 ≠ 0 → eI.node ≠ eJ.node → idxI < idxJ → posJ.2 < posI.2 →
    let tI := Int.fdiv (r.length * (posI.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let bI := depthBone p parI eI.depth tI (children ns eI.node).length (run p r.heights + 3)
    let tJ := Int.fdiv (r.length * (posJ.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let bJ := depthBone p parJ eJ.depth tJ (children ns eJ.node).length (run p r.heights + 3)
    ¬ Polyline.hitsRect
      [⟨bI.x0, ordinate spine r.upper bI.t0⟩,
       ⟨bI.x1, ordinate spine r.upper bI.t1⟩]
      ⟨bJ.x1 - nJ.width, ordinate spine r.upper bJ.t1 - Int.fdiv nJ.height 2,
        nJ.width, nJ.height⟩


/-- Membership in `children ns i` determines the parent. -/
private theorem mem_children_parentOf {ns : List Tree.Node} {i j : Nat}
    (h : j ∈ children ns i) : Tree.parentOf ns j = some i := by
  have ht := (List.mem_filter.mp h).2
  unfold Tree.parentOf
  cases hn : ns[j]? with
  | none => simp [hn] at ht
  | some n => simpa [hn] using ht

/-- Every entry node of a generated rib is a strict descendant of the cause:
`cause < e.node`.  Proved by induction on the entry depth; the parent entry
is read off the executed birth frames of the successful `place` run. -/
private theorem generated_entry_node_gt_cause {ns : List Tree.Node} (p : Params)
    (spine : Int) (ribs : List Rib) (r placed : Rib) (cause k : Nat)
    (hplace : place ns p spine r = .ok placed)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (hr : r = effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))) :
    ∀ (e : Entry) (idx : Nat),
      (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx → cause < e.node := by
  intro e idx heG
  have hre : r.entries = (generatedRib ns (cause, k)).entries := by rw [hr]; rfl
  have he_r : (e, idx) ∈ r.entries.zipIdx := by rw [hre]; exact heG
  obtain ⟨frames, hlen, _hrootF, hrecords, _hpieces⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  suffices key : ∀ d (e : Entry) (idx : Nat), e.depth = d →
      (e, idx) ∈ r.entries.zipIdx → cause < e.node by
    exact key e.depth e idx rfl he_r
  intro d
  induction d with
  | zero =>
    intro e idx hd her
    have heGi : (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx := by
      rw [← hre]; exact her
    by_cases hroot : e.parent = -1
    · have hn := generated_root_child_membership ns cause k e idx heGi hroot
      exact (Tree.link_valid hlink).parentLt e.node cause (mem_children_parentOf hn)
    · obtain ⟨done, rest, hpre, _⟩ := List.eq_append_cons_of_mem her
      obtain ⟨_pos, _parB, _bornB, _hposF, hparF, _hbornF, _hbornEq⟩ :=
        hrecords done e idx rest hpre
      have hlt : (e.parent + 1).toNat < frames.length :=
        (List.getElem?_eq_some_iff.mp hparF).1
      rw [hlen] at hlt
      have hge : 0 ≤ e.parent := by
        have := generated_entry_parent_lower_bound ns cause k e idx heGi
        omega
      have hbound : (e.parent).toNat < r.entries.length := by omega
      let parentEntry := r.entries[(e.parent).toNat]'hbound
      have hple : r.entries[(e.parent).toNat]? = some parentEntry :=
        List.getElem?_eq_getElem hbound
      have hpmem : (parentEntry, (e.parent).toNat) ∈ r.entries.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hple
      have hpmemG : (parentEntry, (e.parent).toNat) ∈
          (generatedRib ns (cause, k)).entries.zipIdx := by
        rw [← hre]; exact hpmem
      have hparEq : e.parent = ((e.parent).toNat : Int) := by omega
      have hdepth := generated_parent_child_depth ns cause k hlink hcause
        parentEntry e (e.parent).toNat idx hpmemG heGi hparEq
      omega
  | succ d ih =>
    intro e idx hd her
    have heGi : (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx := by
      rw [← hre]; exact her
    by_cases hroot : e.parent = -1
    · have hn := generated_root_child_membership ns cause k e idx heGi hroot
      exact (Tree.link_valid hlink).parentLt e.node cause (mem_children_parentOf hn)
    · obtain ⟨done, rest, hpre, _⟩ := List.eq_append_cons_of_mem her
      obtain ⟨_pos, _parB, _bornB, _hposF, hparF, _hbornF, _hbornEq⟩ :=
        hrecords done e idx rest hpre
      have hlt : (e.parent + 1).toNat < frames.length :=
        (List.getElem?_eq_some_iff.mp hparF).1
      rw [hlen] at hlt
      have hge : 0 ≤ e.parent := by
        have := generated_entry_parent_lower_bound ns cause k e idx heGi
        omega
      have hbound : (e.parent).toNat < r.entries.length := by omega
      let parentEntry := r.entries[(e.parent).toNat]'hbound
      have hple : r.entries[(e.parent).toNat]? = some parentEntry :=
        List.getElem?_eq_getElem hbound
      have hpmem : (parentEntry, (e.parent).toNat) ∈ r.entries.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hple
      have hpmemG : (parentEntry, (e.parent).toNat) ∈
          (generatedRib ns (cause, k)).entries.zipIdx := by
        rw [← hre]; exact hpmem
      have hparEq : e.parent = ((e.parent).toNat : Int) := by omega
      have hdepth := generated_parent_child_depth ns cause k hlink hcause
        parentEntry e (e.parent).toNat idx hpmemG heGi hparEq
      have hpd : parentEntry.depth = d := by omega
      have hcp := ih parentEntry (e.parent).toNat hpd hpmem
      have hmem := generated_parent_child_membership ns cause k parentEntry e
        (e.parent).toNat idx hpmemG heGi hparEq
      have hlt2 := (Tree.link_valid hlink).parentLt e.node parentEntry.node
        (mem_children_parentOf hmem)
      omega

/-- The executed-model form of the two residuals, quantified over every rib of
the decoded input. -/
def IshikawaEnvelopeResiduals (m : Model) : Prop :=
  (∀ (e : IshikawaRawExecution m) (cause k : Nat)
    (hsource : generatedRib e.input.nodes (cause, k) ∈ e.ribs)
    (hcause : cause ∈ children e.input.nodes 0) (ribPlaced : Rib)
    (hplace : place e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.spine
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))) = .ok ribPlaced),
    IshikawaCauseRouteEntryBoxClearance e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
      cause k hsource hcause e.spine ribPlaced hplace) ∧
  (∀ (e : IshikawaRawExecution m) (cause k : Nat)
    (hsource : generatedRib e.input.nodes (cause, k) ∈ e.ribs)
    (hcause : cause ∈ children e.input.nodes 0) (ribPlaced : Rib)
    (hplace : place e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.spine
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))) = .ok ribPlaced),
    IshikawaDescendantRouteBoxClearance e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
      cause k hsource
      (Elegant.Kinds.IshikawaValid.successful_link e.input.nodes _ e.raw e.hlayout)
      hcause e.spine ribPlaced hplace)


private theorem env_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `place` only attaches pieces: cause, entries and order are preserved. -/
private theorem env_place_rib_fields_eq (ns : List Tree.Node) (p : Params)
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
    obtain ⟨mid, _, hret⟩ := env_bind_ok h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
    cases hret
    exact ⟨rfl, rfl, rfl⟩

/-- Same node in two entry slots forces equal slots, via node nodup. -/
private theorem env_entry_idx_eq_of_node_eq (es : List Entry)
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

/-- Same-rib envelope clearance from the two entry-level residuals: the
piece-level disjunction is transported through `place`'s field preservation
and `generated_piece_strict_temporal_geometry`; every piece shape is either
the cause shape or an entry shape, and the entry shapes are re-identified
with the residual's entries through node nodup and index/order lookup
uniqueness. -/
theorem ishikawaSameRibEnvelopeClearance (m : Model)
    (hres : IshikawaEnvelopeResiduals m) :
    IshikawaSameRibEnvelopeClearance m := by
  intro e rA _dx _hshift pieceR pieceB hmemR hmemB hne hdisj
  have hmemA : rA ∈ e.placed := assemblyPairShift_mem _hshift
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
    Elegant.Kinds.IshikawaValid.successful_link e.input.nodes _
      e.raw e.hlayout
  have hfields := env_place_rib_fields_eq _ _ _ _ _ hplace
  have hrcause : (effectivePlacedInput e.input.nodes
      (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
      (generatedRib e.input.nodes (cause, k))).cause = cause :=
    (generated_rib_fields e.input.nodes cause k).1
  have hrAcause : rA.cause = cause := by
    rw [hfields.1]
    exact hrcause
  have hndNodes :
      ((effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))).entries.map Entry.node).Nodup := by
    exact generated_entry_nodes_nodup e.input.nodes cause k hlink
  obtain ⟨iR, rectR, pointsR⟩ := pieceR
  obtain ⟨iB, rectB, pointsB⟩ := pieceB
  have hR := generated_piece_strict_temporal_geometry e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
    cause k hsource hcauseMem e.spine rA hplace iR rectR pointsR hmemR
  have hB := generated_piece_strict_temporal_geometry e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
    cause k hsource hcauseMem e.spine rA hplace iB rectB pointsB hmemB
  have hne' : iR ≠ iB := hne
  have hgtC (e' : Entry) (idx' : Nat)
      (he' : (e', idx') ∈ (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))).entries.zipIdx) :
      cause < e'.node :=
    generated_entry_node_gt_cause (Elegant.Kinds.Ishikawa.params m.profile)
      e.spine e.ribs _ rA cause k hplace hlink hcauseMem rfl e' idx' he'
  rcases hdisj with ⟨hRcause, hBc⟩ |
    ⟨eI, eJ, idxI, idxJ, posI, posJ, heIRA, heJRA, hiRI, hiBJ, hoddI,
      hposIRA, hposJRA, hltIdx, hgtPos⟩
  · -- (A) cause route against a non-cause box.
    have hA' := hres.1 e cause k hsource hcauseMem rA hplace
    rcases hR with ⟨nR, _hnR, hiR, _hrectR, hptsR⟩ |
      ⟨eI', idxI', _posI', _parI', _nI', heI', _hposI', _hnI', hiI',
        _hgeneI', _hcountI', _hrectR, hptsR, _hoddI', _hevenI'⟩
    · rcases hB with ⟨_nB, _hnB, hiB, _hrectB, _hptsB⟩ |
        ⟨eJ', idxJ', posJ', parJ', nJ', heJ', hposJ', hnJ', _hiJ', hgeneJ',
          _hcountJ', hrectB, hptsB, _hoddJ', _hevenJ'⟩
      · -- The box piece is cause-shaped: its index is the cause, excluded.
        have hiBc : iB = rA.cause := hiB.trans hfields.1.symm
        exact absurd hiBc hBc
      · rw [hptsR, hrectB]
        exact hA' eJ' idxJ' posJ' parJ' nJ' heJ' hposJ' hnJ' hgeneJ'
    · -- An entry-shaped route with cause index is impossible: entry nodes
      -- are strict descendants of the cause.
      have hiRcause : iR = cause := hRcause.trans hrAcause
      have hnc : eI'.node = cause := hiI'.symm.trans hiRcause
      have hlt' := hgtC eI' idxI' heI'
      rw [hnc] at hlt'
      exact absurd hlt' (by omega)
  · -- (B) odd entry route against a strict-descendant box.
    have hB' := hres.2 e cause k hsource hcauseMem rA hplace
    have heI_r : (eI, idxI) ∈ (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))).entries.zipIdx := by
      rw [← hfields.2.1]
      exact heIRA
    have heJ_r : (eJ, idxJ) ∈ (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))).entries.zipIdx := by
      rw [← hfields.2.1]
      exact heJRA
    have hposI_r : (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))).order.zipIdx.find?
        (fun v => v.1 == idxI) = some posI := by
      rw [← hfields.2.2]
      exact hposIRA
    have hposJ_r : (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))).order.zipIdx.find?
        (fun v => v.1 == idxJ) = some posJ := by
      rw [← hfields.2.2]
      exact hposJRA
    rcases hR with ⟨_nR, _hnR, hiR, _hrectR, _hptsR⟩ |
      ⟨eI', idxI', posI', parI', nI', heI', hposI', hnI', hiI', hgeneI',
        _hcountI', hrectR, hptsR, _hoddI', _hevenI'⟩
    · -- Cause-shaped route with entry index: impossible as above.
      have hiRcause : iR = cause := hiR.trans hrcause
      have hnc : eI.node = cause := hiRI.symm.trans hiRcause
      have hlt' := hgtC eI idxI heI_r
      rw [hnc] at hlt'
      exact absurd hlt' (by omega)
    · rcases hB with ⟨_nB, _hnB, hiB, _hrectB, _hptsB⟩ |
        ⟨eJ', idxJ', posJ', parJ', nJ', heJ', hposJ', hnJ', hiJ', hgeneJ',
          _hcountJ', hrectB, hptsB, _hoddJ', _hevenJ'⟩
      · -- Cause-shaped box with entry index: impossible as above.
        have hiBcause : iB = cause := hiB.trans hrcause
        have hnc : eJ.node = cause := hiBJ.symm.trans hiBcause
        have hlt' := hgtC eJ idxJ heJ_r
        rw [hnc] at hlt'
        exact absurd hlt' (by omega)
      · -- Both pieces are entry-shaped: re-identify them with the residual's
        -- entries and apply the descendant-route residual.
        have hnodeEqI : eI'.node = eI.node := hiI'.symm.trans hiRI
        have hnodeEqJ : eJ'.node = eJ.node := hiJ'.symm.trans hiBJ
        have hidxEqI : idxI' = idxI :=
          env_entry_idx_eq_of_node_eq _ hndNodes eI' eI idxI' idxI heI' heI_r
            hnodeEqI
        have hidxEqJ : idxJ' = idxJ :=
          env_entry_idx_eq_of_node_eq _ hndNodes eJ' eJ idxJ' idxJ heJ' heJ_r
            hnodeEqJ
        have gI' := List.mem_zipIdx_iff_getElem?.mp heI'
        have gI := List.mem_zipIdx_iff_getElem?.mp heI_r
        change _ = some eI' at gI'
        change _ = some eI at gI
        rw [hidxEqI] at gI'
        have heqEI : eI' = eI := Option.some.inj (gI'.symm.trans gI)
        have gJ' := List.mem_zipIdx_iff_getElem?.mp heJ'
        have gJ := List.mem_zipIdx_iff_getElem?.mp heJ_r
        change _ = some eJ' at gJ'
        change _ = some eJ at gJ
        rw [hidxEqJ] at gJ'
        have heqEJ : eJ' = eJ := Option.some.inj (gJ'.symm.trans gJ)
        have hposI'd : (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
            (generatedRib e.input.nodes (cause, k))).order.zipIdx.find?
            (fun v => v.1 == idxI) = some posI' := by
          have h := hposI'
          rw [hidxEqI] at h
          exact h
        have hposEqI : posI' = posI :=
          Option.some.inj (hposI'd.symm.trans hposI_r)
        have hposJ'd : (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
            (generatedRib e.input.nodes (cause, k))).order.zipIdx.find?
            (fun v => v.1 == idxJ) = some posJ' := by
          have h := hposJ'
          rw [hidxEqJ] at h
          exact h
        have hposEqJ : posJ' = posJ :=
          Option.some.inj (hposJ'd.symm.trans hposJ_r)
        have hoddI'd : eI'.depth % 2 ≠ 0 := by
          rw [heqEI]
          exact hoddI
        have hnodeNe' : eI'.node ≠ eJ'.node := by
          rw [heqEI, heqEJ]
          intro h
          exact hne (by rw [hiRI, hiBJ]; exact h)
        have hltIdx' : idxI' < idxJ' := by
          rw [hidxEqI, hidxEqJ]
          exact hltIdx
        have hgtPos' : posJ'.2 < posI'.2 := by
          rw [hposEqJ, hposEqI]
          exact hgtPos
        have hmiss := hB' eI' eJ' idxI' idxJ' posI' posJ' parI' parJ' nI' nJ'
          heI' heJ' hposI' hposJ' hnI' hnJ' hgeneI' hgeneJ' hoddI'd hnodeNe'
          hltIdx' hgtPos'
        rw [hptsR, hrectB]
        exact hmiss

/-- Same-rib piece clearance with the envelope residuals discharged through
the entry-level facts. -/
theorem ishikawaSameRibPieceClearance' (m : Model)
    (hres : IshikawaEnvelopeResiduals m) :
    IshikawaSameRibPieceClearance m :=
  ishikawaSameRibPieceClearance m (ishikawaSameRibEnvelopeClearance m hres)

end Elegant.Kinds.IshikawaFinal
