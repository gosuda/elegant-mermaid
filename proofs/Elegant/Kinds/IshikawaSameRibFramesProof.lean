import Elegant.Kinds.IshikawaCauseRouteClearance
import Elegant.Kinds.IshikawaDescRouteClearance
import Elegant.Kinds.IshikawaSameRibEnvelope
import Elegant.Kinds.IshikawaSameRibClearance
import Elegant.IshikawaClearanceFacts

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-! ### Same-rib envelope clearance over executed frames

The two entry-level leaf defs kept in `IshikawaSameRibEnvelope`
(`IshikawaCauseRouteEntryBoxClearance` and
`IshikawaDescendantRouteBoxClearance`) quantify over an arbitrary
`IndexedBoneGenealogy`, which admits overdrawn bones through `.draw`; both
are false as stated (see the falsity theorems in the two worker files).
This module proves the same-rib envelope conclusions over executed birth
frames instead, redoing the envelope consumer proof with two edits:

* Cause branch: the box piece is identified both by the accounted geometry
  (`place_piece_accounted_geometry`, giving the genealogy bone) and by the
  birth frames (`place_common_birth_frames`, giving the born bone). The two
  rect equations force the bones to agree in `x1`/`t1`, so the frames-only
  `CauseEntryEnvBound` residual transfers to the genealogy bone and the
  proved `ishikawaCauseRouteEntryBoxClearanceAccounted` core closes the
  miss. The ENV bound itself is assumed only about executed frames.
* Descendant branch: both pieces are identified by birth frames; entries
  are re-identified by node nodup exactly as before, and the order
  residual plus the frame gap residual close the miss through the copied
  diagonal chain of `ishikawaDescendantFrameClearance`.

Allowed hypotheses are `DescendantOrdInterval` and `DescendantFrameGap`
(universally quantified, the two residuals of the descendant core) and the
frames-only `CauseEntryEnvBound` below. Nothing genealogy-quantified is
assumed. -/

/-- Frames-only ENV residual for the cause case: the entry bone of the
executed birth frame satisfies the master-diagonal bound. The frame
premises are copied verbatim from `place_common_birth_frames`, so the use
site discharges them directly. Birth-frame sweep over executed layouts:
28 non-vacuous cause-vs-entry pairs, 0 misses, gap
`master - (run p r.heights + 1) - bJ.x1 >= 2` everywhere. -/
def CauseEntryEnvBound (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
  ∀ (frames : List Bone) (eJ : Entry) (idxJ : Nat) (bJ : Bone),
    frames.length = r.entries.length + 1 →
    frames[0]? = some ({ x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length } : Bone) →
    (∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat) (rest : List (Entry × Nat)),
      r.entries.zipIdx = done ++ (e, idx) :: rest →
      ∃ (pos : Nat × Nat) (parent born : Bone),
        r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
        frames[(e.parent + 1).toNat]? = some parent ∧ frames[idx + 1]? = some born ∧
        born = depthBone p
          { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
          e.depth (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
          (children ns e.node).length (run p r.heights + 3)) →
    frames[idxJ + 1]? = some bJ →
    (eJ, idxJ) ∈ r.entries.zipIdx →
    bJ.x1 ≤ envMasterX r p bJ.t1 - (run p r.heights + 1)

/-- Membership in `children ns i` determines the parent. -/
private theorem frames_mem_children_parentOf {ns : List Tree.Node} {i j : Nat}
    (h : j ∈ children ns i) : Tree.parentOf ns j = some i := by
  have ht := (List.mem_filter.mp h).2
  unfold Tree.parentOf
  cases hn : ns[j]? with
  | none => simp [hn] at ht
  | some n => simpa [hn] using ht

/-- Every entry node of a generated rib is a strict descendant of the cause:
`cause < e.node`. Proved by induction on the entry depth; the parent entry
is read off the executed birth frames of the successful `place` run. -/
private theorem frames_entry_node_gt_cause {ns : List Tree.Node} (p : Params)
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
      exact (Tree.link_valid hlink).parentLt e.node cause (frames_mem_children_parentOf hn)
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
      exact (Tree.link_valid hlink).parentLt e.node cause (frames_mem_children_parentOf hn)
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
        (frames_mem_children_parentOf hmem)
      omega

private theorem frames_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `place` only attaches pieces: cause, entries and order are preserved. -/
private theorem frames_place_rib_fields_eq (ns : List Tree.Node) (p : Params)
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
    obtain ⟨mid, _, hret⟩ := frames_bind_ok h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
    cases hret
    exact ⟨rfl, rfl, rfl⟩

/-- Same node in two entry slots forces equal slots, via node nodup. -/
private theorem frames_entry_idx_eq_of_node_eq (es : List Entry)
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

/-- Scaled cross bound for the descendant diagonal chain. -/
private theorem frames_desc_scaled_cross_bound (p : Params) (height span : Int)
    (hh : 0 ≤ height) (ht : 0 ≤ span) (hsin : 0 < p.sin) :
    height * run p span ≤ span * (run p height + 1) := by
  have hq := Int.mul_fdiv_add_fmod (span * p.cos) p.sin
  have hr := Int.fmod_nonneg_of_pos (span * p.cos) hsin
  have hlo : p.sin * run p span ≤ span * p.cos := by
    dsimp only [run]
    omega
  have hhi : height * p.cos ≤ p.sin * (run p height + 1) := by
    have h := Int.le_of_lt (Int.lt_fdiv_add_one_mul_self (height * p.cos) hsin)
    simpa only [run, Int.mul_comm] using h
  have hfirst := Int.mul_le_mul_of_nonneg_right hlo hh
  have hsecond := Int.mul_le_mul_of_nonneg_right hhi ht
  apply Int.le_of_mul_le_mul_left (a := p.sin) _ hsin
  calc
    p.sin * (height * run p span) = (p.sin * run p span) * height := by
      simp only [Int.mul_comm, Int.mul_left_comm]
    _ ≤ (span * p.cos) * height := hfirst
    _ = (height * p.cos) * span := by
      simp only [Int.mul_comm, Int.mul_left_comm]
    _ ≤ (p.sin * (run p height + 1)) * span := hsecond
    _ = p.sin * (span * (run p height + 1)) := by
      simp only [Int.mul_comm, Int.mul_left_comm]

/-- Diagonal miss for the descendant configuration. -/
private theorem frames_desc_diag_miss
    (x0 x1 t0 t1 t width height reservation spine : Int) (up : Bool)
    (ht : t0 < t1) (hx : x1 ≤ x0) (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hcoverage : (x0 - x1) * height ≤ (t1 - t0) * reservation) :
    ¬ Polyline.hitsRect
      [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
      ⟨x0 + Int.fdiv ((x1 - x0) * (t - t0)) (t1 - t0) - reservation - width,
        ordinate spine up t - Int.fdiv height 2, width, height⟩ := by
  let span := t1 - t0
  let fall := x0 - x1
  let q := Int.fdiv ((x1 - x0) * (t - t0)) span
  have hspan : 0 < span := by dsimp only [span]; omega
  have hfall : 0 ≤ fall := by dsimp only [fall]; omega
  have hnormalX : x1 - x0 = -fall := by dsimp only [fall]; omega
  have hfloor : span * q ≤ -(fall * t) + fall * t0 := by
    have hq := Int.mul_fdiv_add_fmod ((x1 - x0) * (t - t0)) span
    have hr := Int.fmod_nonneg_of_pos ((x1 - x0) * (t - t0)) hspan
    have hraw : span * q ≤ (x1 - x0) * (t - t0) := by
      dsimp only [q]
      omega
    rw [hnormalX] at hraw
    simp only [Int.mul_sub, Int.neg_mul] at hraw
    omega
  have hhalf : 0 ≤ Int.fdiv height 2 ∧ Int.fdiv height 2 ≤ height := by
    rw [Tree.fdiv2]
    omega
  have hwidthProduct := Int.mul_nonneg (Int.le_of_lt hspan) hw
  have hhalfProduct := Int.mul_nonneg hfall hhalf.1
  have hremainingProduct := Int.mul_nonneg hfall
    (show 0 ≤ height - Int.fdiv height 2 by omega)
  simp only [Int.mul_sub] at hremainingProduct
  change fall * height ≤ span * reservation at hcoverage
  change ¬ Polyline.hitsRect
    [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
    ⟨x0 + q - reservation - width, ordinate spine up t - Int.fdiv height 2,
      width, height⟩
  have hneq : (⟨x0, ordinate spine up t0⟩ : Point) ≠
      ⟨x1, ordinate spine up t1⟩ := by
    intro heq
    have hy := congrArg Point.y heq
    cases up <;> simp only [ordinate, Bool.false_eq_true, ↓reduceIte] at hy <;> omega
  intro hhit
  apply hhit.2.2
  constructor
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    refine ⟨hneq, ?_⟩
    cases up with
    | false =>
      apply Or.inl
      have hnormalY : (spine + t0) - (spine + t1) = -span := by
        dsimp only [span]
        omega
      simp only [Polyline.minCorner, Int.le_min]
      constructor <;> constructor
      all_goals
        simp only [ordinate, Bool.false_eq_true, ↓reduceIte, Polyline.dot]
        rw [hnormalY, hnormalX]
        simp only [Int.mul_add, Int.mul_sub, Int.neg_mul]
        omega
    | true =>
      apply Or.inr
      have hnormalY : (spine - t0) - (spine - t1) = span := by
        dsimp only [span]
        omega
      simp only [Polyline.maxCorner, Int.max_le]
      constructor <;> constructor
      all_goals
        simp only [ordinate, ↓reduceIte, Polyline.dot]
        rw [hnormalY, hnormalX]
        simp only [Int.mul_add, Int.mul_sub, Int.neg_mul]
        omega
  · trivial

/-- Same-rib envelope clearance over executed frames: the piece-level
disjunction is transported through `place`'s field preservation; every
piece shape is identified by birth frames, the cause box additionally by
the accounted geometry so the ENV residual transfers to the genealogy
bone, and the descendant pair closes through the order and gap
residuals. -/
theorem ishikawaSameRibEnvelopeClearance_frames (m : Model)
    (hord : ∀ (ns : List Tree.Node) (cause k : Nat),
      DescendantOrdInterval ns cause k)
    (hgap : ∀ (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
      (hrun : layout ns p = .ok raw)
      (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
      (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
      (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
      (_hplace : place ns p spine
        (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed),
      DescendantFrameGap ns p raw hrun ribs _hg cause k _hsource _hcause spine placed _hplace)
    (henv : ∀ (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
      (hrun : layout ns p = .ok raw)
      (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
      (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
      (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
      (_hplace : place ns p spine
        (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed),
      CauseEntryEnvBound ns p raw hrun ribs _hg cause k _hsource _hcause spine placed _hplace) :
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
  have hfields := frames_place_rib_fields_eq _ _ _ _ _ hplace
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
  obtain ⟨frames, hlen, hroot, hrecords, hpieces⟩ :=
    place_common_birth_frames _ _ _ _ _ hplace
  have hgtC (e' : Entry) (idx' : Nat)
      (he' : (e', idx') ∈ (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))).entries.zipIdx) :
      cause < e'.node :=
    frames_entry_node_gt_cause (Elegant.Kinds.Ishikawa.params m.profile)
      e.spine e.ribs _ rA cause k hplace hlink hcauseMem rfl e' idx' he'
  rcases hdisj with ⟨hRcause, hBc⟩ |
    ⟨eI, eJ, idxI, idxJ, posI, posJ, heIRA, heJRA, hiRI, hiBJ, hoddI,
      hposIRA, hposJRA, hltIdx, hgtPos⟩
  · -- (A) cause route against a non-cause box, through the accounted core.
    have hA := ishikawaCauseRouteEntryBoxClearanceAccounted e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
      cause k hsource hcauseMem e.spine rA hplace
    have hR := hpieces iR rectR pointsR hmemR
    have hBacc := place_piece_accounted_geometry e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.spine _ rA hplace
      iB rectB pointsB hmemB
    rcases hR with ⟨_nR, _hnR, _hiR, _hrectR, hptsR⟩ |
      ⟨eI', idxI', _nI', _bornI, heI', hiI', _hnI', _hbornI, _hrectR, _hptsR⟩
    · rcases hBacc with ⟨_nB, _hnB, hiB, _hrectB, _hptsB⟩ |
        ⟨eJ', idxJ', posJ', parJ', nJ', _doneJ, _restJ, heJ', hposJ', hnJ', hiJ',
          hgeneJ', _hprefixJ, _hdrawnJ, hrectG, _hptsG⟩
      · -- The box piece is cause-shaped: its index is the cause, excluded.
        have hiBc : iB = rA.cause := hiB.trans hfields.1.symm
        exact absurd hiBc hBc
      · have hBJ := hpieces iB rectB pointsB hmemB
        rcases hBJ with ⟨_nB', _hnB', hiB', _hrectB', _hptsB'⟩ |
          ⟨eJ'', idxJ'', nJ'', bornJ, heJ'', hiJ'', hnJ'', hbornJ, hrectF, _hptsF⟩
        · have hiBc : iB = rA.cause := hiB'.trans hfields.1.symm
          exact absurd hiBc hBc
        · -- Re-identify the accounted entry with the frame entry.
          have hnodeEq : eJ'.node = eJ''.node := hiJ'.symm.trans hiJ''
          have hidxEq : idxJ' = idxJ'' :=
            frames_entry_idx_eq_of_node_eq _ hndNodes eJ' eJ'' idxJ' idxJ''
              heJ' heJ'' hnodeEq
          have gJ' := List.mem_zipIdx_iff_getElem?.mp heJ'
          have gJ'' := List.mem_zipIdx_iff_getElem?.mp heJ''
          change _ = some eJ' at gJ'
          change _ = some eJ'' at gJ''
          rw [hidxEq] at gJ'
          have heqEJ : eJ' = eJ'' := Option.some.inj (gJ'.symm.trans gJ'')
          have heJr : (eJ', idxJ') ∈ (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
            (generatedRib e.input.nodes (cause, k))).entries.zipIdx := by
            rw [heqEJ, hidxEq]
            exact heJ''
          have hnJr : e.input.nodes[eJ'.node]? = some nJ'' := by
            rw [heqEJ]
            exact hnJ''
          have hnEq : nJ' = nJ'' := Option.some.inj (hnJ'.symm.trans hnJr)
          rw [← hnEq] at hrectF
          have hbornJ' : frames[idxJ' + 1]? = some bornJ := by
            rw [hidxEq]
            exact hbornJ
          let bJ' : Bone := depthBone (Elegant.Kinds.Ishikawa.params m.profile)
            parJ' eJ'.depth
            (Int.fdiv ((effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
              (generatedRib e.input.nodes (cause, k))).length * (posJ'.2 + 1 : Nat))
              ((effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
              (generatedRib e.input.nodes (cause, k))).entries.length + 1 : Nat))
            (children e.input.nodes eJ'.node).length
            (run (Elegant.Kinds.Ishikawa.params m.profile)
              (effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
              (generatedRib e.input.nodes (cause, k))).heights + 3)
          have hrectG' : rectB = ⟨bJ'.x1 - nJ'.width,
              ordinate e.spine (effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
              (generatedRib e.input.nodes (cause, k))).upper bJ'.t1 -
              Int.fdiv nJ'.height 2, nJ'.width, nJ'.height⟩ := hrectG
          have hxEq : bornJ.x1 = bJ'.x1 := by
            have h := congrArg Rect.x (hrectF.symm.trans hrectG')
            simp only at h
            omega
          have htEq : bornJ.t1 = bJ'.t1 := by
            have h := congrArg Rect.y (hrectF.symm.trans hrectG')
            simp only at h
            have hord : ordinate e.spine (effectivePlacedInput e.input.nodes
                (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
                (generatedRib e.input.nodes (cause, k))).upper bornJ.t1 =
                ordinate e.spine (effectivePlacedInput e.input.nodes
                (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
                (generatedRib e.input.nodes (cause, k))).upper bJ'.t1 := by omega
            simp only [ordinate] at hord
            split at hord <;> omega
          have hENVborn := henv e.input.nodes
            (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs
            e.hribs cause k hsource hcauseMem e.spine rA hplace
            frames eJ' idxJ' bornJ hlen hroot hrecords hbornJ' heJr
          have hENV' : bJ'.x1 ≤ envMasterX (effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
              (generatedRib e.input.nodes (cause, k)))
              (Elegant.Kinds.Ishikawa.params m.profile) bJ'.t1 -
              (run (Elegant.Kinds.Ishikawa.params m.profile)
              (effectivePlacedInput e.input.nodes
              (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
              (generatedRib e.input.nodes (cause, k))).heights + 1) := by
            rw [← hxEq, ← htEq]
            exact hENVborn
          rw [hptsR, hrectG']
          exact hA eJ' idxJ' posJ' parJ' nJ' heJ' hposJ' hnJ' hgeneJ' hENV'
    · -- An entry-shaped route with cause index is impossible: entry nodes
      -- are strict descendants of the cause.
      have hiRcause : iR = cause := hRcause.trans hrAcause
      have hnc : eI'.node = cause := hiI'.symm.trans hiRcause
      have hlt' := hgtC eI' idxI' heI'
      rw [hnc] at hlt'
      exact absurd hlt' (by omega)
  · -- (B) odd entry route against a strict-descendant box, through frames.
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
    have hRI := hpieces iR rectR pointsR hmemR
    have hBJ := hpieces iB rectB pointsB hmemB
    rcases hRI with ⟨_nR, _hnR, hiR, _hrectR, _hptsR⟩ |
      ⟨eI', idxI', _nI', bornI, heI'', hiRI', _hnI', hbornI, _hrectR, hptsR⟩
    · -- Cause-shaped route with entry index: impossible as above.
      have hiRcause : iR = cause := hiR.trans hrcause
      have hnc : eI.node = cause := hiRI.symm.trans hiRcause
      have hlt' := hgtC eI idxI heI_r
      rw [hnc] at hlt'
      exact absurd hlt' (by omega)
    · rcases hBJ with ⟨_nB, _hnB, hiB, _hrectB, _hptsB⟩ |
        ⟨eJ', idxJ', nJ', bornJ, heJ'', hiBJ', hnJ'', hbornJ, hrectB, _hptsB⟩
      · -- Cause-shaped box with entry index: impossible as above.
        have hiBcause : iB = cause := hiB.trans hrcause
        have hnc : eJ.node = cause := hiBJ.symm.trans hiBcause
        have hlt' := hgtC eJ idxJ heJ_r
        rw [hnc] at hlt'
        exact absurd hlt' (by omega)
      · -- Both pieces are entry-shaped: re-identify them and apply the
        -- order and gap residuals over the executed frames.
        have hnodeEqI : eI'.node = eI.node := hiRI'.symm.trans hiRI
        have hidxEqI : idxI' = idxI :=
          frames_entry_idx_eq_of_node_eq _ hndNodes eI' eI idxI' idxI
            heI'' heI_r hnodeEqI
        have hnodeEqJ : eJ'.node = eJ.node := hiBJ'.symm.trans hiBJ
        have hidxEqJ : idxJ' = idxJ :=
          frames_entry_idx_eq_of_node_eq _ hndNodes eJ' eJ idxJ' idxJ
            heJ'' heJ_r hnodeEqJ
        have gI' := List.mem_zipIdx_iff_getElem?.mp heI''
        have gI := List.mem_zipIdx_iff_getElem?.mp heI_r
        change _ = some eI' at gI'
        change _ = some eI at gI
        rw [hidxEqI] at gI'
        have heqEI : eI' = eI := Option.some.inj (gI'.symm.trans gI)
        have gJ' := List.mem_zipIdx_iff_getElem?.mp heJ''
        have gJ := List.mem_zipIdx_iff_getElem?.mp heJ_r
        change _ = some eJ' at gJ'
        change _ = some eJ at gJ
        rw [hidxEqJ] at gJ'
        have heqEJ : eJ' = eJ := Option.some.inj (gJ'.symm.trans gJ)
        have hbornI' : frames[idxI + 1]? = some bornI := by
          rw [← hidxEqI]
          exact hbornI
        have hbornJ' : frames[idxJ + 1]? = some bornJ := by
          rw [← hidxEqJ]
          exact hbornJ
        have hnJ : e.input.nodes[eJ.node]? = some nJ' := by
          rw [← heqEJ]
          exact hnJ''
        have heI' : (eI, idxI) ∈
            (generatedRib e.input.nodes (cause, k)).entries.zipIdx := heI_r
        have heJ' : (eJ, idxJ) ∈
            (generatedRib e.input.nodes (cause, k)).entries.zipIdx := heJ_r
        have hposI' : (generatedRib e.input.nodes (cause, k)).order.zipIdx.find?
            (fun v => v.1 == idxI) = some posI := hposI_r
        have hposJ' : (generatedRib e.input.nodes (cause, k)).order.zipIdx.find?
            (fun v => v.1 == idxJ) = some posJ := hposJ_r
        have hanc : IndexedAncestor
            (generatedRib e.input.nodes (cause, k)).entries idxI idxJ :=
          hord e.input.nodes cause k eI eJ idxI idxJ posI posJ
            heI' heJ' hposI' hposJ' hoddI hltIdx hgtPos
        have hgapI := hgap e.input.nodes
          (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs
          e.hribs cause k hsource hcauseMem e.spine rA hplace
          eI eJ idxI idxJ frames bornI bornJ
          heI' heJ' hanc hoddI hlen hroot hrecords hbornI' hbornJ'
        obtain ⟨hltT, hle, hfall, hgapBound⟩ := hgapI
        have hne : e.input.nodes ≠ [] := by
          intro heq
          simp [heq, children] at hcauseMem
        have hparameters := successful_slope_parameters e.input.nodes
          (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout
        have hcos : 0 ≤ (Elegant.Kinds.Ishikawa.params m.profile).cos :=
          hparameters.1
        have hsin : 0 < (Elegant.Kinds.Ishikawa.params m.profile).sin := by
          have h1 := hparameters.2
          omega
        have hheight : 0 ≤ (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
            (generatedRib e.input.nodes (cause, k))).heights := by
          change 0 ≤ (generatedRib e.input.nodes (cause, k)).heights
          rw [(generated_rib_fields e.input.nodes cause k).2.2.2]
          exact entry_height_fold_initial _ _ 0
        have hdims := successful_node_dimensions e.input.nodes
          (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout nJ'
          (List.mem_of_getElem? hnJ)
        have hw : 0 ≤ nJ'.width := by omega
        have hh : 0 ≤ nJ'.height := by omega
        have hnjheight : nJ'.height ≤ (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
            (generatedRib e.input.nodes (cause, k))).heights :=
          measured_entry_height_bound e.input.nodes
            (generatedRib e.input.nodes (cause, k)).entries eJ
            (List.fst_mem_of_mem_zipIdx heJ') nJ' hnJ
        have hspan0 : 0 ≤ bornI.t1 - bornI.t0 := by omega
        have hrunSpan : 0 ≤ run (Elegant.Kinds.Ishikawa.params m.profile)
            (bornI.t1 - bornI.t0) :=
          Int.fdiv_nonneg (Int.mul_nonneg hspan0 hcos) (by omega)
        have hfallEq : bornI.x0 - bornI.x1 =
            run (Elegant.Kinds.Ishikawa.params m.profile) (bornI.t1 - bornI.t0) := by
          omega
        have hscale := frames_desc_scaled_cross_bound
          (Elegant.Kinds.Ishikawa.params m.profile)
          (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
            (generatedRib e.input.nodes (cause, k))).heights
          (bornI.t1 - bornI.t0) hheight hspan0 hsin
        rw [Int.mul_comm (effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).heights
          (run (Elegant.Kinds.Ishikawa.params m.profile) (bornI.t1 - bornI.t0))] at hscale
        have hstep1 : run (Elegant.Kinds.Ishikawa.params m.profile)
            (bornI.t1 - bornI.t0) * nJ'.height ≤
            run (Elegant.Kinds.Ishikawa.params m.profile)
            (bornI.t1 - bornI.t0) *
            (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
            (generatedRib e.input.nodes (cause, k))).heights :=
          Int.mul_le_mul_of_nonneg_left hnjheight hrunSpan
        have hstep2 : (bornI.t1 - bornI.t0) *
            (run (Elegant.Kinds.Ishikawa.params m.profile)
            (effectivePlacedInput e.input.nodes
            (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
            (generatedRib e.input.nodes (cause, k))).heights + 1) ≤
            (bornI.t1 - bornI.t0) *
            (bornI.x0 + Int.fdiv ((bornI.x1 - bornI.x0) * (bornJ.t1 - bornI.t0))
              (bornI.t1 - bornI.t0) - bornJ.x1) :=
          Int.mul_le_mul_of_nonneg_left hgapBound hspan0
        have hcoverage : (bornI.x0 - bornI.x1) * nJ'.height ≤
            (bornI.t1 - bornI.t0) *
            (bornI.x0 + Int.fdiv ((bornI.x1 - bornI.x0) * (bornJ.t1 - bornI.t0))
              (bornI.t1 - bornI.t0) - bornJ.x1) := by
          rw [hfallEq]
          omega
        have hmiss := frames_desc_diag_miss bornI.x0 bornI.x1 bornI.t0 bornI.t1
          bornJ.t1 nJ'.width nJ'.height
          (bornI.x0 + Int.fdiv ((bornI.x1 - bornI.x0) * (bornJ.t1 - bornI.t0))
            (bornI.t1 - bornI.t0) - bornJ.x1)
          e.spine (effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
          (generatedRib e.input.nodes (cause, k))).upper
          hltT hle hw hh hcoverage
        have hpos : (bornI.x0 + Int.fdiv ((bornI.x1 - bornI.x0) *
            (bornJ.t1 - bornI.t0)) (bornI.t1 - bornI.t0)) -
            (bornI.x0 + Int.fdiv ((bornI.x1 - bornI.x0) * (bornJ.t1 - bornI.t0))
              (bornI.t1 - bornI.t0) - bornJ.x1) = bornJ.x1 := by
          omega
        rw [hpos] at hmiss
        rw [hptsR, hrectB]
        exact hmiss

/-- Same-rib piece clearance from the frames-based envelope clearance. -/
theorem ishikawaSameRibPieceClearance_frames (m : Model)
    (hord : ∀ (ns : List Tree.Node) (cause k : Nat),
      DescendantOrdInterval ns cause k)
    (hgap : ∀ (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
      (hrun : layout ns p = .ok raw)
      (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
      (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
      (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
      (_hplace : place ns p spine
        (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed),
      DescendantFrameGap ns p raw hrun ribs _hg cause k _hsource _hcause spine placed _hplace)
    (henv : ∀ (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
      (hrun : layout ns p = .ok raw)
      (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
      (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
      (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
      (_hplace : place ns p spine
        (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed),
      CauseEntryEnvBound ns p raw hrun ribs _hg cause k _hsource _hcause spine placed _hplace) :
    IshikawaSameRibPieceClearance m :=
  ishikawaSameRibPieceClearance m
    (ishikawaSameRibEnvelopeClearance_frames m hord hgap henv)

end Elegant.Kinds.IshikawaFinal
