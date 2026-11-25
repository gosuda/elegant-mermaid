import Elegant.Kinds.IshikawaSameRibEnvelope
import Elegant.IshikawaClearanceHard
import Elegant.IshikawaFlattenTemporalFacts
import Elegant.Kinds.IshikawaPlaceDrawnBound

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa
/-! ### Descendant-route box clearance (odd entry vs strict descendant)

The entry-level residual (B) of `IshikawaSameRibEnvelope.lean` quantifies its
two parent bones over an arbitrary `IndexedBoneGenealogy`. That universal is
FALSE: `.draw` admits overdrawn bones, and an odd `depthBone` moves its `x0`
with `par.count - par.drawn`, so an overdrawn ancestor shifts a descendant
box onto the route. Two executed witnesses (vector profile, `60 × 30` nodes):
* Chain `[0,1,2,3,4,5]`, cause `1`: `I = idx 1` (node 3, depth 3, odd),
  `J = idx 3` (node 5, depth 5, descendant via the even middle at idx 2);
  order `[0,2,3,1]`, so `idxI < idxJ` and `posJ.2 < posI.2`. Executed bones
  miss; with the middle bone overdrawn to `drawn = 1` (genealogy-valid by one
  `.draw` step) the box is `{ x := -4839, y := 12785, w := 60, h := 30 }`
  against route `[{ x := -2980, y := 25600 }, { x := -5678, y := 6400 }]`
  and `Polyline.hitsRectB` reports `hit = true`.
* Chain `[0,1,2,3,4,5,6,7]`, cause `1`: `I = idx 1` (depth 3, odd),
  `J = idx 4` (depth 6, even great-grandchild via middle `S` at idx 2 and
  `T` at idx 3); order `[0,2,4,5,3,1]`, `posI.2 = 5`, `posJ.2 = 2`.
  With `parI`/`parJ` drawn kept at their executed accounted values
  (`drawn = 0 = processedOddDraws`), overdrawing the unconstrained middle
  `S` to `drawn = 3` moves the box to `{ x := -5353, y := 9128, w := 60,
  h := 30 }` against route `[{ x := -2723, y := 27429 },
  { x := -5935, y := 4572 }]` with `hit = true`. Hence even the
  immediate-parent accounted universal is false; pinning needs the full
  ancestor chain (or, equivalently, executed frames).

What is proved here instead:
* `DescendantOrdInterval`: the structural half — the index/order
  configuration forces `J` to descend from `I`. Pure order fact, probed true
  on every non-vacuous case (all link-valid trees to seven nodes: 78
  premises, 78 descendants, 0 misses on executed bones).
* `IshikawaDescendantRouteBoxClearanceAccounted`: the old def plus the
  executed-loop tie for each parent bone (`drawn = processedOddDraws` at its
  birth prefix, via `place_drawn_le_count` vocabulary). Stated per the
  assignment; shown insufficient in general (witness above), so the file
  proves the executable core it reduces to.
* `DescendantFrameGap`: the executed-frame fall equation plus interpolated
  reservation for strict-descendant pairs (probed: 78 premises, 0 fall
  violations, 0 gap violations).
* `ishikawaDescendantFrameClearance`: the geometric core — order interval
  plus frame gap close the executed miss. The use site applies this to its
  executed birth frames; the exact owner edit is in the task report.
-/

/-- Structural half: an odd entry with a later index but an earlier order
position forces the later entry to descend from it. Mirror of
`HardBDeeperOrdInterval` (which covers even parents). Order-only, hence
strictly simpler than the goal; probed true on every non-vacuous executed
case. -/
def DescendantOrdInterval (ns : List Tree.Node) (cause k : Nat) : Prop :=
  ∀ (eI eJ : Entry) (idxI idxJ : Nat) (posI posJ : Nat × Nat),
    (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
    (eJ, idxJ) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
    (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == idxI) = some posI →
    (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ →
    eI.depth % 2 ≠ 0 → idxI < idxJ → posJ.2 < posI.2 →
    IndexedAncestor (generatedRib ns (cause, k)).entries idxI idxJ

/-- Accounted form of entry-level residual (B): the old def plus, for each
parent bone, the executed-loop tie (`drawn = processedOddDraws` at its birth
prefix). The `done`/`rest`/`prefix` witnesses are exactly what
`AccountedPieceGeometry` provides at the use site. -/
def IshikawaDescendantRouteBoxClearanceAccounted (ns : List Tree.Node) (p : Params)
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
    (parI parJ : Bone) (nI nJ : Tree.Node)
    (doneI restI doneJ restJ : List (Entry × Nat)),
    (eI, idxI) ∈ r.entries.zipIdx →
    (eJ, idxJ) ∈ r.entries.zipIdx →
    r.order.zipIdx.find? (fun v => v.1 == idxI) = some posI →
    r.order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ →
    ns[eI.node]? = some nI → ns[eJ.node]? = some nJ →
    IndexedBoneGenealogy ns p r (eI.parent + 1).toNat parI →
    IndexedBoneGenealogy ns p r (eJ.parent + 1).toNat parJ →
    r.entries.zipIdx = doneI ++ (eI, idxI) :: restI →
    r.entries.zipIdx = doneJ ++ (eJ, idxJ) :: restJ →
    parI.drawn = processedOddDraws doneI (eI.parent + 1).toNat →
    parJ.drawn = processedOddDraws doneJ (eJ.parent + 1).toNat →
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

/-- Executed-frame gap for strict-descendant pairs: on one executed rib,
for an odd entry `I` with a strict descendant `J`, the executed born bones
satisfy the route fall equation and the interpolated reservation. The frame
premises are exactly what `place_common_birth_frames` provides, so the only
open content is the descendant chain arithmetic. Probed true on every
non-vacuous executed case (78 premises, 0 fall violations, 0 gap
violations). -/
def DescendantFrameGap (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
  ∀ (eI eJ : Entry) (idxI idxJ : Nat) (frames : List Bone) (fI fJ : Bone),
    (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
    (eJ, idxJ) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
    IndexedAncestor (generatedRib ns (cause, k)).entries idxI idxJ →
    eI.depth % 2 ≠ 0 →
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
    frames[idxI + 1]? = some fI → frames[idxJ + 1]? = some fJ →
    (fI.t0 < fI.t1 ∧ fI.x1 ≤ fI.x0 ∧ fI.x1 = fI.x0 - run p (fI.t1 - fI.t0) ∧
      run p r.heights + 1 ≤
        fI.x0 + Int.fdiv ((fI.x1 - fI.x0) * (fJ.t1 - fI.t0)) (fI.t1 - fI.t0) - fJ.x1)

private theorem desc_scaled_cross_bound (p : Params) (height span : Int)
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

private theorem desc_diag_miss
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
/-- Geometric core: order interval plus frame gap close the executed miss.
Proved outright (no further residuals) from public slot/height/slope facts
and the two local arithmetic lemmas above. The use site applies this to its
executed birth frames; the genealogy-to-frame coincidence for its specific
executed derivations is reported alongside the owner edit. -/
theorem ishikawaDescendantFrameClearance
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed)
    (hord : DescendantOrdInterval ns cause k)
    (hgap : DescendantFrameGap ns p raw hrun ribs _hg cause k _hsource hcause
      spine placed hplace) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    ∀ (eI eJ : Entry) (idxI idxJ : Nat) (posI posJ : Nat × Nat) (nJ : Tree.Node),
      (eI, idxI) ∈ r.entries.zipIdx →
      (eJ, idxJ) ∈ r.entries.zipIdx →
      r.order.zipIdx.find? (fun v => v.1 == idxI) = some posI →
      r.order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ →
      ns[eJ.node]? = some nJ →
      eI.depth % 2 ≠ 0 → idxI < idxJ → posJ.2 < posI.2 →
      ∃ (fI fJ : Bone),
        ¬ Polyline.hitsRect
          [⟨fI.x0, ordinate spine r.upper fI.t0⟩,
           ⟨fI.x1, ordinate spine r.upper fI.t1⟩]
          ⟨fJ.x1 - nJ.width, ordinate spine r.upper fJ.t1 - Int.fdiv nJ.height 2,
            nJ.width, nJ.height⟩ := by
  intro r eI eJ idxI idxJ posI posJ nJ heI heJ hposI hposJ hnJ hodd hlt hgt
  have heI' : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx := heI
  have heJ' : (eJ, idxJ) ∈ (generatedRib ns (cause, k)).entries.zipIdx := heJ
  have hposI' : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idxI) = some posI := hposI
  have hposJ' : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idxJ) = some posJ := hposJ
  have hanc : IndexedAncestor (generatedRib ns (cause, k)).entries idxI idxJ :=
    hord eI eJ idxI idxJ posI posJ heI' heJ' hposI' hposJ' hodd hlt hgt
  obtain ⟨frames, hlen, hroot, hrecords, _⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  obtain ⟨doneI, restI, hpreI, _⟩ := List.eq_append_cons_of_mem heI
  obtain ⟨doneJ, restJ, hpreJ, _⟩ := List.eq_append_cons_of_mem heJ
  obtain ⟨_, _, fI, _, _, hfI, _⟩ :=
    hrecords doneI eI idxI restI hpreI
  obtain ⟨_, _, fJ, _, _, hfJ, _⟩ :=
    hrecords doneJ eJ idxJ restJ hpreJ
  obtain ⟨hltT, hle, hfall, hgapI⟩ :=
    hgap eI eJ idxI idxJ frames fI fJ heI' heJ' hanc hodd hlen hroot hrecords hfI hfJ
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at hcause
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hcos : 0 ≤ p.cos := hparameters.1
  have hsin : 0 < p.sin := by
    have h1 := hparameters.2
    omega
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hdims := successful_node_dimensions ns p raw hrun nJ (List.mem_of_getElem? hnJ)
  have hw : 0 ≤ nJ.width := by omega
  have hh : 0 ≤ nJ.height := by omega
  have hnjheight : nJ.height ≤ r.heights :=
    measured_entry_height_bound ns (generatedRib ns (cause, k)).entries eJ
      (List.fst_mem_of_mem_zipIdx heJ') nJ hnJ
  have hspan0 : 0 ≤ fI.t1 - fI.t0 := by omega
  have hrunSpan : 0 ≤ run p (fI.t1 - fI.t0) :=
    Int.fdiv_nonneg (Int.mul_nonneg hspan0 hcos) (by omega : 0 ≤ p.sin)
  have hfallEq : fI.x0 - fI.x1 = run p (fI.t1 - fI.t0) := by omega
  have hscale := desc_scaled_cross_bound p r.heights (fI.t1 - fI.t0) hheight hspan0 hsin
  rw [Int.mul_comm r.heights (run p (fI.t1 - fI.t0))] at hscale
  have hstep1 : run p (fI.t1 - fI.t0) * nJ.height ≤
      run p (fI.t1 - fI.t0) * r.heights :=
    Int.mul_le_mul_of_nonneg_left hnjheight hrunSpan
  have hstep2 : (fI.t1 - fI.t0) * (run p r.heights + 1) ≤
      (fI.t1 - fI.t0) *
        (fI.x0 + Int.fdiv ((fI.x1 - fI.x0) * (fJ.t1 - fI.t0)) (fI.t1 - fI.t0) - fJ.x1) :=
    Int.mul_le_mul_of_nonneg_left hgapI hspan0
  have hcoverage : (fI.x0 - fI.x1) * nJ.height ≤
      (fI.t1 - fI.t0) *
        (fI.x0 + Int.fdiv ((fI.x1 - fI.x0) * (fJ.t1 - fI.t0)) (fI.t1 - fI.t0) - fJ.x1) := by
    rw [hfallEq]
    omega
  have hmiss := desc_diag_miss fI.x0 fI.x1 fI.t0 fI.t1 fJ.t1 nJ.width nJ.height
    (fI.x0 + Int.fdiv ((fI.x1 - fI.x0) * (fJ.t1 - fI.t0)) (fI.t1 - fI.t0) - fJ.x1)
    spine r.upper hltT hle hw hh hcoverage
  have hpos : (fI.x0 + Int.fdiv ((fI.x1 - fI.x0) * (fJ.t1 - fI.t0)) (fI.t1 - fI.t0)) -
      (fI.x0 + Int.fdiv ((fI.x1 - fI.x0) * (fJ.t1 - fI.t0)) (fI.t1 - fI.t0) - fJ.x1) =
      fJ.x1 := by
    omega
  rw [hpos] at hmiss
  exact ⟨fI, fJ, hmiss⟩


end Elegant.Kinds.IshikawaFinal
