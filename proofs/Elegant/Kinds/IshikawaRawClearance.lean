import Elegant.Kinds.IshikawaFinal
import Elegant.IshikawaHardBBranch5Facts
import Elegant.IshikawaClearanceHardBFinal
import Elegant.IshikawaLayoutProvenanceFacts
import Elegant.IshikawaAssemblyBoxFacts
import Elegant.IshikawaEnvFramesFacts

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-! ### HARD B per-rib assembly with the block premise discharged

`ishikawa_hard_b_real` (in `Elegant.Ishikawa`) takes the branch-5 block
classification `hblock` as an unconditional `∀`-premise. That premise is only
*applied* inside the deeper-earlier branch of `hard_b_route_case_split`, where
`child.parent ≠ jIdx` and `j.parent ≠ child.parent` both hold; for the excluded
parent and sibling pairs the block statement is false in general (a sibling
pair under a root parent has block head `H = parent`, so `headPos = parentPos`
and neither disjunct can hold). The theorem below replays the same final
assembly and discharges the classification on the spot through
`hard_b_branch5_placement_block'`, which is exactly its scope
(`hpar : child.parent ≠ jIdx`, `hsib : j.parent ≠ child.parent`). The sibling
branch is discharged by the landed `hard_b_sibling_real` and the ENV side
condition by `ishikawa_env_frames`; the only remaining named obligation is
`HardBDeeperEarlierReal`, carried as `hdeep`. -/

/-- HARD B final assembly over `HardBDeeperEarlierReal` alone: identical
statement to `ishikawa_hard_b_real` except that the unconditional `hblock`
premise is removed and the block classification is proved in place by
`hard_b_branch5_placement_block'` inside the deeper-earlier branch (the only
place `ishikawa_hard_b_real` uses it). -/
theorem ishikawa_hard_b_real'
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (hdeep : ∀ (henv : IshikawaEnvFrames ns p
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k)))),
      HardBDeeperEarlierReal ns p raw hrun ribs hg cause k hsource hcause
        spine placed hplace henv)
    (child j : Entry) (childIdx jIdx : Nat)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hj : (j, jIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : child.depth % 2 ≠ 0)
    (hjlt : jIdx < childIdx)
    (nj : Tree.Node) (hnj : ns[j.node]? = some nj) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))
    ∃ (frames : List Bone) (childBorn jBorn : Bone),
      frames.length = r.entries.length + 1 ∧
      frames[childIdx + 1]? = some childBorn ∧ frames[jIdx + 1]? = some jBorn ∧
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩ ∧
      ∀ (i : Nat) (rect : Rect) (points : List Point), (i, rect, points) ∈ placed.pieces →
        (∃ causeNode : Tree.Node, ns[r.cause]? = some causeNode ∧ i = r.cause ∧
          rect = ⟨-run p r.length - Int.fdiv causeNode.width 2,
            if r.upper then ordinate spine r.upper r.length - causeNode.height
            else ordinate spine r.upper r.length, causeNode.width, causeNode.height⟩ ∧
          points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
        ∃ (e : Entry) (idx : Nat) (node : Tree.Node) (born : Bone),
          (e, idx) ∈ r.entries.zipIdx ∧ i = e.node ∧ ns[e.node]? = some node ∧
          frames[idx + 1]? = some born ∧
          rect = ⟨born.x1 - node.width, ordinate spine r.upper born.t1 - Int.fdiv node.height 2,
            node.width, node.height⟩ ∧
          points = [⟨born.x0, ordinate spine r.upper born.t0⟩,
            ⟨born.x1, ordinate spine r.upper born.t1⟩] := by
  let source := generatedRib ns (cause, k)
  let r := effectivePlacedInput ns (measuredSideLength p ribs) source
  have henv : IshikawaEnvFrames ns p r :=
    ishikawa_env_frames ns p raw hrun ribs hg cause k hcause hsource spine placed hplace
  have hsibProof : HardBSiblingReal ns p raw hrun ribs hg cause k hsource hcause
      spine placed hplace :=
    hard_b_sibling_real ns p raw hrun ribs hg cause k hsource hcause spine placed hplace
  by_cases hparcase : child.parent = (jIdx : Int)
  · obtain ⟨frames2, childBorn2, parentBorn2, n2, hlen2, hcb2, hjb2, hn2, hmiss2,
      hpieces2⟩ :=
      place_generated_odd_entry_route_misses_parent_box ns p raw hrun ribs hg
        cause k hsource hcause spine placed hplace child j childIdx jIdx hchild hj
        hodd hparcase
    have hnEq : n2 = nj := Option.some.inj (hn2.symm.trans hnj)
    rw [hnEq] at hmiss2
    exact ⟨frames2, childBorn2, parentBorn2, hlen2, hcb2, hjb2, hmiss2, hpieces2⟩
  obtain ⟨frames, hlen, _hroot, hrecords, hpieces⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  obtain ⟨childDone, childRest, hchildPrefix, _⟩ := List.eq_append_cons_of_mem hchild
  change r.entries.zipIdx = childDone ++ (child, childIdx) :: childRest at hchildPrefix
  obtain ⟨childPos, parI, childBorn, hchildPos, hparLookup, hchildBorn, hchildEq⟩ :=
    hrecords childDone child childIdx childRest hchildPrefix
  obtain ⟨jDone, jRest, hjPrefix, _⟩ := List.eq_append_cons_of_mem hj
  change r.entries.zipIdx = jDone ++ (j, jIdx) :: jRest at hjPrefix
  obtain ⟨jPos, _parJ, jBorn, hjPos, _hjparLookup, hjBorn, hjEq⟩ :=
    hrecords jDone j jIdx jRest hjPrefix
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hnonempty : source.entries.isEmpty = false := by
    cases hentries : source.entries with
    | nil =>
      change (child, childIdx) ∈ source.entries.zipIdx at hchild
      rw [hentries] at hchild
      simp at hchild
    | cons first rest => rfl
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hnonempty
  have hrootFalse : child.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink hcause child childIdx hchild heq
    exact hodd (by omega)
  have hlb := generated_entry_parent_lower_bound ns cause k child childIdx hchild
  have hparIdx : child.parent = ((child.parent).toNat : Int) := by omega
  have howner : (child.parent + 1).toNat = (child.parent).toNat + 1 := by
    rw [hparIdx]
    omega
  rw [howner] at hparLookup hchildEq
  obtain ⟨hpb, _⟩ := List.getElem?_eq_some_iff.mp hparLookup
  rw [hlen] at hpb
  have hparentBound : (child.parent).toNat < r.entries.length := by omega
  let parentEntry := (generatedRib ns (cause, k)).entries[(child.parent).toNat]'hparentBound
  have hparentLookup : (generatedRib ns (cause, k)).entries[(child.parent).toNat]? = some parentEntry :=
    List.getElem?_eq_getElem hparentBound
  have hparentMem : (parentEntry, (child.parent).toNat) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hparentLookup
  have hpar : child.parent = ((child.parent).toNat : Int) := hparIdx
  have hdepth := generated_parent_child_depth ns cause k hlink hcause parentEntry child
    (child.parent).toNat childIdx hparentMem hchild hpar
  have hparentEven : parentEntry.depth % 2 = 0 :=
    parent_depth_even parentEntry.depth child.depth hdepth hodd
  obtain ⟨parentDone, parentRest, hparentPrefix, _⟩ := List.eq_append_cons_of_mem hparentMem
  change r.entries.zipIdx = parentDone ++ (parentEntry, (child.parent).toNat) :: parentRest
    at hparentPrefix
  obtain ⟨parentPos, grandpar, parentBorn, hparentPos, _hgpLookup, hparentBornLookup,
    hparentEquation⟩ :=
    hrecords parentDone parentEntry (child.parent).toNat parentRest hparentPrefix
  have hsame : parI = parentBorn :=
    Option.some.inj (hparLookup.symm.trans hparentBornLookup)
  rw [hsame] at hchildEq
  have hchildT0 : childBorn.t0 = parentBorn.t0 := by
    rw [hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns child.node).length (run p r.heights + 3) hodd).1
  have hchildT1 : childBorn.t1 =
      Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns child.node).length (run p r.heights + 3) hodd).2.1
  have hparentT0 : parentBorn.t0 =
      Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hparentEquation]
    exact (depthBone_even_endpoints p
      { grandpar with drawn := processedOddDraws parentDone (parentEntry.parent + 1).toNat }
      parentEntry.depth (Int.fdiv (r.length * (parentPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns parentEntry.node).length
      (run p r.heights + 3) hparentEven).1
  have hposLt : parentPos.2 < childPos.2 :=
    (generated_parent_child_order ns cause k parentEntry child (child.parent).toNat
      childIdx hparentMem hchild hpar parentPos childPos hparentPos hchildPos).1
      hparentEven
  have hslotGap := ordinal_slots_gap r.length (r.entries.length + 1 : Nat) r.heights
    (parentPos.2 + 1 : Nat) (childPos.2 + 1 : Nat) (by omega) hheight hbudget (by omega)
  have hspan : childBorn.t0 ≤ childBorn.t1 := by
    rw [hchildT0, hparentT0, hchildT1]
    omega
  have cfg : HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
      childBorn jBorn :=
    ⟨hchild, hj, hodd, hjlt, hnj, hlen, hchildBorn, hjBorn, hspan⟩
  have hreal : HardBRealFrames ns p spine r placed hplace frames :=
    ⟨frames, ⟨hlen, _hroot, hrecords⟩, fun _i _b h => h⟩
  refine ⟨frames, childBorn, jBorn, hlen, hchildBorn, hjBorn, ?_, hpieces⟩
  refine hard_b_route_case_split r child j childIdx jIdx jBorn childBorn nj spine
    ?_ ?_ ?_ ?_ ?_
  · intro hc
    exact absurd hc hparcase
  · intro hs
    exact hsibProof child j childIdx jIdx nj frames childBorn jBorn cfg hreal hs
  · intro he
    exact HardBEarlierSlot ns p raw hrun ribs hg cause k hsource hcause spine
      placed hplace child j childIdx jIdx nj frames childBorn jBorn cfg he
  · intro hl
    exact HardBLaterSlot ns p raw hrun ribs hg cause k hsource hcause spine
      placed hplace child j childIdx jIdx nj frames childBorn jBorn cfg hl
  · intro hc hs he hl
    -- The block classification is proved here, in the only branch that uses
    -- it: `hard_b_branch5_placement_block'` needs exactly `hc` and `hs`.
    have hB := hard_b_branch5_placement_block' ns cause k hlink hcause
      child j childIdx jIdx hchild hj hodd hjlt hc hs
    rcases hB with _hfirst | ⟨hIdx, H, _hH, _hHroot, hHor, hord⟩
    · exact (hdeep henv) child j childIdx jIdx nj frames childBorn jBorn cfg hreal
        (hard_b_branch5_placement_block' ns cause k hlink hcause
          child j childIdx jIdx hchild hj hodd hjlt hc hs) hc hs he hl
    · rcases hHor with ⟨_hHJ, hIdxJ⟩ | _hchain
      · have hjPos' : (generatedRib ns (cause, k)).order.zipIdx.find?
            (fun v => v.1 == hIdx) = some jPos := by
          rw [hIdxJ]
          exact hjPos
        have hdisj := hord jPos parentPos hjPos' hparentPos
        rcases hdisj with hle | hltpos
        · omega
        · have hjT1 : jBorn.t1
              = Int.fdiv (r.length * (jPos.2 + 1 : Nat))
                (r.entries.length + 1 : Nat) := by
            rw [hjEq]
            exact depthBone_endpoint_slot _ _ _ _ _ _
          have hslot : jBorn.t1 + r.heights ≤ childBorn.t0 :=
            hard_b_slot_mono_of_pos_lt r jBorn childBorn parentBorn jPos parentPos
              hjT1 hparentT0 hchildT0 hheight hbudget hltpos
          exact absurd hslot he
      · exact (hdeep henv) child j childIdx jIdx nj frames childBorn jBorn cfg hreal
          (hard_b_branch5_placement_block' ns cause k hlink hcause
            child j childIdx jIdx hchild hj hodd hjlt hc hs) hc hs he hl

/-! ### Named residuals for the raw assembly

The raw pairwise clearance `IshikawaRawForeignRouteClearance` is assembled from
`layout_origin` (rib generation and the `assemblePairs` run), the box/route
origin theorems (`assemblePairs_box_origin`, `assemblePairs_piece_route_origin`),
the per-rib clearance chain, and three named residuals that remain open:

* `IshikawaSameRibPieceClearance`: inside one successfully placed rib, the
  shifted route of every piece misses the shifted box of every other piece.
  Its future proof runs the per-rib chain on the source rib recovered by
  `mapM_index_record` — `ishikawa_hard_b_real'` for odd routes against earlier
  entries (discharging the deeper-earlier branch with the `_hd` hypothesis),
  `place_entry_route_misses_entry_box_even`,
  `place_entry_route_misses_entry_box_odd_later`,
  `place_entry_route_misses_cause_box`,
  `placed_empty_entries_routes_miss_right_box`,
  `placed_pieces_spine_clearance` — then transports the entry-level misses to
  piece triples (piece-index to entry-index correspondence, including the
  odd-route vs later-entry-index position split) and across the rib's attach
  shift by `hitsRect_translate`.
* `IshikawaCrossRibPieceClearance`: the shifted route of a piece of one rib
  misses the shifted box of a piece of a different rib (cross-rib separation
  of the `assemblePairs` attach frontier).
* `IshikawaBoundaryPieceClearance`: the assembly-owned spine route
  (`[⟨a, spine⟩, ⟨0, spine⟩]`) against every non-head raw box, and every
  shifted rib-piece route against the head box.
-/

/-- The executed-layout context shared by every residual: the decoded input,
the successful tree layout, the generated rib list with its measured lengths
and spine, the successful per-rib placements, and the successful
`assemblePairs` run producing `raw`. -/
structure IshikawaRawExecution (m : Model) where
  input : Elegant.Kinds.Ishikawa.Input
  raw : Tree.Layout
  ribs : List Rib
  length : Bool → Int
  spine : Int
  placed : List Rib
  head : Tree.Node
  hdecode : Elegant.Kinds.Ishikawa.decode m = .ok input
  hlayout : Elegant.Ishikawa.layout input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw
  hribs : ribs = (children input.nodes 0).zipIdx.map
    (generatedRib input.nodes)
  hlength : length = measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) ribs
  hspine : spine = max (length true) (Elegant.Kinds.Ishikawa.params m.profile).spineBase
  hplaced : ribs.mapM (fun r => place input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) spine
    (effectivePlacedInput input.nodes length r)) = .ok placed
  hhead : input.nodes[0]? = some head
  hassemble : assemblePairs spine placed
    (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
    ⟨(List.replicate input.nodes.length (⟨0, 0, 0, 0⟩ : Rect)).set 0
      ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩,
      List.replicate input.nodes.length []⟩ = .ok raw

/-- Per-rib deeper-earlier obligation over every executed rib of the decoded
input: `HardBDeeperEarlierReal` instantiated at the rib's own successful
`place` run and ENV frames. This is the hypothesis `ishikawa_hard_b_real'`
consumes; it is the only remaining named obligation of the HARD B assembly. -/
def IshikawaDeeperEarlierRaw (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (cause k : Nat)
    (hsource : generatedRib e.input.nodes (cause, k) ∈ e.ribs)
    (hcause : cause ∈ children e.input.nodes 0) (ribPlaced : Rib)
    (hplace : place e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile) e.spine
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k))) = .ok ribPlaced)
    (henv : IshikawaEnvFrames e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
        (generatedRib e.input.nodes (cause, k)))),
    HardBDeeperEarlierReal e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.raw e.hlayout e.ribs e.hribs cause k hsource hcause e.spine ribPlaced
      hplace henv

/-- Residual (same rib): for the executed `assemblePairs` run, inside one
placed rib the shifted route of every piece misses the shifted box of every
other piece. The `_hd` hypothesis is the deeper-earlier obligation the future
proof consumes through `ishikawa_hard_b_real'`. -/
def IshikawaSameRibPieceClearance (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (_hd : IshikawaDeeperEarlierRaw m)
    (rA : Rib) (dxA dxB : Int),
    AssemblyPairShift e.placed (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
      rA dxA →
    AssemblyPairShift e.placed (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
      rA dxB →
    ∀ (pieceR pieceB : Nat × Rect × List Point),
      pieceR ∈ rA.pieces → pieceB ∈ rA.pieces →
      pieceR.1 ≠ pieceB.1 →
      ¬ Polyline.hitsRect
        (pieceR.2.2.map (fun q => ({ x := q.x + dxA, y := q.y } : Point)))
        { pieceB.2.1 with x := pieceB.2.1.x + dxB }

/-- Residual (cross rib): for the executed `assemblePairs` run, the shifted
route of a piece of one rib misses the shifted box of a piece of a different
rib. -/
def IshikawaCrossRibPieceClearance (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (rA rB : Rib) (dxA dxB : Int)
    (pieceA pieceB : Nat × Rect × List Point),
    AssemblyPairShift e.placed (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
      rA dxA →
    AssemblyPairShift e.placed (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
      rB dxB →
    rA ≠ rB → pieceA ∈ rA.pieces → pieceB ∈ rB.pieces →
    pieceA.1 ≠ pieceB.1 →
    ¬ Polyline.hitsRect
      (pieceA.2.2.map (fun q => ({ x := q.x + dxA, y := q.y } : Point)))
      { pieceB.2.1 with x := pieceB.2.1.x + dxB }

/-- Residual (boundary): the assembly-owned spine route against every non-head
raw box, and every shifted rib-piece route against the head box. -/
def IshikawaBoundaryPieceClearance (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m),
    (∀ (a : Int) (boxIndex : Nat) (rect : Rect), boxIndex ≠ 0 →
      e.raw.boxes[boxIndex]? = some rect →
      ¬ Polyline.hitsRect [⟨a, e.spine⟩, ⟨0, e.spine⟩] rect) ∧
    (∀ (rA : Rib) (dxA : Int) (pieceR : Nat × Rect × List Point),
      AssemblyPairShift e.placed (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
        rA dxA →
      pieceR ∈ rA.pieces →
      ¬ Polyline.hitsRect
        (pieceR.2.2.map (fun q => ({ x := q.x + dxA, y := q.y } : Point)))
        ⟨0, e.spine - Int.fdiv e.head.height 2, e.head.width, e.head.height⟩)

/-- A successful `getElem?` on a replicate list returns the replicated value. -/
private theorem ishikawa_replicate_getElem? {α : Type} (n : Nat) (a : α) :
    ∀ (k : Nat) (x : α), (List.replicate n a)[k]? = some x → x = a := by
  induction n with
  | zero => intro k x h; simp at h
  | succ n ih =>
    intro k x h
    cases k with
    | zero =>
      have h2 : some x = some a := by
        calc some x = (List.replicate (n + 1) a)[0]? := h.symm
        _ = some a := rfl
      exact Option.some_inj.mp h2
    | succ k => exact ih k x h

/-- Reading index `0` of a `set 0` list returns the written value. -/
private theorem ishikawa_set_getElem_zero {α : Type} (l : List α) (hb bx : α)
    (h : (l.set 0 hb)[0]? = some bx) : bx = hb := by
  cases l with
  | nil =>
    have h2 : (none : Option α) = some bx := h
    simp at h2
  | cons a rest =>
    have h2 : some bx = some hb := by
      calc some bx = ((a :: rest).set 0 hb)[0]? := h.symm
      _ = some hb := rfl
    exact Option.some_inj.mp h2

/-- Reading a nonzero index of a `set 0` list reads through to the original. -/
private theorem ishikawa_set_getElem_succ {α : Type} (l : List α) (hb : α)
    (k : Nat) (bx : α) (h : (l.set 0 hb)[k + 1]? = some bx) :
    l[k + 1]? = some bx := by
  cases l with
  | nil => exact h
  | cons a rest => exact h

/-- The empty route hits no box. -/
private theorem ishikawa_hitsRect_empty (rect : Rect) :
    ¬ Polyline.hitsRect [] rect := by
  intro hhit
  obtain ⟨_, _, hmiss⟩ := hhit
  exact hmiss (by trivial)

/-- No route hits the zero rectangle at the origin. -/
private theorem ishikawa_hitsRect_zero (pts : List Point) :
    ¬ Polyline.hitsRect pts ⟨0, 0, 0, 0⟩ := by
  intro hhit
  obtain ⟨hrw, _, _⟩ := hhit
  exact absurd hrw (by decide)

/-- Raw route/box clearance from the per-rib theorems: every raw route misses
every raw box with a distinct index. The per-rib odd-depth clearance enters
through `ishikawa_hard_b_real'` (whose block premise is discharged in place);
the even, cause-box, empty-entry and spine cases, the cross-rib separation and
the piece-index correspondence each stay a named residual. -/
theorem ishikawaRawForeignRouteClearance (m : Model)
    (_hwf : WellFormed m) (_hlimits : WithinLimits m)
    (hdeep : IshikawaDeeperEarlierRaw m)
    (hsame : IshikawaSameRibPieceClearance m)
    (hcross : IshikawaCrossRibPieceClearance m)
    (hbound : IshikawaBoundaryPieceClearance m) :
    IshikawaRawForeignRouteClearance m := by
  intro input raw hdecode hlayout targetIndex boxIndex pts rect hroute hbox hne
  rcases layout_origin input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) raw hlayout with
    ⟨hnil, hraw⟩ | ⟨ribs, length, spine, placed, head,
      hribs, hlength, hspine, hplaced, hhead, hassemble⟩
  · rw [hraw] at hroute
    simp at hroute
  · have hr := assemblePairs_piece_route_origin _ _ _ _ _ _ hassemble
      targetIndex pts hroute
    rcases hr with ⟨rfl, a, rfl⟩ | hinR | ⟨rA, originalA, dxA, hshiftA,
      ⟨rectA, hpieceA⟩, hpts⟩
    · exact (hbound ⟨input, raw, ribs, length, spine, placed, head,
        hdecode, hlayout, hribs, hlength, hspine, hplaced, hhead,
        hassemble⟩).1 a boxIndex rect (Ne.symm hne) hbox
    · have hnil : pts = [] := ishikawa_replicate_getElem? _ _ _ _ hinR
      rw [hnil]
      exact ishikawa_hitsRect_empty rect
    · have hb := assemblePairs_box_origin _ _ _ _ _ _ hassemble
        boxIndex rect hbox
      rcases hb with hBinit | ⟨rB, originalB, pointsB, dxB, hshiftB,
        hpieceB, hrectB⟩
      · by_cases hz : boxIndex = 0
        · subst hz
          have hrect0 : rect =
              ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩ :=
            ishikawa_set_getElem_zero _ _ _ hBinit
          rw [hpts, hrect0]
          exact (hbound ⟨input, raw, ribs, length, spine, placed, head,
            hdecode, hlayout, hribs, hlength, hspine, hplaced, hhead,
            hassemble⟩).2 rA dxA (targetIndex, rectA, originalA)
            hshiftA hpieceA
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
          have hrep := ishikawa_set_getElem_succ _ _ _ _ hBinit
          have hrz : rect = ⟨0, 0, 0, 0⟩ :=
            ishikawa_replicate_getElem? _ _ _ _ hrep
          rw [hpts, hrz]
          exact ishikawa_hitsRect_zero _
      · by_cases heq : rA = rB
        · subst heq
          rw [hpts, hrectB]
          exact hsame ⟨input, raw, ribs, length, spine, placed, head,
            hdecode, hlayout, hribs, hlength, hspine, hplaced, hhead,
            hassemble⟩ hdeep rA dxA dxB hshiftA hshiftB
            (targetIndex, rectA, originalA) (boxIndex, originalB, pointsB)
            hpieceA hpieceB hne
        · rw [hpts, hrectB]
          exact hcross ⟨input, raw, ribs, length, spine, placed, head,
            hdecode, hlayout, hribs, hlength, hspine, hplaced, hhead,
            hassemble⟩ rA rB dxA dxB
            (targetIndex, rectA, originalA) (boxIndex, originalB, pointsB)
            hshiftA hshiftB heq hpieceA hpieceB hne

/-- Public Ishikawa validity from the raw clearance assembly: the per-rib
deeper-earlier obligation and the three piece-level residuals feed
`ishikawa_valid_of_raw_clearance`. -/
theorem ishikawa_valid_of_deeper (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result)
    (hdeep : IshikawaDeeperEarlierRaw m)
    (hsame : IshikawaSameRibPieceClearance m)
    (hcross : IshikawaCrossRibPieceClearance m)
    (hbound : IshikawaBoundaryPieceClearance m) :
    HardConstraints result.scene.layoutDump :=
  ishikawa_valid_of_raw_clearance m result hwf hlimits h
    (ishikawaRawForeignRouteClearance m hwf hlimits hdeep hsame hcross hbound)

end Elegant.Kinds.IshikawaFinal
