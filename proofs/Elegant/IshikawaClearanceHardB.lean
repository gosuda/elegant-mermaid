import Elegant.IshikawaClearanceHard

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-- Master diagonal of the cause route: x-coordinate at parameter `t`. -/
def masterX (r : Rib) (p : Params) (t : Int) : Int :=
  Int.fdiv ((-run p r.length) * t) r.length

/-- The ENV invariant (remaining-gap item 1): every entry-born bone's left end
`x1` stays at least `run p r.heights + 1` left of the master diagonal at its
own `t1`. Stated as a named `Prop` so the sibling lane can discharge it for
generated ribs; this file only consumes it as an explicit hypothesis. -/
def EntryBoneXEnvelope (ns : List Tree.Node) (p : Params) (r : Rib) : Prop :=
  ∀ (idx : Nat) (b : Bone), 0 < idx →
    IndexedBoneGenealogy ns p r idx b →
    b.x1 ≤ masterX r p b.t1 - (run p r.heights + 1)

section IshikawaC6RibHardBHelpers

private theorem fdiv_mono_num {A B s : Int} (hs : 0 < s) (hAB : A ≤ B) :
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

/-- `run` is monotone in its rise for nonnegative cos/sin parameters. -/
theorem run_mono (p : Params) (hcos : 0 ≤ p.cos) {a b : Int}
    (_ha : 0 ≤ a) (hab : a ≤ b) (hsin : 0 < p.sin) : run p a ≤ run p b := by
  unfold run
  apply fdiv_mono_num hsin
  exact Int.mul_le_mul_of_nonneg_right hab hcos

/-- Lower bound on the attachment reservation: with a parent-span reserve of
`(c+1) * m` and `d ≤ c` drawn shares, the interpolated remainder still leaves
the child attachment at least `m - 1` left of the parent bone end. -/
private theorem reservation_lower (x0 x1 d c m : Int) (hden : 0 < c + 1) (hm : 0 ≤ m)
    (hres : (c + 1) * m ≤ x0 - x1) (hdc : d ≤ c) :
    m - 1 ≤ (x0 - x1) + Int.fdiv ((x1 - x0) * d) (c + 1) := by
  have hS0 : 0 ≤ x0 - x1 := Int.le_trans (Int.mul_nonneg (Int.le_of_lt hden) hm) hres
  have hone : (1 : Int) ≤ c + 1 - d := by omega
  have hkey := Int.mul_le_mul_of_nonneg_left hone hS0
  have hkey' : x0 - x1 ≤ (x0 - x1) * (c + 1 - d) := by
    simpa only [Int.mul_one] using hkey
  have hexpand : (x0 - x1) * (c + 1 - d) = (x0 - x1) * (c + 1) - (x0 - x1) * d := by
    rw [Int.mul_sub]
  have hnegF : (x1 - x0) * d = -((x0 - x1) * d) := by
    rw [show x1 - x0 = -(x0 - x1) from by omega, Int.neg_mul]
  have hq := Int.mul_fdiv_add_fmod ((x1 - x0) * d) (c + 1)
  have hr1 : Int.fmod ((x1 - x0) * d) (c + 1) < c + 1 := Int.fmod_lt_of_pos _ hden
  apply Int.le_of_mul_le_mul_left _ hden
  have hpm : (c + 1) * (m - 1) = (c + 1) * m - (c + 1) := by
    rw [Int.mul_sub, Int.mul_one]
  have hprod : (c + 1) * ((x0 - x1) + Int.fdiv ((x1 - x0) * d) (c + 1)) =
      (x0 - x1) * (c + 1) + (c + 1) * Int.fdiv ((x1 - x0) * d) (c + 1) := by
    rw [Int.mul_add, Int.mul_comm]
  rw [hpm, hprod]
  omega

/-- HARD B, parent-box case: an odd-depth entry route misses the box of its
own parent entry. The route's start ordinate coincides with the parent box
centre ordinate; clearance comes from the attachment x-gap
(`attachment_start_margin` plus a nonempty child list) transported through
`interpolated_box_diagonal_miss`. -/
theorem place_generated_odd_entry_route_misses_parent_box
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed)
    (child parent : Entry) (childIdx parentIdx : Nat)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hparent : (parent, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : child.depth % 2 ≠ 0)
    (hpar : child.parent = (parentIdx : Int)) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    ∃ (frames : List Bone) (childBorn parentBorn : Bone) (n : Tree.Node),
      frames.length = r.entries.length + 1 ∧
      frames[childIdx + 1]? = some childBorn ∧ frames[parentIdx + 1]? = some parentBorn ∧
      ns[parent.node]? = some n ∧
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
          ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨parentBorn.x1 - n.width, ordinate spine r.upper parentBorn.t1 - Int.fdiv n.height 2,
          n.width, n.height⟩ ∧
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
  let margin := run p r.heights + 3
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hdepth := generated_parent_child_depth ns cause k hlink hcause
    parent child parentIdx childIdx hparent hchild hpar
  have hparentEven : parent.depth % 2 = 0 := parent_depth_even _ _ hdepth hodd
  obtain ⟨frames, hframesLength, _, hrecords, hpieces⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  obtain ⟨childDone, childRest, hchildPrefix, _⟩ := List.eq_append_cons_of_mem hchild
  change r.entries.zipIdx = childDone ++ (child, childIdx) :: childRest at hchildPrefix
  obtain ⟨childPos, parentFrame, childBorn, hchildPos, hparentFrame, hchildBorn,
    hchildEquation⟩ := hrecords childDone child childIdx childRest hchildPrefix
  have howner : (child.parent + 1).toNat = parentIdx + 1 := by rw [hpar]; omega
  rw [howner] at hparentFrame hchildEquation
  obtain ⟨parentDone, parentRest, hparentPrefix, _⟩ := List.eq_append_cons_of_mem hparent
  change r.entries.zipIdx = parentDone ++ (parent, parentIdx) :: parentRest at hparentPrefix
  obtain ⟨parentPos, grandParent, parentBorn, hparentPos, hgrandParent,
    hparentBornLookup, hparentEquation⟩ :=
    hrecords parentDone parent parentIdx parentRest hparentPrefix
  have hsameParent : parentFrame = parentBorn := by
    have h := hparentFrame.symm.trans hparentBornLookup
    exact Option.some.inj h
  rw [hsameParent] at hchildEquation
  have hchildT0 : childBorn.t0 = parentBorn.t0 := by
    rw [hchildEquation]
    exact (depthBone_odd_endpoints p { parentBorn with drawn := processedOddDraws childDone (parentIdx + 1) } child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).1
  have hchildT1 : childBorn.t1 =
      Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hchildEquation]
    exact (depthBone_odd_endpoints p { parentBorn with drawn := processedOddDraws childDone (parentIdx + 1) } child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.1
  have hparentT0 : parentBorn.t0 =
      Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hparentEquation]
    exact (depthBone_even_endpoints p { grandParent with drawn := processedOddDraws parentDone (parent.parent + 1).toNat } parent.depth
      (Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) (children ns parent.node).length
      (run p r.heights + 3) hparentEven).1
  have hchildX0 : childBorn.x0 = parentBorn.x0 +
      Int.fdiv ((parentBorn.x1 - parentBorn.x0) *
        (parentBorn.count - processedOddDraws childDone (parentIdx + 1)))
        (parentBorn.count + 1) := by
    rw [hchildEquation]
    exact (depthBone_odd_endpoints p { parentBorn with drawn := processedOddDraws childDone (parentIdx + 1) } child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.2.1
  have hchildX1 : childBorn.x1 =
      childBorn.x0 - run p (childBorn.t1 - childBorn.t0) := by
    rw [hchildEquation]
    have h := (depthBone_odd_endpoints p { parentBorn with drawn := processedOddDraws childDone (parentIdx + 1) } child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.2.2
    have ht0 := (depthBone_odd_endpoints p { parentBorn with drawn := processedOddDraws childDone (parentIdx + 1) } child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).1
    have ht1 := (depthBone_odd_endpoints p { parentBorn with drawn := processedOddDraws childDone (parentIdx + 1) } child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.1
    rw [h]
    simp only [ht1, ht0]
  have hchildFall : childBorn.x0 - childBorn.x1 =
      run p (childBorn.t1 - childBorn.t0) := by
    have := hchildX1
    omega
  have hparentX : parentBorn.x1 = parentBorn.x0 -
      boneLength p (children ns parent.node).length margin := by
    rw [hparentEquation]
    exact (depthBone_even_endpoints p _ parent.depth _ _ _ hparentEven).2.2
  have hparentCount : parentBorn.count = (children ns parent.node).length := by
    rw [hparentEquation]
    unfold depthBone
    split <;> rfl
  have hparentFall : parentBorn.x0 - parentBorn.x1 =
      boneLength p (children ns parent.node).length margin := by
    have := hparentX
    omega
  have hchildMem : child.node ∈ children ns parent.node :=
    generated_parent_child_membership ns cause k parent child parentIdx childIdx
      hparent hchild hpar
  have hparentNodeLt : parent.node < ns.length := by
    by_cases hproot : parent.parent = -1
    · have hmem := generated_root_child_membership ns cause k parent parentIdx hparent hproot
      exact List.mem_range.mp (List.mem_filter.mp hmem).1
    · have hlb := generated_entry_parent_lower_bound ns cause k parent parentIdx hparent
      obtain ⟨gpIdx, hgpIdx⟩ := nonroot_parent_index parent.parent hlb hproot
      have hidx : (parent.parent + 1).toNat = gpIdx + 1 := by rw [hgpIdx]; omega
      rw [hidx] at hgrandParent
      have hgpBound : gpIdx < r.entries.length := by
        have hb := (List.getElem?_eq_some_iff.mp hgrandParent).1
        rw [hframesLength] at hb
        omega
      let grandEntry := r.entries[gpIdx]'hgpBound
      have hgrandLookup : r.entries[gpIdx]? = some grandEntry :=
        List.getElem?_eq_getElem hgpBound
      have hgrandMem : (grandEntry, gpIdx) ∈ r.entries.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hgrandLookup
      have hmem := generated_parent_child_membership ns cause k grandEntry parent gpIdx parentIdx
        hgrandMem hparent hgpIdx
      exact List.mem_range.mp (List.mem_filter.mp hmem).1
  let n := ns[parent.node]'hparentNodeLt
  have hn : ns[parent.node]? = some n := List.getElem?_eq_getElem hparentNodeLt
  have hn_mem : n ∈ ns := List.getElem_mem hparentNodeLt
  have hdims := successful_node_dimensions ns p raw hrun n hn_mem
  have hnh : 1 ≤ n.height := hdims.2
  have hmeasured := measured_entry_height_bound ns source.entries parent
    (List.fst_mem_of_mem_zipIdx hparent) n hn
  have hnheight : n.height ≤ r.heights := by
    change n.height ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact hmeasured
  have hne : ns ≠ [] := by
    intro hnil
    rw [hnil] at hparentNodeLt
    exact Nat.not_lt_zero _ hparentNodeLt
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hcos : 0 ≤ p.cos := hparameters.1
  have hsin : 0 < p.sin := Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) hparameters.2
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hrunHeight : 0 ≤ run p r.heights :=
    Int.fdiv_nonneg (Int.mul_nonneg hheight hcos) (Int.le_of_lt hsin)
  have hmargin : 0 ≤ margin := Int.add_nonneg hrunHeight (by decide : (0 : Int) ≤ 3)
  have hneEntries : source.entries.isEmpty = false := by
    cases hentries : source.entries with
    | nil =>
      change (child, childIdx) ∈ source.entries.zipIdx at hchild
      rw [hentries] at hchild
      simp at hchild
    | cons first rest => rfl
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hneEntries
  have hpositive : 0 < r.heights := by omega
  have hposLt : parentPos.2 < childPos.2 :=
    (generated_parent_child_order ns cause k parent child parentIdx childIdx
      hparent hchild hpar parentPos childPos hparentPos hchildPos).1 hparentEven
  have hslotGap : parentBorn.t0 + r.heights ≤ childBorn.t1 := by
    rw [hparentT0, hchildT1]
    have hgap := ordinal_slots_gap r.length (r.entries.length + 1 : Nat) r.heights
      (parentPos.2 + 1 : Nat) (childPos.2 + 1 : Nat) (by omega) hheight hbudget (by omega)
    exact hgap
  have hslotLt : childBorn.t0 < childBorn.t1 := by
    have hgap' : parentBorn.t0 + r.heights ≤ childBorn.t1 := hslotGap
    rw [hparentT0, hchildT1] at hgap'
    have hchildT0' : childBorn.t0 = (r.length * (parentPos.2 + 1 : Nat)).fdiv (r.entries.length + 1 : Nat) := by
      rw [hchildT0, hparentT0]
    rw [hchildT0']
    omega
  have hspan0 : 0 ≤ childBorn.t1 - childBorn.t0 := by omega
  have hfall_nonneg : 0 ≤ run p (childBorn.t1 - childBorn.t0) := by
    unfold run
    apply Int.fdiv_nonneg _ (Int.le_of_lt hsin)
    exact Int.mul_nonneg hspan0 hcos
  have hx : childBorn.x1 ≤ childBorn.x0 := by
    have := hchildX1
    omega
  have hw : 0 ≤ n.width := by have := hdims.1; omega
  have hh : 0 ≤ n.height := by
    have := hdims.2
    omega
  have hcountPos : 1 ≤ parentBorn.count := by
    rw [hparentCount]
    cases hcl : children ns parent.node with
    | nil => simp [hcl] at hchildMem
    | cons head tail => simp; omega
  have hreserve : (parentBorn.count + 1) * margin ≤ parentBorn.x0 - parentBorn.x1 := by
    rw [hparentFall, hparentCount]
    exact Int.le_max_right _ _
  have hdrawn0 : 0 ≤ processedOddDraws childDone (parentIdx + 1) := by
    simp [processedOddDraws]
  have hreservation : margin - 1 ≤ (parentBorn.x0 - parentBorn.x1) + Int.fdiv
      ((parentBorn.x1 - parentBorn.x0) *
        (parentBorn.count - processedOddDraws childDone (parentIdx + 1)))
      (parentBorn.count + 1) :=
    reservation_lower parentBorn.x0 parentBorn.x1
      (parentBorn.count - processedOddDraws childDone (parentIdx + 1))
      parentBorn.count margin (by omega) hmargin hreserve (by omega)
  have hresForm : childBorn.x0 - parentBorn.x1 =
      (parentBorn.x0 - parentBorn.x1) + Int.fdiv
        ((parentBorn.x1 - parentBorn.x0) *
          (parentBorn.count - processedOddDraws childDone (parentIdx + 1)))
        (parentBorn.count + 1) := by
    rw [hchildX0]
    omega
  have hmarginSub : margin - 1 = run p r.heights + 2 := by
    show run p r.heights + 3 - 1 = run p r.heights + 2
    omega
  have hresBound : run p r.heights + 2 ≤ childBorn.x0 - parentBorn.x1 := by
    rw [hresForm, ← hmarginSub]
    exact hreservation
  have hrunH : run p n.height ≤ run p r.heights :=
    run_mono p hcos (by omega) hnheight hsin
  have hcoverage : (childBorn.x0 - childBorn.x1) * n.height ≤
      (childBorn.t1 - childBorn.t0) * (childBorn.x0 - parentBorn.x1) := by
    rw [hchildFall, Int.mul_comm (run p (childBorn.t1 - childBorn.t0)) n.height]
    have hscaled := run_scaled_cross_bound p n.height (childBorn.t1 - childBorn.t0)
      hh hspan0 hsin
    apply Int.le_trans hscaled
    apply Int.mul_le_mul_of_nonneg_left _ hspan0
    omega
  have hmiss := interpolated_box_diagonal_miss childBorn.x0 childBorn.x1
    childBorn.t0 childBorn.t1 parentBorn.t1 n.width n.height
    (childBorn.x0 - parentBorn.x1) spine r.upper hslotLt hx hw hh hcoverage
  have hparentT1 : parentBorn.t1 = parentBorn.t0 := by
    have h := (depthBone_even_endpoints p
      { grandParent with drawn := processedOddDraws parentDone (parent.parent + 1).toNat }
      parent.depth (Int.fdiv (r.length * (parentPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns parent.node).length
      (run p r.heights + 3) hparentEven).2.1
    rw [← hparentEquation] at h
    rw [h, hparentT0]
  have hboxEq : (⟨childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
        (parentBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) -
        (childBorn.x0 - parentBorn.x1) - n.width,
      ordinate spine r.upper parentBorn.t1 - Int.fdiv n.height 2,
      n.width, n.height⟩ : Rect) =
      ⟨parentBorn.x1 - n.width, ordinate spine r.upper parentBorn.t1 - Int.fdiv n.height 2,
        n.width, n.height⟩ := by
    have hxc : childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
        (parentBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) -
        (childBorn.x0 - parentBorn.x1) - n.width = parentBorn.x1 - n.width := by
      rw [show parentBorn.t1 - childBorn.t0 = 0 from by omega, Int.mul_zero]
      rw [show Int.fdiv 0 (childBorn.t1 - childBorn.t0) = 0 from by simp]
      omega
    rw [hxc]
  refine ⟨frames, childBorn, parentBorn, n, hframesLength, hchildBorn,
    hparentBornLookup, hn, ?_, hpieces⟩
  simpa only [hboxEq] using hmiss

end IshikawaC6RibHardBHelpers
end Elegant.Ishikawa
