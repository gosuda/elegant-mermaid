import Elegant.IshikawaSeparationFacts
import Elegant.Kinds.GitgraphFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

def generatedRib (ns : List Tree.Node) (source : Nat × Nat) : Rib :=
  let (entries, order) := flatten ns (upper source.2) 64
    (children ns source.1) (-1) 2 [] []
  { cause := source.1, upper := upper source.2, entries, order,
    heights := entries.foldl (fun h e =>
      max h (((ns[e.node]?).map (·.height)).getD 0)) 0 }

def measuredSideLength (p : Params) (ribs : List Rib) (up : Bool) : Int :=
  let total (side : Bool) : Int :=
    ((ribs.filter (fun r => r.upper == side)).map
      (fun r => (r.entries.length : Int))).sum
  let all := total true + total false
  let initial := if all > 0 then
    max p.ribMin (Int.fdiv (p.ribPool * total up) all) else p.spineBase
  (ribs.filter (fun r => r.upper == up)).foldl (fun l r =>
    if r.entries.isEmpty then l else max l
      (max ((r.entries.length : Int) * p.spacing)
        ((r.entries.length + 1 : Nat) * r.heights))) initial

def effectivePlacedInput (ns : List Tree.Node) (length : Bool → Int)
    (r : Rib) : Rib :=
  { r with length := if (children ns r.cause).isEmpty then
      Int.fdiv (length r.upper) 5 else length r.upper }

private theorem provenance_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem generation_loop_origin (ns : List Tree.Node) (ribs : List Rib)
    (h : ForIn.forIn (children ns 0).zipIdx ([] : List Rib)
      (fun source rs => pure (ForInStep.yield (rs ++ [generatedRib ns source]))) =
        (Except.ok ribs : Except LayoutError (List Rib))) :
    ribs = (children ns 0).zipIdx.map (generatedRib ns) := by
  have result := Elegant.forIn_processed [] _ _ _ _
    (fun done state => state = done.map (generatedRib ns)) rfl
    (by
      intro done a rest state next _ hi hs
      simp only [pure, Except.pure, Except.ok.injEq] at hs
      subst next
      refine ⟨state ++ [generatedRib ns a], rfl, ?_⟩
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        congrArg (fun rs => rs ++ [generatedRib ns a]) hi) h
  simpa using result

def LayoutOrigin (ns : List Tree.Node) (p : Params) (raw : Tree.Layout) : Prop :=
  ∃ (ribs : List Rib) (length : Bool → Int) (spine : Int)
      (placed : List Rib) (head : Tree.Node),
    ribs = (children ns 0).zipIdx.map (generatedRib ns) ∧
    length = measuredSideLength p ribs ∧
    spine = max (length true) p.spineBase ∧
    ribs.mapM (fun r => place ns p spine (effectivePlacedInput ns length r)) =
      .ok placed ∧
    ns[0]? = some head ∧
    assemblePairs spine placed (-p.inset) 0
      ⟨(List.replicate ns.length (⟨0, 0, 0, 0⟩ : Rect)).set 0
        ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩,
        List.replicate ns.length []⟩ = .ok raw

theorem layout_origin (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw) :
    (ns = [] ∧ raw = ⟨[], []⟩) ∨ LayoutOrigin ns p raw := by
  cases ns with
  | nil =>
    left
    refine ⟨rfl, ?_⟩
    simpa only [layout, List.isEmpty_nil, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] using hrun.symm
  | cons first rest =>
    right
    unfold layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    split at hrun
    · simp only [bind, Except.bind] at hrun
      cases hrun
    · split at hrun
      · simp only [bind, Except.bind] at hrun
        cases hrun
      · obtain ⟨ribs, hgenerated, htail⟩ := provenance_bind_ok hrun
        have hg : ribs = (children (first :: rest) 0).zipIdx.map
            (generatedRib (first :: rest)) := by
          apply generation_loop_origin
          exact hgenerated
        obtain ⟨placed, hplaced, hfinal⟩ := provenance_bind_ok htail
        refine ⟨ribs, measuredSideLength p ribs,
          max (measuredSideLength p ribs true) p.spineBase, placed, first,
          hg, rfl, rfl, ?_, rfl, ?_⟩
        · simpa only [effectivePlacedInput, measuredSideLength] using hplaced
        · simpa only [List.getElem?_cons_zero, measuredSideLength] using hfinal

theorem generated_rib_source (ns : List Tree.Node) (ribs : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (r : Rib) (hr : r ∈ ribs) :
    ∃ cause k, (cause, k) ∈ (children ns 0).zipIdx ∧
      r = generatedRib ns (cause, k) := by
  rw [hg] at hr
  obtain ⟨⟨cause, k⟩, hm, he⟩ := List.mem_map.mp hr
  exact ⟨cause, k, hm, he.symm⟩

theorem generated_rib_fields (ns : List Tree.Node) (cause k : Nat) :
    let r := generatedRib ns (cause, k)
    r.cause = cause ∧ r.upper = upper k ∧
    (r.entries, r.order) =
      flatten ns (upper k) 64 (children ns cause) (-1) 2 [] [] ∧
    r.heights = r.entries.foldl (fun h e =>
      max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := by
  cases hf : flatten ns (upper k) 64 (children ns cause) (-1) 2 [] [] with
  | mk entries order => simp [generatedRib, hf]

theorem generated_nonempty_children (ns : List Tree.Node) (cause k : Nat)
    (hne : (generatedRib ns (cause, k)).entries.isEmpty = false) :
    (children ns cause).isEmpty = false := by
  cases hc : children ns cause with
  | nil =>
    have hf : flatten ns (upper k) 64 [] (-1) 2 [] [] = ([], []) := by
      cases upper k <;> rfl
    have he : (generatedRib ns (cause, k)).entries = [] := by
      simp only [generatedRib, hc, hf]
    rw [he] at hne
    cases hne
  | cons child rest => rfl

theorem generated_reservation_budget (ns : List Tree.Node) (p : Params)
    (ribs : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (r : Rib) (hr : r ∈ ribs) (hne : r.entries.isEmpty = false) :
    (r.entries.length + 1 : Nat) * r.heights ≤
      (effectivePlacedInput ns (measuredSideLength p ribs) r).length := by
  obtain ⟨cause, k, _, hsource⟩ := generated_rib_source ns ribs hg r hr
  have hchildren : (children ns r.cause).isEmpty = false := by
    subst r
    exact generated_nonempty_children ns cause k hne
  have hmember : r ∈ ribs.filter (fun q => q.upper == r.upper) := by
    simp only [List.mem_filter, beq_self_eq_true, and_true]
    exact hr
  have hb := measured_rib_length_bound
    (ribs.filter (fun q => q.upper == r.upper)) p.spacing
    (if (((ribs.filter (fun q => q.upper == true)).map
          (fun q => (q.entries.length : Int))).sum +
        ((ribs.filter (fun q => q.upper == false)).map
          (fun q => (q.entries.length : Int))).sum) > 0 then
      max p.ribMin (Int.fdiv (p.ribPool *
        ((ribs.filter (fun q => q.upper == r.upper)).map
          (fun q => (q.entries.length : Int))).sum)
        (((ribs.filter (fun q => q.upper == true)).map
            (fun q => (q.entries.length : Int))).sum +
          ((ribs.filter (fun q => q.upper == false)).map
            (fun q => (q.entries.length : Int))).sum)) else p.spineBase)
    r hmember hne
  simpa only [effectivePlacedInput, hchildren, Bool.false_eq_true, ↓reduceIte,
    measuredSideLength] using hb

theorem placed_rib_source (ns : List Tree.Node) (p : Params)
    (ribs placed : List Rib) (length : Bool → Int) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun r =>
      place ns p spine (effectivePlacedInput ns length r)) = .ok placed)
    (r : Rib) (hr : r ∈ placed) :
    ∃ (source : Rib) (cause k : Nat),
      source ∈ ribs ∧ (cause, k) ∈ (children ns 0).zipIdx ∧
      source = generatedRib ns (cause, k) ∧
      place ns p spine (effectivePlacedInput ns length source) = .ok r := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨source, hsource, hplace⟩ :=
    (Elegant.Kinds.Gitgraph.mapM_index_record _ _ _ hplaces).2 j r hj
  have hm := List.mem_of_getElem? hsource
  obtain ⟨cause, k, hindex, heq⟩ := generated_rib_source ns ribs hg source hm
  exact ⟨source, cause, k, hm, hindex, heq, hplace⟩

theorem generated_leaf_entries (ns : List Tree.Node) (cause k : Nat)
    (hchildren : (children ns cause).isEmpty = true) :
    (generatedRib ns (cause, k)).entries = [] := by
  have hc : children ns cause = [] := List.isEmpty_iff.mp hchildren
  have hf : flatten ns (upper k) 64 [] (-1) 2 [] [] = ([], []) := by
    cases upper k <;> rfl
  simp only [generatedRib, hc, hf]

theorem generated_nonempty_effective_length_nonnegative
    (ns : List Tree.Node) (p : Params) (ribs : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (r : Rib) (hr : r ∈ ribs) (hne : r.entries.isEmpty = false) :
    0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs) r).length := by
  have hb := generated_reservation_budget ns p ribs hg r hr hne
  obtain ⟨cause, k, _, heq⟩ := generated_rib_source ns ribs hg r hr
  have hh : 0 ≤ r.heights := by
    rw [heq]
    exact entry_height_fold_initial ns _ 0
  exact Int.le_trans (Int.mul_nonneg (by omega) hh) hb

theorem measured_side_length_nonnegative (p : Params) (ribs : List Rib)
    (hmin : 0 ≤ p.ribMin) (hbase : 0 ≤ p.spineBase) (up : Bool) :
    0 ≤ measuredSideLength p ribs up := by
  unfold measuredSideLength
  dsimp only
  split
  · exact Int.le_trans (Int.le_trans hmin (Int.le_max_left _ _))
      (rib_length_fold_initial _ _ _)
  · exact Int.le_trans hbase (rib_length_fold_initial _ _ _)

theorem effective_length_nonnegative (ns : List Tree.Node) (p : Params)
    (ribs : List Rib) (r : Rib)
    (hmin : 0 ≤ p.ribMin) (hbase : 0 ≤ p.spineBase) :
    0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs) r).length := by
  have hs := measured_side_length_nonnegative p ribs hmin hbase r.upper
  simp only [effectivePlacedInput]
  split
  · exact Int.fdiv_nonneg hs (by decide)
  · exact hs

theorem successful_nonempty_length_parameters (ns : List Tree.Node)
    (p : Params) (raw : Tree.Layout) (hne : ns ≠ [])
    (hrun : layout ns p = .ok raw) :
    5 ≤ p.ribMin ∧ 5 ≤ p.spineBase := by
  cases ns with
  | nil => exact False.elim (hne rfl)
  | cons head rest =>
    unfold layout at hrun
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

theorem successful_nonempty_effective_length_nonnegative
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hne : ns ≠ []) (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (r : Rib) :
    0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs) r).length := by
  obtain ⟨hmin, hbase⟩ := successful_nonempty_length_parameters ns p raw hne hrun
  exact effective_length_nonnegative ns p ribs r (by omega) (by omega)

end Elegant.Ishikawa
