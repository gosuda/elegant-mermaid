import Elegant.Layered.RegionNotesContractedRootFacts
import Elegant.Layered.RegionFoundation

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl.ContractedC8a

open RegionImpl

private theorem bind_congr {α β : Type} {a b : Except LayoutError α}
    {f g : α → Except LayoutError β} (hab : a = b) (hfg : ∀ x, f x = g x) :
    a >>= f = b >>= g := by
  cases hab
  exact congrArg (fun k => a >>= k) (funext hfg)

private theorem findIdx_missing (boxes : List ModelBox) (s : String)
    (hs : s ∉ boxes.map (·.id)) : boxes.findIdx? (fun b => b.id == s) = none := by
  apply List.findIdx?_eq_none_iff.mpr
  intro b hb
  have hn : b.id ≠ s := fun he => hs (he ▸ List.mem_map_of_mem hb)
  simp [hn]

private theorem rooted_ancestors (boxes : List ModelBox) (ids : List String)
    (hids : ∀ b ∈ boxes, b.id ∈ ids) (n : Nat) (s : String) :
    Compound.ancestors (boxes.map (rootModelBox ids)) n (rootParent ids s) =
      Compound.ancestors boxes n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases he : s = ""
    · subst s
      simp only [rootParent_empty, Compound.ancestors.eq_2]
    by_cases hm : s ∈ ids
    · rw [rootParent, ite_eq_left hm, Compound.ancestors.eq_3 _ _ _ he,
        Compound.ancestors.eq_3 _ _ _ he, List.findIdx?_map]
      change (match boxes.findIdx? (fun b => b.id == s) with
        | none => []
        | some i => match (boxes.map (rootModelBox ids))[i]? with
          | none => []
          | some b => Compound.ancestors (boxes.map (rootModelBox ids)) n b.parent ++ [i]) = _
      cases hf : boxes.findIdx? (fun b => b.id == s) with
      | none => rfl
      | some i =>
        change (match (boxes.map (rootModelBox ids))[i]? with
          | none => []
          | some b => Compound.ancestors (boxes.map (rootModelBox ids)) n b.parent ++ [i]) =
          (match boxes[i]? with
          | none => []
          | some b => Compound.ancestors boxes n b.parent ++ [i])
        rw [List.getElem?_map]
        cases hb : boxes[i]? with
        | none => rfl
        | some b => exact congrArg (· ++ [i]) (ih b.parent)
    · have hmissing : s ∉ boxes.map (·.id) := by
        intro hs
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hs
        exact hm (hids b hb)
      rw [rootParent, ite_eq_right hm, Compound.ancestors.eq_2,
        Compound.ancestors.eq_3 _ _ _ he, findIdx_missing boxes s hmissing]

private theorem rooted_path (boxes : List ModelBox) (ids : List String)
    (hids : ∀ b ∈ boxes, b.id ∈ ids) (b : ModelBox) :
    Compound.path (boxes.map (rootModelBox ids)) (rootModelBox ids b) =
      Compound.path boxes b := by
  unfold Compound.path
  rw [List.length_map]
  exact rooted_ancestors boxes ids hids _ b.parent

private theorem rooted_inside (boxes : List ModelBox) (ids : List String)
    (hids : ∀ b ∈ boxes, b.id ∈ ids) (g s : String) :
    Compound.inside (boxes.map (rootModelBox ids)) g s = Compound.inside boxes g s := by
  unfold Compound.inside
  rw [List.find?_map, List.findIdx?_map]
  change (match (boxes.find? (fun b => b.id == s)).map (rootModelBox ids),
      boxes.findIdx? (fun b => b.id == g) with
      | some b, some i => (Compound.path (boxes.map (rootModelBox ids)) b).contains i
      | _, _ => false) = _
  cases hf : boxes.find? (fun b => b.id == s) <;>
    cases hi : boxes.findIdx? (fun b => b.id == g) <;> simp [rooted_path boxes ids hids]

private theorem rooted_endpoint (boxes : List ModelBox) (ids : List String)
    (hids : ∀ b ∈ boxes, b.id ∈ ids) (source : Bool) (i j : Nat) :
    Compound.endpoint (boxes.map (rootModelBox ids)) source i j =
      Compound.endpoint boxes source i j := by
  have hbottom : Compound.bottomIndex (boxes.map (rootModelBox ids)) i =
      Compound.bottomIndex boxes i := by
    simp only [Compound.bottomIndex, List.length_map, ← List.map_take, List.filter_map,
      Function.comp_def] <;> rfl
  unfold Compound.endpoint
  simp only [List.getElem?_map]
  cases hi : boxes[i]? <;> cases hj : boxes[j]? <;>
    simp only [Option.map_some, Option.map_none, rooted_inside boxes ids hids, hbottom] <;> rfl

private theorem rooted_prepare (boxes : List ModelBox) (ids : List String)
    (hids : ∀ b ∈ boxes, b.id ∈ ids) (pad : Int) (titles : List (Int × Int)) (g : Graph) :
    Compound.prepare (boxes.map (rootModelBox ids)) pad titles g = Compound.prepare boxes pad titles g := by
  have hnodes : Compound.markNodes (boxes.map (rootModelBox ids)) pad titles g.nodes =
      Compound.markNodes boxes pad titles g.nodes := by
    unfold Compound.markNodes
    dsimp only
    congr 1
    · apply List.map_congr_left
      intro q _
      rw [List.getElem?_map]
      cases he : boxes[q.2]? with
      | none => rfl
      | some b =>
        have hrole : (rootModelBox ids b).role = b.role := rfl
        simp only [Option.map_some, hrole]
        rw [rooted_path boxes ids hids]
    · simp only [List.zipIdx_map, List.filterMap_map, Function.comp_def]
      apply congrArg (fun f : ModelBox × Nat → Option Node => boxes.zipIdx.filterMap f)
      funext q
      dsimp only [Prod.map_fst, Prod.map_snd, id_eq]
      have hrole : (rootModelBox ids q.1).role = q.1.role := rfl
      simp only [hrole]
      rw [rooted_path boxes ids hids]
  have hedges : g.edges.map (Compound.aliasEdge (boxes.map (rootModelBox ids))) =
      g.edges.map (Compound.aliasEdge boxes) := by
    apply List.map_congr_left
    intro e _
    simp only [Compound.aliasEdge, rooted_endpoint boxes ids hids]
  simp only [Compound.prepare, hnodes, hedges]

@[simp] theorem rootInput_length (inp : Input) : (rootInput inp).boxes.length = inp.boxes.length := by
  simp only [rootInput, List.length_map]

@[simp] theorem rooted_reindex (idSets : List (String × List String)) (inp : Input) :
    reindexRegionSets idSets (rootInput inp) = reindexRegionSets idSets inp := by
  simp only [reindexRegionSets, rootInput_ids]

@[simp] theorem rooted_boxLines (m : Measure.Metric) (target : Int) (inp : Input) :
    boxLines m target (rootInput inp) = boxLines m target inp := by
  simp only [rootInput, boxLines, List.zipIdx_map, List.mapM_map, Function.comp_def] <;> rfl

private theorem rooted_edges (inp : Input) (n : Nat) (rs : List ModelRoute) :
    graphEdgesFrom (rootInput inp) n rs = graphEdgesFrom inp n rs := by
  have hedge (r : ModelRoute) (i : Nat) : edgeOf (rootInput inp) r i = edgeOf inp r i := by
    simp only [edgeOf, rootInput, List.findIdx?_map, Function.comp_def] <;> rfl
  induction rs generalizing n with
  | nil => rfl
  | cons r rs ih => simp only [graphEdgesFrom, hedge, ih]

@[simp] theorem rooted_exactDecls (inp : Input) (exactIds : List String) :
    exactDecls exactIds (rootInput inp) = exactDecls exactIds inp := by
  simp only [rootInput, exactDecls, List.zipIdx_map, List.filterMap_map, Function.comp_def] <;> rfl

@[simp] theorem rooted_exactGraph (P : Params) (exactIds : List String) (inp : Input)
    (o : Options) (labels : List MeasuredLabel) (g : Graph) :
    exactGraph P exactIds (rootInput inp) o labels g = exactGraph P exactIds inp o labels g := by
  unfold exactGraph
  dsimp only [rootInput]
  simp only [List.getElem?_map]
  congr 1
  congr 1
  funext node
  cases h : inp.boxes[node.decl]? <;> rfl

@[simp] theorem rooted_measuredGraph (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) :
    measuredGraph P (rootInput inp) o lines = measuredGraph P inp o lines := by
  let ids := inp.boxes.map (·.id)
  let demote (b : ModelBox) :=
    if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then { b with role := .node } else b
  have hid : ∀ b ∈ inp.boxes.map demote, b.id ∈ ids := by
    intro b hb
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hb
    have he : (demote old).id = old.id := by unfold demote; split <;> rfl
    rw [he]
    exact List.mem_map_of_mem hold
  have hdemote : (rootInput inp).boxes.map demote =
      (inp.boxes.map demote).map (rootModelBox ids) := by
    simp only [rootInput, List.map_map]
    apply List.map_congr_left
    intro b _
    change demote (rootModelBox ids b) = rootModelBox ids (demote b)
    unfold demote
    have hid' : (rootModelBox ids b).id = b.id := rfl
    rw [hid']
    by_cases h : (inp.fixedSizes.any (fun fixed => fixed.1 == b.id)) = true
    · simp only [ite_eq_left h] <;> rfl
    · simp only [ite_eq_right h] <;> rfl
  have hprepare (pad : Int) (titles : List (Int × Int)) (g : Graph) :
      Compound.prepare ((rootInput inp).boxes.map demote) pad titles g =
        Compound.prepare (inp.boxes.map demote) pad titles g := by
    rw [hdemote, rooted_prepare (inp.boxes.map demote) ids hid]
  have hpath (b : ModelBox) :
      Compound.path (rootInput inp).boxes (rootModelBox ids b) =
        Compound.path inp.boxes b :=
    rooted_path inp.boxes ids (fun b hb => List.mem_map_of_mem hb) b
  have hget (i : Nat) : (rootInput inp).boxes[i]? =
      inp.boxes[i]?.map (rootModelBox ids) := List.getElem?_map
  have hedge : graphEdges (rootInput inp) = graphEdges inp := rooted_edges inp 0 inp.routes
  have hlabels (m : Measure.Metric) (target : Int) :
      measureLabels P m target (rootInput inp) o.direction =
        measureLabels P m target inp o.direction := by
    unfold measureLabels
    rfl
  unfold measuredGraph
  refine bind_congr rfl ?_
  intro nodes
  refine bind_congr hedge ?_
  intro edges
  refine bind_congr rfl ?_
  intro m
  refine bind_congr (hlabels m _) ?_
  intro labels
  apply bind_congr
  · apply congrArg (fun f : Node × Nat → Except LayoutError Node =>
      (nodes.map (orientNode o.direction)).zipIdx.mapM f)
    funext q
    cases h : inp.boxes[q.2]? with
    | none => simp only [hget, h, Option.map_none] <;> rfl
    | some b => simp only [hget, h, Option.map_some, hpath] <;> rfl
  · intro ns
    apply congrArg (fun graph : Graph => (pure graph : Except LayoutError Graph))
    exact hprepare _ _ _

private theorem rooted_clusterRows (inp : Input) (s : RegionSpec) (cg : Graph) :
    clusterRows (rootInput inp) s cg = clusterRows inp s cg := by
  simp only [clusterRows, boxId, rootInput, List.getElem?_map, Option.map_map] <;> rfl

private theorem clusterRows_find_missing (inp : Input) (s : RegionSpec) (cg : Graph)
    (parent : String) (hn : parent ≠ "") (hm : parent ∉ inp.boxes.map (·.id)) :
    (clusterRows inp s cg).findIdx? (fun c => c.id == parent) = none := by
  apply List.findIdx?_eq_none_iff.mpr
  intro c hc
  unfold clusterRows at hc
  obtain ⟨q, _, he⟩ := List.mem_filterMap.mp hc
  split at he
  · contradiction
  · have hid := congrArg RegionCluster.id (Option.some.inj he).symm
    change c.id = boxId inp q.1.decl at hid
    rw [hid]
    unfold boxId
    cases h : inp.boxes[q.1.decl]? with
    | none => simp [Ne.symm hn]
    | some b =>
      have hb := List.mem_of_getElem? h
      have hne : b.id ≠ parent := fun he => hm (he ▸ List.mem_map_of_mem hb)
      simp [hne]

@[simp] theorem rooted_newComponentRegions (inp : Input) (spec : Option RegionSpec) (P : Params)
    (cg : Graph) : newComponentRegions spec P (rootInput inp) cg = newComponentRegions spec P inp cg := by
  cases spec with
  | none => rfl
  | some s =>
    let clusters := clusterRows inp s cg
    let parentIndex (id : String) : Int :=
      match id with
      | "" => -1
      | pid => match clusters.findIdx? (fun c => c.id == pid) with
        | some k => (k : Int)
        | none => -1
    have hparent (c : RegionCluster) :
        parentIndex (boxParent (rootInput inp) c.decl) = parentIndex (boxParent inp c.decl) := by
      simp only [boxParent, rootInput, List.getElem?_map, Option.map_map]
      cases h : inp.boxes[c.decl]? with
      | none => rfl
      | some b =>
        change parentIndex (rootParent (inp.boxes.map (·.id)) b.parent) = parentIndex b.parent
        by_cases he : b.parent = ""
        · simp only [he, rootParent_empty]
        by_cases hm : b.parent ∈ inp.boxes.map (·.id)
        · simp only [rootParent, ite_eq_left hm]
        have hnone := clusterRows_find_missing inp s cg b.parent he hm
        simp [rootParent, hm, parentIndex, clusters, hnone]
    have hparents : clusters.map (fun c => parentIndex (boxParent (rootInput inp) c.decl)) =
        clusters.map (fun c => parentIndex (boxParent inp c.decl)) := by
      apply List.map_congr_left
      intro c _
      exact hparent c
    by_cases hempty : s.sets.isEmpty = true
    · simp only [newComponentRegions, ite_eq_left hempty]
    · simp only [newComponentRegions, rooted_clusterRows, ite_eq_right hempty]
      refine bind_congr rfl ?_
      intro sets
      by_cases hsets : sets.isEmpty = true
      · simp only [ite_eq_left hsets]
      · simp only [ite_eq_right hsets]
        apply congrArg (fun parents : List Int =>
          (pure (some { clusters := clusters, parents := parents, sets := sets, lineH := P.lineH }) :
            Except LayoutError (Option ComponentRegions)))
        exact hparents

@[simp] theorem rooted_componentRunR (P : Params) (exact : List Nat) (spec : Option RegionSpec)
    (inp : Input) (cg : Graph) (labels : List MeasuredLabel) (order : OrderOptions) :
    componentRunR P exact spec (rootInput inp) cg labels order =
      componentRunR P exact spec inp cg labels order := by
  simp only [componentRunR, rooted_newComponentRegions]

end Elegant.Layered.PipelineImpl.ContractedC8a
