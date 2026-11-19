import Elegant.Layered.RegionFlatC4

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-- Peel helper for the region cross-coordinate replay (prefixed copy: `bind_ok` is private
in every module that uses it). -/
private theorem rccmd_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Array `set!` with the same dummy flag keeps the dummy projection. -/
private theorem rccmd_set_dummy (arr : Array ProperNode) (idx : Nat) (v : ProperNode)
    (hv : v.dummy = (arr.getD idx default).dummy) :
    (arr.set! idx v).toList.map ProperNode.dummy = arr.toList.map ProperNode.dummy := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
  rw [Array.set!_eq_setIfInBounds]
  by_cases heq : idx = j
  · subst heq
    by_cases hlt : idx < arr.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hlt]
      rw [Array.getElem?_eq_getElem hlt]
      have hget : arr.getD idx default = arr[idx]'hlt := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
      rw [hget] at hv
      simp [hv]
    · have hnone : arr[idx]? = none := Array.getElem?_eq_none (Nat.le_of_not_gt hlt)
      have hset : (arr.setIfInBounds idx v)[idx]? = none := by
        rw [Array.getElem?_setIfInBounds_self]
        simp [Nat.not_lt.mpr (Nat.le_of_not_gt hlt)]
      rw [hset, hnone]
  · rw [Array.getElem?_setIfInBounds_ne heq]

-- Single reserved-ports step preserves the dummy projection: it only rewrites
-- one node height and leaves the dummy flag untouched.
private theorem rccmd_step_dummy (pl : RegionPlacement) (cg : Graph)
    (labels : List MeasuredLabel) (acc : List Int × Array ProperNode)
    (q : RegionCluster × Nat) (out : List Int × Array ProperNode)
    (h : (do
      let c := q.1
      let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
      if c.titleW < 0 ∨ footprint < 0 then (Except.error LayoutError.domain : Except LayoutError (List Int × Array ProperNode))
      else
        let x ← clusterPortR pl q.2 c.top acc.1
        let x ← clusterPortR pl q.2 c.bottom x
        let top := acc.2.getD c.top default
        let nodes := acc.2.set! c.top { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
        pure (x, nodes)) = .ok out) :
    out.2.toList.map ProperNode.dummy = acc.2.toList.map ProperNode.dummy := by
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · obtain ⟨x1, hx1, h⟩ := rccmd_bind_ok h
    obtain ⟨x2, hx2, h⟩ := rccmd_bind_ok h
    have he := Except.ok.inj h
    have h2 := (congrArg Prod.snd he).symm
    rw [h2]
    apply rccmd_set_dummy
    rfl
-- The cluster fold preserves the dummy projection from the initial array.
private theorem rccmd_fold_dummy (pl : RegionPlacement) (cg : Graph)
    (labels : List MeasuredLabel) (xs : List (RegionCluster × Nat)) (x : List Int)
    (arr : Array ProperNode) (x' : List Int) (arr' : Array ProperNode)
    (harr : arr.toList.map ProperNode.dummy = pl.p.nodes.map ProperNode.dummy)
    (h : (xs.foldlM (fun acc q => do
      let c := q.1
      let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
      if c.titleW < 0 ∨ footprint < 0 then (Except.error LayoutError.domain : Except LayoutError (List Int × Array ProperNode))
      else
        let x ← clusterPortR pl q.2 c.top acc.1
        let x ← clusterPortR pl q.2 c.bottom x
        let top := acc.2.getD c.top default
        let nodes := acc.2.set! c.top { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
        pure (x, nodes)) (x, arr)) = .ok (x', arr')) :
    arr'.toList.map ProperNode.dummy = pl.p.nodes.map ProperNode.dummy := by
  induction xs generalizing x arr x' arr' with
  | nil =>
    have he := Except.ok.inj h
    have harr' : arr' = arr := (congrArg Prod.snd he).symm
    rw [harr']
    exact harr
  | cons q rest ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := rccmd_bind_ok h
    have hstep := rccmd_step_dummy pl cg labels (x, arr) q mid hmid
    have hmidarr : mid.2.toList.map ProperNode.dummy = pl.p.nodes.map ProperNode.dummy := by
      have h1 : mid.2.toList.map ProperNode.dummy = (x, arr).2.toList.map ProperNode.dummy := hstep
      simp only at h1
      rw [h1]
      exact harr
    exact ih mid.1 mid.2 x' arr' hmidarr hrest
-- `reservedPortsR` only raises top nodes; dummy flags survive the whole fold.
private theorem rccmd_reserved_metadata (pl : RegionPlacement) (cg : Graph)
    (labels : List MeasuredLabel) (x : List Int) (out : List Int × Proper)
    (h : reservedPortsR pl cg labels x = .ok out) :
    Metadata.NodeMetadata pl.p out.2 := by
  unfold reservedPortsR at h
  obtain ⟨foldout, hfold, h⟩ := rccmd_bind_ok h
  have he := Except.ok.inj h
  have hnodes : out.2.nodes = foldout.2.toList := by
    have hc := congrArg (fun q : List Int × Proper => q.2.nodes) he
    simp only at hc
    exact hc.symm
  have harr0 : (pl.p.nodes.toArray).toList.map ProperNode.dummy = pl.p.nodes.map ProperNode.dummy := by
    rw [List.toList_toArray]
  have hfoldmap := rccmd_fold_dummy pl cg labels (pl.rm.clusters.zipIdx) x (pl.p.nodes.toArray) foldout.1 foldout.2 harr0 hfold
  have hmap : out.2.nodes.map ProperNode.dummy = pl.p.nodes.map ProperNode.dummy := by
    rw [hnodes]
    exact hfoldmap
  exact Metadata.nodeMetadata_of_dummy_list_eq hmap
/-- The open cross-coordinate fact holds: a successful `crossCoordsR` run keeps
node dummy flags, since only `reservedPortsR` rewrites nodes and it preserves
the dummy projection. -/
theorem rfc4CrossCoordsR_metadata_holds : rfc4CrossCoordsR_metadata_factR := by
  intro P rm cg labels p minimum layers placed h
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := rccmd_bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    exact absurd h (by simp)
  · obtain ⟨ngs, _, h⟩ := rccmd_bind_ok h
    obtain ⟨xc, _, h⟩ := rccmd_bind_ok h
    obtain ⟨_, _, h⟩ := rccmd_bind_ok h
    obtain ⟨⟨alloc, x2⟩, _, h⟩ := rccmd_bind_ok h
    obtain ⟨⟨x3, p3⟩, hres, h⟩ := rccmd_bind_ok h
    have he := Except.ok.inj h
    have hmeta := rccmd_reserved_metadata _ _ _ _ _ hres
    have hp3 : placed.2.snd.snd = p3 := (congrArg (fun q : List Int × List (List Nat) × List (Option Int) × Proper => q.2.snd.snd) he).symm
    rw [hp3]
    exact hmeta
/-- Closed C4 discharge for the region base: every scene route of `layoutRIds`
is orthogonal, with the cross-coordinate residual proved above. -/
theorem flatC4B_layoutRIds_closed (exactIds : List String)
    (idSets : List (String × List String)) : FlatC4B (layoutRIds exactIds idSets) :=
  flatC4B_layoutRIds exactIds idSets rfc4CrossCoordsR_metadata_holds





end PipelineImpl
end Layered
end Elegant
