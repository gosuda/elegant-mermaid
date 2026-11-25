import Elegant.Layered.RegionMemberFramesNest
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionFlatC3
import Elegant.Layered.RegionPlacement
import Elegant.Layered.RegionPipeline
import Elegant.Layered.RegionModel
import Elegant.Layered.RegionReduction
import Elegant.Layered.RegionFoundation
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.CgShape
import Elegant.Layered.Compound
import Elegant.Layered.CoordGraph
import Elegant.Layered.ComponentCoverage
set_option autoImplicit false

namespace Elegant
namespace Layered
open CoordsImpl
namespace PipelineImpl

open RegionImpl

/-! # Region plain-member x-bracket (`R_regionNestPlain_holds`).

Proves conjunct one of `R_RegionNestResidual`
(`RegionMemberFramesNest.lean`): for a plain member, the proper node at the
same index carries the member path and the parent frame brackets the member
rect in `x`. The `none`-spec case replays the exact coordinate chain
(`ExactRunFrameNestingProof.lean`) over `SceneExecutionR` with `rnc`-prefixed
copies: the run coincides with the exact run (`componentRunR_none`), so the
border-interval argument transfers. The `some`-spec case needs the region
allocation code (`crossCoordsR`) and stays as the named residual
`R_RegionNestGroupResidual` covers child groups (conjunct two).
-/

/-- Region plain-some residual: conjunct one of `R_RegionNestResidual`
restricted to `some` specs. Needs the `crossCoordsR` allocation code. -/
def R_RegionNestSomeResidual (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec) (cg' : Graph)
    (run : Run) (orderOptions : OrderOptions),
    spec'.isSome = true →
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg', run) →
    ∀ (index memberIndex : Nat) (node member : Node),
      (componentCandidateR spec' execution.graph comp candidate).nodes[index]? =
        some node →
      node.border = -2 →
      (componentCandidateR spec' execution.graph comp candidate).nodes[memberIndex]? =
        some member →
      member.border = 0 → member.clusterPath.contains node.decl = true →
      ∃ actual : ProperNode, run.proper.nodes[memberIndex]? = some actual ∧
        actual.node.clusterPath = member.clusterPath ∧
        (frameRect execution.params
          (componentCandidateR spec' execution.graph comp candidate)
          run index).x ≤
          (Labels.rectAt run.proper run.xs run.ys memberIndex).x ∧
        (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
          (Labels.rectAt run.proper run.xs run.ys memberIndex).w ≤
          (frameRect execution.params
            (componentCandidateR spec' execution.graph comp candidate)
            run index).x +
          (frameRect execution.params
            (componentCandidateR spec' execution.graph comp candidate)
            run index).w

/-- Region group residual: conjunct two of `R_RegionNestResidual` (child
group frames are `Contained` in the parent frame). Needs the region
allocation code for both axes. -/
def R_RegionNestGroupResidual (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec) (cg' : Graph)
    (run : Run) (orderOptions : OrderOptions),
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg', run) →
    ∀ (parentIndex childIndex : Nat) (parent child : Node),
      (componentCandidateR spec' execution.graph comp candidate).nodes[parentIndex]? =
        some parent →
      parent.border = -2 →
      (componentCandidateR spec' execution.graph comp candidate).nodes[childIndex]? =
        some child →
      child.border = -2 →
      ∀ (parentBox childBox : ModelBox),
        inp.boxes[parent.decl]? = some parentBox →
        inp.boxes[child.decl]? = some childBox →
        childBox.parent = parentBox.id → childBox.parent ≠ "" →
        (frameRect execution.params
          (componentCandidateR spec' execution.graph comp candidate)
          run parentIndex).Contained
          (frameRect execution.params
            (componentCandidateR spec' execution.graph comp candidate)
            run childIndex)

/-! ## Probe evidence for the residuals. -/

private def rncp_o : Options := { profile := .vector, direction := .TB }

private def rncp_nBox (id parent : String) : ModelBox :=
  { id := id, parent := parent, exclusive := false }

private def rncp_gBox (id parent : String) : ModelBox :=
  { id := id, role := .group, parent := parent, exclusive := false }

private def rncp_rt (id fromId toId : String) : ModelRoute :=
  { id := id, fromId := fromId, toId := toId }

private def rncp_inp2 : Input := { kind := "state", boxes := [rncp_gBox "G1" "", rncp_gBox "A" "G1", rncp_gBox "B" "G1", rncp_gBox "G2" "", rncp_gBox "C" "G2", rncp_gBox "D" "G2"], routes := [rncp_rt "e1" "A" "B", rncp_rt "e2" "C" "D"], texts := ["G1", "A", "B", "G2", "C", "D"], edges := [.plain], labels := [] }

private def rncp_sets2 : List ModelRegionSet :=
  [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]

private def rncp_inpN : Input := { kind := "state", boxes := [rncp_gBox "G" "", rncp_gBox "H" "G", rncp_gBox "J" "H", rncp_nBox "a" "J", rncp_nBox "b" "G"], routes := [rncp_rt "e1" "b" "a"], texts := ["G", "H", "J", "a", "b"], edges := [.plain], labels := [] }

private def rncp_setsN : List ModelRegionSet :=
  [{ parent := 0, regions := [1] }, { parent := 1, regions := [2] }]

private def rncp_inpT : Input := { kind := "state", boxes := [rncp_gBox "T" "", rncp_gBox "G1" "T", rncp_gBox "A" "G1", rncp_gBox "B" "G1", rncp_nBox "a1" "A", rncp_nBox "b1" "B"], routes := [rncp_rt "e1" "a1" "b1"], texts := ["T", "G1", "A", "B", "a1", "b1"], edges := [.plain], labels := [] }

private def rncp_setsT : List ModelRegionSet :=
  [{ parent := 1, regions := [2, 3] }]

private def rncp_inpD : Input := { kind := "state", boxes := [rncp_nBox "solo" ""], routes := [], texts := ["solo"], edges := [.plain], labels := [] }

private def rncp_setsD : List ModelRegionSet := []

/-- Real prefix of `layoutRIds`: params, exact graph, measured labels, spec. -/
private def rncp_prefix (inp : Input) (sets : List ModelRegionSet) :
    Except LayoutError (Params × Graph × List MeasuredLabel × Option RegionSpec) := do
  let P ← checkedParams .vector inp.kind
  let m ← metricOf .vector
  let target := Measure.wrapTarget m.profile P.wrapWidth 0
  let lines ← boxLines m target inp
  let measured ← measureLabels P m target inp .TB
  let g0 ← measuredGraph P inp rncp_o lines
  let g ← exactGraph P [] inp rncp_o measured g0
  let idSets ← graphRegions inp sets
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    (width, height)
  pure (P, g, measured, if idSets.isEmpty then none else some (RegionSpec.mk idSets titles))

/-- Decidable plain-member x-bracket for one executed component run. -/
private def rncp_checkPlain (P : Params) (inp : Input) (labels : List MeasuredLabel)
    (g : Graph) (spec : Option RegionSpec) (comp : List Nat) (idx : Nat) : Bool :=
  match componentRunR P [] spec inp (componentCandidateR spec g comp idx) labels {} with
  | .error _ => true
  | .ok (cg', run) =>
    ((List.range comp.length).filterMap fun mi =>
      match comp[mi]? with
      | none => none
      | some key => match inp.boxes[key]? with
        | none => none
        | some cb => if cb.parent == "" then none
          else match (inp.boxes.zipIdx.find? fun q => q.1.id == cb.parent).map Prod.snd with
            | none => none
            | some pi => some (mi, pi)).all fun q =>
      match (comp.zipIdx.find? fun r => r.1 == q.2).map Prod.snd with
      | none => true
      | some pj =>
        match cg'.nodes[q.1]? with
        | none => false
        | some member =>
          let parentFrame := frameRect P cg' run pj
          if member.border == 0 then
            match run.proper.nodes[q.1]? with
            | none => false
            | some actual =>
              actual.node.clusterPath == member.clusterPath &&
              decide (parentFrame.x ≤ (Labels.rectAt run.proper run.xs run.ys q.1).x) &&
              decide ((Labels.rectAt run.proper run.xs run.ys q.1).x +
                (Labels.rectAt run.proper run.xs run.ys q.1).w ≤
                parentFrame.x + parentFrame.w)
          else true

/-- Decidable group containment for one executed component run. -/
private def rncp_checkGroup (P : Params) (inp : Input) (labels : List MeasuredLabel)
    (g : Graph) (spec : Option RegionSpec) (comp : List Nat) (idx : Nat) : Bool :=
  match componentRunR P [] spec inp (componentCandidateR spec g comp idx) labels {} with
  | .error _ => true
  | .ok (cg', run) =>
    ((List.range comp.length).filterMap fun mi =>
      match comp[mi]? with
      | none => none
      | some key => match inp.boxes[key]? with
        | none => none
        | some cb => if cb.parent == "" then none
          else match (inp.boxes.zipIdx.find? fun q => q.1.id == cb.parent).map Prod.snd with
            | none => none
            | some pi => some (mi, pi)).all fun q =>
      match (comp.zipIdx.find? fun r => r.1 == q.2).map Prod.snd with
      | none => true
      | some pj =>
        match cg'.nodes[q.1]? with
        | none => false
        | some member =>
          let parentFrame := frameRect P cg' run pj
          if member.border == -2 then
            decide (parentFrame.Contained (frameRect P cg' run q.1))
          else true

/-- Plain evidence over all components and candidates `0‥4`. -/
private def rncp_plainEvidence (sets : List ModelRegionSet) (inp : Input) : Bool :=
  match rncp_prefix inp sets with
  | .error _ => false
  | .ok (P, g, measured, spec) =>
    (components g).all fun comp =>
      ([0, 1, 2, 3, 4].all fun idx =>
        rncp_checkPlain P inp measured g spec comp idx)

/-- Group evidence over all components and candidates `0‥4`. -/
private def rncp_groupEvidence (sets : List ModelRegionSet) (inp : Input) : Bool :=
  match rncp_prefix inp sets with
  | .error _ => false
  | .ok (P, g, measured, spec) =>
    (components g).all fun comp =>
      ([0, 1, 2, 3, 4].all fun idx =>
        rncp_checkGroup P inp measured g spec comp idx)

#eval rncp_plainEvidence rncp_sets2 rncp_inp2
#eval rncp_plainEvidence rncp_setsN rncp_inpN
#eval rncp_plainEvidence rncp_setsT rncp_inpT
#eval rncp_plainEvidence rncp_setsD rncp_inpD
#eval rncp_groupEvidence rncp_sets2 rncp_inp2
#eval rncp_groupEvidence rncp_setsN rncp_inpN
#eval rncp_groupEvidence rncp_setsT rncp_inpT
#eval rncp_groupEvidence rncp_setsD rncp_inpD
#eval (framedParents rncp_inp2, framedParents rncp_inpN, framedParents rncp_inpT, framedParents rncp_inpD)

private theorem rnc_ranked_source {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      ∀ edge ∈ (Compound.rankingGraph cg).edges,
        edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
  unfold componentRunX at h
  obtain ⟨rr, hrr, h⟩ := bind_ok h
  obtain ⟨normalized, hn, h⟩ := bind_ok h
  obtain ⟨labeled, hl, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨lanes, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨shifted, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have heq := Except.ok.inj h
  subst run
  refine ⟨rr, normalized, labeled, hrr, hn, hl, rfl, ?_⟩
  apply rank_feasible (Compound.rankingGraph cg) rr.ranks
  simp only [RankImpl.rank, hrr]

private theorem rnc_plain_node_dims {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

private theorem rnc_plain_anchor_dims (P : Params) {exact : List Nat} {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨sized, hs, he, hb', hw, hh⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.edge = nd.edge ∧ sized.node.border = 0 ∧
        nd.node.w ≤ sized.node.w ∧ sized.node.h = nd.node.h := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, rfl, hb, Int.le_refl _, rfl⟩
    · refine ⟨_, rfl, rfl, hb, ?_, rfl⟩
      exact Int.le_max_left _ _
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? = some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split <;> exact ⟨_, rfl, he, hb', hw, hh⟩

private theorem rnc_sized_length (P : Params) (exact : List Nat) (p : Proper) :
    (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
  unfold sizeProperPortsX
  simp

private theorem rnc_coordinateGraph0_lookup_at (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd)
    (hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := rnc_sized_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  rw [List.getElem?_append_left hv1] at hl
  rw [titleReservations_nodes] at hl
  by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
  · rw [List.getElem?_append_left (by simpa using hv2)] at hl
    left
    cases hs : (sizeProperPortsX P exact p).nodes[v]? with
    | none => simp [List.getElem?_map, hs] at hl
    | some s =>
      simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
      subst hl
      have hk := sizeProperPortsX_key P exact p v
      rw [hs] at hk
      cases hp : p.nodes[v]? with
      | none => simp [hp] at hk
      | some mp =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hd, hb, hpth⟩ := hk
        obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
        refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
        · rw [c1, t1, hd]
        · rw [c2, t2, hb]
        · rw [c3, t3, hpth]
        · intro hbd
          rw [c4]
          exact t4 (by rw [← t2, ← c2]; exact hbd)
  · right; right
    rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
    obtain ⟨q, hq, rfl⟩ := hl
    refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
    · simpa [hlen] using hq
    · rw [c1]; rfl
    · rw [c2]; rfl
    · rw [c3]; rfl

private theorem rnc_coordinateGraph0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · exact rnc_coordinateGraph0_lookup_at P exact p h hv1
  · rw [clearProxyExtents_nodes] at h
    rw [hx] at h
    simp only [List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨m, hl, rfl⟩ := h
    rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

private theorem rnc_coordinateGraph_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases rnc_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3
private theorem rnc_original_plain_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = node.clusterPath ∧ actual.edge = none ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, normalized, labeled, _, hn, hl, hc, _⟩ := rnc_ranked_source hrun
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, hedge, hborder, hwidth, hheight⟩ :=
    rnc_plain_anchor_dims P hsource hplain
  have hmetadata : actual.dummy = false ∧ actual.node.clusterPath = node.clusterPath := by
    rcases rnc_coordinateGraph_lookup P exact labeled hactual with
      ⟨original, horiginal, hd, _, hp, _⟩ | ⟨_, hside⟩ |
        ⟨_, _, _, _, _, hb3, _⟩
    · have heq : original = ⟨node, false, none, false⟩ :=
        Option.some.inj (horiginal.symm.trans hsource)
      subst original
      exact ⟨hd, hp rfl⟩
    · rcases hside with hside | hside <;> omega
    · omega
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := rnc_plain_node_dims hrun hcoordinate hborder
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _, _, _, _⟩ := componentRunX_spec hrun
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hmetadata.1, hborder, hmetadata.2,
    hedge, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]


private theorem rnc_sized_origin (P : Params) (exact : List Nat) (source : Proper)
    {index : Nat} {node : ProperNode}
    (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
    ∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath := by
  have hkey := sizeProperPortsX_key P exact source index
  rw [hnode] at hkey
  cases horiginal : source.nodes[index]? with
  | none => simp [horiginal] at hkey
  | some original =>
      simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      exact ⟨original, rfl, hkey⟩

private theorem rnc_titled_origin {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source) {index : Nat} {node : ProperNode}
    (hnode : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some node) :
    (∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath) ∨
    (node.dummy = false ∧ node.node.border = 3) := by
  rw [titleReservations_nodes] at hnode
  by_cases hi : index < (sizeProperPortsX P exact source).nodes.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
      List.getElem?_map] at hnode
    obtain ⟨sized, hsized, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨original, horiginal, hd, hb, hp⟩ :=
      rnc_sized_origin P exact source hsized
    have ht := titleF_keys sized
    rw [heq] at ht
    exact Or.inl ⟨original, horiginal, ht.1.trans hd,
      ht.2.1.trans hb, ht.2.2.1.trans hp⟩
  · rw [List.getElem?_append_right (by
      simpa only [List.length_map] using Nat.le_of_not_gt hi),
      List.getElem?_map] at hnode
    obtain ⟨entry, hentry, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨hsized, hborder⟩ := titleNodes_spec hentry
    obtain ⟨original, horiginal, hd, hb, _⟩ :=
      rnc_sized_origin P exact source hsized
    have hreal : original.dummy = false := by
      rcases hkeys entry.2 original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · exact hreal
      · rw [hplain] at hb
        omega
    right
    rw [← heq]
    exact ⟨hd.trans hreal, rfl⟩
private theorem rnc_titled_marker_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some (titleF node) := by
  have hnonplain : node.node.border ≠ 0 := by
    rcases hborder with hborder | hborder <;> omega
  have hsized : (sizeProperPortsX P exact source).nodes[index]? = some node := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hnode, Option.map_some,
      Nat.zero_add]
    simp [hnonplain]
  rw [titleReservations_nodes, List.getElem?_append_left (by
    simp only [List.length_map, rnc_sized_length]
    exact (List.getElem?_eq_some_iff.mp hnode).1)]
  simp only [List.getElem?_map, hsized, Option.map_some]

private theorem rnc_titled_marker_source_record {cg : Graph} {P : Params} {exact : List Nat}
    {source : Proper}
    (hkeys : NodeKeys cg source)
    (hrecords : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      source.nodes[index]? = some ⟨node, false, none, false⟩)
    {index : Nat} {marker : ProperNode}
    (hmarker : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some marker)
    (hborder : marker.node.border = -2 ∨ marker.node.border = 2) :
    ∃ original : Node, cg.nodes[index]? = some original ∧
      marker.node.border = original.border ∧
      marker = titleF ⟨original, false, none, false⟩ := by
  rcases rnc_titled_origin hkeys hmarker with
    ⟨before, hbefore, _, hb, _⟩ | ⟨_, hb⟩
  · rcases hkeys index before hbefore with
      ⟨original, horiginal, _, hsourceBorder, _⟩ | ⟨_, hplain, _⟩
    · have hborderOriginal : original.border = -2 ∨ original.border = 2 := by
        rcases hborder with hborder | hborder <;> omega
      have hforward := rnc_titled_marker_record (P := P) (exact := exact)
        (hrecords index original horiginal) hborderOriginal
      exact ⟨original, horiginal, hb.trans hsourceBorder,
        Option.some.inj (hmarker.symm.trans hforward)⟩
    · rcases hborder with hborder | hborder <;> omega
  · rcases hborder with hborder | hborder <;> omega


private theorem rnc_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

private theorem rnc_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := rnc_titled_rank_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

private theorem rnc_titled_original_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact source)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have htitledLookup := rnc_titled_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index
private theorem rnc_map_edge_map (nodes : List ProperNode) (f : ProperNode → ProperNode)
    (hf : ∀ n, (f n).edge = n.edge) :
    (nodes.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
  simp only [List.map_map]
  apply congrArg (fun g => nodes.map g)
  funext n
  exact hf n


private theorem rnc_map_edge_zipIdx (nodes : List ProperNode)
    (f : ProperNode × Nat → ProperNode)
    (hf : ∀ n, (f n).edge = n.1.edge) :
    (nodes.zipIdx.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
  calc
    (nodes.zipIdx.map f).map ProperNode.edge =
        (nodes.zipIdx.map Prod.fst).map ProperNode.edge := by
      simp only [List.map_map]
      apply congrArg (fun g => nodes.zipIdx.map g)
      funext n
      exact hf n
    _ = nodes.map ProperNode.edge := by rw [List.zipIdx_map_fst]

private theorem rnc_coordinate_anchor_nodes (P : Params) (exact : List Nat)
    (source : Proper) :
    ∃ extra, (coordinateGraphX P exact source).nodes.map ProperNode.edge =
      source.nodes.map ProperNode.edge ++ extra := by
  have hs : (sizeProperPortsX P exact source).nodes.map ProperNode.edge =
      source.nodes.map ProperNode.edge := by
    unfold sizeProperPortsX
    apply rnc_map_edge_zipIdx
    intro n
    split <;> rfl
  have ht : ∀ nodes : List ProperNode,
      (nodes.map titleF).map ProperNode.edge = nodes.map ProperNode.edge := by
    intro nodes
    apply rnc_map_edge_map
    intro n
    unfold titleF
    split <;> rfl
  have hc : ∀ q : Proper,
      (clearProxyExtents q).nodes.map ProperNode.edge = q.nodes.map ProperNode.edge := by
    intro q
    rw [clearProxyExtents_nodes]
    apply rnc_map_edge_map
    intro n
    unfold clearF
    split <;> rfl
  have hm : ∀ q : Proper,
      (materializeDummyPaths q).nodes.map ProperNode.edge = q.nodes.map ProperNode.edge := by
    intro q
    unfold materializeDummyPaths
    apply rnc_map_edge_zipIdx
    intro n
    split <;> rfl
  obtain ⟨extraNodes, hn, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
  unfold coordinateGraphX
  rw [hm, hc, hn, List.map_append, titleReservations_nodes, List.map_append, ht, hs]
  refine ⟨((titleNodes (sizeProperPortsX P exact source)).map copyF).map ProperNode.edge ++
    extraNodes.map ProperNode.edge, ?_⟩
  rw [List.append_assoc]

private theorem rnc_coordinate_anchor_prefix (P : Params) (exact : List Nat)
    (source : Proper) :
    (∃ extra, (coordinateGraphX P exact source).nodes.map ProperNode.edge =
      source.nodes.map ProperNode.edge ++ extra) ∧
    (∃ extra, (coordinateGraphX P exact source).rank = source.rank ++ extra) := by
  constructor
  · exact rnc_coordinate_anchor_nodes P exact source
  · obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
    have htitle : ∃ tail, (titleReservations (sizeProperPortsX P exact source)).rank =
        source.rank ++ tail :=
      ⟨_, rfl⟩
    obtain ⟨tail, htitle⟩ := htitle
    refine ⟨tail ++ extraRanks, ?_⟩
    change (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).rank = _
    rw [hr, htitle, List.append_assoc]
private theorem rnc_coordinate_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := (rnc_coordinate_anchor_prefix P exact source).2
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h



private theorem rnc_coordinate_original_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (coordinateGraphX P exact source).rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hcoordinateLookup := rnc_coordinate_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]

private theorem rnc_marker_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2)
    (hdummy : node.dummy = false) :
    (coordinateGraphX P exact source).nodes[index]? = some (clearF (titleF node)) := by
  have htitled := rnc_titled_marker_record (P := P) (exact := exact) hnode hborder
  obtain ⟨extra, hextension, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
  have hbordered : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some (titleF node) := by
    rw [hextension, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitled).1]
    exact htitled
  have hcleared : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some (clearF (titleF node)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hbordered]
    rfl
  have hreal : (clearF (titleF node)).dummy = false :=
    (clearF_keys _).1.trans ((titleF_keys node).1.trans hdummy)
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hcleared, Option.map_some,
    Nat.zero_add, hreal, Bool.false_eq_true, ↓reduceIte]



private theorem rnc_side_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some node)
    (hdummy : node.dummy = false)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    (coordinateGraphX P exact source).nodes[index]? = some node := by
  have hnotProxy :
      (node.node.border == -2 || node.node.border == 2) = false := by
    rcases hborder with hborder | hborder <;> simp [hborder]
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some node := by
    simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
    simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
    Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

private theorem rnc_coordinate_rank_pair (P : Params) (exact : List Nat)
    (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
      rank)
    (hhi : rank ≤
      (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraphX P exact source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).rank[left]? = some (rank : Int) ∧
      (coordinateGraphX P exact source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, rnc_side_record hl rfl (Or.inl rfl),
    rnc_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

private theorem rnc_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraphX P exact labeled).nodes[a]? = some na)
    (hb : (coordinateGraphX P exact labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  have key : ∀ {v : Nat} {nd : ProperNode},
      (coordinateGraphX P exact labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat),
        (titleNodes (sizeProperPortsX P exact labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases rnc_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hp : labeled.nodes[q.2]? with
      | none => simp [hp] at hk
      | some mp =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPortsX_key P exact labeled qi.2
  have kJ := sizeProperPortsX_key P exact labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi)
          (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]
private theorem rnc_border_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

private theorem rnc_sizeProperPorts_node_origin (P : Params) (exact : List Nat)
    (source : Proper)
    {index : Nat} {node : ProperNode}
    (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
    ∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath := by
  have hkey := sizeProperPortsX_key P exact source index
  rw [hnode] at hkey
  cases horiginal : source.nodes[index]? with
  | none => simp [horiginal] at hkey
  | some original =>
      simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      exact ⟨original, rfl, hkey⟩

private theorem rnc_source_alignment_of_titled (P : Params) (exact : List Nat)
    {source : Proper}
    (h : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length) :
    source.nodes.length = source.rank.length := by
  rw [titleReservations_nodes] at h
  simp only [List.length_append, List.length_map, rnc_sized_length] at h
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank] at h
  simp only [List.length_append, List.length_map] at h
  omega

private def rnc_proj (n : Node) : Nat × Int × List Nat := (n.decl, n.border, n.clusterPath)


private theorem rnc_projMap {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
    List.map rnc_proj execution.graph.nodes =
      List.map rnc_proj execution.graph0.nodes := by
  have hlen : execution.graph.nodes.length = execution.graph0.nodes.length :=
    exactGraph_length execution.graph_eq
  apply List.ext_getElem?
  intro v
  rw [List.getElem?_map, List.getElem?_map]
  cases h0 : execution.graph0.nodes[v]? with
  | none =>
    have hnone : execution.graph.nodes[v]? = none := by
      rw [List.getElem?_eq_none_iff] at h0 ⊢
      omega
    rw [hnone]
  | some nd0 =>
    obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key execution.graph_eq h0
    rw [hnd']
    simp only [Option.map_some, rnc_proj, hnb, hnap, hnd]

private theorem rnc_revKey {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {v : Nat} {nd : Node} (h : execution.graph.nodes[v]? = some nd) :
    ∃ nd0, execution.graph0.nodes[v]? = some nd0 ∧ nd0.decl = nd.decl ∧
      nd0.border = nd.border ∧ nd0.clusterPath = nd.clusterPath := by
  have hmap := rnc_projMap execution
  have h1 : (List.map rnc_proj execution.graph.nodes)[v]? = some (rnc_proj nd) := by
    simp only [List.getElem?_map, h, Option.map_some]
  rw [hmap] at h1
  rw [List.getElem?_map] at h1
  obtain ⟨nd0, hnd0, hproj⟩ := Option.map_eq_some_iff.mp h1
  simp only [rnc_proj, Prod.mk.injEq] at hproj
  exact ⟨nd0, hnd0, hproj.1, hproj.2.1, hproj.2.2⟩

private theorem rnc_lines_len {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  exact ((mapM_getElem? _ _ _ h).1).trans List.length_zipIdx

private theorem rnc_cgShape {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
    CgShape execution.graph := by
  have hshape := measuredGraph_shape execution.graph0_eq
  refine ⟨?_, ?_⟩
  · intro a b na nb ha hb h1 h2 hp
    obtain ⟨na0, ha0, _, hb1, hp1⟩ := rnc_revKey execution ha
    obtain ⟨nb0, hb0, _, hb2, hp2⟩ := rnc_revKey execution hb
    exact hshape.1 a b na0 nb0 ha0 hb0 (by rw [hb1]; exact h1) (by rw [hb2]; exact h2)
      (by rw [hp1, hp2]; exact hp)
  · intro n hn
    obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hn
    obtain ⟨n0, h0, _, hb, _⟩ := rnc_revKey execution hv
    have h3 := hshape.2 n0 (List.mem_of_getElem? h0)
    rw [hb] at h3
    exact h3

private theorem rnc_plainPath {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  have hlineLength : execution.lines.length = inp.boxes.length :=
    rnc_lines_len execution
  obtain ⟨nodes, edges, titles, hprepared, hnodeLength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hpreparedNode := hnode
  rw [hprepared] at hpreparedNode
  have hi : index < nodes.length := by
    by_cases hi : index < nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega)
        hpreparedNode
      omega
  have hibox : index < inp.boxes.length := by omega
  let box := inp.boxes[index]'hibox
  have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hibox
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨hdecl, hpath⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hplain hchangedBox
  exact ⟨box, hbox, hdecl, hpath.trans hpathMap⟩

private theorem rnc_groupPath {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box ++ [index] := by
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph0_eq hnode hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, hdecl, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap, hdecl] at hpath
  exact hpath
private theorem rnc_titled_alignment (P : Params) (exact : List Nat) {source : Proper}
    (h : source.nodes.length = source.rank.length) :
    (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length := by
  rw [titleReservations_nodes]
  simp only [List.length_append, List.length_map, rnc_sized_length]
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank]
  simp only [List.length_append, List.length_map]
  omega


private theorem rnc_marker_shape {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node) :
    (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
      (node.border = -2 → node.clusterPath ≠ []) := by
  by_cases hplain : node.border = 0
  · exact ⟨Or.inl hplain, fun hgroup => by omega⟩
  · obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hnode hplain
    obtain ⟨member0, hmember0, _, hborder, hpath⟩ := rnc_revKey execution hsource
    obtain ⟨hdisj, hne⟩ := measuredGraph_marker_shape execution.graph0_eq hmember0
    refine ⟨?_, ?_⟩
    · rcases hdisj with h0 | h2 | h2
      · exact Or.inl (hborder.symm.trans h0)
      · exact Or.inr (Or.inl (hborder.symm.trans h2))
      · exact Or.inr (Or.inr (hborder.symm.trans h2))
    · intro hgroup
      have h0 : member0.border = -2 := hborder.trans hgroup
      rw [← hpath]
      exact hne h0
private theorem rnc_titled_border_ready {cg : Graph} {P : Params} {exact : List Nat}
    {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []))
    (haligned : source.nodes.length = source.rank.length) :
    OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)) := by
  refine ⟨?_, ?_, ?_, rnc_titled_alignment P _ haligned, ?_⟩
  · intro node hnode
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases rnc_titled_origin hkeys hindex with
      ⟨original, horiginal, _, hb, _⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, _⟩ | ⟨_, hborder, _⟩
      · have hc := (hmarkers index before hbefore).1
        rw [hb, hborder]
        rcases hc with hc | hc | hc <;> omega
      · rw [hb, hborder]
        exact ⟨by decide, by decide⟩
    · rw [hb]
      exact ⟨by decide, by decide⟩
  · intro node hnode hgroup
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases rnc_titled_origin hkeys hindex with
      ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
      · have hbeforeGroup : before.border = -2 := by omega
        rw [hp, hpath]
        exact (hmarkers index before hbefore).2 hbeforeGroup
      · omega
    · omega
  · intro a b na nb ha hb hgroupA hgroupB hpath
    rcases rnc_titled_origin hkeys ha with
      ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
    · rcases rnc_titled_origin hkeys hb with
        ⟨ob, hob, _, hbb, hpb⟩ | ⟨_, hbb⟩
      · apply labeled_topUnique hkeys hshape hoa hob
        · omega
        · omega
        · rw [← hpa, ← hpb]
          exact hpath
      · omega
    · omega
  · intro node hnode hdummy
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases rnc_titled_origin hkeys hindex with
      ⟨original, horiginal, hd, hb, _⟩ | ⟨hd, _⟩
    · rcases hkeys index original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · rw [hreal] at hd
        rw [hd] at hdummy
        cases hdummy
      · exact hb.trans hplain
    · rw [hd] at hdummy
      cases hdummy

private theorem rnc_prepared_titled_source {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
        run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) := by
  obtain ⟨rr, normalized, labeled, hrr, hn, hl, hc, _⟩ := rnc_ranked_source hrun
  have hk := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (rnc_cgShape execution) candidate
  have hready := rnc_titled_border_ready (P := execution.params)
    (exact := exactDecls exactIds inp) hk hshape
    (fun _ _ hnode => rnc_marker_shape execution hnode) haligned
  refine ⟨rr, labeled, hrr, hc, hk, hready, ?_, ?_⟩
  · intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  · intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank


private theorem rnc_group_path_iff_decl {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate firstIndex secondIndex : Nat} {first second : Node}
    (hfirst : (componentCandidate execution.graph comp candidate).nodes[firstIndex]? =
      some first)
    (hsecond : (componentCandidate execution.graph comp candidate).nodes[secondIndex]? =
      some second)
    (hfirstBorder : first.border = -2) (hsecondBorder : second.border = -2) :
    first.clusterPath = second.clusterPath ↔ first.decl = second.decl := by
  obtain ⟨_, _, hfirstSource⟩ := componentCandidate_nonplain_source hfirst (by omega)
  obtain ⟨_, _, hsecondSource⟩ := componentCandidate_nonplain_source hsecond (by omega)
  obtain ⟨first0, hfirst0, hfirstDecl, hfirstBorder0, hfirstPath⟩ :=
    rnc_revKey execution hfirstSource
  obtain ⟨second0, hsecond0, hsecondDecl, hsecondBorder0, hsecondPath⟩ :=
    rnc_revKey execution hsecondSource
  have hfirstGroup : first0.border = -2 := hfirstBorder0.trans hfirstBorder
  have hsecondGroup : second0.border = -2 := hsecondBorder0.trans hsecondBorder
  obtain ⟨_, firstBox, hfirstBox, _, hfirstOrigin⟩ :=
    measuredGraph_group_origin execution.graph0_eq hfirst0 hfirstGroup
  obtain ⟨_, secondBox, hsecondBox, _, hsecondOrigin⟩ :=
    measuredGraph_group_origin execution.graph0_eq hsecond0 hsecondGroup
  constructor
  · intro hp
    have hlast := congrArg List.getLast? hp
    have hdecl : first0.decl = second0.decl := by
      simpa [← hfirstPath, ← hsecondPath, hfirstOrigin, hsecondOrigin] using hlast
    rw [← hfirstDecl, ← hsecondDecl]
    exact hdecl
  · intro hd
    have hdecl : first0.decl = second0.decl := by
      rw [hfirstDecl, hsecondDecl]
      exact hd
    rw [hdecl] at hfirstBox hfirstOrigin
    have hbox : firstBox = secondBox := Option.some.inj (hfirstBox.symm.trans hsecondBox)
    rw [← hfirstPath, ← hsecondPath, hfirstOrigin, hsecondOrigin, hbox]
private theorem rnc_proxy_side_source {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner sideIndex : Nat) (side : ProperNode),
      node.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some owner ∧
      rk run.coordinateProper.rank sideIndex = rk run.coordinateProper.rank index := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRunX_spec h
  obtain ⟨owner, span, howner, hspan⟩ :=
    proxyWidths_proxy_span_source hproxy hnode hborder
  obtain ⟨sideIndex, side, hside, hsideBorder, hsideOwner, hsideRank⟩ :=
    proxySpan_side_source hspan
  exact ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, hsideRank⟩


private theorem rnc_side_original {P : Params} {exact : List Nat} {source : Proper}
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)))
    {index : Nat} {side : ProperNode}
    (hside : (coordinateGraphX P exact source).nodes[index]? = some side)
    (hborder : side.node.border = -1 ∨ side.node.border = 1) :
    (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source))
        P.clusterBorderW).nodes[index]? = some side := by
  have hwf : OrderImpl.BordersWellFormed (coordinateGraphX P exact source) := by
    unfold coordinateGraphX
    exact materializeDummyPaths_bordersWellFormed
      (clearProxyExtents_bordersWellFormed
        (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hreal : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
        have hz := hwf.2.2 index side hside hd
        rcases hborder with hborder | hborder <;> omega
  obtain ⟨cleared, hcleared, hd, _, _, heq⟩ :=
    materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)) hside
  have hclearedReal : cleared.dummy = false := hd.symm.trans hreal
  have hsame : side = cleared := heq hclearedReal
  have hclearLookup : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some side := by
    rw [hsame]
    exact hcleared
  rw [clearProxyExtents_nodes, List.getElem?_map] at hclearLookup
  obtain ⟨original, horiginal, hclearEq⟩ := Option.map_eq_some_iff.mp hclearLookup
  have hb : side.node.border = original.node.border := by
    rw [← hclearEq]
    exact (clearF_keys original).2.1
  have hoside : original.node.border = -1 ∨ original.node.border = 1 := by
    rwa [hb] at hborder
  have hclearId : clearF original = original := by
    unfold clearF
    rcases hoside with hoside | hoside <;> simp [hoside]
  exact horiginal.trans (congrArg some (hclearId.symm.trans hclearEq))


private theorem rnc_titled_group_owner_unique {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {source : Proper}
    (hkeys : NodeKeys (componentCandidate execution.graph comp candidate) source)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
        source.nodes[index]? = some ⟨node, false, none, false⟩)
    {a b : Nat} {first second : ProperNode}
    (hfirst : (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) source)).nodes[a]? = some first)
    (hsecond : (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) source)).nodes[b]? = some second)
    (hfirstBorder : first.node.border = -2) (hsecondBorder : second.node.border = -2)
    (howner : first.node.clusterPath.getLast? = second.node.clusterPath.getLast?) :
    a = b := by
  obtain ⟨oa, hoa, hba, hea⟩ :=
    rnc_titled_marker_source_record hkeys hrecords hfirst (Or.inl hfirstBorder)
  obtain ⟨ob, hob, hbb, heb⟩ :=
    rnc_titled_marker_source_record hkeys hrecords hsecond (Or.inl hsecondBorder)
  have hgroupA : oa.border = -2 := hba.symm.trans hfirstBorder
  have hgroupB : ob.border = -2 := hbb.symm.trans hsecondBorder
  obtain ⟨_, _, hoaSource⟩ := componentCandidate_nonplain_source hoa (by omega)
  obtain ⟨_, _, hobSource⟩ := componentCandidate_nonplain_source hob (by omega)
  obtain ⟨oa0, ha0, hdA0, hbA0, hpA0⟩ := rnc_revKey execution hoaSource
  obtain ⟨ob0, hb0, hdB0, hbB0, hpB0⟩ := rnc_revKey execution hobSource
  have hgroupA0 : oa0.border = -2 := hbA0.trans hgroupA
  have hgroupB0 : ob0.border = -2 := hbB0.trans hgroupB
  obtain ⟨_, boxA, _, _, hpathA⟩ :=
    measuredGraph_group_origin execution.graph0_eq ha0 hgroupA0
  obtain ⟨_, boxB, _, _, hpathB⟩ :=
    measuredGraph_group_origin execution.graph0_eq hb0 hgroupB0
  have hlastA : first.node.clusterPath.getLast? = some oa.decl := by
    rw [hea, (titleF_keys _).2.2.1, ← hpA0, hpathA]
    simp [hdA0]
  have hlastB : second.node.clusterPath.getLast? = some ob.decl := by
    rw [heb, (titleF_keys _).2.2.1, ← hpB0, hpathB]
    simp [hdB0]
  have hdecl : oa.decl = ob.decl := by
    rw [hlastA, hlastB] at howner
    exact Option.some.inj howner
  have hpath := (rnc_group_path_iff_decl execution hoa hob
    hgroupA hgroupB).mpr hdecl
  exact (componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (rnc_cgShape execution) candidate).1 a b oa ob hoa hob hgroupA hgroupB hpath



private theorem rnc_prepared_group_side {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {labeled : Proper}
    (hc : coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
      run.coordinateProper)
    (_hk : NodeKeys (componentCandidate execution.graph comp candidate) labeled)
    (hready : OrderImpl.BorderConstructionReady (titleReservations
      (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)))
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
        labeled.nodes[key]? = some ⟨original, false, none, false⟩)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (requested proxy : ProperNode) (owner sideIndex : Nat) (side : ProperNode),
      requested = titleF ⟨node, false, none, false⟩ ∧
      proxy = clearF requested ∧
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[index]? = some requested ∧
      run.coordinateProper.nodes[index]? = some proxy ∧
      (coordinateGraphX execution.params
        (exactDecls exactIds inp) labeled).nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some owner ∧
      proxy.node.clusterPath.getLast? = some owner ∧
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled))
        execution.params.clusterBorderW).nodes[sideIndex]? = some side := by
  let requested : ProperNode := titleF ⟨node, false, none, false⟩
  let proxy : ProperNode := clearF requested
  have hrequested : (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).nodes[index]? =
      some requested := rnc_titled_marker_record (hrecords index node hnode) (Or.inl hgroup)
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact rnc_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys requested).2.1.trans ((titleF_keys _).2.1.trans hgroup)
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    rnc_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  have hsideCoordinate : (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).nodes[sideIndex]? = some side := by
    rw [hc]
    exact hside
  have hsideOriginal := rnc_side_original hready hsideCoordinate hsideBorder
  exact ⟨requested, proxy, owner, sideIndex, side, rfl, rfl, hrequested, hproxy,
    hsideCoordinate, hsideBorder, hsideOwner, howner, hsideOriginal⟩

private theorem rnc_prepared_group_bottom {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {labeled : Proper}
    (hc : coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
      run.coordinateProper)
    (hk : NodeKeys (componentCandidate execution.graph comp candidate) labeled)
    (hready : OrderImpl.BorderConstructionReady (titleReservations
      (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)))
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
        labeled.nodes[key]? = some ⟨original, false, none, false⟩)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ bottom : ProperNode × Nat,
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
          some bottom := by
  obtain ⟨requested, proxy, owner, _, side, hreqId, hproxyId, hrequested,
      _, _, hsideBorder, hsideOwner, howner, hsideOriginal⟩ :=
    rnc_prepared_group_side execution hcomp hrun hc hk hready hrecords hnode hgroup
  obtain ⟨anchor, hanchor, bottom, hbottom, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hsideOriginal)
      hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  have hownerEq : anchor.1.node.clusterPath.getLast? =
      requested.node.clusterPath.getLast? := by
    have hsp : side.node.clusterPath.getLast? = proxy.node.clusterPath.getLast? :=
      hsideOwner.trans howner.symm
    rw [hproxyId] at hsp
    rw [← hpath, hsp, (clearF_keys requested).2.2.1]
  have hrequestBorder : requested.node.border = -2 := by
    rw [hreqId]; exact (titleF_keys _).2.1.trans hgroup
  have hindex := rnc_titled_group_owner_unique execution hcomp hk hrecords
    hanchorLookup hrequested hanchorBorder hrequestBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[anchor.2]? = some requested := by
    rw [hindex]
    exact hrequested
  have hanchorEq : anchor.1 = requested :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  refine ⟨bottom, ?_, ?_⟩
  · rw [← hreqId]; exact hrequested
  · rw [hanchorEq, hreqId] at hbottom
    simpa only [titleF, hgroup, beq_self_eq_true, Bool.true_or,
      ↓reduceIte] using hbottom
private theorem rnc_group_bottom_source {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper) (bottom : ProperNode × Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
        run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
          some bottom := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
    rnc_prepared_titled_source execution hcomp hrun
  obtain ⟨bottom, htitled, hbottom⟩ :=
    rnc_prepared_group_bottom execution hcomp hrun hc hk hready hrecords hnode hgroup
  exact ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩
private theorem rnc_bottom_find_candidate {cg : Graph} {P : Params} {exact : List Nat}
    {source : Proper}
    (hrecords : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      source.nodes[index]? = some ⟨node, false, none, false⟩)
    {path : List Nat} {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == path) = some bottom)
    {original : Node}
    (horiginal : cg.nodes[bottom.2]? = some original)
    (horiginalBorder : original.border = 2) (horiginalPath : original.clusterPath = path) :
    ((cg.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.clusterPath == path) =
        some (original, bottom.2)) := by
  obtain ⟨_, position, hposition, hpositionRecord, hbefore⟩ :=
    List.find?_eq_some_iff_getElem.mp hfind
  have hpositionIndex : position = bottom.2 := by
    simpa only [List.getElem_zipIdx, Nat.zero_add] using
      congrArg Prod.snd hpositionRecord
  have hsourceZip : cg.nodes.zipIdx[bottom.2]? =
      some (original, bottom.2) := by
    simp only [List.getElem?_zipIdx, horiginal, Option.map_some, Nat.zero_add]
  obtain ⟨hsourceBound, hsourceRecord⟩ := List.getElem?_eq_some_iff.mp hsourceZip
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp [horiginalBorder, horiginalPath], bottom.2, hsourceBound,
    hsourceRecord, ?_⟩
  intro earlier hearlier
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  apply Bool.eq_false_iff.mpr
  intro hmatch
  have hearlierSource : earlier < cg.nodes.length := by
    have hlen : cg.nodes.length = cg.nodes.zipIdx.length := by
      simp only [List.length_zipIdx]
    omega
  let previous := cg.nodes[earlier]'hearlierSource
  have hprevious : cg.nodes[earlier]? = some previous :=
    List.getElem?_eq_getElem hearlierSource
  have hpreviousMatch : previous.border = 2 ∧ previous.clusterPath = path := by
    simpa only [List.getElem_zipIdx, Nat.zero_add, Bool.and_eq_true, beq_iff_eq] using hmatch
  have hforward := rnc_titled_marker_record (P := P) (exact := exact)
    (hrecords earlier previous hprevious) (Or.inr hpreviousMatch.1)
  have hprior := hbefore earlier (by omega)
  have htargetZip :
      (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx[earlier]? =
        some (titleF ⟨previous, false, none, false⟩, earlier) := by
    simp only [List.getElem?_zipIdx, hforward, Option.map_some, Nat.zero_add]
  rw [(List.getElem?_eq_some_iff.mp htargetZip).2] at hprior
  simp [titleF, hpreviousMatch.1, hpreviousMatch.2] at hprior
private theorem rnc_group_bottom_path_iff_decl {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {index : Nat} {top bottom : Node} (htop : execution.graph.nodes[index]? = some top)
    (hgroup : top.border = -2) (hbottom : bottom ∈ execution.graph.nodes)
    (hbottomBorder : bottom.border = 2) :
    bottom.clusterPath = top.clusterPath ↔ bottom.decl = top.decl := by
  obtain ⟨top0, htop0, hdTop, hbTop, hpTop⟩ := rnc_revKey execution htop
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hbottom
  obtain ⟨bottom0, hbottom0, hdBottom, hbBottom, hpBottom⟩ := rnc_revKey execution hbi
  have hgroup0 : top0.border = -2 := hbTop.trans hgroup
  have hborder0 : bottom0.border = 2 := hbBottom.trans hbottomBorder
  have hkey := measuredGraph_group_bottom_path_iff_decl execution.graph0_eq htop0
    hgroup0 (List.mem_of_getElem? hbottom0) hborder0
  rw [← hpBottom, ← hpTop, ← hdBottom, ← hdTop]
  exact hkey

private theorem rnc_bottom_lookup_keys {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate index : Nat} {top : Node}
    (htop : (componentCandidate execution.graph comp candidate).nodes[index]? = some top)
    (hgroup : top.border = -2) :
    ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.clusterPath == top.clusterPath) =
    ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.decl) := by
  obtain ⟨_, _, htopSource⟩ := componentCandidate_nonplain_source htop (by omega)
  apply RankImpl.find?_congr'
  intro entry hentry
  by_cases hb : entry.1.border = 2
  · have hentryLookup := List.mem_zipIdx_iff_getElem?.mp hentry
    obtain ⟨_, _, hbottomSource⟩ :=
      componentCandidate_nonplain_source hentryLookup (by omega)
    have hkey := rnc_group_bottom_path_iff_decl execution htopSource hgroup
      (List.mem_of_getElem? hbottomSource) hb
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun h => ⟨h.1, hkey.mp h.2⟩, fun h => ⟨h.1, hkey.mpr h.2⟩⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun h => (hb h.1).elim, fun h => (hb h.1).elim⟩
private theorem rnc_bottom_find_source {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {source : Proper}
    (hkeys : NodeKeys (componentCandidate execution.graph comp candidate) source)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
        source.nodes[index]? = some ⟨node, false, none, false⟩)
    {path : List Nat} {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == path) = some bottom) :
    ∃ original : Node,
      (componentCandidate execution.graph comp candidate).nodes[bottom.2]? =
        some original ∧
      original.border = 2 ∧ original.clusterPath = path ∧
      bottom.1 = titleF ⟨original, false, none, false⟩ ∧
      ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.clusterPath == path) =
          some (original, bottom.2) := by
  have hbottomLookup := List.mem_zipIdx_iff_getElem?.mp
    (List.mem_of_find?_eq_some hfind)
  have hpredicate := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpredicate
  obtain ⟨original, horiginal, hborder, hrecord⟩ :=
    rnc_titled_marker_source_record hkeys hrecords hbottomLookup (Or.inr hpredicate.1)
  have horiginalBorder : original.border = 2 := hborder.symm.trans hpredicate.1
  have horiginalPath : original.clusterPath = path := by
    simpa [hrecord, titleF, horiginalBorder] using hpredicate.2
  refine ⟨original, horiginal, horiginalBorder, horiginalPath, hrecord, ?_⟩
  exact rnc_bottom_find_candidate hrecords hfind horiginal horiginalBorder horiginalPath



private theorem rnc_bottom_constraint_source {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate index : Nat} {source : Proper} {node : Node}
    (hkeys : NodeKeys (componentCandidate execution.graph comp candidate) source)
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
        source.nodes[key]? = some ⟨original, false, none, false⟩)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == node.clusterPath) = some bottom) :
    ∃ original : Node,
      (componentCandidate execution.graph comp candidate).nodes[bottom.2]? = some original ∧
      original.border = 2 ∧ original.clusterPath = node.clusterPath ∧
      bottom.1 = titleF ⟨original, false, none, false⟩ ∧
      ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == node.decl) = some (original, bottom.2) := by
  obtain ⟨original, horiginal, hborder, hpath, hrecord, hsourceFind⟩ :=
    rnc_bottom_find_source execution hkeys hrecords hfind
  refine ⟨original, horiginal, hborder, hpath, hrecord, ?_⟩
  rw [← rnc_bottom_lookup_keys execution hnode hgroup]
  exact hsourceFind

private theorem rnc_group_member_borders {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
    ∃ left right : Nat,
      run.coordinateProper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? =
        some (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank memberIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank memberIndex := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩ :=
    rnc_group_bottom_source execution hcomp hrun hnode hgroup
  obtain ⟨originalBottom, horiginalBottom, _, _, _, hconstraintBottom⟩ :=
    rnc_bottom_constraint_source execution hk hrecords hnode hgroup hbottom
  have hinterval := ranked_compound_member_interval hrr (List.mk_mem_zipIdx_iff_getElem?.mpr hnode)
    hgroup hconstraintBottom (List.mk_mem_zipIdx_iff_getElem?.mpr hmember) hplain hinside
  have htopRank := rnc_titled_original_rk (P := execution.params) (exact := exactDecls exactIds inp)
    hrr hranks (List.getElem?_eq_some_iff.mp hnode).1
  have hmemberRank := rnc_titled_original_rk (P := execution.params) (exact := exactDecls exactIds inp)
    hrr hranks (List.getElem?_eq_some_iff.mp hmember).1
  have hbottomRank := rnc_titled_original_rk (P := execution.params) (exact := exactDecls exactIds inp)
    hrr hranks (List.getElem?_eq_some_iff.mp horiginalBottom).1
  have hbottomForTop :
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨node, false, none, false⟩).node.clusterPath) =
        some bottom := by
    simpa [titleF, hgroup] using hbottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    rnc_coordinate_rank_pair execution.params (exactDecls exactIds inp) labeled
      hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitled) ((titleF_keys _).2.1.trans hgroup)
      hbottomForTop (rank := (rk rr.ranks memberIndex).toNat)
      (by dsimp only at hinterval htopRank hmemberRank hbottomRank ⊢; omega)
      (by dsimp only at hinterval htopRank hmemberRank hbottomRank ⊢; omega)
  have hmemberCoordinate := (rnc_coordinate_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks (List.getElem?_eq_some_iff.mp hmember).1)
  have hnatcast : ((rk rr.ranks memberIndex).toNat : Int) = rk rr.ranks memberIndex := by
    omega
  have hleftValue : rk (coordinateGraphX execution.params (exactDecls exactIds inp) labeled).rank left =
      rk rr.ranks memberIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hnatcast
  have hrightValue : rk (coordinateGraphX execution.params (exactDecls exactIds inp) labeled).rank right =
      rk rr.ranks memberIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hnatcast
  rw [← hc]; exact ⟨left, right, hleft, hright, hleftValue.trans hmemberCoordinate.symm,
    hrightValue.trans hmemberCoordinate.symm⟩

private theorem rnc_member_path_prefix {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    node.clusterPath <+: member.clusterPath := by
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := rnc_revKey execution hgroupSource
  have hnonempty : member.clusterPath ≠ [] := by
    intro hempty
    simp [hempty] at hinside
  obtain ⟨_, _, hmemberSource⟩ :=
    componentCandidate_nonempty_path_source hmember hnonempty
  obtain ⟨member0, hmember0, _hmemberDeclM, hbM, hpM⟩ := rnc_revKey execution hmemberSource
  obtain ⟨groupBox, hgroupBox, hgroupDecl, hgroupPath⟩ :=
    rnc_groupPath execution hgroup0 (hbG.trans hgroup)
  obtain ⟨memberBox, hmemberBox, hmemberDecl, hmemberPath⟩ :=
    rnc_plainPath execution hmember0 (hbM.trans hplain)
  have hin : group0.decl ∈ Compound.path inp.boxes memberBox := by
    have h := hinside
    rw [← hpM, hmemberPath, List.contains_iff_mem] at h
    rwa [← hdG] at h
  have hg : (inputModel inp o).boxes[group0.decl]? = some groupBox := by
    rw [hgroupDecl]
    exact hgroupBox
  have hm : (inputModel inp o).boxes[member0.decl]? = some memberBox := by
    rw [hmemberDecl]
    exact hmemberBox
  have hprefix := Compound.path_ancestor_prefix (inputModel inp o) hwf hg hm hin
  rw [← hpG, hgroupPath, ← hgroupDecl, ← hpM, hmemberPath]
  exact hprefix
private theorem rnc_bordersWellFormed {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨_, labeled, _, hc, _, hready, _, _⟩ :=
    rnc_prepared_titled_source execution hcomp hrun
  rw [← hc]
  unfold coordinateGraphX
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready

private theorem rnc_member_bracket_setup {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    ∃ (actual : ProperNode) (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧
      ord.layers = run.layers ∧
      run.coordinateProper.nodes[memberIndex]? = some actual ∧
      run.proper.nodes[memberIndex]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = member.clusterPath ∧
      run.xs.getD memberIndex 0 = run.coordinateXs.getD memberIndex 0 ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank memberIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank memberIndex ∧
      OrderImpl.lay run.coordinateProper left =
        OrderImpl.lay run.coordinateProper memberIndex ∧
      OrderImpl.lay run.coordinateProper right =
        OrderImpl.lay run.coordinateProper memberIndex ∧
      OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨actual, hcoordinate, hproper, hreal, hactualPlain, hactualPath,
      _, _, _, hx⟩ :=
    rnc_original_plain_record hrun hmember hplain
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    rnc_group_member_borders execution hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hwformed := rnc_bordersWellFormed execution hcomp hrun
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper memberIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper memberIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  exact ⟨actual, ord, left, right, horder, hlayers, hcoordinate, hproper, hreal,
    hactualPlain, hactualPath, hx, hleft, hright, hleftRank, hrightRank, hleftLay,
    hrightLay, hwformed⟩


private theorem rnc_member_bracket {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    ∃ (actual : ProperNode) (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧ ord.layers = run.layers ∧
      run.coordinateProper.nodes[memberIndex]? = some actual ∧
      run.proper.nodes[memberIndex]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = member.clusterPath ∧
      run.xs.getD memberIndex 0 = run.coordinateXs.getD memberIndex 0 ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left memberIndex right := by
  obtain ⟨actual, ord, left, right, horder, hlayers, hcoordinate, hproper, hreal,
    hactualPlain, hactualPath, hx, hleft, hright, _, _, hleftLay, hrightLay,
    hwformed⟩ :=
    rnc_member_bracket_setup execution hcomp hrun hnode hgroup hmember hplain hinside
  have hprefix := rnc_member_path_prefix execution hwf hnode hgroup hmember hplain hinside
  have hsidePrefix :
      (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
        execution.params.clusterBorderW).node.clusterPath <+: actual.node.clusterPath := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath <+: actual.node.clusterPath
    rw [(titleF_keys _).2.2.1, hactualPath]
    exact hprefix
  have hleftNe : left ≠ memberIndex := by
    intro heq
    rw [heq] at hleft
    have hn := Option.some.inj (hleft.symm.trans hcoordinate)
    have hb := congrArg (fun value : ProperNode => value.node.border) hn
    change (-1 : Int) = actual.node.border at hb
    omega
  have hrightNe : right ≠ memberIndex := by
    intro heq
    rw [heq] at hright
    have hn := Option.some.inj (hright.symm.trans hcoordinate)
    have hb := congrArg (fun value : ProperNode => value.node.border) hn
    change (1 : Int) = actual.node.border at hb
    omega
  refine ⟨actual, ord, left, right, horder, hlayers, hcoordinate, hproper, hreal,
    hactualPlain, hactualPath, hx, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord horder hwformed
    left memberIndex right _ actual _ hleft hcoordinate hright hleftLay hrightLay
    rfl rfl rfl hreal rfl hsidePrefix hsidePrefix hleftNe hrightNe

private theorem rnc_coordinate_alignment {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ labeled : Proper, coordinateGraphX P exact labeled = run.coordinateProper ∧
      NodeKeys cg labeled ∧ labeled.nodes.length = labeled.rank.length ∧
      (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
        (titleReservations (sizeProperPortsX P exact labeled)).rank.length := by
  obtain ⟨_, normalized, labeled, _, hn, hl, hc, _⟩ := rnc_ranked_source h
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  exact ⟨labeled, hc, addLabelNodes_keys _ _ _ (normalize_keys hn) hl,
    haligned, rnc_titled_alignment P exact haligned⟩

private theorem rnc_member_border_sep {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    ∃ (actual : ProperNode) (left right : Nat),
      run.proper.nodes[memberIndex]? = some actual ∧
      actual.node.clusterPath = member.clusterPath ∧
      run.coordinateProper.nodes[memberIndex]? = some actual ∧
      run.xs.getD memberIndex 0 = run.coordinateXs.getD memberIndex 0 ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      coordSep (min execution.params.nodeGap execution.params.clusterPad)
        run.coordinateProper left memberIndex ≤
        run.coordinateXs.getD memberIndex 0 - run.coordinateXs.getD left 0 ∧
      coordSep (min execution.params.nodeGap execution.params.clusterPad)
        run.coordinateProper memberIndex right ≤
        run.coordinateXs.getD right 0 - run.coordinateXs.getD memberIndex 0 := by
  obtain ⟨actual, ord, left, right, _, hlayers, hcoordinate, hproper, _, hactualPlain,
    hactualPath, hx, hleft, hright, hbracket⟩ :=
    rnc_member_bracket execution hwf hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨labeled, hc, hk, _, _⟩ := rnc_coordinate_alignment hrun
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (rnc_cgShape execution) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact rnc_pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb)
      hba hbb hp
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi left memberIndex _ _ hlt hli hmi hleft hcoordinate
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    mi ri memberIndex right _ _ htr hmi hri hcoordinate hright
    (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  exact ⟨actual, left, right, hproper, hactualPath, hcoordinate, hx, hleft, hright,
    hleftSep, hrightSep⟩

/-- Region run with `none` spec coincides with the exact run, with the graph. -/
private theorem rnc_runR_none_eq {P : Params} {exact : List Nat} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact none inp cg labels orderOptions = .ok (cg', run)) :
    componentRunX P exact cg labels orderOptions = .ok run ∧ cg' = cg := by
  have hmap := (componentRunR_none P exact inp cg labels orderOptions) ▸ h
  cases hX0 : componentRunX P exact cg labels orderOptions with
  | error e =>
    simp only [hX0, Except.map] at hmap
    cases hmap
  | ok r =>
    simp only [hX0, Except.map] at hmap
    obtain ⟨hcg, hr⟩ := Prod.mk.inj (Except.ok.inj hmap)
    exact ⟨congrArg Except.ok hr, hcg.symm⟩

/-- Region member border intervals upgrade to the parent frame interval. -/
private theorem rnc_member_border_interval {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    ∃ actual : ProperNode, run.proper.nodes[memberIndex]? = some actual ∧
      actual.node.clusterPath = member.clusterPath ∧
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate)
        run index).x ≤
        (Labels.rectAt run.proper run.xs run.ys memberIndex).x ∧
      (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
        (Labels.rectAt run.proper run.xs run.ys memberIndex).w ≤
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate)
          run index).x +
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate)
          run index).w := by
  obtain ⟨actual, left, right, hproper, hactualPath, hcoordinate, hx, hleft, hright,
    hleftSep, hrightSep⟩ :=
    rnc_member_border_sep execution hwf hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨hleftFinal, hleftX⟩ := rnc_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ := rnc_border_record hrun hright (Or.inr rfl)
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  have hactualWidth := (sizesNonneg_lookup hsizes memberIndex actual hcoordinate).1
  have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
  have hrightWidth := (sizesNonneg_lookup hsizes right _ hright).1
  have hactualLoops : 0 ≤ (actual.node.loopExtent : Int) := Int.natCast_nonneg _
  have hgroupLoops : 0 ≤ (node.loopExtent : Int) := Int.natCast_nonneg _
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  change 0 ≤ execution.params.clusterBorderW at hleftWidth hrightWidth
  have hleftInterval :
      (Labels.rectAt run.proper run.xs run.ys left).x ≤
        (Labels.rectAt run.proper run.xs run.ys memberIndex).x := by
    simp only [coordSep, CoordsImpl.nodeW, hleft, hcoordinate,
      OrderImpl.borderLeft] at hleftSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hproper, hleftX, hx, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  have hrightInterval :
      (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
          (Labels.rectAt run.proper run.xs run.ys memberIndex).w ≤
        (Labels.rectAt run.proper run.xs run.ys right).x +
          (Labels.rectAt run.proper run.xs run.ys right).w := by
    simp only [coordSep, CoordsImpl.nodeW, hcoordinate, hright, OrderImpl.borderRight,
      titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hrightSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hproper, hrightFinal, hx, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega
  have hgroupGet :
      (componentCandidate execution.graph comp candidate).nodes.getD index default =
        node := by
    simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := rnc_revKey execution hgroupSource
  obtain ⟨box, _, hdeclG, hpath0⟩ := rnc_groupPath execution hgroup0 (hbG.trans hgroup)
  have hgroupPath : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
    rw [← hpG, hpath0, ← hdeclG, hdG]
  have hframeGroup :
      ((componentCandidate execution.graph comp candidate).nodes.getD index default).border =
        -2 := by
    rw [hgroupGet]
    exact hgroup
  have hleftPath :
      (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
        execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++
          [((componentCandidate execution.graph comp candidate).nodes.getD index
            default).decl] := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hgroupGet]
    exact hgroupPath
  have hrightPath :
      (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
        execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++
          [((componentCandidate execution.graph comp candidate).nodes.getD index
            default).decl] := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
    exact hleftPath
  have hleftContained :=
    frameRect_side_marker_contained (P := execution.params)
      (cg := componentCandidate execution.graph comp candidate)
      hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleftFinal) (Or.inl rfl) hleftPath
  have hrightContained :=
    frameRect_side_marker_contained (P := execution.params)
      (cg := componentCandidate execution.graph comp candidate)
      hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal) (Or.inr rfl)
      hrightPath
  refine ⟨actual, hproper, hactualPath,
    Int.le_trans hleftContained.1 hleftInterval,
    Int.le_trans hrightInterval hrightContained.2.1⟩

/-- Plain-member x-bracket for runs with `spec' = none. -/
private theorem R_regionNestPlain_none_holds {exactIds : List String}
    {idSets : List (String × List String)} :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (cg' : Graph)
    (run : Run) (orderOptions : OrderOptions),
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) none inp
      (componentCandidateR none execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg', run) →
    ∀ (index memberIndex : Nat) (node member : Node),
      (componentCandidateR none execution.graph comp candidate).nodes[index]? =
        some node →
      node.border = -2 →
      (componentCandidateR none execution.graph comp candidate).nodes[memberIndex]? =
        some member →
      member.border = 0 → member.clusterPath.contains node.decl = true →
      ∃ actual : ProperNode, run.proper.nodes[memberIndex]? = some actual ∧
        actual.node.clusterPath = member.clusterPath ∧
        (frameRect execution.params
          (componentCandidateR none execution.graph comp candidate)
          run index).x ≤
          (Labels.rectAt run.proper run.xs run.ys memberIndex).x ∧
        (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
          (Labels.rectAt run.proper run.xs run.ys memberIndex).w ≤
          (frameRect execution.params
            (componentCandidateR none execution.graph comp candidate)
            run index).x +
          (frameRect execution.params
            (componentCandidateR none execution.graph comp candidate)
            run index).w := by
  intro inp o res execution hwf hframed comp candidate cg' run orderOptions hcomp hrun
  intro index memberIndex node member hnode hgroup hmember hplain hinside
  rw [componentCandidateR_none] at hnode hmember hrun ⊢
  obtain ⟨hX, hcg⟩ := rnc_runR_none_eq hrun
  subst hcg
  exact rnc_member_border_interval execution hwf hcomp hX hnode hgroup hmember hplain
    hinside

/-- The region nesting residual from its `some` and group halves. -/
theorem R_regionNestResidual_of_some_group {exactIds : List String}
    {idSets : List (String × List String)}
    (hsome : R_RegionNestSomeResidual exactIds idSets)
    (hgroup : R_RegionNestGroupResidual exactIds idSets) :
    R_RegionNestResidual exactIds idSets := by
  constructor
  · intro inp o res execution hwf hframed comp candidate spec' cg' run orderOptions
      hcomp hrun index memberIndex node member hnode hgroupB hmember hplain hinside
    cases spec' with
    | none =>
      exact R_regionNestPlain_none_holds execution hwf hframed comp candidate cg' run
        orderOptions hcomp hrun index memberIndex node member hnode hgroupB hmember
        hplain hinside
    | some s =>
      exact hsome execution hwf hframed comp candidate (some s) cg' run orderOptions
        rfl hcomp hrun index memberIndex node member hnode hgroupB hmember hplain
        hinside
  · exact hgroup

/-- The full member-frame nesting from the two region residuals. -/
theorem R_memberFramesNestR_closed {exactIds : List String}
    {idSets : List (String × List String)}
    (hsome : R_RegionNestSomeResidual exactIds idSets)
    (hgroup : R_RegionNestGroupResidual exactIds idSets) :
    R_MemberFramesNestR exactIds idSets :=
  R_memberFramesNestR_holds (R_regionNestResidual_of_some_group hsome hgroup)

end PipelineImpl


end Layered
end Elegant
