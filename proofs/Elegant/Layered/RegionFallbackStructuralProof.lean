import Elegant.Layered.RegionFallbackCaption
import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionReduction
import Elegant.Layered.LabelsC8b
import Elegant.Layered.InputFixedFit
import Elegant.Layered.ExactCaptionTitleBranchProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region fallback structural facts.

Proves two of the three structural leaves consumed by
`R_fallbackCaptionClearB8W_closed` (`RegionFallbackCaption.lean`):

* `R_NonfixedGroupTitle` (`R_nonfixedGroupTitle_holds`): a non-fixed group box
  records an installed title;
* `R_FallbackOwnerCasesW` (`R_fallbackOwnerCasesW_holds`): a title-less owner
  is a node or is fixed.

The third leaf, `R_FixedOwnerFit`, is narrowed: `R_fixedOwnerFit_none_holds`
proves it for empty region sets by transport from the exact twin
`xctb_fixedOwnerFitX_holds`, and `R_fixedOwnerFit_of_dominates` reduces the
general case to the strictly narrower packed-domination residual
`R_FixedBoxDominates`.

Probe evidence (`proofs/wip/Probe/RegionFallbackStructuralTProbe.lean`,
vector profile, `layoutRIds` recomputed phases): the title/cases mirrors hold
on every executed row (flat with and without region sets, nested, self-loop,
fixed boxes, fixed group, empty group, duplicate-id row); the fix mirror
holds wherever fixed boxes with fitting captions occur and fails only on the
zero-size fixed box whose caption cannot fit (so the `InputFixedFit` premise
is false there). The flat-with-sets row takes the region arm
(`rs.isSome = true`), so the region-arm transport below is exercised.
-/

/-- Peel helper (prefixed copy: `bind_ok` is private in every module). -/
private theorem rfs_bind_ok {α β : Type}
    {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Region lines cover every input box (copy of `xfs_lines_length`). -/
private theorem rfs_lines_length {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
      (mapM_getElem? _ _ _ h).1
    _ = inp.boxes.length := List.length_zipIdx

/-- Packing preserves the rect array size (copy of `xfs_packFold_rects_size`). -/
private theorem rfs_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- Region packed rect array size (via `SceneExecutionR.components_rects_sizeR`). -/
private theorem rfs_packedAcc_rects_sizeR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := rfs_bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width
      canvasH := packed.height
      titles := [] }).rects.size = inp.boxes.length
  rw [rfs_packFold_rects_size]
  exact execution.components_rects_sizeR

/-- Region packed rect existence from the input length. -/
private theorem rfs_packed_rect_existsR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {i : Nat} (hi : i < inp.boxes.length) :
    ∃ rect, execution.packedAcc.rects[i]? = some rect := by
  have hsize : i < execution.packedAcc.rects.size := by
    rw [rfs_packedAcc_rects_sizeR execution]
    exact hi
  exact ⟨execution.packedAcc.rects[i],
    Array.getElem?_eq_some_iff.mpr ⟨hsize, rfl⟩⟩

/-- Forward title transport through the packing fold (copy of `xfs_titles_mono`). -/
private theorem rfs_titles_mono (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) {t : Nat × Rect} (hmem : t ∈ start.titles) :
    t ∈ (pairs.foldl packStep start).titles := by
  induction pairs generalizing start with
  | nil => exact hmem
  | cons hd tl ih =>
    rw [List.foldl_cons]
    exact ih _ (List.mem_append.mpr (Or.inl hmem))

/-- A part title entry appears in the folded accumulator (copy of
`xfs_titles_fold_mem`). -/
private theorem rfs_titles_fold_mem (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) {q : (List Nat × Part) × Rect} (hmem : q ∈ pairs)
    {r : Nat × Rect} (hr : r ∈ q.1.2.titles) :
    (q.1.1.getD r.1 0, shiftRect q.2.x q.2.y r.2) ∈
      (pairs.foldl packStep start).titles := by
  induction pairs generalizing start with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact rfs_titles_mono tl _ (List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩)))
    · exact ih _ hmem

/-- A specless region run is the exact run (copy of `rpc_runR_none_to_X`). -/
private theorem rfs_runR_none_to_X {P : Params} {exact : List Nat} {inp : Input}
    {cgIn cgOut : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact none inp cgIn labels orderOptions =
      .ok (cgOut, run)) :
    componentRunX P exact cgIn labels orderOptions = .ok run ∧
      cgOut = cgIn := by
  have hmap := (componentRunR_none P exact inp cgIn labels orderOptions).symm.trans h
  cases hX : componentRunX P exact cgIn labels orderOptions with
  | error e =>
    simp only [hX, Except.map] at hmap
    cases hmap
  | ok r =>
    simp only [hX, Except.map] at hmap
    have hpair : (cgIn, r) = (cgOut, run) := Except.ok.inj hmap
    have hcg : cgIn = cgOut := congrArg Prod.fst hpair
    have hrun : r = run := congrArg Prod.snd hpair
    exact ⟨congrArg Except.ok hrun, hcg.symm⟩
/-- Group run data over an executed region scene: the part, position, candidate
node, and actual geometry run (common prefix of `xfs_group_title_run_data`). -/
private theorem rfs_group_part_data {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {k : Nat} {obox : ModelBox}
    (hbox : inp.boxes[k]? = some obox) (hrole : obox.role = .group)
    (hfix : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false) :
    ∃ (part : List Nat × Part) (pIdx pos : Nat) (ndX : Node)
      (index : Nat) (cg : Graph) (run : Run)
      (loops : List (Nat × LoopPlacement)) (area : Int)
      (spec' : Option RegionSpec),
      execution.componentsAcc.parts[pIdx]? = some part ∧
      part.1[pos]? = some k ∧
      execution.graph.nodes[k]? = some ndX ∧ ndX.border = -2 ∧
      componentRunR execution.params (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok (cg, run) ∧
      (componentCandidateR spec' execution.graph part.1 index).nodes[pos]? =
        some ndX ∧
      part.2 = { placeComponentExact execution.params cg run 0
        execution.measured loops with area := area } := by
  have hlines : execution.lines.length = inp.boxes.length :=
    rfs_lines_length execution
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmeta⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hkb : k < inp.boxes.length := (List.getElem?_eq_some_iff.mp hbox).1
  have hi : k < nodes.length := by rw [hlength, hlines]; exact hkb
  have hpreparedSource :
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[k]? = some obox := by
    simp [List.getElem?_map, hbox, hfix]
  have hrecord := Compound.prepare_group_title_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
    execution.params.clusterPad titles
    { nodes := nodes, edges := edges, slot := execution.params.slot }
    hi hpreparedSource hrole
  rw [← hprepared] at hrecord
  obtain ⟨nd0, hnd0, hbord0, hdecl0⟩ : ∃ nd : Node,
      execution.graph0.nodes[k]? = some nd ∧ nd.border = -2 ∧ nd.decl = k := by
    refine ⟨_, hrecord, rfl, ?_⟩
    exact (hmeta k _ (List.getElem?_eq_getElem hi)).1
  obtain ⟨ndX, hndX, hbordX, hpathX, hdeclX⟩ :=
    exactGraph_node_key execution.graph_eq hnd0
  have hbord2 : ndX.border = -2 := hbordX.trans hbord0
  obtain ⟨part, pos, pIdx, hpartMem, hpartsIdx, hpos⟩ :=
    key_part_positionR execution hkb
  obtain ⟨index, chosen, cg, run, loops, area, spec', _, _, _, _, hrun, _,
      hpartdef⟩ :=
    (actual_components_parts_geometryR (by rfl) execution.components_eq).2
      part hpartMem
  exact ⟨part, pIdx, pos, ndX, index, cg, run, loops, area, spec', hpartsIdx,
    hpos, hndX, hbord2, hrun, component_node_lookupR hpos hndX, hpartdef⟩

/-- X copy of `coordinateGraph_title_record` (`CaptionWidthFacts.lean:9`): the
exact coordinate construction keeps a border-`-2` node and appends its
border-`3` title copy. -/
private theorem rfs_coord_title_recordX {P : Params} {exact : List Nat}
    {p : Proper} {i : Nat} {node : ProperNode}
    (hnode : p.nodes[i]? = some node) (hborder : node.node.border = -2)
    (hdummy : node.dummy = false) :
    ∃ j : Nat, (coordinateGraphX P exact p).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
  have hne : (node.node.border != 0) = true := by rw [hborder]; decide
  have hsized : (sizeProperPortsX P exact p).nodes[i]? = some node := by
    simp only [sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx,
      hnode, Option.map_some]
    simp [hne]
  have hmember : (node, i) ∈ titleNodes (sizeProperPortsX P exact p) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_zipIdx_iff_getElem?.mpr hsized, by simp [hborder]⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmember
  have hjlt := (List.getElem?_eq_some_iff.mp hj).1
  have hlength : p.nodes.length + j <
      (titleReservations (sizeProperPortsX P exact p)).nodes.length := by
    rw [titleReservations_nodes]
    simp only [List.length_append, List.length_map, sizeProperPortsX_length]
    omega
  have hreserved : (titleReservations (sizeProperPortsX P exact p)).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
    rw [titleReservations_nodes]
    rw [List.getElem?_append_right (by
      simp only [List.length_map, sizeProperPortsX_length]
      omega : ((sizeProperPortsX P exact p).nodes.map titleF).length ≤ p.nodes.length + j)]
    have hoffset : p.nodes.length + j -
        ((sizeProperPortsX P exact p).nodes.map titleF).length = j := by
      simp only [List.length_map, sizeProperPortsX_length]
      omega
    rw [hoffset, List.getElem?_map, hj]
    rfl
  obtain ⟨extra, hextra, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hborders : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
    rw [hextra, List.getElem?_append_left hlength]
    exact hreserved
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hborders]
    simp [clearF, copyF]
  refine ⟨j, ?_⟩
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  simp [copyF, hdummy]
/-- None-arm title source: a specless run keeps the group title node (copy of
`xfs_componentRun_group_title_sourceX`). -/
private theorem rfs_group_title_source_none {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {pos : Nat} {ndX : Node} (hlocal : cg.nodes[pos]? = some ndX)
    (hbord2 : ndX.border = -2) :
    ∃ (v : Nat) (title : ProperNode), run.proper.nodes[v]? = some title ∧
      title.node.border = 3 ∧ title.node.clusterPath = ndX.clusterPath := by
  obtain ⟨ranks, p0, labeled, q0, hnormalize, hlabels, hcoordinate, -, -,
      hproxy, hdrop, -, -, -⟩ := componentRunX_spec h
  have hnormalized := normalize_node_record hnormalize hlocal
  have hlabeled := addLabelNodes_untouched_node hlabels hnormalized (by rfl)
  obtain ⟨j, hj⟩ := rfs_coord_title_recordX hlabeled hbord2 (by rfl)
  have hcoord : run.coordinateProper.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨ndX, false, none, false⟩, pos)) := by
    rw [← hcoordinate]
    exact hj
  obtain ⟨-, -, -, -, -, hpreserve⟩ := proxyWidths_rel hproxy
  have hrouted : q0.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨ndX, false, none, false⟩, pos)) :=
    (hpreserve _ _ hcoord (by simp [copyF])).1
  have hnodes : run.proper.nodes = q0.nodes := by
    have heq := congrArg Proper.nodes hdrop
    rw [OrderImpl.dropSynthetic_nodes] at heq
    exact heq.symm
  exact ⟨labeled.nodes.length + j, copyF (⟨ndX, false, none, false⟩, pos),
    by rw [hnodes]; exact hrouted, rfl, rfl⟩
/-- Region title reservation node equation (copy of `rfc4TitleReservationsR_nodes`). -/
private theorem rfs_titleReservationsR_nodes (titles : List (Int × Int)) (pad : Int) (p : Proper) : (titleReservationsR titles pad p).nodes = (p.nodes.map fun node => if node.node.border == -2 || node.node.border == 2 then { node with node := { node.node with w := 0, h := 0 } } else node) ++ (p.nodes.zipIdx.filter fun q => q.1.node.border == -2).map fun q => { q.1 with node := { q.1.node with border := 3, loopExtent := 0, h := (titles.getD q.1.node.decl (0, 0)).2 + pad } } := rfl

/-- The some-spec coordinate graph unfolds to the region title reservation. -/
private theorem rfs_coordinateGraphR_some (P : Params) (exact : List Nat)
    (s : RegionSpec) (p : Proper) :
    coordinateGraphR P exact (some s) p =
      materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p))
        P.clusterBorderW)) := rfl
/-- Region-arm title record: the some-spec coordinate construction appends a
border-`3` title copy for the border-`-2` node. -/
private theorem rfs_coord_title_recordR {P : Params} {exact : List Nat}
    {s : RegionSpec} {p : Proper} {i : Nat} {node : ProperNode}
    (hnode : p.nodes[i]? = some node) (hborder : node.node.border = -2)
    (hdummy : node.dummy = false) :
    ∃ j : Nat, (coordinateGraphR P exact (some s) p).nodes[p.nodes.length + j]? = some { node with node := { node.node with border := 3, loopExtent := 0, h := (s.titles.getD node.node.decl (0, 0)).2 + P.clusterPad } } := by
  have hne : (node.node.border != 0) = true := by rw [hborder]; decide
  have hsized : (sizeProperPortsX P exact p).nodes[i]? = some node := by
    simp only [sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hnode, Option.map_some]
    simp [hne]
  have hmember : (node, i) ∈ (sizeProperPortsX P exact p).nodes.zipIdx.filter fun q => q.1.node.border == -2 := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_zipIdx_iff_getElem?.mpr hsized, by simp [hborder]⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmember
  have hjlt := (List.getElem?_eq_some_iff.mp hj).1
  have hlength : p.nodes.length + j < (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p)).nodes.length := by
    rw [rfs_titleReservationsR_nodes]
    simp only [List.length_append, List.length_map, sizeProperPortsX_length]
    omega
  have hreserved : (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p)).nodes[p.nodes.length + j]? = some { node with node := { node.node with border := 3, loopExtent := 0, h := (s.titles.getD node.node.decl (0, 0)).2 + P.clusterPad } } := by
    rw [rfs_titleReservationsR_nodes]
    rw [List.getElem?_append_right (by simp only [List.length_map, sizeProperPortsX_length]; omega : ((sizeProperPortsX P exact p).nodes.map fun node => if node.node.border == -2 || node.node.border == 2 then { node with node := { node.node with w := 0, h := 0 } } else node).length ≤ p.nodes.length + j)]
    have hoffset : p.nodes.length + j - (((sizeProperPortsX P exact p).nodes.map fun node => if node.node.border == -2 || node.node.border == 2 then { node with node := { node.node with w := 0, h := 0 } } else node).length) = j := by simp only [List.length_map, sizeProperPortsX_length]; omega
    rw [hoffset, List.getElem?_map, hj]
    rfl
  obtain ⟨extra, hextra, _⟩ := addClusterBorders_extra (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p)) P.clusterBorderW
  have hborders : (OrderImpl.addClusterBorders (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[p.nodes.length + j]? = some { node with node := { node.node with border := 3, loopExtent := 0, h := (s.titles.getD node.node.decl (0, 0)).2 + P.clusterPad } } := by
    rw [hextra, List.getElem?_append_left hlength]
    exact hreserved
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[p.nodes.length + j]? = some { node with node := { node.node with border := 3, loopExtent := 0, h := (s.titles.getD node.node.decl (0, 0)).2 + P.clusterPad } } := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hborders]
    simp [clearF]
  refine ⟨j, ?_⟩
  rw [rfs_coordinateGraphR_some]
  unfold materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  simp [hdummy]
/-- The `reservedPortsR` cluster fold only raises top-node heights: borders and
cluster paths survive every step (copy of `rpf_reservedPortsR_fold_w` with the
path key in place of the width key). -/
private theorem rfs_reservedPortsR_fold_keys (pl : RegionPlacement)
    (cg : Graph) (labels : List MeasuredLabel)
    (l : List (RegionCluster × Nat))
    (x0 : List Int) (arr : Array ProperNode)
    (ih : ∀ (i : Nat) (m' : ProperNode), arr[i]? = some m' →
      ∃ m, pl.p.nodes[i]? = some m ∧ m'.node.border = m.node.border ∧
        m'.node.clusterPath = m.node.clusterPath)
    (out : List Int × Array ProperNode)
    (h : l.foldlM (fun acc q => do
      let c := q.1
      let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
      if c.titleW < 0 ∨ footprint < 0 then throw LayoutError.domain
      else
        let x ← clusterPortR pl q.2 c.top acc.1
        let x ← clusterPortR pl q.2 c.bottom x
        let top := acc.2.getD c.top default
        let nodes := acc.2.set! c.top { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
        pure (x, nodes)) (x0, arr) = .ok out) :
    ∀ (i : Nat) (m' : ProperNode), out.2[i]? = some m' →
      ∃ m, pl.p.nodes[i]? = some m ∧ m'.node.border = m.node.border ∧
        m'.node.clusterPath = m.node.clusterPath := by
  induction l generalizing x0 arr with
  | nil =>
      intro i m' hm'
      simp only [List.foldlM_nil] at h
      have he := Except.ok.inj h
      subst he
      exact ih i m' hm'
  | cons q l ihl =>
      intro i m' hm'
      simp only [List.foldlM_cons] at h
      obtain ⟨mid, hmid, hrest⟩ := rfs_bind_ok h
      split at hmid
      · simp at hmid
      · obtain ⟨x1, _, hmid⟩ := rfs_bind_ok hmid
        obtain ⟨x2, _, hmid⟩ := rfs_bind_ok hmid
        have he := Except.ok.inj hmid
        have hsetKeys : ∀ (j : Nat) (m'' : ProperNode), mid.2[j]? = some m'' →
            ∃ m, pl.p.nodes[j]? = some m ∧ m''.node.border = m.node.border ∧
              m''.node.clusterPath = m.node.clusterPath := by
          intro j m'' hm''
          rw [← he] at hm''
          dsimp only at hm''
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hm''
          by_cases heq : q.1.top = j
          · subst heq
            rw [ite_eq_left rfl] at hm''
            by_cases hin : q.1.top < arr.size
            · simp only [ite_eq_left hin] at hm''
              have hget : arr[q.1.top]? = some (arr.toList[q.1.top]) := by
                have hlen : q.1.top < arr.toList.length := by
                  rw [Array.length_toList]; exact hin
                have hg := List.getElem?_eq_getElem hlen
                rwa [Array.getElem?_toList] at hg
              obtain ⟨m0, hm0, hb0, hp0⟩ := ih q.1.top _ hget
              refine ⟨m0, hm0, ?_, ?_⟩
              · rw [← Option.some.inj hm'']
                show (arr.getD q.1.top default).node.border = m0.node.border
                rw [Array.getD_eq_getD_getElem?, hget, Option.getD_some]
                exact hb0
              · rw [← Option.some.inj hm'']
                show (arr.getD q.1.top default).node.clusterPath = m0.node.clusterPath
                rw [Array.getD_eq_getD_getElem?, hget, Option.getD_some]
                exact hp0
            · simp only [ite_eq_right hin] at hm''
              simp at hm''
          · simp only [ite_eq_right heq] at hm''
            exact ih j m'' hm''
        have he1 : x2 = mid.1 := congrArg Prod.fst he
        have he2 : (x2, mid.2) = mid := by
          rw [he1]
        rw [← he2] at hrest
        exact ihl x2 mid.2 hsetKeys hrest i m' hm'
/-- `crossCoordsR` keeps borders and cluster paths at every index (copy of
`rpf_crossCoordsR_w` with the path key added). -/
private theorem rfs_crossCoordsR_keys (P : Params) (rm : ComponentRegions)
    (cg : Graph) (labels : List MeasuredLabel) (p : Proper)
    (m : RegionConstraints) (layers : List (List Nat))
    (out : List Int × List (List Nat) × List (Option Int) × Proper)
    (h : crossCoordsR P rm cg labels p m layers = .ok out) :
    ∀ (i : Nat) (n : ProperNode), out.2.2.2.nodes[i]? = some n →
      ∃ m0, p.nodes[i]? = some m0 ∧ n.node.border = m0.node.border ∧
        n.node.clusterPath = m0.node.clusterPath := by
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := rfs_bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    exact absurd h (by simp)
  · obtain ⟨ngs, _, h⟩ := rfs_bind_ok h
    obtain ⟨xcr, _, h⟩ := rfs_bind_ok h
    obtain ⟨_, _, h⟩ := rfs_bind_ok h
    obtain ⟨allocx, _, h⟩ := rfs_bind_ok h
    obtain ⟨xp, hxp, h⟩ := rfs_bind_ok h
    have he := Except.ok.inj h
    have hC : out.2.2.2 = xp.2 :=
      (congrArg (fun q : List Int × List (List Nat) × List (Option Int) × Proper => q.2.2.2) he).symm
    unfold reservedPortsR at hxp
    obtain ⟨fout, hfold, h1⟩ := rfs_bind_ok hxp
    have he1 := Except.ok.inj h1
    have hxp2 : xp.2.nodes = fout.2.toList :=
      (congrArg (fun q : List Int × Proper => q.2.nodes) he1).symm
    have hbase : ∀ (j : Nat) (m' : ProperNode), (p.nodes.toArray)[j]? = some m' →
        ∃ m0, p.nodes[j]? = some m0 ∧ m'.node.border = m0.node.border ∧
          m'.node.clusterPath = m0.node.clusterPath := by
      intro j m' hj
      rw [List.getElem?_toArray] at hj
      exact ⟨m', hj, rfl, rfl⟩
    have hfoldKeys := rfs_reservedPortsR_fold_keys _ cg labels _ _ _ hbase _ hfold
    intro i n hn
    rw [hC, hxp2, Array.getElem?_toList] at hn
    obtain ⟨m0, hm0, hb0, hp0⟩ := hfoldKeys i n hn
    exact ⟨m0, hm0, hb0, hp0⟩
/-- The `reservedPortsR` cluster fold preserves the node array size. -/
private theorem rfs_reservedPortsR_fold_length (pl : RegionPlacement)
    (cg : Graph) (labels : List MeasuredLabel)
    (l : List (RegionCluster × Nat))
    (x0 : List Int) (arr : Array ProperNode)
    (out : List Int × Array ProperNode)
    (h : l.foldlM (fun acc q => do
      let c := q.1
      let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
      if c.titleW < 0 ∨ footprint < 0 then throw LayoutError.domain
      else
        let x ← clusterPortR pl q.2 c.top acc.1
        let x ← clusterPortR pl q.2 c.bottom x
        let top := acc.2.getD c.top default
        let nodes := acc.2.set! c.top { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
        pure (x, nodes)) (x0, arr) = .ok out) :
    out.2.size = arr.size := by
  induction l generalizing x0 arr with
  | nil =>
      simp only [List.foldlM_nil] at h
      have he := Except.ok.inj h
      subst he
      rfl
  | cons q l ihl =>
      simp only [List.foldlM_cons] at h
      obtain ⟨mid, hmid, hrest⟩ := rfs_bind_ok h
      split at hmid
      · simp at hmid
      · obtain ⟨x1, _, hmid⟩ := rfs_bind_ok hmid
        obtain ⟨x2, _, hmid⟩ := rfs_bind_ok hmid
        have he := Except.ok.inj hmid
        have hsize : mid.2.size = arr.size := by
          rw [← he]
          dsimp only
          rw [size_set!_eq]
        have he1 : x2 = mid.1 := congrArg Prod.fst he
        have he2 : (x2, mid.2) = mid := by rw [he1]
        rw [← he2] at hrest
        have htail := ihl x2 mid.2 hrest
        omega
/-- `crossCoordsR` preserves the node count. -/
private theorem rfs_crossCoordsR_length (P : Params) (rm : ComponentRegions)
    (cg : Graph) (labels : List MeasuredLabel) (p : Proper)
    (m : RegionConstraints) (layers : List (List Nat))
    (out : List Int × List (List Nat) × List (Option Int) × Proper)
    (h : crossCoordsR P rm cg labels p m layers = .ok out) :
    out.2.2.2.nodes.length = p.nodes.length := by
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := rfs_bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    exact absurd h (by simp)
  · obtain ⟨ngs, _, h⟩ := rfs_bind_ok h
    obtain ⟨xcr, _, h⟩ := rfs_bind_ok h
    obtain ⟨_, _, h⟩ := rfs_bind_ok h
    obtain ⟨allocx, _, h⟩ := rfs_bind_ok h
    obtain ⟨xp, hxp, h⟩ := rfs_bind_ok h
    have he := Except.ok.inj h
    have hC : out.2.2.2 = xp.2 :=
      (congrArg (fun q : List Int × List (List Nat) × List (Option Int) × Proper => q.2.2.2) he).symm
    unfold reservedPortsR at hxp
    obtain ⟨fout, hfold, h1⟩ := rfs_bind_ok hxp
    have he1 := Except.ok.inj h1
    have hxp2 : xp.2.nodes = fout.2.toList :=
      (congrArg (fun q : List Int × Proper => q.2.nodes) he1).symm
    have hlen := rfs_reservedPortsR_fold_length _ cg labels _ _ _ _ hfold
    rw [hC, hxp2, Array.length_toList, hlen, List.size_toArray]
/-- Region-run title data: a some-spec run keeps the group title node and the
output graph keeps the candidate node (both region arms). -/
private theorem rfs_some_title_data {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cgIn cgOut : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact (some s) inp cgIn labels orderOptions = .ok (cgOut, run))
    {pos : Nat} {ndX : Node} (hlocal : cgIn.nodes[pos]? = some ndX)
    (hbord2 : ndX.border = -2) :
    ∃ (v : Nat) (title : ProperNode), run.proper.nodes[v]? = some title ∧
      title.node.border = 3 ∧ title.node.clusterPath = ndX.clusterPath ∧
      cgOut.nodes[pos]? = some ndX := by
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hrsEq, hRank, hNorm, hLabels, hCoord,
    hMin, hOrd, hLabelWidths, hPlaced, hProxy, hDrop, hLanes, hYt, hYsMid,
    hReserve, hRoutes, hRouting, hCoordProper, hCoordYs, hBudget, hExact⟩ :=
    componentRunR_specR h
  have hcg' : cgOut.nodes[pos]? = some ndX := by
    rcases hRank with ⟨rr, _, _, _, hcgEq, _⟩ | ⟨rm', _, hrank⟩
    · rw [hcgEq]; exact hlocal
    · have heq := rankEquivalentR_nodes_eq hrank
      rw [heq]; exact hlocal
  have hnormalized := normalize_node_record hNorm hcg'
  have hlabeled := addLabelNodes_untouched_node hLabels hnormalized (by rfl)
  obtain ⟨j, hj⟩ := rfs_coord_title_recordR (s := s) hlabeled hbord2 (by rfl)
  rw [hCoord] at hj
  have hplace : ∃ t : ProperNode, placedProper.nodes[labeled.nodes.length + j]? = some t ∧
      t.node.border = 3 ∧ t.node.clusterPath = ndX.clusterPath := by
    rcases hPlaced with ⟨_, _, _, _, hppEq⟩ | ⟨rm2, m, _, _, hcross⟩
    · rw [hppEq]
      exact ⟨_, hj, rfl, rfl⟩
    · have hlen : placedProper.nodes.length = pCoord.nodes.length :=
        rfs_crossCoordsR_length _ _ _ _ _ _ _ _ hcross
      have hlt : labeled.nodes.length + j < placedProper.nodes.length := by
        rw [hlen]
        exact (List.getElem?_eq_some_iff.mp hj).1
      have ht' : placedProper.nodes[labeled.nodes.length + j]? =
          some (placedProper.nodes[labeled.nodes.length + j]) :=
        List.getElem?_eq_getElem hlt
      obtain ⟨m0, hm0, hb0, hp0⟩ :=
        rfs_crossCoordsR_keys _ _ _ _ _ _ _ _ hcross _ _ ht'
      obtain ⟨hb3, hp3⟩ : m0.node.border = 3 ∧
          m0.node.clusterPath = ndX.clusterPath := by
        have hmm := Option.some.inj (hm0.symm.trans hj)
        subst hmm
        exact ⟨rfl, rfl⟩
      refine ⟨placedProper.nodes[labeled.nodes.length + j], ht', ?_, ?_⟩
      · rw [hb0]; exact hb3
      · rw [hp0]; exact hp3
  obtain ⟨t, ht, hb3t, hp3t⟩ := hplace
  have hneg : ¬(t.node.border = -2 ∨ t.node.border = 2) := by
    rw [hb3t]; decide
  obtain ⟨-, -, -, -, -, hpreserve⟩ := proxyWidths_rel hProxy
  have hq0 : q0.nodes[labeled.nodes.length + j]? = some t :=
    (hpreserve _ _ ht hneg).1
  have hnodes : run.proper.nodes = q0.nodes := by
    have heq := congrArg Proper.nodes hDrop
    rw [OrderImpl.dropSynthetic_nodes] at heq
    exact heq.symm
  refine ⟨labeled.nodes.length + j, t, by rw [hnodes]; exact hq0, hb3t, hp3t, hcg'⟩
/-- A part title entry reaches the packed accumulator (shared tail of
`xfs_group_title_packed_mem` over the region fold). -/
private theorem rfs_part_title_mem {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {part : List Nat × Part} {pIdx : Nat}
    (hpartsIdx : execution.componentsAcc.parts[pIdx]? = some part)
    {pos k : Nat} (hpos : part.1[pos]? = some k)
    {cg : Graph} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hpartdef : part.2 = { placeComponentExact execution.params cg run 0
      execution.measured loops with area := area })
    {ndX : Node} (hposCg : cg.nodes[pos]? = some ndX)
    (hbord2 : ndX.border = -2)
    {v : Nat} {title : ProperNode}
    (hproper : run.proper.nodes[v]? = some title)
    (hbord : title.node.border = 3)
    (hpath : title.node.clusterPath = ndX.clusterPath) :
    ∃ srect, (k, srect) ∈ execution.packedAcc.titles := by
  have htop : (ndX, pos) ∈ cg.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hposCg
  have hmemTitle : (title, v) ∈ run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hproper
  have hpred : (title.node.border == 3 &&
      title.node.clusterPath == ndX.clusterPath) = true := by
    simp [hbord, hpath]
  have hcond : (ndX.border != -2) = false := by rw [hbord2]; decide
  have hneg : ¬ ((ndX.border != -2) = true) := by rw [hcond]; decide
  cases hfindT : run.proper.nodes.zipIdx.find?
      (fun q : ProperNode × Nat =>
        q.1.node.border == 3 && q.1.node.clusterPath == ndX.clusterPath) with
  | none =>
    have hcon : ¬ ((title.node.border == 3 &&
        title.node.clusterPath == ndX.clusterPath) = true) :=
      List.find?_eq_none.mp hfindT (title, v) hmemTitle
    exact False.elim (hcon hpred)
  | some t =>
    have hrect : (pos, Rect.mk
        (run.xs.getD t.2 0 - Int.fdiv t.1.node.w 2)
        ((frameRect execution.params cg run pos).y +
          execution.params.clusterPad)
        ndX.w (ndX.h - execution.params.clusterPad)) ∈ componentTitles
        execution.params cg run := by
      unfold componentTitles
      apply List.mem_filterMap.mpr
      refine ⟨(ndX, pos), htop, ?_⟩
      show ((if ndX.border != -2 then (none : Option (Nat × Rect)) else bind (run.proper.nodes.zipIdx.find? (fun q : ProperNode × Nat => q.1.node.border == 3 && q.1.node.clusterPath == ndX.clusterPath)) (fun title => let frame := frameRect execution.params cg run pos; pure (pos, Rect.mk (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2) (frame.y + execution.params.clusterPad) ndX.w (ndX.h - execution.params.clusterPad)))) : Option (Nat × Rect)) = _
      rw [ite_eq_right hneg, hfindT]
      rfl
    have hex : ∃ s0, (pos, s0) ∈ part.2.titles := by
      rw [hpartdef]
      exact ⟨_, List.mem_map.mpr ⟨_, hrect, rfl⟩⟩
    obtain ⟨s0, hs0⟩ := hex
    have hpack2 := execution.packed_eq
    unfold packAcc at hpack2
    obtain ⟨packedB, hpackedB, _⟩ := rfs_bind_ok hpack2
    have hpIdxB : pIdx < packedB.boxes.length := by
      have hbl := (List.getElem?_eq_some_iff.mp hpartsIdx).1
      have hcount := Pack.pack_count hpackedB
      simp only [List.length_map] at hcount
      omega
    have hboxgetB : packedB.boxes[pIdx]? = some packedB.boxes[pIdx] :=
      List.getElem?_eq_getElem hpIdxB
    have hselectedEq : (execution.componentsAcc.parts.zip
        packedB.boxes)[pIdx]? = some (part, packedB.boxes[pIdx]) :=
      List.getElem?_zip_eq_some.mpr ⟨hpartsIdx, hboxgetB⟩
    have hpair : (part, packedB.boxes[pIdx]) ∈
        execution.componentsAcc.parts.zip packedB.boxes :=
      List.mem_of_getElem? hselectedEq
    have hfoldEqT : (((execution.componentsAcc.parts.zip packedB.boxes).foldl packStep
      { execution.componentsAcc with
        canvasW := packedB.width
        canvasH := packedB.height
        titles := [] }).titles) = execution.packedAcc.titles := by
      have h := execution.packed_eq
      unfold packAcc at h
      obtain ⟨packed', hpacked', h⟩ := rfs_bind_ok h
      have hpeq : packed' = packedB :=
        Except.ok.inj (hpacked'.symm.trans hpackedB)
      subst hpeq
      exact congrArg Acc.titles (Except.ok.inj h)
    have hkeyGet : part.1.getD pos 0 = k := by simp [List.getD, hpos]
    have hfold := rfs_titles_fold_mem (execution.componentsAcc.parts.zip packedB.boxes)
      { execution.componentsAcc with
        canvasW := packedB.width
        canvasH := packedB.height
        titles := [] } hpair hs0
    rw [hkeyGet, hfoldEqT] at hfold
    exact ⟨_, hfold⟩
/-- A packed title entry yields an installed scene title (copy of the
`xfs_` scene-title step). -/
private theorem rfs_sceneTitle_mem {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {k : Nat} {obox : ModelBox}
    (hbox : inp.boxes[k]? = some obox)
    {srect : Rect} (hsrect : (k, srect) ∈ execution.packedAcc.titles) :
    (obox.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin (orientRect o.direction execution.packedAcc.canvasH { srect with w := (titleCaptionSize execution.params o (execution.lines.getD k [])).w, h := (titleCaptionSize execution.params o (execution.lines.getD k [])).h })) ∈ sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc := by
  unfold sceneTitlesExpr
  apply List.mem_filterMap.mpr
  refine ⟨(k, srect), hsrect, ?_⟩
  show (Option.bind (inp.boxes[k]?) (fun box => let size := titleCaptionSize execution.params o (execution.lines.getD k []); pure (box.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin (orientRect o.direction execution.packedAcc.canvasH { srect with w := size.w, h := size.h })))) = _
  rw [hbox]
  rfl
/-- A non-fixed group box records an installed title over the region scene. -/
theorem R_nonfixedGroupTitle_holds (exactIds : List String)
    (idSets : List (String × List String)) :
    R_NonfixedGroupTitle exactIds idSets := by
  intro inp o res execution k obox hbox hrole hfix
  obtain ⟨part, pIdx, pos, ndX, index, cg, run, loops, area, spec', hpartsIdx,
    hpos, hndX, hbord2, hrun, hlocal, hpartdef⟩ :=
    rfs_group_part_data execution hbox hrole hfix
  have hsrect : ∃ srect, (k, srect) ∈ execution.packedAcc.titles := by
    cases spec' with
    | none =>
        obtain ⟨hrunX, hcgEq⟩ := rfs_runR_none_to_X hrun
        rw [componentCandidateR_none] at hlocal
        obtain ⟨v, title, hproper, hb3, hpath⟩ :=
          rfs_group_title_source_none hrunX hlocal hbord2
        have hposCg : cg.nodes[pos]? = some ndX := by rw [hcgEq]; exact hlocal
        obtain ⟨srect, hs⟩ := rfs_part_title_mem execution hpartsIdx hpos
          hpartdef hposCg hbord2 hproper hb3 hpath
        exact ⟨srect, hs⟩
    | some s =>
        obtain ⟨v, title, hproper, hb3, hpath, hposCg⟩ :=
          rfs_some_title_data hrun hlocal hbord2
        obtain ⟨srect, hs⟩ := rfs_part_title_mem execution hpartsIdx hpos
          hpartdef hposCg hbord2 hproper hb3 hpath
        exact ⟨srect, hs⟩
  obtain ⟨srect, hsrect⟩ := hsrect
  have hmemS := rfs_sceneTitle_mem execution hbox hsrect
  cases hfind : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find? (fun title => title.1 == obox.id) with
  | some _ => rfl
  | none =>
    have hcon := List.find?_eq_none.mp hfind (obox.id, _) hmemS
    simp at hcon
/-- A title-less owner is a node or is fixed (replay of
`X_FallbackOwnerCasesX_holds` over the region title fact). -/
theorem R_fallbackOwnerCasesW_holds (exactIds : List String)
    (idSets : List (String × List String))
    (htitle : R_NonfixedGroupTitle exactIds idSets) :
    R_FallbackOwnerCasesW exactIds idSets := by
  intro inp o res execution hwf k obox hbox hnone
  by_cases hfix : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true
  · exact Or.inr hfix
  · have hfixFalse : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false :=
      Bool.eq_false_iff.mpr hfix
    by_cases hrole : obox.role = .group
    · exfalso
      have hsome := htitle execution hbox hrole hfixFalse
      have hnoneSome : ((sceneTitlesExpr execution.params inp o execution.lines
          execution.packedAcc).find? (fun title => title.1 == obox.id)).isSome = false := by
        rw [hnone]
        rfl
      rw [hsome] at hnoneSome
      exact absurd hnoneSome (by decide)
    · have hroleNode : obox.role = .node := by
        cases h : obox.role with
        | node => rfl
        | group => exact absurd h hrole
      exact Or.inl hroleNode
/-- Packed-domination residual for the region fixed-owner fit: every fixed-size
entry is dominated by its scene output box. Strictly narrower than
`R_FixedOwnerFit` (one step of its proof); true on the fitting probe rows
(`rfstFixB` in `RegionFallbackStructuralTProbe.lean`). -/
def R_FixedBoxDominates (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionR exactIds idSets inp o res)
    {i : Nat} {box : Box} {source : ModelBox} {entry : String × Size}
    (_hbox : res.scene.boxes[i]? = some box)
    (_hsource : inp.boxes[i]? = some source)
    (_hfixed : inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry),
    entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h

/-- The region fixed-owner fit follows from packed domination (replay of
`SceneExecution.fixed_owner_fit`). -/
theorem R_fixedOwnerFit_of_dominates (exactIds : List String)
    (idSets : List (String × List String))
    (hdom : R_FixedBoxDominates exactIds idSets) :
    R_FixedOwnerFit exactIds idSets := by
  intro inp o res execution hfit i box source hbox hsource hany hex hown
  obtain ⟨entry, hfixed⟩ :
      ∃ entry, inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry := by
    cases hf : inp.fixedSizes.find? (fun e => e.1 == source.id) with
    | none =>
      obtain ⟨e, hmem, hid⟩ := List.any_eq_true.mp hany
      exact absurd (List.find?_eq_none.mp hf e hmem) (by rw [hid]; decide)
    | some entry => exact ⟨entry, rfl⟩
  have hmem : entry ∈ inp.fixedSizes := List.mem_of_find?_eq_some hfixed
  have hid : entry.1 = source.id := by simpa using List.find?_some hfixed
  have hwrap : StyledMeasure.wrap execution.metric
      (Measure.wrapTarget execution.metric.profile execution.params.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD i source.id).toList =
        .ok (execution.lines.getD i []) := by
    have hlines := execution.lines_eq
    simp only [boxLines] at hlines
    obtain ⟨_, hlookup⟩ := mapM_getElem? _ _ _ hlines
    obtain ⟨measured, hmeasured, hindex⟩ := hlookup i (source, i)
      (by simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add])
    dsimp only at hmeasured
    have hget : execution.lines.getD i [] = measured := by
      simp only [List.getD_eq_getElem?_getD, hindex, Option.getD_some]
    rw [hget]
    exact hmeasured
  have hfit' : FixedSizeFit execution.params source.role (execution.lines.getD i [])
      entry.2 :=
    hfit entry hmem i source hsource hid.symm hex hown
      execution.params execution.metric (execution.lines.getD i [])
      execution.checked execution.metric_eq hwrap
  have hdom' := hdom execution hbox hsource hfixed
  exact FixedSizeFit.mono hfit' hdom'.1 hdom'.2
/-- The region fixed-owner fit for empty region sets, transported from the
exact twin `xctb_fixedOwnerFitX_holds` (the region fold coincides with the
exact fold when `idSets = []`). -/
theorem R_fixedOwnerFit_none_holds (exactIds : List String) :
    R_FixedOwnerFit exactIds [] := by
  intro inp o res execution hfit i box source hbox hsource hany hex hown
  have hR := execution.components_eq
  have hRnone : ((components execution.graph).foldlM
      (fun acc comp => layoutComponentR execution.params exactIds none inp o
        execution.graph acc comp execution.measured)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [],
        Array.replicate inp.labels.length default, false, [], []⟩) =
      .ok execution.componentsAcc := hR
  have hfun : ∀ (acc : Acc) (comp : List Nat),
      layoutComponentR execution.params exactIds none inp o execution.graph
        acc comp execution.measured =
      layoutComponentX execution.params exactIds inp o execution.graph
        acc comp execution.measured := fun acc comp =>
    layoutComponentR_none execution.params exactIds inp o execution.graph
      acc comp execution.measured
  have heq : (fun acc comp => layoutComponentR execution.params exactIds none
      inp o execution.graph acc comp execution.measured) =
      (fun acc comp => layoutComponentX execution.params exactIds inp o
      execution.graph acc comp execution.measured) := by
    funext acc comp
    exact hfun acc comp
  have hXcomp : ((components execution.graph).foldlM
      (fun acc comp => layoutComponentX execution.params exactIds inp o
        execution.graph acc comp execution.measured)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [],
        Array.replicate inp.labels.length default, false, [], []⟩) =
      .ok execution.componentsAcc := by
    rw [← heq]
    exact hRnone
  let execX : SceneExecutionX exactIds inp o res :=
    ⟨execution.params, execution.metric, execution.lines,
      execution.measured, execution.graph0, execution.graph,
      execution.componentsAcc, execution.packedAcc, execution.checked,
      execution.metric_eq, execution.lines_eq, execution.measured_eq,
      execution.graph0_eq, execution.graph_eq, hXcomp, execution.packed_eq,
      execution.scene_eq⟩
  exact xctb_fixedOwnerFitX_holds exactIds execX hfit hbox hsource hany hex hown
end PipelineImpl
end Layered
end Elegant
