import Elegant.Layered.ExactFallbackCaptionFactsProof
import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactFallbackCaptionClearProof
import Elegant.Layered.ExactPackedTransportProof
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactFlatC8b
import Elegant.Layered.FallbackCaptionClearProof
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.InputFixedFit
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.LabelsC8b
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Pipeline
import Elegant.Layered.Compound
import Elegant.Layered.CoordGraph
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.SizingFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.SceneBounds
import Elegant.Layered.Order
import Elegant.Model
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact fallback structural facts.

Proves the three narrow structural leaves consumed by
`X_fallbackCaptionClearBW_closed`
(`ExactFallbackCaptionFactsProof.lean:479`):

* `X_NonfixedGroupTitleX`: a non-fixed group box records a title;
* `X_FallbackOwnerCasesX`: a title-less owner is a node or is fixed;
* `X_FixedOwnerFitX`: fixed owners keep their fixed size in the scene.

Probe evidence (see `#eval`s below): title/cases mirrors hold on every
executed row; the fix mirror holds where `InputFixedFit` holds. -/

/-- Shared options for the probes (vector profile, top-to-bottom). -/
private def xfsOpts : Options := { profile := .vector, direction := .TB }

/-- Flat two groups with a fallback label owned by node `a1`. -/
private def xfsFitInp : Input :=
  { kind := "state"
    boxes := [{ id := "G1", role := .group, parent := "", exclusive := false },
      { id := "A", role := .group, parent := "G1", exclusive := false },
      { id := "B", role := .group, parent := "G1", exclusive := false },
      { id := "G2", role := .group, parent := "", exclusive := false },
      { id := "C", role := .group, parent := "G2", exclusive := false },
      { id := "D", role := .group, parent := "G2", exclusive := false },
      { id := "a1", parent := "A", exclusive := false },
      { id := "b1", parent := "B", exclusive := false },
      { id := "c1", parent := "C", exclusive := false },
      { id := "d1", parent := "D", exclusive := false }]
    routes := [{ id := "e1", fromId := "a1", toId := "c1" },
      { id := "e2", fromId := "b1", toId := "d1" },
      { id := "e3", fromId := "c1", toId := "b1" }]
    texts := ["G1", "A", "B", "G2", "C", "D", "a1", "b1", "c1", "d1"]
    edges := [.plain, .plain, .plain]
    labels := [{ id := "L1", owner := "a1", text := "hi" }] }

/-- Nested groups with a fallback label owned by the innermost node. -/
private def xfsNestInp : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "H", role := .group, parent := "G", exclusive := false },
      { id := "h", parent := "H", exclusive := false }]
    routes := []
    texts := ["G", "H", "h"]
    edges := []
    labels := [{ id := "L1", owner := "h", text := "deep" }] }

/-- Self-loop route with a fallback label on the looping node. -/
private def xfsSelfInp : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "a", parent := "G", exclusive := false }]
    routes := [{ id := "e0", fromId := "a", toId := "a" }]
    texts := ["G", "a"]
    edges := [.plain]
    labels := [{ id := "L1", owner := "a", text := "loop" }] }

/-- Zero-size and wide fixed boxes owning fallback labels. -/
private def xfsFixedInp : Input :=
  { kind := "state"
    boxes := [{ id := "Z", parent := "", exclusive := false },
      { id := "W", parent := "", exclusive := false }]
    routes := []
    texts := ["Z", "W"]
    edges := []
    fixedSizes := [("Z", { w := 0, h := 0 }), ("W", { w := 5000, h := 5000 })]
    labels := [{ id := "L1", owner := "Z", text := "zero" },
      { id := "L2", owner := "W", text := "wide" }] }

/-- Fixed-size group owning a fallback label. -/
private def xfsGroupFixInp : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "a", parent := "G", exclusive := false }]
    routes := []
    texts := ["G", "a"]
    edges := []
    fixedSizes := [("G", { w := 5000, h := 5000 })]
    labels := [{ id := "L1", owner := "G", text := "gcap" }] }

/-- Empty group beside a labelled node. -/
private def xfsEmptyGroupInp : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "a", parent := "", exclusive := false }]
    routes := []
    texts := ["G", "a"]
    edges := []
    labels := [{ id := "L1", owner := "a", text := "hi" }] }

/-- Ill-formed row: duplicate box id `A` (second box parented elsewhere). -/
private def xfsDupInp : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "A", parent := "G", exclusive := false },
      { id := "A", parent := "", exclusive := false }]
    routes := []
    texts := ["G", "A", "A"]
    edges := []
    labels := [{ id := "L1", owner := "A", text := "dup" }] }

/-- Layout success mirror. -/
private def xfsOk (exactIds : List String) (inp : Input) : Bool :=
  match layoutX exactIds inp xfsOpts with
  | .ok _ => true
  | .error _ => false

#eval xfsOk [] xfsFitInp
#eval xfsOk [] xfsNestInp
#eval xfsOk [] xfsSelfInp
#eval xfsOk ["W"] xfsFixedInp
#eval xfsOk ["G"] xfsGroupFixInp
#eval xfsOk [] xfsEmptyGroupInp
#eval xfsOk [] xfsDupInp

/-- Recomputed exact phases for the mirror (same equations as `layoutX`). -/
private def xfsPhases (exactIds : List String) (inp : Input)
    (o : Options) : Except LayoutError (Params × List (List Measure.Line) × Acc) := do
  let P ← checkedParams o.profile inp.kind
  let m ← metricOf o.profile o.fontFamily
  let target := Measure.wrapTarget m.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)
  let lines ← boxLines m target inp
  let measured ← measureLabels P m target inp o.direction
  let g0 ← measuredGraph P inp o lines
  let g ← exactGraph P exactIds inp o measured g0
  let start : Acc :=
    ⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩
  let mid ← (components g).foldlM (fun acc comp => layoutComponentX P exactIds inp o g acc comp measured) start
  let packed ← packAcc P o mid
  pure (P, lines, packed)

/-- Bool mirror of `X_NonfixedGroupTitleX` on recomputed phases. -/
private def xfsTitleB (exactIds : List String) (inp : Input) (o : Options) : Bool :=
  match xfsPhases exactIds inp o with
  | .error _ => true
  | .ok (P, lines, packed) =>
    let titles := sceneTitlesExpr P inp o lines packed
    inp.boxes.all fun obox =>
      if obox.role != .group then true
      else if inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) then true
      else ((titles.find? (fun title => title.1 == obox.id)).isSome)

/-- Bool mirror of `X_FallbackOwnerCasesX` on recomputed phases. -/
private def xfsCasesB (exactIds : List String) (inp : Input) (o : Options) : Bool :=
  match xfsPhases exactIds inp o with
  | .error _ => true
  | .ok (P, lines, packed) =>
    let titles := sceneTitlesExpr P inp o lines packed
    inp.boxes.all fun obox =>
      if (titles.find? (fun title => title.1 == obox.id)).isSome then true
      else (obox.role == .node) || inp.fixedSizes.any (fun fixed => fixed.1 == obox.id)

/-- Bool mirror of `X_FixedOwnerFitX` on recomputed phases. -/
private def xfsFixB (exactIds : List String) (inp : Input) (o : Options) : Bool :=
  match xfsPhases exactIds inp o with
  | .error _ => true
  | .ok (P, lines, packed) =>
    let boxes := sceneBoxesExpr P inp o packed
    inp.fixedSizes.all fun entry =>
      match inp.boxes.findIdx? (fun box : ModelBox => box.id == entry.1) with
      | none => true
      | some i =>
        match inp.boxes[i]?, boxes[i]? with
        | some src, some box =>
          if src.exclusive then true
          else if !(inp.labels.any fun l => l.owner == src.id) then true
          else
            let ls := lines.getD i []
            match src.role with
            | .group => decide (2 * P.clusterPad ≤ box.rect.w) && decide (P.clusterPad + (max 1 ls.length : Int) * P.lineH < box.rect.h)
            | .node => decide ((ls.length : Int) * P.lineH ≤ box.rect.h)
        | _, _ => false

#eval xfsTitleB [] xfsFitInp xfsOpts
#eval xfsTitleB [] xfsNestInp xfsOpts
#eval xfsTitleB [] xfsSelfInp xfsOpts
#eval xfsTitleB ["W"] xfsFixedInp xfsOpts
#eval xfsTitleB ["G"] xfsGroupFixInp xfsOpts
#eval xfsTitleB [] xfsEmptyGroupInp xfsOpts
#eval xfsTitleB [] xfsDupInp xfsOpts
#eval xfsCasesB [] xfsFitInp xfsOpts
#eval xfsCasesB [] xfsNestInp xfsOpts
#eval xfsCasesB [] xfsSelfInp xfsOpts
#eval xfsCasesB ["W"] xfsFixedInp xfsOpts
#eval xfsCasesB ["G"] xfsGroupFixInp xfsOpts
#eval xfsCasesB [] xfsEmptyGroupInp xfsOpts
#eval xfsCasesB [] xfsDupInp xfsOpts
#eval xfsFixB [] xfsFitInp xfsOpts
#eval xfsFixB ["W"] xfsFixedInp xfsOpts
#eval xfsFixB ["G"] xfsGroupFixInp xfsOpts

private theorem xfs_lines_length {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
      (mapM_getElem? _ _ _ h).1
    _ = inp.boxes.length := List.length_zipIdx

/-- X copy of `coordinateGraph_title_record`
(`CaptionWidthFacts.lean:9`): the exact coordinate construction keeps a
border-`-2` node and appends its border-`3` title copy. -/
private theorem xfs_coordinateGraph_title_recordX {P : Params} {exact : List Nat}
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

/-- X copy of `componentRun_group_title_width_source`
(`CaptionWidthFacts.lean:58`): the exact run keeps a border-`3` title node
with the group cluster path in its proper graph. -/
private theorem xfs_componentRun_group_title_sourceX {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ (v : Nat) (title : ProperNode), run.proper.nodes[v]? = some title ∧
      title.node.border = 3 ∧ title.node.clusterPath = node.clusterPath := by
  obtain ⟨ranks, p0, labeled, q0, hnormalize, hlabels, hcoordinate, -, -,
      hproxy, hdrop, -, -, -⟩ := componentRunX_spec h
  have hnormalized := normalize_node_record hnormalize hnode
  have hlabeled := addLabelNodes_untouched_node hlabels hnormalized (by rfl)
  obtain ⟨j, hj⟩ := xfs_coordinateGraph_title_recordX hlabeled hborder (by rfl)
  have hcoord : run.coordinateProper.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨node, false, none, false⟩, i)) := by
    rw [← hcoordinate]
    exact hj
  obtain ⟨-, -, -, -, -, hpreserve⟩ := proxyWidths_rel hproxy
  have hrouted : q0.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨node, false, none, false⟩, i)) :=
    (hpreserve _ _ hcoord (by simp [copyF])).1
  have hnodes : run.proper.nodes = q0.nodes := by
    have heq := congrArg Proper.nodes hdrop
    rw [OrderImpl.dropSynthetic_nodes] at heq
    exact heq.symm
  exact ⟨labeled.nodes.length + j, copyF (⟨node, false, none, false⟩, i),
    by rw [hnodes]; exact hrouted, rfl, rfl⟩
private theorem xfs_titles_mono (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) {t : Nat × Rect} (hmem : t ∈ start.titles) :
    t ∈ (pairs.foldl packStep start).titles := by
  induction pairs generalizing start with
  | nil => exact hmem
  | cons hd tl ih =>
    rw [List.foldl_cons]
    exact ih _ (List.mem_append.mpr (Or.inl hmem))

/-- Forward title transport through the packing fold: a part title entry
appears in the folded accumulator with its packed key and shift. -/
private theorem xfs_titles_fold_mem (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) {q : (List Nat × Part) × Rect} (hmem : q ∈ pairs)
    {r : Nat × Rect} (hr : r ∈ q.1.2.titles) :
    (q.1.1.getD r.1 0, shiftRect q.2.x q.2.y r.2) ∈
      (pairs.foldl packStep start).titles := by
  induction pairs generalizing start with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact xfs_titles_mono tl _ (List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩)))
    · exact ih _ hmem

private theorem xfs_group_title_run_data {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {k : Nat} {obox : ModelBox}
    (hbox : inp.boxes[k]? = some obox) (hrole : obox.role = .group)
    (hfix : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false) :
    ∃ (candidate : Nat) (run : Run) (loops : List (Nat × LoopPlacement))
      (area : Int) (part : List Nat × Part) (pIdx pos : Nat) (ndX : Node)
      (v : Nat) (title : ProperNode),
      execution.componentsAcc.parts[pIdx]? = some part ∧
      part.1[pos]? = some k ∧
      part.2 = { placeComponentExact execution.params
        (componentCandidate execution.graph part.1 candidate) run 0
        execution.measured loops with area := area } ∧
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph part.1 candidate)
        execution.measured (candidateOrder candidate) = .ok run ∧
      (componentCandidate execution.graph part.1 candidate).nodes[pos]? =
        some ndX ∧
      run.proper.nodes[v]? = some title ∧ title.node.border = 3 ∧
      title.node.clusterPath = ndX.clusterPath ∧ ndX.border = -2 := by
  have hlines : execution.lines.length = inp.boxes.length :=
    xfs_lines_length execution
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
    key_part_positionX execution hkb
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, _⟩ := bind_ok hpack
  have hpIdx : pIdx < packed.boxes.length := by
    have hbl := (List.getElem?_eq_some_iff.mp hpartsIdx).1
    have hcount := Pack.pack_count hpacked
    simp only [List.length_map] at hcount
    omega
  have hboxget : packed.boxes[pIdx]? = some packed.boxes[pIdx] :=
    List.getElem?_eq_getElem hpIdx
  obtain ⟨candidate, run, loops, area, hrun, hloops, hpartdef, _⟩ :=
    part_frame_lookupX execution packed hpacked hpartsIdx hboxget
  have hlocal : (componentCandidate execution.graph part.1 candidate).nodes[pos]? =
      some ndX := component_node_lookupX hpos hndX
  obtain ⟨v, title, hproper, htitleBorder, htitlePath⟩ :=
    xfs_componentRun_group_title_sourceX hrun hlocal hbord2
  exact ⟨candidate, run, loops, area, part, pIdx, pos, ndX, v, title,
    hpartsIdx, hpos, hpartdef, hrun, hlocal, hproper, htitleBorder,
    htitlePath, hbord2⟩

private theorem xfs_group_title_packed_mem {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {k : Nat} {obox : ModelBox}
    (hbox : inp.boxes[k]? = some obox) (hrole : obox.role = .group)
    (hfix : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false) :
    ∃ srect, (k, srect) ∈ execution.packedAcc.titles := by
  obtain ⟨candidate, run, loops, area, part, pIdx, pos, ndX, v, title,
      hpartsIdx, hpos, hpartdef, hrun, hlocal, hproper, htitleBorder,
      htitlePath, hbord2⟩ :=
    xfs_group_title_run_data execution hbox hrole hfix
  have htop : (ndX, pos) ∈
      (componentCandidate execution.graph part.1 candidate).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hlocal
  have hmemTitle : (title, v) ∈ run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hproper
  have hpred : (title.node.border == 3 &&
      title.node.clusterPath == ndX.clusterPath) = true := by
    simp [htitleBorder, htitlePath]
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
        ((frameRect execution.params
          (componentCandidate execution.graph part.1 candidate) run pos).y +
          execution.params.clusterPad)
        ndX.w (ndX.h - execution.params.clusterPad)) ∈ componentTitles
        execution.params
        (componentCandidate execution.graph part.1 candidate) run := by
      unfold componentTitles
      apply List.mem_filterMap.mpr
      refine ⟨(ndX, pos), htop, ?_⟩
      show ((if ndX.border != -2 then (none : Option (Nat × Rect)) else bind (run.proper.nodes.zipIdx.find? (fun q : ProperNode × Nat => q.1.node.border == 3 && q.1.node.clusterPath == ndX.clusterPath)) (fun title => let frame := frameRect execution.params (componentCandidate execution.graph part.1 candidate) run pos; pure (pos, Rect.mk (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2) (frame.y + execution.params.clusterPad) ndX.w (ndX.h - execution.params.clusterPad)))) : Option (Nat × Rect)) = _
      rw [ite_eq_right hneg, hfindT]
      rfl
    have hex : ∃ s0, (pos, s0) ∈ part.2.titles := by
      rw [hpartdef]
      exact ⟨_, List.mem_map.mpr ⟨_, hrect, rfl⟩⟩
    obtain ⟨s0, hs0⟩ := hex
    have hpack2 := execution.packed_eq
    unfold packAcc at hpack2
    obtain ⟨packedB, hpackedB, _⟩ := bind_ok hpack2
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
    have hfoldEqT : (((execution.componentsAcc.parts.zip packedB.boxes).foldl packStep { execution.componentsAcc with canvasW := packedB.width, canvasH := packedB.height, titles := [] }).titles) = execution.packedAcc.titles := by
      have h := execution.packed_eq
      unfold packAcc at h
      obtain ⟨packed', hpacked', h⟩ := bind_ok h
      have hpeq : packed' = packedB :=
        Except.ok.inj (hpacked'.symm.trans hpackedB)
      subst hpeq
      exact congrArg Acc.titles (Except.ok.inj h)
    have hkeyGet : part.1.getD pos 0 = k := by simp [List.getD, hpos]
    have hfold := xfs_titles_fold_mem (execution.componentsAcc.parts.zip packedB.boxes) { execution.componentsAcc with canvasW := packedB.width, canvasH := packedB.height, titles := [] } hpair hs0
    rw [hkeyGet, hfoldEqT] at hfold
    exact ⟨_, hfold⟩


theorem X_NonfixedGroupTitleX_holds (exactIds : List String) :
    X_NonfixedGroupTitleX exactIds := by
  intro inp o res execution k obox hbox hrole hfix
  obtain ⟨srect, hsrect⟩ := xfs_group_title_packed_mem execution hbox hrole hfix
  have hmemS : (obox.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin (orientRect o.direction execution.packedAcc.canvasH { srect with w := (titleCaptionSize execution.params o (execution.lines.getD k [])).w, h := (titleCaptionSize execution.params o (execution.lines.getD k [])).h })) ∈ sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc := by
    unfold sceneTitlesExpr
    apply List.mem_filterMap.mpr
    refine ⟨(k, srect), hsrect, ?_⟩
    show (Option.bind (inp.boxes[k]?) (fun box => let size := titleCaptionSize execution.params o (execution.lines.getD k []); pure (box.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin (orientRect o.direction execution.packedAcc.canvasH { srect with w := size.w, h := size.h })))) = _
    rw [hbox]
    rfl
  cases hfind : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find? (fun title => title.1 == obox.id) with
  | some _ => rfl
  | none =>
    have hcon := List.find?_eq_none.mp hfind (obox.id, _) hmemS
    simp at hcon

private theorem xfs_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

private theorem xfs_packedAcc_rects_sizeX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] }).rects.size = inp.boxes.length
  rw [xfs_packFold_rects_size]
  exact execution.components_rects_size

private theorem xfs_packed_rect_existsX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {i : Nat} (hi : i < inp.boxes.length) :
    ∃ rect, execution.packedAcc.rects[i]? = some rect := by
  have hsize : i < execution.packedAcc.rects.size := by
    rw [xfs_packedAcc_rects_sizeX execution]
    exact hi
  exact ⟨execution.packedAcc.rects[i],
    Array.getElem?_eq_some_iff.mpr ⟨hsize, rfl⟩⟩

theorem X_FallbackOwnerCasesX_holds (exactIds : List String)
    (htitle : X_NonfixedGroupTitleX exactIds) :
    X_FallbackOwnerCasesX exactIds := by
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


private theorem xfs_exactGraph_fixed_node_dims {exactIds : List String} {P : Params}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hg : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {i : Nat} {ls : List Measure.Line} (hline : lines[i]? = some ls)
    {box : ModelBox} (hbox : inp.boxes[i]? = some box)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = some entry) :
    ∃ node, graph.nodes[i]? = some node ∧ node.decl = i ∧ node.border = 0 ∧
      (match o.direction with
        | .LR | .RL => entry.2.h
        | .TB | .BT => entry.2.w) ≤ node.w ∧
      (match o.direction with
        | .LR | .RL => entry.2.w
        | .TB | .BT => entry.2.h) ≤ node.h := by
  obtain ⟨node0, hnode0, hdecl0, hborder0, hw0, hh0⟩ :=
    measuredGraph_fixed_node_dims hg0 hline hbox hfixed
  unfold exactGraph at hg
  obtain ⟨nodes, hnodes, h⟩ := bind_ok hg
  have he := Except.ok.inj h
  have hgnodes : graph.nodes = nodes := by simpa using (congrArg Graph.nodes he).symm
  obtain ⟨_, hmapGet⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨nodeX, hfX, hmem⟩ := hmapGet i node0 hnode0
  rw [← hgnodes] at hmem
  cases hbox0 : inp.boxes[node0.decl]? with
  | none =>
    simp only [hbox0, pure, Except.pure] at hfX
    have hred : nodeX = node0 := Except.ok.inj hfX.symm
    rw [hred] at hmem
    exact ⟨node0, hmem, hdecl0, hborder0, hw0, hh0⟩
  | some box' =>
    rw [hdecl0] at hbox0
    have hbeq : box' = box := Option.some.inj (hbox0.symm.trans hbox)
    rw [hbeq] at hbox0
    simp only [hdecl0, hbox0] at hfX
    split at hfX
    · simp only [pure, Except.pure] at hfX
      have hred : nodeX = node0 := Except.ok.inj hfX.symm
      rw [hred] at hmem
      exact ⟨node0, hmem, hdecl0, hborder0, hw0, hh0⟩
    · cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
      | none =>
        simp only [hfind] at hfX
        cases hfX
      | some fixed =>
        simp only [hfind] at hfX
        have hentry : fixed = entry := Option.some.inj (hfind.symm.trans hfixed)
        rw [hentry] at hfX
        split at hfX
        · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hfX
          cases hfX
        · split at hfX
          · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hfX
            cases hfX
          · simp only [pure, Except.pure] at hfX
            obtain rfl := Except.ok.inj hfX
            refine ⟨_, hmem, ?_, ?_, ?_, ?_⟩
            · cases hd : o.direction <;> rfl
            · cases hd : o.direction <;> exact hborder0
            · cases hd : o.direction <;> exact Int.le_refl _
            · cases hd : o.direction <;> exact Int.le_refl _
end PipelineImpl
end Layered
end Elegant
