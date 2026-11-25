import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.BracketInsideRankFacts
import Elegant.Layered.BottomClearanceNesting
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CgShape
import Elegant.Layered.CoordGraph
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Executed same-declaration marker disjointness

`CaptionSameDeclMarkerDisjoint` for an executed run: a same-declaration
position that is not the group frame is disjoint from the transported caption.

Candidate-graph nodes have border `0`, `-2` or `2`
(`componentCandidate_marker_shape`), so a same-declaration non-`-2` position
is either a bottom marker (`2`) or a plain member (`0`); side markers
(`±1`) and title copies (`3`) do not occur in the candidate graph.

* `border = 2`: bottom-marker uniqueness
  (`BracketInsideRankFacts.measuredGraph_bottom_pair_eq` transported through
  the component map, whose `Nodup` pins the candidate index) identifies the
  position with the bottom found by `componentRun_cg_bottom_find`; its rank
  lies strictly below the top rank (`componentRun_group_top_lt_bottom`), so
  its band top lies strictly below the caption bottom
  (`rankAxis_band_top_strict` with `captionInTopBand_executed`, lower-bounded
  by `fbs_run_node_band`).
* `border = 0`: impossible. Both declarations equal their source-graph
  indices (`SceneExecution.group_node_path_source` and
  `SceneExecution.plain_node_path_source`), hence the two positions share one
  graph index and coincide, contradicting `-2 ≠ 0`. -/

/-- Copied from the private `CaptionLocalClearProof.run_rank_eq_coordinate_copy`:
executed proper rank equals coordinate rank. -/
private theorem run_rank_eq_coordinate_copy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (i : Nat) :
    rk run.proper.rank i = rk run.coordinateProper.rank i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]

/-- Same-declaration marker case, proved: a bottom marker sits on a rank
strictly below the top marker, so its band lies strictly below the caption;
a same-declaration plain member cannot exist. -/
theorem captionSameDeclMarkerDisjoint_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run) :
    CaptionSameDeclMarkerDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp := by
  intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hsame hne hframe
  have hshape := (componentCandidate_marker_shape execution.graph_eq hfn).1
  rcases hshape with hbor0 | hborNe | hbor2
  · -- A same-declaration plain member is impossible: both declarations are
    -- their source-graph indices, so the two positions coincide.
    obtain ⟨origT, _, hsrcT⟩ := componentCandidate_nonplain_source hnode (by omega)
    obtain ⟨_, _, hdeclT, _⟩ := execution.group_node_path_source hsrcT hborder
    have hfn2 : (comp.map fun v => execution.graph.nodes.getD v default)[pos]? =
        some fNode := by
      simpa [componentCandidate_nodes, componentGraph] using hfn
    rw [List.getElem?_map] at hfn2
    obtain ⟨origP, hcompP, hgetP⟩ := Option.map_eq_some_iff.mp hfn2
    have hltP : origP < execution.graph.nodes.length := by
      have hmemP : origP ∈ comp := List.mem_of_getElem? hcompP
      have hcomp' := hcomp
      simp only [components] at hcomp'
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hcomp'
      exact List.mem_range.mp (List.mem_filter.mp hmemP).1
    have hsrcP : execution.graph.nodes[origP]? = some fNode := by
      obtain ⟨n, hn⟩ : ∃ n, execution.graph.nodes[origP]? = some n :=
        ⟨_, List.getElem?_eq_some_iff.mpr ⟨hltP, rfl⟩⟩
      have hget : execution.graph.nodes.getD origP default = n := by
        simp [List.getD_eq_getElem?_getD, hn]
      rw [hget] at hgetP
      rw [hgetP] at hn
      exact hn
    obtain ⟨_, _, hdeclP, _⟩ := execution.plain_node_path_source hsrcP hbor0
    have hTP : origT = origP := hdeclT.symm.trans (hsame.trans hdeclP)
    have hcontra : tNode = fNode := by
      have h1 : execution.graph.nodes[origT]? = some tNode := hsrcT
      rw [hTP] at h1
      exact Option.some.inj (h1.symm.trans hsrcP)
    have hb := congrArg Node.border hcontra
    rw [hborder, hbor0] at hb
    omega
  · exact (hne hborNe).elim
  · -- The bottom marker: uniqueness pins the candidate index, then the band
    -- argument mirrors `captionSelfBottom_proved` with the node rect.
    have hlines : execution.lines.length = inp.boxes.length := by
      have h := (mapM_getElem? _ _ _ execution.lines_eq).1
      simpa only [List.length_zipIdx] using h
    obtain ⟨bottom, hbottom⟩ :=
      componentRun_cg_bottom_find execution.graph_eq hlines hcomp hnode hborder
    have hbordB : bottom.1.border = 2 := by
      have hcond := List.find?_some hbottom
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.1
    have hdeclB : bottom.1.decl = tNode.decl := by
      have hcond := List.find?_some hbottom
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.2
    have hnodeB : (componentCandidate execution.graph comp candidate).nodes[bottom.2]? =
        some bottom.1 :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hbottom)
    obtain ⟨origP, hcompP, hsrcP⟩ := componentCandidate_nonplain_source hfn (by omega)
    obtain ⟨origB, hcompB, hsrcB⟩ := componentCandidate_nonplain_source hnodeB (by omega)
    have hmemP : (fNode, origP) ∈ execution.graph.nodes.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hsrcP
    have hmemB : (bottom.1, origB) ∈ execution.graph.nodes.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hsrcB
    have hde : fNode.decl = bottom.1.decl := (hdeclB.trans hsame).symm
    have hpair :=
      measuredGraph_bottom_pair_eq execution.graph_eq hmemP hmemB hbor2 hbordB hde
    have horig : origP = origB := congrArg Prod.snd hpair
    have hpos : pos = bottom.2 := by
      have hnd := components_nodup execution.graph comp hcomp
      have hmapnd : (comp.map id).Nodup := by simpa using hnd
      have hcompB' : comp[bottom.2]? = some origP := by rw [horig]; exact hcompB
      exact nodup_map_inj_aux id hmapnd hcompP hcompB' rfl
    subst hpos
    have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp hnode).1
    have hbotLt : bottom.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp hnodeB).1
    obtain ⟨rrB, _, hrrB, hcB, _, _, hranksB, hlt⟩ :=
      componentRun_group_top_lt_bottom execution.graph_eq hcomp hrun
    have htopLtBot := hlt i tNode bottom hnode hborder hbottom
    have eTop : rk run.coordinateProper.rank i = rk rrB.ranks i := by
      have h2x := prepared_coordinate_original_rk (P := execution.params) hrrB hranksB hindexLt
      rw [hcB] at h2x
      exact h2x
    have eBottom : rk run.coordinateProper.rank bottom.2 = rk rrB.ranks bottom.2 := by
      have h2x := prepared_coordinate_original_rk (P := execution.params) hrrB hranksB hbotLt
      rw [hcB] at h2x
      exact h2x
    have rEqT := run_rank_eq_coordinate_copy hrun i
    have rEqB := run_rank_eq_coordinate_copy hrun bottom.2
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, hry, _, _⟩ :=
      componentRun_spec hrun
    have hindexLen : i < run.proper.nodes.length :=
      componentRun_original_nodes_covered hrun i hindexLt
    have hbotLen : bottom.2 < run.proper.nodes.length :=
      componentRun_original_nodes_covered hrun bottom.2 hbotLt
    have hcov :=
      (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
    obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
    obtain ⟨ltB, hlyB, _, hnnB⟩ := hcov bottom.2 hbotLen
    rw [rEqT] at hlyT hnnT
    rw [rEqB] at hlyB hnnB
    have hltTB : (rk run.coordinateProper.rank i).toNat <
        (rk run.coordinateProper.rank bottom.2).toNat := by
      have h1 := eTop
      have h2y := eBottom
      have h3 : rk rrB.ranks i + 1 ≤ rk rrB.ranks bottom.2 := htopLtBot
      have h4 := hnnT
      have h5 := hnnB
      omega
    have hbandTB := rankAxis_band_top_strict hry _ _ _ _ hltTB hlyT hlyB
    have hbandLo := (fbs_run_node_band hrun bottom.2 hbotLen).1
    rw [rEqB] at hbandLo
    have hcap := (captionInTopBand_executed execution hcomp hrun hmem hnode hborder).2
    have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
      simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
    have hposGet : (componentCandidate execution.graph comp candidate).nodes.getD bottom.2 default =
        fNode := by
      simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
    have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate) run bottom.2 =
        nodeRect (componentCandidate execution.graph comp candidate) run bottom.2 := by
      unfold frameRect
      simp only []
      rw [hposGet, hbor2]
      rfl
    have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run bottom.2).y =
        run.ys.getD bottom.2 0 := rfl
    rw [← hframe, hfr]
    unfold Disjoint
    intro hcon
    obtain ⟨-, hy⟩ := hcon
    rw [hltTget] at hcap
    omega

end PipelineImpl
end Layered
end Elegant
