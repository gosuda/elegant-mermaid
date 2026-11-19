import Elegant.Layered.ExactCaptionMembersProof
import Elegant.Layered.Pipeline
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Compound
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CgShape
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ParentContainmentFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl
/-- Candidate nodes are positional: a candidate `-2` node comes from one
component index with the same full record. Copy of `xcsn_candidate_comp_index`. -/
private theorem xccb_candidate_comp_index {g : Graph} {comp : List Nat}
    {candidate i : Nat} {tNode : Node}
    (hnode : (componentCandidate g comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    ∃ j, comp[i]? = some j ∧ comp.getD i 0 = j ∧ g.nodes[j]? = some tNode ∧
      g.nodes.getD j default = tNode := by
  rw [componentCandidate_nodes] at hnode
  unfold componentGraph at hnode
  simp only [List.getElem?_map] at hnode
  obtain ⟨j, hj, hget⟩ := Option.map_eq_some_iff.mp hnode
  have hjlt : j < g.nodes.length := by
    by_cases hjlt : j < g.nodes.length
    · exact hjlt
    · have hnone : g.nodes[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hdef : (default : Node) = tNode := by simpa [List.getD, hnone] using hget
      rw [← hdef] at hborder
      change (0 : Int) = -2 at hborder
      omega
  have hgetElem : g.nodes[j]? = some tNode := by
    have he : g.nodes[j] = tNode := by simpa [List.getD, hjlt] using hget
    simpa [hjlt] using congrArg some he
  exact ⟨j, hj, by simp [List.getD, hj], hgetElem, hget⟩


/-- Copy of `xcsn_exactGraph_node_key_rev`: a node of the exact graph comes
from the same-index measured node with border, cluster path, and declaration
preserved. -/
private theorem xccb_exactGraph_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g')
    {v : Nat} {nd' : Node} (hv : g'.nodes[v]? = some nd') :
    ∃ nd, g.nodes[v]? = some nd ∧ nd'.border = nd.border ∧
      nd'.clusterPath = nd.clusterPath ∧ nd'.decl = nd.decl := by
  have hlen : g'.nodes.length = g.nodes.length := exactGraph_length h
  have hvlt : v < g.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have hmem : g.nodes[v]? = some g.nodes[v] := List.getElem?_eq_getElem hvlt
  obtain ⟨nd'', hnd'', hb, hc, hd⟩ := exactGraph_node_key h hmem
  have heq : nd'' = nd' := Option.some.inj (hnd''.symm.trans hv)
  subst heq
  exact ⟨g.nodes[v], hmem, hb, hc, hd⟩

/-- A `find?` for a fixed id is `none` when the `any` test is false.
Copy of `xcsn_find?_of_any_false`. -/
private theorem xccb_find?_of_any_false (l : List (String × Size)) (id : String)
    (h : l.any (fun fixed => fixed.1 == id) = false) :
    l.find? (fun fixed => fixed.1 == id) = none := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases he : (hd.1 == id) with
    | true =>
      simp [he, List.any_cons] at h
    | false =>
      have htl : tl.any (fun fixed => fixed.1 == id) = false := by
        simp only [List.any_cons, he, Bool.false_or] at h
        exact h
      simp only [List.find?_cons, he, ih htl]

/-- An exact-graph node whose box is neither exact nor group-fixed is
unchanged: full record equality, not just key fields.
Copy of `xcsn_exact_node_unchanged`. -/
private theorem xccb_exact_node_unchanged {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g')
    {v : Nat} {nd : Node} (hv : g.nodes[v]? = some nd)
    {box : ModelBox} (hbox : inp.boxes[nd.decl]? = some box)
    (hnotexact : exactIds.contains box.id = false)
    (hnofixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false) :
    g'.nodes[v]? = some nd := by
  unfold exactGraph at h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst he
  obtain ⟨out, hout, hmem⟩ := (mapM_getElem? _ _ _ hnodes).2 v nd hv
  dsimp only at hout
  simp only [hbox] at hout
  have hcond : ((!exactIds.contains box.id) &&
      !(box.role == .group && inp.fixedSizes.any (fun fixed => fixed.1 == box.id))) = true := by
    simp only [hnotexact, hnofixed, Bool.not_false, Bool.and_false, Bool.true_and]
  rw [ite_eq_left hcond] at hout
  simp only [pure, Except.pure] at hout
  have hred : out = nd := Except.ok.inj hout.symm
  rw [hred] at hmem
  exact hmem

/-- Box source for a measured border-`-2` node: the input box at its
declaration has group role and is not fixed. Derived from the public
`measuredGraph_group_origin` by unfolding the mapped fixed-role change. -/
private theorem xccb_box_of_measured {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph0 : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    {j : Nat} {nd : Node} (hnd : graph0.nodes[j]? = some nd) (hbord : nd.border = -2) :
    ∃ box : ModelBox, inp.boxes[nd.decl]? = some box ∧ box.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false := by
  obtain ⟨hdecl, box, hbox, hrole, hpath⟩ := measuredGraph_group_origin h0 hnd hbord
  rw [hdecl] at hbox
  have hblt : j < inp.boxes.length := by
    have h := (List.getElem?_eq_some_iff.mp hbox).1
    simpa [List.length_map] using h
  obtain ⟨orig, horig⟩ : ∃ orig, inp.boxes[j]? = some orig :=
    ⟨_, List.getElem?_eq_getElem hblt⟩
  have heq : box = (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
      { orig with role := .node } else orig) := by
    simp only [List.getElem?_map, horig, Option.map_some] at hbox
    exact (Option.some.inj hbox).symm
  cases hc : inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) with
  | true =>
    simp only [heq, hc, ite_true] at hrole
    cases hrole
  | false =>
    have hboxOrig : box = orig := by simp only [heq, hc, Bool.false_eq_true, ite_false]
    have hrole' : orig.role = .group := by rw [← hboxOrig]; exact hrole
    refine ⟨orig, ?_, hrole', hc⟩
    rw [hdecl]
    exact horig

/-- Exact title width and height fit: a border-`-2` exact-candidate node
carries the measured title dimensions, because the measured source is
non-fixed (so `exactGraph` leaves it unchanged) and exact membership would
have thrown. Proved via the public `actual_title_caption_fit` on the measured
candidate plus full-record transport across `exactGraph`. -/
private theorem xccb_exact_title_fit {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate i : Nat} {tNode : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    tNode.w = (match o.direction with
      | .LR | .RL => (max 1 (execution.lines.getD (comp.getD i 0) []).length : Int) *
        execution.params.lineH
      | .TB | .BT => (execution.lines.getD (comp.getD i 0) []).foldl
        (fun w line => max w line.width) 0) ∧
    (match o.direction with
      | .LR | .RL => (execution.lines.getD (comp.getD i 0) []).foldl
        (fun w line => max w line.width) 0
      | .TB | .BT => (max 1 (execution.lines.getD (comp.getD i 0) []).length : Int) *
        execution.params.lineH) +
        execution.params.clusterPad ≤ tNode.h := by
  obtain ⟨j, hj, hcompD, hgraphGet, hgetElem⟩ := xccb_candidate_comp_index hnode hborder
  obtain ⟨nd, hnd, hb, hc, hd⟩ := xccb_exactGraph_node_key_rev execution.graph_eq hgraphGet
  have hbord0 : nd.border = -2 := by omega
  obtain ⟨box, hboxJ, hrole, hnofixed⟩ := xccb_box_of_measured execution.graph0_eq hnd hbord0
  have hnotexact : exactIds.contains box.id = false := by
    cases he : exactIds.contains box.id with
    | true =>
      have hge := execution.graph_eq
      unfold exactGraph at hge
      obtain ⟨nodes, hnodes, _⟩ := bind_ok hge
      obtain ⟨out, hout, _⟩ := (mapM_getElem? _ _ _ hnodes).2 j nd hnd
      dsimp only at hout
      simp only [hboxJ] at hout
      by_cases hcnd : ((!exactIds.contains box.id) &&
          !(box.role == .group && inp.fixedSizes.any (fun fixed => fixed.1 == box.id))) = true
      · rw [ite_eq_left hcnd] at hout
        simp only [pure, Except.pure] at hout
        have hcontra : ((!exactIds.contains box.id) &&
            !(box.role == .group && inp.fixedSizes.any (fun fixed => fixed.1 == box.id))) = false := by
          simp only [he, Bool.not_true, Bool.false_and]
        rw [hcontra] at hcnd
        cases hcnd
      · rw [ite_eq_right hcnd] at hout
        have hfind := xccb_find?_of_any_false _ _ hnofixed
        simp only [hfind] at hout
        cases hout
    | false => rfl
  have hunch := xccb_exact_node_unchanged execution.graph_eq hnd hboxJ hnotexact hnofixed
  have heq : tNode = nd := Option.some.inj (hgraphGet.symm.trans hunch)
  have hcand0 : (componentCandidate execution.graph0 comp candidate).nodes[i]? = some nd := by
    rw [componentCandidate_nodes]
    unfold componentGraph
    dsimp only
    rw [List.getElem?_map, hj, Option.map_some]
    have hgetD : execution.graph0.nodes.getD j default = nd := by
      simp only [List.getD_eq_getElem?_getD, hnd, Option.getD_some]
    exact congrArg some hgetD
  obtain ⟨hw, hh⟩ := actual_title_caption_fit execution.graph0_eq hcand0 hbord0
  rw [← heq] at hw hh
  exact ⟨hw, hh⟩

/-- Copy of `xcsn_coordinateGraphX_title_record`: a border-`-2` labeled node
has its title copy in the exact coordinate graph. -/
private theorem xccb_coordinateGraphX_title_record (P : Params) (exact : List Nat)
    {p : Proper} {i : Nat} {node : ProperNode}
    (hnode : p.nodes[i]? = some node) (hborder : node.node.border = -2)
    (hdummy : node.dummy = false) :
    ∃ j, (titleNodes (sizeProperPortsX P exact p))[j]? = some (node, i) ∧
      (coordinateGraphX P exact p).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
  have hsized : (sizeProperPortsX P exact p).nodes[i]? = some node := by
    simp only [sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx,
      hnode, Option.map_some]
    simp [hborder]
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
  refine ⟨j, hj, ?_⟩
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  simp [copyF, hdummy]

/-- Copy of `xcsn_titled_rank_record` (prefix inlined): the titled rank list
extends the source rank list. -/
private theorem xccb_titled_rank_record (P : Params) (exact : List Nat) {source : Proper}
    {index : Nat} {rank : Int}
    (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  have heq : ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
    unfold titleReservations sizeProperPortsX
    exact ⟨_, rfl⟩
  obtain ⟨extra, heq⟩ := heq
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Copy of `xcsn_source_alignment_of_titled`: titled length alignment
implies source length alignment. -/
private theorem xccb_source_alignment_of_titled (P : Params) (exact : List Nat) {source : Proper}
    (h : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length) :
    source.nodes.length = source.rank.length := by
  rw [titleReservations_nodes] at h
  simp only [List.length_append, List.length_map, sizeProperPortsX_length] at h
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun value => rk source.rank value.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank] at h
  simp only [List.length_append, List.length_map] at h
  omega

/-- Copy of `xcsn_prepared_titled_original_rk`: the titled rank at a graph
index equals the prepared rank, nonnegatively. -/
private theorem xccb_prepared_titled_original_rk {P : Params} {cg : Graph} {exact : List Nat}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact source)).rank index = rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact source)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have htitledLookup := xccb_titled_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index
/-- Copy of `X_coordinateGraph_anchor_prefix`: exact coordinate rank list
extends the source rank list. -/
private theorem xccb_coordinateGraph_anchor_prefix (P : Params) (exact : List Nat) (p : Proper) :
    ∃ extra, (coordinateGraphX P exact p).rank = p.rank ++ extra := by
  obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have htitle : ∃ tail, (titleReservations (sizeProperPortsX P exact p)).rank =
      p.rank ++ tail := by
    unfold titleReservations sizeProperPortsX
    exact ⟨_, rfl⟩
  obtain ⟨tail, htitle⟩ := htitle
  refine ⟨tail ++ extraRanks, ?_⟩
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).rank = _
  rw [hr, htitle, List.append_assoc]

/-- Copy of `X_coordinateGraph_rank_record`: source rank entries survive in
the exact coordinate rank list. -/
private theorem xccb_coordinateGraph_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := xccb_coordinateGraph_anchor_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h
/-- Copy of `X_prepared_coordinate_original_rk`: the exact coordinate rank
at a graph index equals the prepared rank. -/
private theorem xccb_prepared_coordinate_original_rk {P : Params} {exact : List Nat} {cg : Graph}
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
  have hcoordinateLookup := xccb_coordinateGraph_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]
/-- Copy of `xcsn_titled_copy_rank_record`: the titled rank at a title-copy
position records its anchor rank. -/
private theorem xccb_titled_copy_rank_record (P : Params) (exact : List Nat) {source : Proper}
    (haligned : source.nodes.length = source.rank.length)
    {position : Nat} {entry : ProperNode × Nat}
    (hentry : (titleNodes (sizeProperPortsX P exact source))[position]? = some entry) :
    (titleReservations (sizeProperPortsX P exact source)).rank[source.nodes.length + position]? =
      some (rk source.rank entry.2) := by
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun value => rk source.rank value.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank, List.getElem?_append_right (by omega)]
  have hindex : source.nodes.length + position - source.rank.length = position := by omega
  rw [hindex, List.getElem?_map, hentry]
  rfl



/-- Copy of `xcsn_coordinateGraph_titled_rank_record`: titled rank entries
survive in the exact coordinate rank list. -/
private theorem xccb_coordinateGraph_titled_rank_record (P : Params) (exact : List Nat)
    {source : Proper} {index : Nat} {rank : Int}
    (h : (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).rank[index]? =
      some rank
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Copy of `xcsn_stored_y_eq`: the stored title y equals its own frame y
plus `clusterPad`. -/
private theorem xccb_stored_y_eq {P : Params} {cg : Graph} {run : Run}
    {i : Nat} {stored0 : Rect}
    (hmem : (i, stored0) ∈ componentTitles P cg run) :
    stored0.y = (frameRect P cg run i).y + P.clusterPad := by
  unfold componentTitles at hmem
  obtain ⟨top, htopMem, htopEmit⟩ := List.mem_filterMap.mp hmem
  dsimp only at htopEmit
  by_cases hb : top.1.border = -2
  · simp [hb] at htopEmit
    cases hfind : run.proper.nodes.zipIdx.find?
        (fun q => q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
    | none =>
      simp [hfind] at htopEmit
    | some title =>
      simp [hfind] at htopEmit
      obtain ⟨hi, hrect⟩ := htopEmit
      have hy : stored0.y = (frameRect P cg run top.2).y + P.clusterPad := by
        have hcongr : (Rect.mk
          (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
          ((frameRect P cg run top.2).y + P.clusterPad) top.1.w
          (top.1.h - P.clusterPad)).y = stored0.y := congrArg Rect.y hrect
        simpa using hcongr.symm
      rw [hi] at hy
      exact hy
  · simp [hb] at htopEmit

/-- Exact title-coordinate rank bundle: the title copy of an exact group sits
in both run graphs at the reserved index and shares its anchor rank. Replay
of the plain `captionInTopBand_executed` title-rank chain over
`componentRunX`, without any uniqueness indirection. -/
private theorem xccb_title_coord_rank {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {i : Nat} {tNode : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2)
    (hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length) :
    ∃ v, run.coordinateProper.nodes[v]? =
        some (copyF (⟨tNode, false, none, false⟩, i)) ∧
      run.proper.nodes[v]? = some (copyF (⟨tNode, false, none, false⟩, i)) ∧
      rk run.coordinateProper.rank v = rk run.coordinateProper.rank i := by
  obtain ⟨rr, labeled, _, hrr, hc, _, hready, hrecords, hranks, _, _⟩ :=
    X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hnode hborder
  have halignedB := xccb_source_alignment_of_titled _ _ hready.2.2.2.1
  obtain ⟨j, hj, hjCoord⟩ := xccb_coordinateGraphX_title_record execution.params
    (exactDecls exactIds inp) (hrecords i tNode hnode) hborder (by rfl)
  have hsourceBound : i < labeled.rank.length := by
    have hn := (List.getElem?_eq_some_iff.mp (hrecords i tNode hnode)).1
    have hlen := halignedB
    omega
  have hsourceRank : labeled.rank[i]? = some labeled.rank[i] :=
    List.getElem?_eq_getElem hsourceBound
  have htitledRank := xccb_titled_rank_record execution.params (exactDecls exactIds inp)
    hsourceRank
  have hsourceToTitled : rk labeled.rank i =
      rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank i := by
    simp only [rk, List.getD_eq_getElem?_getD, hsourceRank, htitledRank, Option.getD_some]
  have htopRank := xccb_prepared_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks hindexLt
  have eTop : rk run.coordinateProper.rank i = rk rr.ranks i := by
    have h2 := xccb_prepared_coordinate_original_rk (P := execution.params)
      (exact := exactDecls exactIds inp) hrr hranks hindexLt
    rw [hc] at h2
    exact h2
  have hcopyRank := xccb_titled_copy_rank_record execution.params
    (exactDecls exactIds inp) halignedB hj
  have hcoordRank := xccb_coordinateGraph_titled_rank_record execution.params
    (exactDecls exactIds inp) hcopyRank
  have hcoordC : run.coordinateProper.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨tNode, false, none, false⟩, i)) := by
    rw [← hc]
    exact hjCoord
  have htitleRankEq : rk run.coordinateProper.rank (labeled.nodes.length + j) =
      rk run.coordinateProper.rank i := by
    have h1 : rk (coordinateGraphX execution.params
        (exactDecls exactIds inp) labeled).rank (labeled.nodes.length + j) =
        rk labeled.rank i := by
      simp only [rk, List.getD_eq_getElem?_getD, hcoordRank, hsourceRank, Option.getD_some]
    rw [hc] at h1
    rw [h1, hsourceToTitled, htopRank.1, ← eTop]
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hproperC : run.proper.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨tNode, false, none, false⟩, i)) := by
    obtain ⟨_, _, _, _, _, hpreserve⟩ := proxyWidths_rel hproxy
    have hrouted : q0.nodes[labeled.nodes.length + j]? =
        some (copyF (⟨tNode, false, none, false⟩, i)) :=
      (hpreserve _ _ hcoordC (by simp [copyF])).1
    have hnodes : run.proper.nodes = q0.nodes := by
      have he := congrArg Proper.nodes hdrop
      rw [OrderImpl.dropSynthetic_nodes] at he
      exact he.symm
    rw [hnodes]
    exact hrouted
  exact ⟨_, hcoordC, hproperC, htitleRankEq⟩
/-- Exact caption band: the transported caption bottom lies at or before the
bottom of its own top rank band. Replay of the plain
`captionInTopBand_executed` upper bound over `componentRunX`: title-copy
placement, width, fit, and title rank replay through the exact machinery,
and the band covers the title height by `componentRunX_node_band`. -/
theorem XC_capBandX_holds (exactIds : List String) : XC_CapBandX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder
  have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  obtain ⟨v, hcoordC, hproperC, htitleRankEq⟩ :=
    xccb_title_coord_rank execution hcomp hrun hnode hborder hindexLt
  have hy0 := xccb_stored_y_eq (P := execution.params) hmem
  have hfit := xccb_exact_title_fit execution hnode hborder
  have hth : (transportCapSize execution.params o execution.lines comp i).2 +
      execution.params.clusterPad ≤ tNode.h := by
    have hfit2 := hfit.2
    cases hdir : o.direction <;> simp_all [transportCapSize, titleCaptionSize]
  have hgroupGet : (componentCandidate execution.graph comp candidate).nodes.getD i default =
      tNode := by
    simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hframeGroup : ((componentCandidate execution.graph comp candidate).nodes.getD i
      default).border = -2 := by
    rw [hgroupGet]
    exact hborder
  obtain ⟨box, hbox, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq hnode hborder
  have hpathCopy : (copyF (⟨tNode, false, none, false⟩, i)).node.clusterPath =
      tNode.clusterPath := rfl
  have hmemRect : (copyF (⟨tNode, false, none, false⟩, i), v) ∈
      run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hproperC
  have hcontains : (copyF (⟨tNode, false, none, false⟩, i)).node.clusterPath.contains
      ((componentCandidate execution.graph comp candidate).nodes.getD i default).decl =
      true := by
    rw [hgroupGet, hpathCopy, hpath]
    simp
  have htopLe := (frameRect_member_vertical (P := execution.params) hframeGroup hmemRect
    hcontains).1
  have hrectY : (Labels.rectAt run.proper run.xs run.ys v).y = run.ys.getD v 0 := rfl
  have hframeY : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run i).y ≤ run.ys.getD v 0 := by
    rw [← hrectY]
    exact htopLe
  obtain ⟨lvV, hlyV, _, hhiV⟩ := componentRunX_node_band hrun hproperC
    ⟨_, hcoordC, rfl, rfl⟩
  rw [htitleRankEq] at hlyV hhiV
  have hnodeH : RouteImpl.nodeH run.proper v = tNode.h := by
    simp only [RouteImpl.nodeH, hproperC, copyF]
  rw [hnodeH] at hhiV
  have hget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = lvV := by
    simp only [List.getD_eq_getElem?_getD, hlyV, Option.getD_some]
  have hhi : run.ys.getD v 0 + tNode.h ≤
      run.top.getD (rk run.coordinateProper.rank i).toNat 0 +
        CoordsImpl.layerHeight run.coordinateProper
          (run.layers.getD (rk run.coordinateProper.rank i).toNat []) := by
    rw [hget]
    exact hhiV
  have hcap : (transportCaption execution.params o execution.lines comp i stored0).y +
        (transportCaption execution.params o execution.lines comp i stored0).h =
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y +
          execution.params.clusterPad +
          (transportCapSize execution.params o execution.lines comp i).2 := by
    show stored0.y + (transportCapSize execution.params o execution.lines comp i).2 = _
    rw [hy0]
  omega



end PipelineImpl
end Layered
end Elegant
