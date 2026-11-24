import Elegant.Layered.ExactCaptionSelfProof
import Elegant.Layered.ExactTitleRunContext
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

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Copy of the private `PipelineFacts.mapM_index_record`: `mapM` preserves
length and each output element comes from one input element. -/
private theorem xcsn_mapM_index_record {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      xs.length = ys.length ∧
      ∀ (i : Nat) (y : β), ys[i]? = some y →
        ∃ x, xs[i]? = some x ∧ f x = .ok y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    change Except.ok [] = Except.ok ys at h
    injection h with heq
    subst ys
    refine ⟨rfl, ?_⟩
    intro i y hy
    simp at hy
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h
    cases hf : f x with
    | error e =>
      rw [hf] at h
      change Except.error e = Except.ok ys at h
      cases h
    | ok y =>
      cases ht : xs.mapM f with
      | error e =>
        rw [hf, ht] at h
        change Except.error e = Except.ok ys at h
        cases h
      | ok tail =>
        rw [hf, ht] at h
        change Except.ok (y :: tail) = Except.ok ys at h
        injection h with heq
        subst ys
        obtain ⟨hlen, hget⟩ := ih tail ht
        refine ⟨by simp [hlen], ?_⟩
        intro i z hz
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
          subst z
          exact ⟨x, rfl, hf⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hz
          obtain ⟨a, ha, he⟩ := hget i z hz
          exact ⟨a, by simpa using ha, he⟩

/-- Copy of the private `PipelineFacts.sizedNodes_index_metadata`: sized nodes
carry their index as declaration with border `0`. -/
private theorem xcsn_sizedNodes_index_metadata {P : Params}
    {lines : List (List Measure.Line)} {nodes : List Node}
    (h : sizedNodes P lines = .ok nodes) :
    nodes.length = lines.length ∧
      ∀ (i : Nat) (n : Node), nodes[i]? = some n → n.decl = i ∧ n.border = 0 := by
  unfold sizedNodes at h
  obtain ⟨hlen, hget⟩ := xcsn_mapM_index_record
    (fun (q : List Measure.Line × Nat) => sizedNode P q.2 q.1)
    lines.zipIdx nodes h
  refine ⟨by simpa using hlen.symm, ?_⟩
  intro i n hn
  obtain ⟨q, hq, hs⟩ := hget i n hn
  have hi : i < lines.length := by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hq
    simpa using hi
  have hqi : q.2 = i := by
    have hq' : lines.zipIdx[i]? = some (lines[i], i) := by simp [hi]
    rw [hq] at hq'
    exact congrArg Prod.snd (Option.some.inj hq')
  unfold sizedNode at hs
  cases hh : nodeSize P q.1 with
  | error e =>
    rw [hh] at hs
    change Except.error e = Except.ok n at hs
    cases hs
  | ok size =>
    rw [hh] at hs
    change Except.ok { decl := q.2, w := size.1, h := size.2, loopExtent := 0 } =
      Except.ok n at hs
    injection hs with heq
    subst n
    exact ⟨hqi, rfl⟩

/-- Copy of the private `PipelineFacts.measuredGraph_title_metadata`: a
border-`-2` node of the measured graph comes from a non-fixed group box and
carries the measured title dimensions. In particular a fixed-size box never
contributes a `-2` node, so the advisor's fixed-`w`-below-capW case cannot
occur for a titled group in any successful run. -/
private theorem xcsn_measuredGraph_title_metadata {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g) {j : Nat} {top : Node}
    (htop : g.nodes[j]? = some top) (hborder : top.border = -2) :
    j < lines.length ∧ top.decl = j ∧
      ∃ box, inp.boxes[j]? = some box ∧ box.role = .group ∧
        inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false ∧
        top.w = (match o.direction with
          | .LR | .RL => (max 1 (lines.getD j []).length : Int) * P.lineH
          | .TB | .BT => (lines.getD j []).foldl (fun w line => max w line.width) 0) ∧
        (match o.direction with
          | .LR | .RL => (lines.getD j []).foldl (fun w line => max w line.width) 0
          | .TB | .BT => (max 1 (lines.getD j []).length : Int) * P.lineH) +
            P.clusterPad ≤ top.h := by
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hg' := Except.ok.inj hg
  subst g
  obtain ⟨hlen, hinit⟩ := xcsn_sizedNodes_index_metadata hinitial
  obtain ⟨hprocessed, hget⟩ := xcsn_mapM_index_record _ _ _ hnodes
  have hnodeslen : nodes.length = lines.length := by simpa [hlen] using hprocessed.symm
  have hj : j < nodes.length := by
    by_cases hj : j < nodes.length
    · exact hj
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ j (by dsimp only; omega) htop
      omega
  obtain ⟨before, hbefore, hstep⟩ := hget j (nodes[j]) (by simp [hj])
  have hjinit : j < initial.length := by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hbefore
    simpa using hi
  have hbeforeEq : before = (orientNode o.direction initial[j], j) := by
    have he : ((initial.map (orientNode o.direction)).zipIdx)[j]? =
        some (orientNode o.direction initial[j], j) := by simp [hjinit]
    rw [hbefore] at he
    exact Option.some.inj he
  subst before
  have hmeta := hinit j initial[j] (by simp [hjinit])
  have hz : nodes[j].decl = j ∧ nodes[j].border = 0 := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · simp at hstep
    · split at hstep <;> (try split at hstep) <;>
        (try split at hstep) <;> (try split at hstep) <;>
        first
        | (have he := Except.ok.inj hstep
           rw [← he]
           cases o.direction <;> simpa [orientNode] using hmeta)
        | (simp [throw, throwThe, MonadExceptOf.throw] at hstep)
  obtain ⟨box, hb, hrole, hdecl, hw, hh, _, _⟩ :=
    Compound.prepare_group_title_of_border _ _ _ _ hj htop hborder
      (by dsimp only; rw [hz.2]; decide)
  cases horiginal : inp.boxes[j]? with
  | none => simp [List.getElem?_map, horiginal] at hb
  | some original =>
    simp only [List.getElem?_map, horiginal, Option.map_some, Option.some.injEq] at hb
    have heq := hb
    have hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == original.id) = false := by
      cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == original.id) with
      | false => rfl
      | true =>
        have hr := hrole
        rw [← heq] at hr
        simp [hf] at hr
    have hbox : original = box := by simpa [hfixed] using heq
    clear hb heq
    subst box
    have hjlines : j < lines.length := by omega
    refine ⟨hjlines, hdecl.trans hz.1, original, rfl, hrole, hfixed, ?_, ?_⟩
    · cases hd : o.direction <;>
        simpa [List.getD, List.getElem?_map, hjlines, hd] using hw
    · cases hd : o.direction <;>
        simpa [List.getD, List.getElem?_map, hjlines, hd] using hh

/-- Copy of the private `ExactFlatC5Rank.X_exactGraph_node_key_rev`: a node of
the exact graph comes from the same-index measured node with border, cluster
path, and declaration preserved. -/
private theorem xcsn_exactGraph_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
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

/-- Candidate nodes are positional: a candidate `-2` node comes from one
component index with the same full record. -/
private theorem xcsn_candidate_comp_index {g : Graph} {comp : List Nat}
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

/-- A `find?` for a fixed id is `none` when the `any` test is false. -/
private theorem xcsn_find?_of_any_false (l : List (String × Size)) (id : String)
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
unchanged: full record equality, not just key fields. -/
private theorem xcsn_exact_node_unchanged {P : Params} {exactIds : List String} {inp : Input}
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

/-- Exact title width and height fit: a border-`-2` exact-candidate node
carries the measured title dimensions, because the measured source is
non-fixed (so `exactGraph` leaves it unchanged) and exact membership would
have thrown. Plain path: `actual_title_caption_fit` transported across
`exactGraph`. -/
private theorem xcsn_exact_title_fit {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactTitleRunContext exactIds inp o)
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
  obtain ⟨j, hj, hcompD, hgraphGet, _⟩ := xcsn_candidate_comp_index hnode hborder
  obtain ⟨top0, htop0, hbord0, _, hdecl0⟩ :=
    xcsn_exactGraph_node_key_rev execution.graph_eq hgraphGet
  have hbord0' : top0.border = -2 := by omega
  obtain ⟨_, hdeclJ, box, hboxJ, _, hnofixed, hw0, hh0⟩ :=
    xcsn_measuredGraph_title_metadata execution.graph0_eq htop0 hbord0'
  have hbox0 : inp.boxes[top0.decl]? = some box := by rw [hdeclJ]; exact hboxJ
  have hnotexact : exactIds.contains box.id = false := by
    cases he : exactIds.contains box.id with
    | true =>
      have hge := execution.graph_eq
      unfold exactGraph at hge
      obtain ⟨nodes, hnodes, _⟩ := bind_ok hge
      obtain ⟨out, hout, _⟩ := (mapM_getElem? _ _ _ hnodes).2 j top0 htop0
      dsimp only at hout
      simp only [hbox0] at hout
      by_cases hc : ((!exactIds.contains box.id) &&
          !(box.role == .group && inp.fixedSizes.any (fun fixed => fixed.1 == box.id))) = true
      · rw [ite_eq_left hc] at hout
        simp only [pure, Except.pure] at hout
        have hcontra : ((!exactIds.contains box.id) &&
            !(box.role == .group && inp.fixedSizes.any (fun fixed => fixed.1 == box.id))) = false := by
          simp only [he, Bool.not_true, Bool.false_and]
        rw [hcontra] at hc
        cases hc
      · rw [ite_eq_right hc] at hout
        have hfind := xcsn_find?_of_any_false _ _ hnofixed
        simp only [hfind] at hout
        cases hout
    | false => rfl
  have hunch := xcsn_exact_node_unchanged execution.graph_eq htop0 hbox0 hnotexact hnofixed
  have heq : tNode = top0 := Option.some.inj (hgraphGet.symm.trans hunch)
  rw [heq, hcompD]
  exact ⟨hw0, hh0⟩


/-- Copy of `CaptionWidthFacts.coordinateGraph_title_record` over
`coordinateGraphX`/`sizeProperPortsX`: a border-`-2` labeled node has its
title copy in the exact coordinate graph. The size hook leaves border-`-2`
nodes alone, so the proof is the plain one with the `X` hook. -/
private theorem xcsn_coordinateGraphX_title_record (P : Params) (exact : List Nat)
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

/-- Copy of `CaptionWidthFacts.componentRun_group_title_width_source` over
`componentRunX`: the title copy of an exact group is present in both the
coordinate and the proper run graphs. -/
private theorem xcsn_group_title_width_source_X {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ v : Nat, run.coordinateProper.nodes[v]? =
        some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.proper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) := by
  obtain ⟨_, p0, labeled, q0, hnormalize, hlabels, hcoordinate, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have hnormalized := normalize_node_record hnormalize hnode
  have hlabeled := addLabelNodes_untouched_node hlabels hnormalized (by rfl)
  obtain ⟨j, _, hj⟩ := xcsn_coordinateGraphX_title_record P exact hlabeled hborder (by rfl)
  have hcoord : run.coordinateProper.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨node, false, none, false⟩, i)) := by
    rw [← hcoordinate]
    exact hj
  obtain ⟨_, _, _, _, _, hpreserve⟩ := proxyWidths_rel hproxy
  have hrouted : q0.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨node, false, none, false⟩, i)) :=
    (hpreserve _ _ hcoord (by simp [copyF])).1
  have hnodes : run.proper.nodes = q0.nodes := by
    have heq := congrArg Proper.nodes hdrop
    rw [OrderImpl.dropSynthetic_nodes] at heq
    exact heq.symm
  exact ⟨labeled.nodes.length + j, hcoord, by rw [hnodes]; exact hrouted⟩

/-- Copy of `CaptionWidthFacts.componentRun_title_coordinate_record` over
`componentRunX`: a border-`3` proper title keeps its coordinate record and
`xs` entry. -/
private theorem xcsn_title_coordinate_record_X {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {title : ProperNode} (htitle : run.proper.nodes[v]? = some title)
    (hborder : title.node.border = 3) :
    run.coordinateProper.nodes[v]? = some title ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  obtain ⟨_, _, hlength, _, hrecords, hunchanged⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by
    have heq := congrArg Proper.nodes hdrop
    rw [OrderImpl.dropSynthetic_nodes] at heq
    exact heq.symm
  have hv : v < run.coordinateProper.nodes.length := by
    have hv := (List.getElem?_eq_some_iff.mp htitle).1
    rw [hnodes, hlength] at hv
    exact hv
  have hsource : run.coordinateProper.nodes[v]? =
      some (run.coordinateProper.nodes[v]'hv) := List.getElem?_eq_getElem hv
  obtain ⟨updated, hupdated, _, hb, _⟩ := hrecords v _ hsource
  have heq : updated = title := by
    rw [← hnodes, htitle] at hupdated
    exact Option.some.inj hupdated.symm
  have hb3 : (run.coordinateProper.nodes[v]'hv).node.border = 3 := by
    rw [← hb, heq, hborder]
  obtain ⟨hrecord, hx⟩ := hunchanged v _ hsource (by omega)
  have hsourceEq : run.coordinateProper.nodes[v]'hv = title := by
    rw [← hnodes, htitle] at hrecord
    exact Option.some.inj hrecord.symm
  refine ⟨by simpa only [hsourceEq] using hsource, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Copy of `CaptionWidthFacts.componentRun_group_title_interval_source`
over `componentRunX`: title interval, `xs` agreement, and nonnegativity. -/
private theorem xcsn_group_title_interval_source_X {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ v : Nat, run.coordinateProper.nodes[v]? =
        some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.proper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 ∧
      (Labels.rectAt run.proper run.xs run.ys v).x =
        run.coordinateXs.getD v 0 - Int.fdiv node.w 2 ∧
      (Labels.rectAt run.proper run.xs run.ys v).w = node.w ∧
      0 ≤ node.w := by
  obtain ⟨v, hcoordinate, hproper⟩ :=
    xcsn_group_title_width_source_X h hnode hborder
  obtain ⟨_, _, _, _, _, _, _, _, hcross, hproxy, _⟩ := componentRunX_spec h
  obtain ⟨_, _, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  have hnonneg : 0 ≤ node.w := by
    simpa only [copyF] using
      (sizesNonneg_lookup hsizes v _ hcoordinate).1
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 v _ hcoordinate
    (by simp [copyF])).2
  have hxs : run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
  refine ⟨v, hcoordinate, hproper, hxs, ?_, ?_, hnonneg⟩
  · simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt,
      RouteImpl.nodeW, hproper, copyF, hxs]
  · simp only [Labels.rectAt, Labels.labelRect, RouteImpl.nodeW, hproper, copyF]

/-- Copy of `CaptionWidthFacts.componentRun_group_caption_placement_source`
over `componentRunX`: the installed title selected by the border-`3` search. -/
private theorem xcsn_group_caption_placement_source_X {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ title : ProperNode × Nat,
      (run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == node.clusterPath)) = some title ∧
      run.proper.nodes[title.2]? = some title.1 ∧
      title.1.node.border = 3 ∧ title.1.node.clusterPath = node.clusterPath ∧
      (i, Rect.mk
        (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
        ((frameRect P cg run i).y + P.clusterPad)
        node.w (node.h - P.clusterPad)) ∈ componentTitles P cg run := by
  obtain ⟨v, _, hproper⟩ := xcsn_group_title_width_source_X h hnode hborder
  have hmember :
      (copyF (⟨node, false, none, false⟩, i), v) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hproper
  cases hfind : run.proper.nodes.zipIdx.find? (fun q =>
      q.1.node.border == 3 && q.1.node.clusterPath == node.clusterPath) with
  | none =>
    have hmissing := List.find?_eq_none.mp hfind _ hmember
    simp [copyF] at hmissing
  | some title =>
    have hselected := List.find?_some hfind
    have hmetadata : title.1.node.border = 3 ∧
        title.1.node.clusterPath = node.clusterPath := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using hselected
    have hlookup : run.proper.nodes[title.2]? = some title.1 :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind)
    refine ⟨title, rfl, hlookup, hmetadata.1, hmetadata.2, ?_⟩
    unfold componentTitles
    apply List.mem_filterMap.mpr
    refine ⟨(node, i), List.mk_mem_zipIdx_iff_getElem?.mpr hnode, ?_⟩
    simp [hborder, hfind]

/-- Copy of the private `ExactBorderChainXAlignedProof.XBC_border_record`:
border markers keep their coordinates and `xs` entries through the exact
reserve stage (which shifts only `ys`/`top`). -/
private theorem xcsn_border_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Copy of the private `CaptionSelfSidesProof.captionTitles_keys_nodup_copy`:
installed titles carry at most one rect per component index. -/
private theorem xcsn_captionTitles_keys_nodup_copy (P : Params) (cg : Graph) (run : Run) :
    ((componentTitles P cg run).map Prod.fst).Nodup := by
  let emit : Node × Nat → Option (Nat × Rect) := fun top => do
    if top.1.border != -2 then none else do
      let title ← run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath)
      let frame := frameRect P cg run top.2
      pure (top.2, Rect.mk
        (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
        (frame.y + P.clusterPad) top.1.w (top.1.h - P.clusterPad))
  have identity : ∀ top caption, emit top = some caption → caption.1 = top.2 := by
    intro top caption he
    unfold emit at he
    split at he
    · contradiction
    · cases hf : run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
      | none => simp [hf] at he
      | some title =>
        simp [hf] at he
        subst caption
        rfl
  have hindices : (cg.nodes.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hp := List.pairwise_map.mp hindices
  change ((componentTitles P cg run).map Prod.fst).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  change (cg.nodes.zipIdx.filterMap emit).Pairwise (fun a b => a.1 ≠ b.1)
  apply List.Pairwise.filterMap emit _ hp
  intro a b hne ca hca cb hcb
  rw [identity a ca hca, identity b cb hcb]
  exact hne

/-- Copy of the private `xcs_stored_y_eq` from `ExactCaptionSelfProof`: the
stored title y equals its own frame y plus `clusterPad`. -/
private theorem xcsn_stored_y_eq {P : Params} {cg : Graph} {run : Run}
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


/-- Copy of `titled_rank_prefix` over `sizeProperPortsX`. -/
private theorem xcsn_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank = source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

/-- Copy of `titled_rank_record` over `sizeProperPortsX`. -/
private theorem xcsn_titled_rank_record (P : Params) (exact : List Nat) {source : Proper}
    {index : Nat} {rank : Int}
    (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := xcsn_titled_rank_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Copy of `source_alignment_of_titled` over `sizeProperPortsX`. -/
private theorem xcsn_source_alignment_of_titled (P : Params) (exact : List Nat) {source : Proper}
    (h : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length) :
    source.nodes.length = source.rank.length := by
  rw [titleReservations_nodes] at h
  simp only [List.length_append, List.length_map, sizeProperPortsX_length] at h
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank] at h
  simp only [List.length_append, List.length_map] at h
  omega

/-- Copy of `prepared_titled_original_rk` over `sizeProperPortsX`. -/
private theorem xcsn_prepared_titled_original_rk {P : Params} {cg : Graph} {exact : List Nat}
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
  have htitledLookup := xcsn_titled_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index

/-- Copy of `titled_copy_rank_record` over `sizeProperPortsX`. -/
private theorem xcsn_titled_copy_rank_record (P : Params) (exact : List Nat) {source : Proper}
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

/-- Copy of `coordinateGraph_titled_rank_record` over `coordinateGraphX`. -/
private theorem xcsn_coordinateGraph_titled_rank_record (P : Params) (exact : List Nat)
    {source : Proper} {index : Nat} {rank : Int}
    (h : (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).rank[index]? = some rank
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Copy of `coordinateGraph_side_record` over `coordinateGraphX`. -/
private theorem xcsn_coordinateGraph_side_record (P : Params) (exact : List Nat) {source : Proper}
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

/-- Copy of `coordinateGraph_rank_pair` over `coordinateGraphX`: the two side
borders at one title rank. -/
private theorem xcsn_coordinateGraph_rank_pair_X (P : Params) (exact : List Nat) (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤ rank)
    (hhi : rank ≤ (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
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
  refine ⟨left, right, xcsn_coordinateGraph_side_record P exact hl rfl (Or.inl rfl),
    xcsn_coordinateGraph_side_record P exact hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

/-- Copy of `componentRun_requested_group_range` over `componentRunX`: the
requested group rank covers its bottom marker rank. -/
private theorem xcsn_requested_group_range_X {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactTitleRunContext exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {labeled : Proper}
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
    (hgroup : node.border = -2) {bottom : ProperNode × Nat}
    (hbottom : ((titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
        some bottom) :
    (rk (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).rank index).toNat ≤
      (rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank bottom.2).toNat := by
  let requested : ProperNode := titleF ⟨node, false, none, false⟩
  let proxy : ProperNode := clearF requested
  have htitled : (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).nodes[index]? =
      some requested := X_titled_marker_record (hrecords index node hnode) (Or.inl hgroup)
  have htitledBorder : requested.node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys requested).2.1.trans htitledBorder
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact X_coordinateGraph_marker_record (hrecords index node hnode)
      (Or.inl hgroup) rfl
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  have hcoordinate : (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).nodes[sideIndex]? = some side := by
    rw [hc]
    exact hside
  have hsource := X_side_original hready hcoordinate hsideBorder
  obtain ⟨anchor, hanchor, generatedBottom, hfind, hpath, hrange⟩ :=
    addClusterBorders_side_range_source _ _ hready (List.mem_of_getElem? hsource) hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  have hownerEq : anchor.1.node.clusterPath.getLast? =
      requested.node.clusterPath.getLast? := by
    rw [← hpath, ← (clearF_keys requested).2.2.1]
    exact hsideOwner.trans howner.symm
  have hindex := X_titled_group_owner_unique execution.graph0_eq execution.graph_eq
    hcomp hk hrecords hanchorLookup htitled hanchorBorder htitledBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[anchor.2]? = some requested := by
    rw [hindex]
    exact htitled
  have hanchorEq : anchor.1 = requested :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  rw [hanchorEq] at hfind
  have hfindForNode :
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == node.clusterPath) =
          some generatedBottom := by
    simpa only [requested, titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] using hfind
  have hbottomEq : generatedBottom = bottom := Option.some.inj (hfindForNode.symm.trans hbottom)
  rw [hindex, hbottomEq] at hrange
  exact hrange

/-- Exact coordinate borders are well formed: copy of
`componentRun_coordinate_bordersWellFormed` over `coordinateGraphX`. -/
private theorem xcsn_bordersWellFormed_X {P : Params} {exact : List Nat} {labeled : Proper}
    {run : Run}
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady (titleReservations
      (sizeProperPortsX P exact labeled))) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  rw [← hc]
  unfold coordinateGraphX
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready



/-- Copy of the private `ExactFlatC2.X_sized_length`: `sizeProperPortsX`
preserves the node count. -/
private theorem xcsn_sized_length (P : Params) (exact : List Nat) (p : Proper) :
    (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
  unfold sizeProperPortsX
  simp

/-- Copy of the private `ExactFlatC2.X_coordinateGraph0_lookup`: node
classification below materialization. -/
private theorem xcsn_coordinateGraph0_lookup (P : Params) (exact : List Nat)
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
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := xcsn_sized_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
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
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Copy of the private `ExactFlatC2.X_coordinateGraph_lookup`: node
classification for `coordinateGraphX`. -/
private theorem xcsn_coordinateGraph_lookup (P : Params) (exact : List Nat)
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
  rcases xcsn_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
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

/-- Copy of the private `ExactFlatC2.X_pc_title_unique`: exact coordinate
titles are unique per cluster path. -/
private theorem xcsn_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
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
    rcases xcsn_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
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
/-- Copy of `componentRun_group_title_borders` over `componentRunX`: the two
side borders at the title rank of an exact group. The title copy index comes
straight from the title reservation (no top-uniqueness indirection needed). -/
private theorem xcsn_group_title_borders_X {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactTitleRunContext exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index titleIndex : Nat} {node : Node} {title : ProperNode}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (htitle : run.coordinateProper.nodes[titleIndex]? = some title)
    (htitleBorder : title.node.border = 3)
    (htitlePath : title.node.clusterPath = node.clusterPath) :
    title.dummy = false ∧ ∃ left right : Nat,
      run.coordinateProper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? =
        some (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank titleIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank titleIndex := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩ :=
    X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hnode hgroup
  have hshape : CgShape (componentCandidate execution.graph comp candidate) :=
    componentCandidate_shape (components_nodup execution.graph comp hcomp)
      (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate
  obtain ⟨j, hjEntry, hjCoord⟩ := xcsn_coordinateGraphX_title_record
    execution.params (exactDecls exactIds inp)
    (hrecords index node hnode) hgroup (by rfl)
  have htitleX : (coordinateGraphX execution.params (exactDecls exactIds inp) labeled).nodes[titleIndex]? =
      some title := by
    rw [hc]
    exact htitle
  have htitleIdx : titleIndex = labeled.nodes.length + j :=
    xcsn_pc_title_unique hk hshape htitleX hjCoord htitleBorder (by rfl)
      (by rw [htitlePath]; rfl)
  have hjCoordRun : run.coordinateProper.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨node, false, none, false⟩, index)) := by
    rw [← hc]
    exact hjCoord
  have htitleEq : title = copyF (⟨node, false, none, false⟩, index) := by
    have h1 := htitle
    rw [htitleIdx] at h1
    exact Option.some.inj (h1.symm.trans hjCoordRun)
  have htitleReal : title.dummy = false := by rw [htitleEq]; rfl
  have halignedSrc := xcsn_source_alignment_of_titled execution.params
    (exactDecls exactIds inp) hready.2.2.2.1
  have hcopyRank := xcsn_titled_copy_rank_record execution.params
    (exactDecls exactIds inp) halignedSrc hjEntry
  have hcoordRank := xcsn_coordinateGraph_titled_rank_record execution.params
    (exactDecls exactIds inp) hcopyRank
  have hsourceBound : index < labeled.rank.length := by
    have hn := (List.getElem?_eq_some_iff.mp (hrecords index node hnode)).1
    omega
  have hsourceRank : labeled.rank[index]? = some labeled.rank[index] :=
    List.getElem?_eq_getElem hsourceBound
  have htitledRank := xcsn_titled_rank_record execution.params
    (exactDecls exactIds inp) hsourceRank
  have hsourceToTitled :
      rk labeled.rank index =
        rk (titleReservations (sizeProperPortsX execution.params
          (exactDecls exactIds inp) labeled)).rank index := by
    simp only [rk, List.getD_eq_getElem?_getD, hsourceRank, htitledRank, Option.getD_some]
  have htitleToTitled : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank titleIndex =
      rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank index := by
    have htitleRankEqX : rk (coordinateGraphX execution.params
        (exactDecls exactIds inp) labeled).rank (labeled.nodes.length + j) =
        rk labeled.rank index := by
      simp only [rk, List.getD_eq_getElem?_getD, hcoordRank, Option.getD_some]
    rw [htitleIdx, htitleRankEqX]
    exact hsourceToTitled
  obtain ⟨htopRank, htopNN⟩ := xcsn_prepared_titled_original_rk hrr hranks
    (List.getElem?_eq_some_iff.mp hnode).1
  have hrange := xcsn_requested_group_range_X execution hcomp hrun hc hk hready
    hrecords hnode hgroup hbottom
  have htopBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hpathTF : (titleF ⟨node, false, none, false⟩).node.clusterPath = node.clusterPath :=
    (titleF_keys _).2.2.1
  have hbottom' : ((titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 &&
        entry.1.node.clusterPath ==
          (titleF ⟨node, false, none, false⟩).node.clusterPath) =
      some bottom := by
    rw [hpathTF]
    exact hbottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    xcsn_coordinateGraph_rank_pair_X execution.params (exactDecls exactIds inp) labeled
      hready.2.2.2.1 (List.mk_mem_zipIdx_iff_getElem?.mpr htitled) htopBorder hbottom'
      (rank := (rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank index).toNat)
      (Nat.le_refl _)
      hrange
  have hcast : ((rk (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).rank index).toNat : Int) =
      rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank index :=
    Int.toNat_of_nonneg htopNN
  have hlvalue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank left =
      rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank index := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hcast
  have hrightValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank right =
      rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank index := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hcast
  refine ⟨htitleReal, ?_⟩
  rw [← hc]
  exact ⟨left, right, hleft, hright, hlvalue.trans htitleToTitled.symm,
    hrightValue.trans htitleToTitled.symm⟩

/-- Copy of `componentRun_group_title_bracket` over `componentRunX`: the
title, left, and right markers lie on one layer in order. -/
private theorem xcsn_group_title_bracket_X {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactTitleRunContext exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index titleIndex : Nat} {node : Node} {title : ProperNode}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (htitle : run.coordinateProper.nodes[titleIndex]? = some title)
    (htitleBorder : title.node.border = 3)
    (htitlePath : title.node.clusterPath = node.clusterPath) :
    ∃ (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧ ord.layers = run.layers ∧
      run.coordinateProper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? =
        some (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left titleIndex right := by
  obtain ⟨_, _, _, hc, _, hready, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  obtain ⟨htitleReal, left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    xcsn_group_title_borders_X execution hcomp hrun hnode hgroup htitle htitleBorder htitlePath
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hwf := xcsn_bordersWellFormed_X hc hready
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper titleIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper titleIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  have hprefix :
      (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
        execution.params.clusterBorderW).node.clusterPath <+: title.node.clusterPath := by
    refine ⟨[], ?_⟩
    simp only [List.append_nil]
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = title.node.clusterPath
    exact (titleF_keys _).2.2.1.trans htitlePath.symm
  refine ⟨ord, left, right, horder, hlayers, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.title_bracket run.coordinateProper orderOptions ord horder hwf
    left titleIndex right _ title _ hleft htitle hright hleftLay hrightLay
    rfl htitleBorder rfl rfl htitleReal rfl hprefix hprefix



/-- Exact cross-axis bundle: the title copy, its `xs` agreement, the installed
placement at measured size, and the measured width fit. Replay of
`measured_component_caption_cross_axis_source` plus the selected-copy step
and `actual_title_caption_fit`, transported across `exactGraph`. -/
private theorem xcsn_cross_axis_bundle_X {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactTitleRunContext exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {i : Nat} {tNode : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    ∃ (v : Nat) (title : ProperNode × Nat),
      (run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == tNode.clusterPath)) =
        some title ∧
      run.proper.nodes[title.2]? = some title.1 ∧
      run.coordinateProper.nodes[v]? =
        some (copyF (⟨tNode, false, none, false⟩, i)) ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 ∧
      (i, Rect.mk (run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2)
        ((frameRect execution.params
          (componentCandidate execution.graph comp candidate) run i).y +
          execution.params.clusterPad) tNode.w (tNode.h - execution.params.clusterPad)) ∈
        componentTitles execution.params
          (componentCandidate execution.graph comp candidate) run ∧
      tNode.w = (match o.direction with
        | .LR | .RL => (max 1 (execution.lines.getD (comp.getD i 0) []).length : Int) *
          execution.params.lineH
        | .TB | .BT => (execution.lines.getD (comp.getD i 0) []).foldl
          (fun w line => max w line.width) 0) := by
  obtain ⟨v, hcoordC, hproperC, hxs, _, _, _⟩ :=
    xcsn_group_title_interval_source_X hrun hnode hborder
  obtain ⟨titleSel, hfindSel, hlookup, hselBord, hselPath, hplaceXS⟩ :=
    xcsn_group_caption_placement_source_X hrun hnode hborder
  obtain ⟨hcoordSel, _⟩ := xcsn_title_coordinate_record_X hrun hlookup hselBord
  obtain ⟨_, labeled, _, hc, hk, _, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hshape : CgShape (componentCandidate execution.graph comp candidate) :=
    componentCandidate_shape (components_nodup execution.graph comp hcomp)
      (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate
  have hidx : titleSel.2 = v := by
    apply xcsn_pc_title_unique hk hshape
    · rw [hc]; exact hcoordSel
    · rw [hc]; exact hcoordC
    · exact hselBord
    · rfl
    · rw [hselPath]; rfl
  have htitleEq : titleSel = (copyF (⟨tNode, false, none, false⟩, i), v) := by
    have hrec : titleSel.1 = copyF (⟨tNode, false, none, false⟩, i) := by
      have h1 := hlookup
      rw [hidx] at h1
      exact Option.some.inj (h1.symm.trans hproperC)
    exact Prod.ext hrec hidx
  subst titleSel
  obtain ⟨hw, _⟩ := xcsn_exact_title_fit execution hnode hborder
  refine ⟨v, _, hfindSel, hlookup, hcoordC, hxs, ?_, hw⟩
  have h2 := hplaceXS
  dsimp only at h2
  rw [hxs] at h2
  exact h2

/-- Exact self-sides core: the transported caption keeps a positive gap from
the left and right edges of its own frame. Replay of
`captionSelfSidesStrict_executed` over `componentRunX`. -/
theorem componentRunX_title_inside_frame_x
    {exactIds : List String} {inp : Input} {o : Options}
    (execution : ExactTitleRunContext exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {i : Nat} {stored0 : Rect} {tNode : Node}
    (hmem : (i, stored0) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run i).x <
      (transportCaption execution.params o execution.lines comp i stored0).x ∧
    (transportCaption execution.params o execution.lines comp i stored0).x +
        (transportCaption execution.params o execution.lines comp i stored0).w <
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run i).x +
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run i).w := by
  obtain ⟨v, _, _, _, hcoordC, hxs, hplacement, hwidthEq⟩ :=
    xcsn_cross_axis_bundle_X execution hcomp hrun hnode hborder
  obtain ⟨ord, left, right, _, hlayers, hleft, hright, hbracket⟩ :=
    xcsn_group_title_bracket_X execution hcomp hrun hnode hborder hcoordC (by rfl) (by rfl)
  obtain ⟨li, ti, ri, hli, hti, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hti hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨_, labeled, _, hc, hk, _, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hshape : CgShape (componentCandidate execution.graph comp candidate) :=
    componentCandidate_shape (components_nodup execution.graph comp hcomp)
      (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact xcsn_pc_title_unique hk hshape
      (by rw [hc]; exact ha) (by rw [hc]; exact hb) hba hbb hp
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li ti left v _ _ hlt hli hti hleft hcoordC
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    (by change (3 : Int) ≠ -2; decide) (by change (3 : Int) ≠ 2; decide)
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    ti ri v right _ _ htr hti hri hcoordC hright
    (by change (3 : Int) ≠ -2; decide) (by change (3 : Int) ≠ 2; decide)
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  obtain ⟨hleftFinal, hleftX⟩ :=
    xcsn_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ :=
    xcsn_border_record hrun hright (Or.inr rfl)
  have hwidth : 0 ≤ tNode.w := by
    simpa only [copyF] using (sizesNonneg_lookup hsizes v _ hcoordC).1
  have hsideWidth : 0 ≤ execution.params.clusterBorderW := by
    simpa only [OrderImpl.borderLeft] using
      (sizesNonneg_lookup hsizes left _ hleft).1
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  have htitleLeftStrict : (Labels.rectAt run.proper run.xs run.ys left).x <
      run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2 := by
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hleft, hcoordC, copyF,
      OrderImpl.borderLeft, titleF, hborder] at hleftSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hleftX, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  have htitleRightStrict : run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2 + tNode.w <
      (Labels.rectAt run.proper run.xs run.ys right).x +
        (Labels.rectAt run.proper run.xs run.ys right).w := by
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hright, hcoordC, copyF,
      OrderImpl.borderRight, titleF, hborder] at hrightSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hrightFinal, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega
  obtain ⟨_, _, _, hgraphGet, _⟩ := xcsn_candidate_comp_index hnode hborder
  obtain ⟨top0, htop0, hbord0, hpath0, hdecl0⟩ :=
    xcsn_exactGraph_node_key_rev execution.graph_eq hgraphGet
  have hbord0' : top0.border = -2 := by omega
  obtain ⟨_, _, _, _, hpathG⟩ :=
    measuredGraph_group_origin execution.graph0_eq htop0 hbord0'
  have howner : tNode.clusterPath.getLast? = some tNode.decl := by
    rw [hpath0, hdecl0, hpathG]
    simp
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some tNode.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, left), List.mk_mem_zipIdx_iff_getElem?.mpr hleftFinal, ?_⟩
    simp [OrderImpl.borderLeft, titleF, hborder, howner]
  have hrightMem : Labels.rectAt run.proper run.xs run.ys right ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, right), List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal, ?_⟩
    simp [OrderImpl.borderRight, titleF, hborder, howner]
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys left) hleftMem
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hframeX :
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).x =
        (boundsOf borders []).minX := by
    simp [frameRect, List.getD_eq_getElem?_getD, hnode, hborder, borders]
  have hframeW :
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).w =
        (boundsOf borders []).right - (boundsOf borders []).minX := by
    exact frameRect_group_width_eq_horizontal_span hnode hborder
  have hnodup := xcsn_captionTitles_keys_nodup_copy execution.params
    (componentCandidate execution.graph comp candidate) run
  have huniq : stored0 = Rect.mk
      (run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2)
      ((frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y +
        execution.params.clusterPad) tNode.w (tNode.h - execution.params.clusterPad) :=
    captionTitles_at_inj hnodup hmem hplacement
  have hcapW : (transportCapSize execution.params o execution.lines comp i).1 = tNode.w := by
    have e1 : (transportCapSize execution.params o execution.lines comp i).1 =
        (match o.direction with
          | .LR | .RL => (max 1 (execution.lines.getD (comp.getD i 0) []).length : Int) *
            execution.params.lineH
          | .TB | .BT => (execution.lines.getD (comp.getD i 0) []).foldl
            (fun w line => max w line.width) 0) := by
      unfold transportCapSize titleCaptionSize
      cases o.direction <;> rfl
    rw [e1]
    exact hwidthEq.symm
  have hcapX : (transportCaption execution.params o execution.lines comp i stored0).x =
      run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2 := by
    have hx : (transportCaption execution.params o execution.lines comp i stored0).x =
      stored0.x := rfl
    rw [hx, huniq]
  have hcapW' : (transportCaption execution.params o execution.lines comp i stored0).w =
      tNode.w := by
    have hw : (transportCaption execution.params o execution.lines comp i stored0).w =
      (transportCapSize execution.params o execution.lines comp i).1 := rfl
    rw [hw, hcapW]
  constructor
  · rw [hcapX]
    omega
  · rw [hcapX, hcapW', hframeX, hframeW]
    omega

/-- Exact self-sides left narrow fact, proved by replaying the plain
title-copy versus left-marker separation over `componentRunX`. -/
theorem XC_selfSidesLeftNarrowX_holds (exactIds : List String) :
    XC_SelfSidesLeftNarrowX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder
  exact (componentRunX_title_inside_frame_x execution.exactTitleContext hcomp hrun
    hmem hnode hborder).1

/-- Exact self-sides right narrow fact, proved by replaying the plain
title-copy versus right-marker separation over `componentRunX`. -/
theorem XC_selfSidesRightNarrowX_holds (exactIds : List String) :
    XC_SelfSidesRightNarrowX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder
  exact (componentRunX_title_inside_frame_x execution.exactTitleContext hcomp hrun
    hmem hnode hborder).2

/-- Closed exact self-sides: both narrow halves hold, so the combination
theorem from `ExactCaptionSelfProof` applies. -/
theorem XC_selfSidesX_closed (exactIds : List String) : XC_SelfSidesX exactIds :=
  XC_selfSidesX_holds exactIds (XC_selfSidesLeftNarrowX_holds exactIds)
    (XC_selfSidesRightNarrowX_holds exactIds)

theorem componentRunX_group_frame_dims_pos {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run index).w ∧
    0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run index).h := by
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  have hpad : 0 < execution.params.clusterPad :=
    checkedParams_clusterPad_pos execution.checked
  obtain ⟨_, hfit⟩ := xcsn_exact_title_fit execution.exactTitleContext hnode hgroup
  obtain ⟨v, hcoordC, hproperTitle, _, _, _, _⟩ :=
    xcsn_group_title_interval_source_X hrun hnode hgroup
  obtain ⟨_, left, _, hleft, _, _, _⟩ :=
    xcsn_group_title_borders_X execution.exactTitleContext hcomp hrun hnode hgroup hcoordC
    (by rfl) (by rfl)
  obtain ⟨hleftFinal, _⟩ := xcsn_border_record hrun hleft (Or.inl rfl)
  obtain ⟨_, _, _, hgraphGet, _⟩ := xcsn_candidate_comp_index hnode hgroup
  obtain ⟨top0, htop0, hbord0, hpath0, hdecl0⟩ :=
    xcsn_exactGraph_node_key_rev execution.graph_eq hgraphGet
  have hbord0' : top0.border = -2 := by omega
  obtain ⟨_, _, _, _, hpathG⟩ :=
    measuredGraph_group_origin execution.graph0_eq htop0 hbord0'
  have howner : node.clusterPath.getLast? = some node.decl := by
    rw [hpath0, hdecl0, hpathG]
    simp
  have hownerMem := List.mem_of_getLast? howner
  have hleftW : (Labels.rectAt run.proper run.xs run.ys left).w =
      execution.params.clusterBorderW := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.nodeW, hleftFinal,
      OrderImpl.borderLeft]
    rfl
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some node.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, left), List.mk_mem_zipIdx_iff_getElem?.mpr hleftFinal, ?_⟩
    simp [OrderImpl.borderLeft, titleF, hgroup, howner]
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys left) hleftMem
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys left) hleftMem
  have htitleH : (Labels.rectAt run.proper run.xs run.ys v).h = node.h := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.nodeH, hproperTitle, copyF]
  let members := run.proper.nodes.zipIdx.filterMap fun q =>
    if q.1.node.clusterPath.contains node.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have htitleMem : Labels.rectAt run.proper run.xs run.ys v ∈ members := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, v), List.mk_mem_zipIdx_iff_getElem?.mpr hproperTitle, ?_⟩
    simp [copyF, hownerMem]
  have htop := boundsOf_minY_le_rect_y members []
    (Labels.rectAt run.proper run.xs run.ys v) htitleMem
  have hbot := rect_bottom_le_boundsOf_bottom members []
    (Labels.rectAt run.proper run.xs run.ys v) htitleMem
  let lines := execution.lines.getD (comp.getD index 0) []
  have hwidth : 0 ≤ lines.foldl (fun w line => max w line.width) 0 := by
    simpa only [List.foldl_map, Function.comp_def] using
      CoordsImpl.le_foldl_max (lines.map (·.width)) 0
  have hheight : 0 ≤ (max 1 (lines.length : Int)) * execution.params.lineH :=
    Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg execution.checked)
  have hnodeHpos : 0 < node.h := by
    change (match o.direction with
      | .LR | .RL => lines.foldl (fun w line => max w line.width) 0
      | .TB | .BT => (max 1 (lines.length : Int)) * execution.params.lineH) +
        execution.params.clusterPad ≤ node.h at hfit
    cases hd : o.direction <;> rw [hd] at hfit <;>
      first
      | exact Int.lt_of_lt_of_le
          (show 0 < lines.foldl (fun w line => max w line.width) 0 +
            execution.params.clusterPad by omega) hfit
      | exact Int.lt_of_lt_of_le
          (show 0 < (max 1 (lines.length : Int)) * execution.params.lineH +
            execution.params.clusterPad by omega) hfit
  refine ⟨?_, ?_⟩
  · have hframeW :
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run index).w =
          (boundsOf borders []).right - (boundsOf borders []).minX :=
      frameRect_group_width_eq_horizontal_span hnode hgroup
    rw [hframeW]
    omega
  · have hframeH :
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run index).h =
          (boundsOf members []).bottom - (boundsOf members []).minY :=
      frameRect_group_height_eq_vertical_span hnode hgroup
    rw [hframeH]
    omega

end PipelineImpl
end Layered
end Elegant
