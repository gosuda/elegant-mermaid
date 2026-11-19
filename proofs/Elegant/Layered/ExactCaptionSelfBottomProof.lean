import Elegant.Layered.ExactCaptionSelfProof
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
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.GroupFrameSizingFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Target: `XC_SelfBottomHeightNarrowX` (`ExactCaptionSelfProof.lean`).
For a group caption in an exact run, the caption band at the group's top
fits above the group's bottom: frame height exceeds the padded caption
height. Fixed-size groups carry no border-`-2` node (the fixed treatment
replaces them), so the fact is vacuous for them; the probes
(`ExactCaptionSelfBottomProbe`: flat, empty, nested-fixed, fixed-10x10
with short and long titles) all hold. Proved below via the measured
title fit plus a strict frame excess from the bottom marker band. -/

/-- Copy of the private `PipelineFacts.mapM_index_record`. -/
private theorem xcsbb_mapM_index_record {α β : Type} (f : α → Except LayoutError β) :
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

 /-- Copy of the private `PipelineFacts.sizedNodes_index_metadata`. -/
 private theorem xcsbb_sizedNodes_index_metadata {P : Params}
     {lines : List (List Measure.Line)} {nodes : List Node}
     (h : sizedNodes P lines = .ok nodes) :
     nodes.length = lines.length ∧
       ∀ (i : Nat) (n : Node), nodes[i]? = some n → n.decl = i ∧ n.border = 0 := by
   unfold sizedNodes at h
   obtain ⟨hlen, hget⟩ := xcsbb_mapM_index_record
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

 /-- Copy of the private `PipelineFacts.measuredGraph_title_metadata`. -/
 private theorem xcsbb_measuredGraph_title_metadata {P : Params} {inp : Input} {o : Options}
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
   obtain ⟨hlen, hinit⟩ := xcsbb_sizedNodes_index_metadata hinitial
   obtain ⟨hprocessed, hget⟩ := xcsbb_mapM_index_record _ _ _ hnodes
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

 /-- Copy of the private `ExactFlatC5Rank.X_exactGraph_node_key_rev`. -/
 private theorem xcsbb_exactGraph_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
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

 /-- Candidate nodes are positional. -/
 private theorem xcsbb_candidate_comp_index {g : Graph} {comp : List Nat}
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
 private theorem xcsbb_find?_of_any_false (l : List (String × Size)) (id : String)
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

 /-- An exact-graph node whose box is neither exact nor group-fixed is unchanged. -/
 private theorem xcsbb_exact_node_unchanged {P : Params} {exactIds : List String} {inp : Input}
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

 /-- Exact title width and height fit for a border-`-2` exact-candidate node. -/
 private theorem xcsbb_exact_title_fit {exactIds : List String} {inp : Input}
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
   obtain ⟨j, hj, hcompD, hgraphGet, _⟩ := xcsbb_candidate_comp_index hnode hborder
   obtain ⟨top0, htop0, hbord0, _, hdecl0⟩ :=
     xcsbb_exactGraph_node_key_rev execution.graph_eq hgraphGet
   have hbord0' : top0.border = -2 := by omega
   obtain ⟨_, hdeclJ, box, hboxJ, _, hnofixed, hw0, hh0⟩ :=
     xcsbb_measuredGraph_title_metadata execution.graph0_eq htop0 hbord0'
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
         have hfind := xcsbb_find?_of_any_false _ _ hnofixed
         simp only [hfind] at hout
         cases hout
     | false => rfl
   have hunch := xcsbb_exact_node_unchanged execution.graph_eq htop0 hbox0 hnotexact hnofixed
   have heq : tNode = top0 := Option.some.inj (hgraphGet.symm.trans hunch)
   rw [heq, hcompD]
   exact ⟨hw0, hh0⟩

 /-- Copy of `CaptionWidthFacts.coordinateGraph_title_record` over `coordinateGraphX`. -/
 private theorem xcsbb_coordinateGraphX_title_record (P : Params) (exact : List Nat)
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

 /-- `XCM_` copy of `componentRun_proxy_interval` over `componentRunX_spec`. -/
 private theorem xcsbb_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run)
     {index : Nat} {node : ProperNode}
     (hnode : run.coordinateProper.nodes[index]? = some node)
     (hborder : node.node.border = -2 ∨ node.node.border = 2) :
     ∃ (owner : Nat) (span : FramePorts.Span),
       node.node.clusterPath.getLast? = some owner ∧
       proxySpan run.coordinateProper run.coordinateXs owner index = .ok span ∧
       run.proper.nodes[index]? =
         some { node with node := { node.node with w := span.hi - span.lo } } ∧
       0 ≤ span.hi - span.lo ∧
       RouteImpl.leftOf run.proper run.xs index = span.lo ∧
       RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index = span.hi := by
   obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
   have nodesEq : run.proper.nodes = q0.nodes := by
     rw [← hdrop]
     rfl
   obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
     proxyWidths_proxy_interval hproxy hnode hborder
   refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
   · simpa only [nodesEq] using outputNode
   · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
   · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

 /-- X bottom marker coordinate record from candidate records and the public marker record. -/
 private theorem xcsbb_bottom_coordinate {P : Params} {exact : List Nat} {cg : Graph}
     {labeled : Proper} {run : Run}
     (hc : coordinateGraphX P exact labeled = run.coordinateProper)
     (hrec : ∀ (index : Nat) (node : Node),
       cg.nodes[index]? = some node → labeled.nodes[index]? = some ⟨node, false, none, false⟩)
     {v : Nat} {nd : Node}
     (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = 2) :
     ∃ coord : ProperNode,
       run.coordinateProper.nodes[v]? = some coord ∧
       coord.node.border = 2 ∧ coord.dummy = false ∧
       coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
   have hrec := hrec v nd hnode
   have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact) hrec (Or.inr hgroup) rfl
   rw [hc] at hmarker
   refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
   · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
     rw [hb, (titleF_keys _).2.1]
     exact hgroup
   · exact (clearF_keys _).1.trans (titleF_keys _).1
   · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
   · exact (clearF_keys _).2.2.2.trans
       ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))

 /-- X bottom marker proper record with zero height from the proxy interval. -/
 private theorem xcsbb_bottom_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     {v : Nat} {coord : ProperNode}
     (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      p.node.border = coord.node.border ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
    xcsbb_proxy_interval hrun hcoord (Or.inr hb)
  refine ⟨_, hproper, rfl, rfl, ?_⟩
  simp only [RouteImpl.nodeH, hproper]
  exact hcoordH

 /-- Exact pre-reserve coordinates: unfold one `componentRunX` to expose the rank-axis output. -/
 private theorem xcsbb_run_pre {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run) :
     ∃ (y_pre top_pre ys_pre : List Int),
       rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
         (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
       proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
       reserveExactRanks cg exact labels run.coordinateProper run.layers ys_pre top_pre =
         .ok (run.ys, run.top) ∧
       run.coordinateYs = y_pre := by
   unfold componentRunX at h
   obtain ⟨rr, _, h⟩ := bind_ok h
   obtain ⟨p0, hp0, h⟩ := bind_ok h
   obtain ⟨q, hq, h⟩ := bind_ok h
   obtain ⟨ord, hord, h⟩ := bind_ok h
   obtain ⟨xs, hxs, h⟩ := bind_ok h
   obtain ⟨routed, hprojection, h⟩ := bind_ok h
   obtain ⟨lanes, hr, h⟩ := bind_ok h
   obtain ⟨yt, hy, h⟩ := bind_ok h
   obtain ⟨⟨ysV, topV⟩, hres, h⟩ := bind_ok h
   obtain ⟨routes, hroutes, h⟩ := bind_ok h
   have he := Except.ok.inj h
   subst he
   cases yt with
   | mk y top =>
     exact ⟨y, top, _, hy, rfl, hres, rfl⟩

 private theorem xcsbb_foldl_preserves (step : List Int → (Node × Nat) → List Int)
     (topLen : Nat)
     (hstep : ∀ acc q, acc.length = topLen → (∀ i, 0 ≤ acc.getD i 0) →
       (step acc q).length = topLen ∧ ∀ i, 0 ≤ (step acc q).getD i 0)
     (xs : List (Node × Nat)) (acc : List Int)
     (hlen : acc.length = topLen) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
     (xs.foldl step acc).length = topLen ∧
       ∀ i, 0 ≤ (xs.foldl step acc).getD i 0 := by
   induction xs generalizing acc with
   | nil => exact ⟨hlen, hpos⟩
   | cons q xs ih =>
     simp only [List.foldl_cons]
     obtain ⟨hlen', hpos'⟩ := hstep acc q hlen hpos
     exact ih _ hlen' hpos'

 private theorem xcsbb_extra_step_preserves (acc : List Int) (m : Nat) (needed : Int)
     (hpos : ∀ i, 0 ≤ acc.getD i 0) :
     (acc.set m (max (acc.getD m 0) needed)).length = acc.length ∧
       ∀ i, 0 ≤ (acc.set m (max (acc.getD m 0) needed)).getD i 0 := by
   refine ⟨List.length_set, ?_⟩
   intro i
   have hset : (acc.set m (max (acc.getD m 0) needed))[i]? =
       if m = i then if m < acc.length then some (max (acc.getD m 0) needed) else none
       else acc[i]? :=
     List.getElem?_set
   rw [List.getD_eq_getElem?_getD, hset]
   by_cases heq : m = i
   · subst heq
     by_cases hlt : m < acc.length
     · have h0 : 0 ≤ acc[m] := by
         have h := hpos m
         simpa [hlt] using h
       simp [hlt]
       exact Int.le_trans h0 (Int.le_max_left _ _)
     · simp [hlt]
   · have hne : m ≠ i := heq
     simp [hne]
     exact hpos i

 private theorem xcsbb_extra_step_concrete (cg : Graph) (exact : List Nat)
     (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
     (acc : List Int) (q : Node × Nat)
     (hlen : acc.length = top.length) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
     (if !exact.contains q.1.decl then acc
       else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
       else acc.set ((p.rank.getD q.2 0).toNat)
         (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
           (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length * Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 - heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
       ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
         else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
         else acc.set ((p.rank.getD q.2 0).toNat)
           (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
             (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length * Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 - heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
   by_cases h1 : (!exact.contains q.1.decl) = true
   · rw [ite_eq_left h1]
     exact ⟨hlen, hpos⟩
   · rw [ite_eq_right h1]
     by_cases h2 : (loopSizes cg.edges labels q.2 cg.slot).isEmpty = true
     · rw [ite_eq_left h2]
       exact ⟨hlen, hpos⟩
     · rw [ite_eq_right h2]
       obtain ⟨hlen', hpos'⟩ := xcsbb_extra_step_preserves acc _ _ hpos
       exact ⟨hlen'.trans hlen, hpos'⟩

 private theorem xcsbb_extra_fold (cg : Graph) (exact : List Nat)
     (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int) :
     let extra := cg.nodes.zipIdx.foldl (fun (acc : List Int) (q : Node × Nat) =>
       if !exact.contains q.1.decl then acc
       else
         let sizes := loopSizes cg.edges labels q.2 cg.slot
         if sizes.isEmpty then acc
         else
           let rank := (p.rank.getD q.2 0).toNat
           let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
           let needed := ys.getD q.2 0 + reserved - top.getD rank 0 -
             heights.getD rank 0
           acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top.length (0 : Int))
     extra.length = top.length ∧ ∀ i, 0 ≤ extra.getD i 0 := by
   have hbase : (List.replicate top.length (0 : Int)).length = top.length := by simp
   have hbasePos : ∀ i, 0 ≤ (List.replicate top.length (0 : Int)).getD i 0 := by
     intro i
     by_cases h : i < top.length
     · have hg : (List.replicate top.length (0 : Int))[i]? = some 0 := by
         rw [List.getElem?_eq_getElem (by simpa using h)]
         simp
       rw [List.getD_eq_getElem?_getD, hg]
       simp
     · have hg : (List.replicate top.length (0 : Int))[i]? = none :=
         List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt h)
       rw [List.getD_eq_getElem?_getD, hg]
       simp
   have hstep : ∀ (acc : List Int) (q : Node × Nat), acc.length = top.length →
     (∀ i, 0 ≤ acc.getD i 0) →
       (if !exact.contains q.1.decl then acc
       else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
       else acc.set ((p.rank.getD q.2 0).toNat)
         (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
           (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
             Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
             top.getD ((p.rank.getD q.2 0).toNat) 0 -
             heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
       ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
         else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
         else acc.set ((p.rank.getD q.2 0).toNat)
           (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
             (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
               Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
               top.getD ((p.rank.getD q.2 0).toNat) 0 -
               heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
     intro acc q hlen hpos
     exact xcsbb_extra_step_concrete cg exact labels p ys top heights acc q hlen hpos
   have h := xcsbb_foldl_preserves (fun (acc : List Int) (q : Node × Nat) =>
     if !exact.contains q.1.decl then acc
     else
       let sizes := loopSizes cg.edges labels q.2 cg.slot
       if sizes.isEmpty then acc
       else
         let rank := (p.rank.getD q.2 0).toNat
         let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
         let needed := ys.getD q.2 0 + reserved - top.getD rank 0 -
           heights.getD rank 0
         acc.set rank (max (acc.getD rank 0) needed)) top.length hstep
     cg.nodes.zipIdx (List.replicate top.length (0 : Int)) hbase hbasePos
   exact h

 private theorem xcsbb_prefix_length (es : List Int) (s : Int) (out : List Int) :
     ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).length =
       out.length + es.length := by
   induction es generalizing s out with
   | nil => simp
   | cons e es ih =>
     simp only [List.foldl_cons]
     rw [ih]
     simp
     omega

 private theorem xcsbb_prefix_pairwise (es : List Int) (hpos : ∀ e ∈ es, 0 ≤ e)
     (s : Int) (out : List Int)
     (hm : out.Pairwise (· ≤ ·)) (hle : ∀ x ∈ out, x ≤ s) :
     ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).Pairwise
       (· ≤ ·) := by
   induction es generalizing s out with
   | nil => simpa
   | cons e es ih =>
     have he : 0 ≤ e := hpos e List.mem_cons_self
     simp only [List.foldl_cons]
     apply ih
     · intro e' he'
       exact hpos e' (List.mem_cons_of_mem e he')
     · apply List.pairwise_append.mpr
       refine ⟨hm, by simp, ?_⟩
       intro x hx y hy
       simp only [List.mem_singleton] at hy
       rw [hy]
       exact hle x hx
     · intro x hx
       simp only [List.mem_append, List.mem_singleton] at hx
       rcases hx with hx | rfl
       · have := hle x hx
         omega
       · omega

 private theorem xcsbb_pairwise_getD_le {l : List Int} (hp : l.Pairwise (· ≤ ·))
     {i j : Nat} (hij : i < j) (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
   have hi : i < l.length := by omega
   have hgi : l[i]? = some l[i] := List.getElem?_eq_getElem hi
   have hgj : l[j]? = some l[j] := List.getElem?_eq_getElem hj
   rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hgi, hgj]
   simp only [Option.getD_some]
   exact hp.rel_getElem_of_lt hi hj hij

 /-- Strict shift transfer for tops only: a strict pre-reserve gap survives nondecreasing shifts. -/
 private theorem xcsbb_shift_strict_tops {p : Proper} {layers : List (List Nat)}
     {top : List Int} {extra shifts : List Int} {top' : List Int}
     (hdisj : ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
       layers[r']? = some l' →
       top.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top.getD r' 0)
     (hextraLen : extra.length = top.length)
     (hpos : ∀ e ∈ extra, 0 ≤ e)
     (hshifts : shifts =
       (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)
     (htopLen : top.length = layers.length)
     (htop : ∀ (r : Nat), r < top.length → top'.getD r 0 = top.getD r 0 + shifts.getD r 0) :
     ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
       layers[r']? = some l' →
       top'.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top'.getD r' 0 := by
   have hshiftsLen : shifts.length = top.length := by
     rw [hshifts, xcsbb_prefix_length]
     simp [hextraLen]
   have hpair : shifts.Pairwise (· ≤ ·) := by
     rw [hshifts]
     exact xcsbb_prefix_pairwise extra hpos 0 [] (by simp) (by simp)
   have hmono : ∀ i j, i < j → j < shifts.length →
       shifts.getD i 0 ≤ shifts.getD j 0 :=
     fun i j hij hj => xcsbb_pairwise_getD_le hpair hij hj
   intro r r' l l' hlt hly hly'
   have hrTop : r < top.length := by
     rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly).1
   have hrTop' : r' < top.length := by
     rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly').1
   have hrShift' : r' < shifts.length := by rw [hshiftsLen]; exact hrTop'
   have e1 := htop r hrTop
   have e1' := htop r' hrTop'
   have hle := hmono r r' hlt hrShift'
   have hd := hdisj r r' l l' hlt hly hly'
   rw [e1, e1']
   omega

 private theorem xcsbb_top_eq {inp : Input} {exactIds : List String}
     {cg : Graph} {run : Run} {labels : List MeasuredLabel}
     {top_pre ys_pre : List Int}
     (hreserve : reserveExactRanks cg (exactDecls exactIds inp) labels run.coordinateProper
       run.layers ys_pre top_pre = .ok (run.ys, run.top)) :
     ∀ (r : Nat), r < top_pre.length → run.top.getD r 0 =
       top_pre.getD r 0 +
         ((cg.nodes.zipIdx.foldl
           (fun (acc : List Int) (q : Node × Nat) =>
             if !(exactDecls exactIds inp).contains q.1.decl then acc
             else
               let sizes := loopSizes cg.edges labels q.2 cg.slot
               if sizes.isEmpty then acc
               else
                 let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                 let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
                 let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                   (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                 acc.set rank (max (acc.getD rank 0) needed))
           (List.replicate top_pre.length (0 : Int))).foldl
           (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 := by
   intro r hr
   have hrZ : r < (top_pre.zipIdx).length := by
     rw [List.length_zipIdx]
     exact hr
   have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
     have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
     simp [List.getElem?_zipIdx, h1]
   unfold reserveExactRanks at hreserve
   obtain ⟨topNew, htopM, h1⟩ := bind_ok hreserve
   obtain ⟨ysNew, hysM, h2⟩ := bind_ok h1
   have hpair := Except.ok.inj h2
   have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
   rw [htopNew_eq] at htopM
   obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
   obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
   have hbeq : b = top_pre[r] +
       ((cg.nodes.zipIdx.foldl
         (fun (acc : List Int) (q : Node × Nat) =>
           if !(exactDecls exactIds inp).contains q.1.decl then acc
           else
             let sizes := loopSizes cg.edges labels q.2 cg.slot
             if sizes.isEmpty then acc
             else
               let rank := (run.coordinateProper.rank.getD q.2 0).toNat
               let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
               let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                 (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
               acc.set rank (max (acc.getD rank 0) needed))
         (List.replicate top_pre.length (0 : Int))).foldl
         (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 :=
     Measure.checkedI32_ok hb
   have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
   have e3 : top_pre.getD r 0 = top_pre[r] := by
     rw [List.getD_eq_getElem?_getD, h1]
     rfl
   have e4 : run.top.getD r 0 = b := by
     rw [List.getD_eq_getElem?_getD, hbr]
     rfl
   rw [e4, e3]
   exact hbeq

 private theorem xcsbb_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
     ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
       source.rank ++ extra := by
   unfold titleReservations sizeProperPortsX
   exact ⟨_, rfl⟩

 private theorem xcsbb_coordinateGraph_anchor_prefix (P : Params) (exact : List Nat) (p : Proper) :
     ∃ extra, (coordinateGraphX P exact p).rank = p.rank ++ extra := by
   obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
     (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
   obtain ⟨tail, htitle⟩ := xcsbb_titled_rank_prefix P exact p
   refine ⟨tail ++ extraRanks, ?_⟩
   change (OrderImpl.addClusterBorders
     (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).rank = _
   rw [hr, htitle, List.append_assoc]
/-- Copy of the private `ExactFlatC5Rank.X_titled_rank_record`. -/
private theorem xcsbb_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int}
    (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := xcsbb_titled_rank_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h
/-- Copy of the private `ExactCaptionSelfNarrowProof.xcsn_source_alignment_of_titled`. -/
private theorem xcsbb_source_alignment_of_titled (P : Params) {exact : List Nat} {source : Proper}
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



/-- Copy of the private `ExactFlatC5Rank.X_titled_copy_rank_record`. -/
private theorem xcsbb_titled_copy_rank_record (P : Params) {exact : List Nat} {source : Proper}
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

/-- Copy of the private `ExactFlatC5Rank.X_coordinateGraph_titled_rank_record`. -/
private theorem xcsbb_coordinateGraph_titled_rank_record (P : Params) {exact : List Nat}
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

/-- Copy of the private `ExactFlatC5Rank.X_prepared_titled_original_rk`. -/
private theorem xcsbb_prepared_titled_original_rk {P : Params} {exact : List Nat} {cg : Graph}
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
  have htitledLookup := xcsbb_titled_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index
/-- Copy of the private `ExactFlatC5Rank.X_prepared_coordinate_original_rk`,
with the coordinate record inlined through `xcsbb_coordinateGraph_anchor_prefix`. -/
private theorem xcsbb_prepared_coordinate_original_rk {P : Params} {exact : List Nat} {cg : Graph}
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
  have hsrc := hranks index rr.ranks[index] hrrLookup
  obtain ⟨extra, heq⟩ := xcsbb_coordinateGraph_anchor_prefix P exact source
  have hcoordinateLookup : (coordinateGraphX P exact source).rank[index]? =
      some rr.ranks[index] := by
    rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hsrc).1]
    exact hsrc
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]
/-- Title-copy rank equals the titled rank of its group top: the reservation
position `labeled.length + j` carries `rk labeled.rank index` by construction. -/
private theorem xcsbb_title_rank_eq {P : Params} {exact : List Nat} {labeled : Proper}
    {cg : Graph} {run : Run}
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady (titleReservations
      (sizeProperPortsX P exact labeled)))
    (hrecords : ∀ (key : Nat) (original : Node),
      cg.nodes[key]? = some original →
        labeled.nodes[key]? = some ⟨original, false, none, false⟩)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    {j : Nat}
    (hjEntry : (titleNodes (sizeProperPortsX P exact labeled))[j]? =
      some (⟨node, false, none, false⟩, index)) :
    rk run.coordinateProper.rank (labeled.nodes.length + j) =
      rk (titleReservations (sizeProperPortsX P exact labeled)).rank index := by
  have halignedSrc := xcsbb_source_alignment_of_titled P (exact := exact) hready.2.2.2.1
  have hsourceBound : index < labeled.rank.length := by
    have hn := (List.getElem?_eq_some_iff.mp (hrecords index node hnode)).1
    omega
  have hsourceRank : labeled.rank[index]? = some labeled.rank[index] :=
    List.getElem?_eq_getElem hsourceBound
  have htitledRank := xcsbb_titled_rank_record (P := P) (exact := exact) hsourceRank
  have hsourceToTitled : rk labeled.rank index =
      rk (titleReservations (sizeProperPortsX P exact labeled)).rank index := by
    simp only [rk, List.getD_eq_getElem?_getD, hsourceRank, htitledRank, Option.getD_some]
  have hcopyRank := xcsbb_titled_copy_rank_record P (exact := exact) halignedSrc hjEntry
  have hcoordRank := xcsbb_coordinateGraph_titled_rank_record P (exact := exact) hcopyRank
  have htitleRankEqX : rk (coordinateGraphX P exact labeled).rank (labeled.nodes.length + j) =
      rk labeled.rank index := by
    simp only [rk, List.getD_eq_getElem?_getD, hcoordRank, Option.getD_some]
  rw [hc] at htitleRankEqX
  exact htitleRankEqX.trans hsourceToTitled
/-- Post-reserve strict band tops: the pre-reserve `+ 1` gap from
`rankAxis_band_top_strict` survives the nondecreasing exact reserve shifts. -/
private theorem xcsbb_post_strict_gap {P : Params} {exactIds : List String} {inp : Input}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run) :
    ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        run.top.getD r' 0 := by
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := xcsbb_run_pre hrun
  have hdisjPre : ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      top_pre.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        top_pre.getD r' 0 :=
    fun r r' l l' hlt hly hly' => rankAxis_band_top_strict hry r r' l l' hlt hly hly'
  have hextra := xcsbb_extra_fold cg (exactDecls exactIds inp) labels run.coordinateProper
    ys_pre top_pre
    (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0)
  have hposM : ∀ e ∈ cg.nodes.zipIdx.foldl
      (fun (acc : List Int) (q : Node × Nat) =>
        if !(exactDecls exactIds inp).contains q.1.decl then acc
        else
          let sizes := loopSizes cg.edges labels q.2 cg.slot
          if sizes.isEmpty then acc
          else
            let rank := (run.coordinateProper.rank.getD q.2 0).toNat
            let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
            let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
              (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
            acc.set rank (max (acc.getD rank 0) needed))
      (List.replicate top_pre.length (0 : Int)), 0 ≤ e := by
    intro e he
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    have h := hextra.2 i
    rw [List.getD_eq_getElem?_getD, hi] at h
    simp at h
    exact h
  have htopLen : top_pre.length = run.layers.length :=
    (CoordsImpl.rankCoordsWith_length hry).2
  exact xcsbb_shift_strict_tops hdisjPre hextra.1 hposM rfl htopLen
    (xcsbb_top_eq hreserve)
/-- A candidate group top's cluster path contains its own declaration,
transported across `exactGraph` to the measured origin. -/
private theorem xcsbb_top_path {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate : Nat} {i : Nat} {tNode : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    tNode.clusterPath.contains tNode.decl = true := by
  obtain ⟨j, hj, hcompD, hgraphGet, hgetElem⟩ :=
    xcsbb_candidate_comp_index hnode hborder
  obtain ⟨top0, htop0, hbord0, hpath0, hdecl0⟩ :=
    xcsbb_exactGraph_node_key_rev execution.graph_eq hgraphGet
  have hbord0' : top0.border = -2 := by omega
  obtain ⟨_, _, _, _, hpathG⟩ :=
    measuredGraph_group_origin execution.graph0_eq htop0 hbord0'
  rw [hpath0, hdecl0, hpathG]
  simp
/-- Candidate nodes are positional (border-`2` version): a candidate bottom
marker comes from one component index with the same full record. -/
private theorem xcsbb_candidate_comp_index2 {g : Graph} {comp : List Nat}
    {candidate i : Nat} {fNode : Node}
    (hnode : (componentCandidate g comp candidate).nodes[i]? = some fNode)
    (hborder : fNode.border = 2) :
    ∃ j, comp[i]? = some j ∧ comp.getD i 0 = j ∧ g.nodes[j]? = some fNode ∧
      g.nodes.getD j default = fNode := by
  rw [componentCandidate_nodes] at hnode
  unfold componentGraph at hnode
  simp only [List.getElem?_map] at hnode
  obtain ⟨j, hj, hget⟩ := Option.map_eq_some_iff.mp hnode
  have hjlt : j < g.nodes.length := by
    by_cases hjlt : j < g.nodes.length
    · exact hjlt
    · have hnone : g.nodes[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hdef : (default : Node) = fNode := by simpa [List.getD, hnone] using hget
      rw [← hdef] at hborder
      change (0 : Int) = 2 at hborder
      omega
  have hgetElem : g.nodes[j]? = some fNode := by
    have he : g.nodes[j] = fNode := by simpa [List.getD, hjlt] using hget
    simpa [hjlt] using congrArg some he
  exact ⟨j, hj, by simp [List.getD, hj], hgetElem, hget⟩
/-- A candidate bottom marker's cluster path contains its own declaration,
transported across `exactGraph` to the measured origin. -/
private theorem xcsbb_bottom_path {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate : Nat} {b : Nat} {fNode : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[b]? = some fNode)
    (hborder : fNode.border = 2) :
    fNode.clusterPath.contains fNode.decl = true := by
  obtain ⟨j, hj, _, hgraphGet, _⟩ := xcsbb_candidate_comp_index2 hnode hborder
  obtain ⟨m0, hm0, hbord0, hpath0, hdecl0⟩ :=
    xcsbb_exactGraph_node_key_rev execution.graph_eq hgraphGet
  have hbord0' : m0.border = 2 := by omega
  obtain ⟨_, _, _, hpathM, _, _⟩ :=
    measuredGraph_bottom_origin execution.graph0_eq (List.mem_of_getElem? hm0) hbord0'
  rw [hpath0, hdecl0, hpathM]
  simp
/-- The title copy keeps its record in the proper run: border-`3` nodes are
not side borders, so `proxyWidths` leaves them unchanged. -/
private theorem xcsbb_title_proper_w {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {w : Nat} {title : ProperNode}
    (hcoord : run.coordinateProper.nodes[w]? = some title)
    (hborder3 : title.node.border = 3) :
    run.proper.nodes[w]? = some title := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨_, _, _, _, _, hpreserve⟩ := proxyWidths_rel hproxy
  have hside : ¬ (title.node.border = -2 ∨ title.node.border = 2) := by omega
  have hrouted := (hpreserve w title hcoord hside).1
  have hnodes : run.proper.nodes = q0.nodes := by
    have heq := congrArg Proper.nodes hdrop
    rw [OrderImpl.dropSynthetic_nodes] at heq
    exact heq.symm
  rw [hnodes]
  exact hrouted
/-- The transported caption height is the measured title height: unfold the
`LR/RL` versus `TB/BT` cases of `titleCaptionSize`. -/
private theorem xcsbb_capH_eq {P : Params} {o : Options} {lines : List (List Measure.Line)}
    {comp : List Nat} {i : Nat} :
    (transportCapSize P o lines comp i).2 =
      (match o.direction with
        | .LR | .RL => (lines.getD (comp.getD i 0) []).foldl
          (fun w line => max w line.width) 0
        | .TB | .BT => (max 1 (lines.getD (comp.getD i 0) []).length : Int) * P.lineH) := by
  unfold transportCapSize titleCaptionSize
  cases o.direction <;> rfl
/-- Title-side facts for the exact self-bottom height: the reservation title
copy lies in its rank band, the frame starts at or above its rect, and its
rank equals the ranking rank of the group top. -/
private theorem xcsbb_title_facts_X {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {i : Nat} {tNode : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    ∃ (rr : RankImpl.RankResult) (w : Nat) (lT : List Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      run.layers[(rk run.coordinateProper.rank w).toNat]? = some lT ∧
      run.top.getD (rk run.coordinateProper.rank w).toNat 0 ≤ run.ys.getD w 0 ∧
      run.ys.getD w 0 + tNode.h ≤
        run.top.getD (rk run.coordinateProper.rank w).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper lT ∧
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run i).y ≤
        (Labels.rectAt run.proper run.xs run.ys w).y ∧
      (Labels.rectAt run.proper run.xs run.ys w).y = run.ys.getD w 0 ∧
      (Labels.rectAt run.proper run.xs run.ys w).h = tNode.h ∧
      rk run.coordinateProper.rank w = rk rr.ranks i := by
  obtain ⟨rr, labeled, _, hrr, hc, _, hready, hrecords, hranks, _, _⟩ :=
    X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hnode hborder
  obtain ⟨j, hjEntry, hjCoord⟩ := xcsbb_coordinateGraphX_title_record
    execution.params (exactDecls exactIds inp) (hrecords i tNode hnode) hborder rfl
  have hjCoordRw : run.coordinateProper.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨tNode, false, none, false⟩, i)) := by
    rw [← hc]
    exact hjCoord
  have hborder3 : (copyF (⟨tNode, false, none, false⟩, i)).node.border = 3 := rfl
  have hproperW := xcsbb_title_proper_w hrun hjCoordRw hborder3
  have hnodeH_w : RouteImpl.nodeH run.proper (labeled.nodes.length + j) = tNode.h := by
    simp only [RouteImpl.nodeH, hproperW, copyF]
  obtain ⟨lT, hlyT, hloT, hhiT⟩ := componentRunX_node_band hrun hproperW
    ⟨_, hjCoordRw, rfl, rfl⟩
  rw [hnodeH_w] at hhiT
  have htitleEq := xcsbb_title_rank_eq hc hready hrecords hnode hjEntry
  have htopRank := xcsbb_prepared_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks (List.getElem?_eq_some_iff.mp hnode).1
  have hrkW : rk run.coordinateProper.rank (labeled.nodes.length + j) = rk rr.ranks i :=
    htitleEq.trans htopRank.1
  have hgroupGet : (componentCandidate execution.graph comp candidate).nodes.getD i default =
      tNode := by
    simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hframeGroup : ((componentCandidate execution.graph comp candidate).nodes.getD i
      default).border = -2 := by
    rw [hgroupGet]
    exact hborder
  have hTpath := xcsbb_top_path execution hnode hborder
  have hcontainsW : ((copyF (⟨tNode, false, none, false⟩, i)),
      labeled.nodes.length + j).1.node.clusterPath.contains
      ((componentCandidate execution.graph comp candidate).nodes.getD i default).decl =
      true := by
    show (copyF (⟨tNode, false, none, false⟩, i)).node.clusterPath.contains
      ((componentCandidate execution.graph comp candidate).nodes.getD i default).decl = true
    rw [hgroupGet, show (copyF (⟨tNode, false, none, false⟩, i)).node.clusterPath =
      tNode.clusterPath from rfl]
    exact hTpath
  have hTW := frameRect_member_vertical (P := execution.params) hframeGroup
    (List.mk_mem_zipIdx_iff_getElem?.mpr hproperW) hcontainsW
  have hTy : (Labels.rectAt run.proper run.xs run.ys (labeled.nodes.length + j)).y =
      run.ys.getD (labeled.nodes.length + j) 0 := rfl
  have hTh : (Labels.rectAt run.proper run.xs run.ys (labeled.nodes.length + j)).h =
      tNode.h := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.nodeH, hproperW, copyF]
  exact ⟨rr, _, _, hrr, hlyT, hloT, hhiT, hTW.1, hTy, hTh, hrkW⟩
/-- Marker-side facts for the exact self-bottom height: the paired bottom
marker lies in its rank band at zero height, its band reaches the frame
bottom, and its rank is strictly below no bound yet — the strict ranking
inequality in ranking-rank terms. -/
private theorem xcsbb_marker_facts_X {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {i : Nat} {tNode : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    ∃ (rr : RankImpl.RankResult) (b : Nat) (lB : List Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      run.layers[(rk run.coordinateProper.rank b).toNat]? = some lB ∧
      run.top.getD (rk run.coordinateProper.rank b).toNat 0 ≤ run.ys.getD b 0 ∧
      (Labels.rectAt run.proper run.xs run.ys b).y +
        (Labels.rectAt run.proper run.xs run.ys b).h = run.ys.getD b 0 ∧
      (Labels.rectAt run.proper run.xs run.ys b).y +
        (Labels.rectAt run.proper run.xs run.ys b).h ≤
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run i).y +
          (frameRect execution.params
            (componentCandidate execution.graph comp candidate) run i).h ∧
      rk run.coordinateProper.rank b = rk rr.ranks b ∧
      rk rr.ranks i + 1 ≤ rk rr.ranks b := by
  obtain ⟨rr, _, hrr, hc, _, hrecords, hranks, hlt⟩ :=
    X_group_top_lt_bottom execution.graph0_eq execution.graph_eq hcomp hrun
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  obtain ⟨bottom, hfindB⟩ := X_componentRun_cg_bottom_find execution.graph0_eq
    execution.graph_eq hlines hcomp hnode hborder
  have hbordV : bottom.1.border = 2 := by
    have hcond := List.find?_some hfindB
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.1
  have hdeclV : bottom.1.decl = tNode.decl := by
    have hcond := List.find?_some hfindB
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.2
  have hnodeB : (componentCandidate execution.graph comp candidate).nodes[bottom.2]? =
      some bottom.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfindB)
  have hlt' : rk rr.ranks i + 1 ≤ rk rr.ranks bottom.2 :=
    hlt i tNode bottom hnode hborder hfindB
  obtain ⟨bcoord, hbcoord, hbb, _, hbpath, bh0⟩ :=
    xcsbb_bottom_coordinate (P := execution.params) (exact := exactDecls exactIds inp)
      hc hrecords hnodeB hbordV
  obtain ⟨bprop, hbprop, hbpropP, hbordprop, hnodeH⟩ :=
    xcsbb_bottom_proper hrun hbcoord hbb bh0
  have hbpropH : bprop.node.h = 0 := by
    simpa [RouteImpl.nodeH, hbprop] using hnodeH
  obtain ⟨lB, hlyB, hloB, _⟩ := componentRunX_node_band hrun hbprop
    ⟨_, hbcoord, hbordprop.symm, bh0.trans hbpropH.symm⟩
  have hByH : (Labels.rectAt run.proper run.xs run.ys bottom.2).y +
      (Labels.rectAt run.proper run.xs run.ys bottom.2).h = run.ys.getD bottom.2 0 := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt]
    simp [hnodeH]
  have eBottomX : rk run.coordinateProper.rank bottom.2 = rk rr.ranks bottom.2 := by
    have h := xcsbb_prepared_coordinate_original_rk (P := execution.params)
      (exact := exactDecls exactIds inp) hrr hranks (List.getElem?_eq_some_iff.mp hnodeB).1
    rw [hc] at h
    exact h
  have hBpath0 := xcsbb_bottom_path execution hnodeB hbordV
  have hBpath : bottom.1.clusterPath.contains tNode.decl = true := by
    rw [← hdeclV]
    exact hBpath0
  have hgroupGet : (componentCandidate execution.graph comp candidate).nodes.getD i default =
      tNode := by
    simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hframeGroup : ((componentCandidate execution.graph comp candidate).nodes.getD i
      default).border = -2 := by
    rw [hgroupGet]
    exact hborder
  have hcontainsB : (bprop, bottom.2).1.node.clusterPath.contains
      ((componentCandidate execution.graph comp candidate).nodes.getD i default).decl =
      true := by
    show bprop.node.clusterPath.contains
      ((componentCandidate execution.graph comp candidate).nodes.getD i default).decl = true
    rw [hgroupGet, hbpropP, hbpath]
    exact hBpath
  have hBW := frameRect_member_vertical (P := execution.params) hframeGroup
    (List.mk_mem_zipIdx_iff_getElem?.mpr hbprop) hcontainsB
  exact ⟨rr, _, _, hrr, hlyB, hloB, hByH, hBW.2, eBottomX, hlt'⟩
/-- Exact self-bottom height core: the padded measured caption fits strictly
inside its own frame height. The caption bottom sits at or below the title
band bottom; the bottom marker band starts a full `+ 1` gap below; the frame
bottom reaches at least the marker bottom. -/
private theorem xcsbb_bottom_core_X {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {i : Nat} {tNode : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    execution.params.clusterPad + (transportCapSize execution.params o execution.lines comp i).2 <
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run i).h := by
  obtain ⟨rr, w, lT, hrr, hlyT, hloT, hhiT, hminY, hTy, hTh, hrkW⟩ :=
    xcsbb_title_facts_X execution hcomp hrun hnode hborder
  obtain ⟨rr', b, lB, hrr', hlyB, hloB, hByH, hBW2, eBottomX, hlt'⟩ :=
    xcsbb_marker_facts_X execution hcomp hrun hnode hborder
  have heq : rr' = rr := Except.ok.inj (hrr'.symm.trans hrr)
  rw [heq] at hlt' eBottomX
  have hnnR : 0 ≤ rk rr.ranks i := rankWithBudget_rk_nonneg hrr i
  have hnnRB : 0 ≤ rk rr.ranks b := rankWithBudget_rk_nonneg hrr b
  have hltTB : (rk run.coordinateProper.rank w).toNat <
      (rk run.coordinateProper.rank b).toNat := by
    omega
  have hgap := xcsbb_post_strict_gap hrun _ _ _ _ hltTB hlyT hlyB
  have hfit := (xcsbb_exact_title_fit execution hnode hborder).2
  rw [xcsbb_capH_eq]
  omega
/-- Exact self-bottom narrow height fact, proved by replaying the plain
`captionSelfBottom_proved` bottom half over `componentRunX`: title-band
caption bound plus strict rank-band gap to the bottom marker. -/
theorem XC_selfBottomHeightNarrowX_holds (exactIds : List String) :
    XC_SelfBottomHeightNarrowX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro i tNode hnode hborder
  exact xcsbb_bottom_core_X execution hcomp hrun hnode hborder

/-- Closed exact self-bottom: the narrow height fact gives the residual
through the existing combination theorem. -/
theorem XC_selfBottomX_closed (exactIds : List String) : XC_SelfBottomX exactIds :=
  XC_selfBottomX_holds exactIds (XC_selfBottomHeightNarrowX_holds exactIds)












end PipelineImpl
end Layered
end Elegant
