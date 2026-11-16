import Elegant.Layered.Pipeline
import Elegant.Layered.Metadata
import Elegant.Layered.LaneValidity
import Elegant.Layered.Assembly
import Elegant.Layered.CgShape
import Elegant.Layered.SelectFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

theorem route_label_stack_disjoint (cg : Graph) (labels : List MeasuredLabel)
    (edge : Nat) (x y : Int) (hg : 0 ≤ cg.slot)
    (hh : ∀ l ∈ routeLabels labels edge, 0 ≤ l.height) :
    (Labels.stackRects x y cg.slot
      ((routeLabels labels edge).map fun l => (l.width, l.height))).Pairwise
      (fun a b => ¬ Rect.meetsInterior a b) := by
  apply Labels.stackRects_disjoint x cg.slot hg
  intro size hs
  obtain ⟨label, hl, rfl⟩ := List.mem_map.mp hs
  exact hh label hl

theorem nodeLoops_outside_node {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {v : Nat} {out : List LoopPlacement} (h : nodeLoops cg run labels v = .ok out) :
    ∀ p ∈ out, ¬ Polyline.hitsRect p.points (nodeRect cg run v) :=
  Loops.loops_result_outside_node h

theorem bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem packAcc_components_disjoint {P : Params} {o : Options} {acc out : Acc}
    (h : packAcc P o acc = .ok out) :
    ∃ packed, Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 ((constantOf o.profile "component_aspect_num").getD 1)
      ((constantOf o.profile "component_aspect_den").getD 1)
      (acc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed ∧
      packed.boxes.Pairwise Disjoint := by
  unfold packAcc at h
  obtain ⟨packed, hp, _⟩ := bind_ok h
  exact ⟨packed, hp, Pack.pack_components_disjoint hp⟩

theorem edgeOf_decl {inp : Input} {r : ModelRoute} {i : Nat} {e : Edge}
    (h : edgeOf inp r i = .ok e) : e.decl = i := by
  unfold edgeOf at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl
  · simp at h

theorem graphEdgesFrom_decls (inp : Input) :
    ∀ (rs : List ModelRoute) (k : Nat) (es : List Edge),
      graphEdgesFrom inp k rs = .ok es → es.map (·.decl) = List.range' k rs.length := by
  intro rs
  induction rs with
  | nil =>
    intro k es h
    simp only [graphEdgesFrom, Except.ok.injEq] at h
    subst h
    simp
  | cons r rs ih =>
    intro k es h
    unfold graphEdgesFrom at h
    obtain ⟨edge, he, h⟩ := bind_ok h
    obtain ⟨edges, hes, h⟩ := bind_ok h
    have h := Except.ok.inj h
    subst h
    rw [List.map_cons, edgeOf_decl he, ih (k + 1) edges hes, List.length_cons, List.range'_succ]

theorem graphEdges_decls_nodup {inp : Input} {es : List Edge} (h : graphEdges inp = .ok es) :
    (es.map (·.decl)).Nodup := by
  unfold graphEdges at h
  rw [graphEdgesFrom_decls inp _ _ _ h]
  exact List.nodup_range'

theorem orient_decl (g : Graph) (e : Edge) : (g.orient e).decl = e.decl := by
  unfold Graph.orient
  split <;> rfl

theorem breakCycles_decls (g : Graph) :
    (breakCycles g).edges.map (·.decl) = g.edges.map (·.decl) := by
  rw [breakCycles_edges_eq, List.map_map]
  have hf : ((·.decl) ∘ g.orient : Edge → Nat) = (·.decl) := funext (orient_decl g)
  rw [hf]

theorem cycleGraph_decls (g : Graph) :
    (cycleGraph g).edges.map (·.decl) = g.edges.map (·.decl) := by
  unfold cycleGraph
  split
  · exact Compound.protect_decls g
  · exact breakCycles_decls g

theorem greedy_decls (g : Graph) :
    (breakCyclesGreedy g).edges.map (·.decl) = g.edges.map (·.decl) := by
  unfold breakCyclesGreedy
  simp only [List.map_map]
  apply List.map_congr_left
  intro edge _
  dsimp only [Function.comp_apply]
  unfold GreedyCycles.orient
  split <;> rfl

theorem componentCandidate_decls (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).edges.map (·.decl) =
      (componentGraph g comp).edges.map (·.decl) := by
  unfold componentCandidate
  dsimp only
  split
  · split
    · rw [Compound.protect_decls, greedy_decls]
      simp only [List.map_map, Function.comp_def, Edge.original_decl]
    · rw [greedy_decls]
      simp only [List.map_map, Function.comp_def, Edge.original_decl]
  · rw [cycleGraph_decls]
    simp only [List.map_map, Function.comp_def, Edge.original_decl]

theorem componentGraph_decls_nodup (g : Graph) (comp : List Nat)
    (h : (g.edges.map (·.decl)).Nodup) :
    ((componentGraph g comp).edges.map (·.decl)).Nodup := by
  unfold componentGraph
  simp only [List.map_map]
  exact List.Nodup.sublist ((List.filter_sublist).map _) h

theorem measuredGraph_decls_nodup {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (h : measuredGraph P inp o lines = .ok g0) : (g0.edges.map (·.decl)).Nodup := by
  unfold measuredGraph at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨edges, he, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  rw [Compound.prepare_decls]
  exact graphEdges_decls_nodup he

theorem actual_title_caption_fit {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    {comp : List Nat} {index i : Nat} {top : Node}
    (htop : (componentCandidate g comp index).nodes[i]? = some top)
    (hborder : top.border = -2) :
    top.w = (match o.direction with
      | .LR | .RL => (max 1 (lines.getD (comp.getD i 0) []).length : Int) * P.lineH
      | .TB | .BT =>
        (lines.getD (comp.getD i 0) []).foldl (fun width line => max width line.width) 0) ∧
    (match o.direction with
      | .LR | .RL =>
        (lines.getD (comp.getD i 0) []).foldl (fun width line => max width line.width) 0
      | .TB | .BT => (max 1 (lines.getD (comp.getD i 0) []).length : Int) * P.lineH) +
        P.clusterPad ≤ top.h := by
  rw [componentCandidate_nodes_record] at htop
  cases hc : comp[i]? with
  | none => simp [List.getElem?_map, hc] at htop
  | some j =>
    have hgetD : comp.getD i 0 = j := by simp [List.getD, hc]
    have hv : g.nodes.getD j default = top := by
      simpa [List.getElem?_map, hc] using htop
    have hj : j < g.nodes.length := by
      by_cases hj : j < g.nodes.length
      · exact hj
      · have hnone : g.nodes[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        have hdefault : (default : Node) = top := by simpa [List.getD, hnone] using hv
        rw [← hdefault] at hborder
        change (0 : Int) = -2 at hborder
        omega
    have hget : g.nodes[j]? = some top := by
      have he : g.nodes[j] = top := by simpa [List.getD, hj] using hv
      simpa [hj] using congrArg some he
    obtain ⟨_, _, _, _, _, _, hw, hh⟩ := measuredGraph_title_metadata hg hget hborder
    rw [hgetD]
    exact ⟨hw, hh⟩

/-- Every title anchor selected from the measured graph has the measured title
dimensions, independently of whether a caller can already identify its box. -/
theorem actual_title_dims_nonneg {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g) (hline : 0 ≤ P.lineH)
    {comp : List Nat} {index i : Nat} {top : Node}
    (htop : (componentCandidate g comp index).nodes[i]? = some top)
    (hborder : top.border = -2) :
    0 ≤ top.w ∧ P.clusterPad ≤ top.h := by
  rw [componentCandidate_nodes_record] at htop
  cases hc : comp[i]? with
  | none => simp [List.getElem?_map, hc] at htop
  | some j =>
    have hv : g.nodes.getD j default = top := by
      simpa [List.getElem?_map, hc] using htop
    have hj : j < g.nodes.length := by
      by_cases hj : j < g.nodes.length
      · exact hj
      · have hnone : g.nodes[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        have hdefault : (default : Node) = top := by
          simpa [List.getD, hnone] using hv
        rw [← hdefault] at hborder
        change (0 : Int) = -2 at hborder
        omega
    have hget : g.nodes[j]? = some top := by
      have he : g.nodes[j] = top := by simpa [List.getD, hj] using hv
      simpa [hj] using congrArg some he
    obtain ⟨_, _, _, _, _, _, hw, hh⟩ := measuredGraph_title_metadata hg hget hborder
    have width_nonneg : ∀ (ls : List Measure.Line) (start : Int),
        0 ≤ start → 0 ≤ ls.foldl (fun w line => max w line.width) start := by
      intro ls
      induction ls with
      | nil => intro start hs; exact hs
      | cons line ls ih =>
        intro start hs
        exact ih _ (Int.le_trans hs (Int.le_max_left _ _))
    have hw0 := width_nonneg (lines.getD j []) 0 (by omega)
    have hh0 : 0 ≤ (max 1 (lines.getD j []).length : Int) * P.lineH :=
      Int.mul_nonneg (by omega) hline
    cases hd : o.direction <;> simp only [hd] at hw hh <;> constructor <;> omega

theorem foldlM_ok_mem {α β : Type} (f : β → α → Except LayoutError β) :
    ∀ (l : List α) (a b : β), l.foldlM f a = .ok b → ∀ x ∈ l, ∃ a' b', f a' x = .ok b' := by
  intro l
  induction l with
  | nil =>
    intro a b _ x hx
    simp at hx
  | cons y ys ih =>
    intro a b h x hx
    rw [List.foldlM_cons] at h
    cases hy : f a y with
    | error e =>
      rw [hy] at h
      simp [bind, Except.bind] at h
    | ok a1 =>
      rw [hy] at h
      simp only [bind, Except.bind] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨a, a1, hy⟩
      · exact ih a1 b h x hx'

theorem layoutComponent_run {P : Params} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {labels : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp labels = .ok acc') :
    ∃ index run, index < 5 ∧
      componentRun P (componentCandidate g comp index) labels (candidateOrder index) = .ok run := by
  unfold layoutComponent at h
  obtain ⟨chosen, hchosen, _⟩ := bind_ok h
  obtain ⟨index, trial, hi, htrial, _, _⟩ := Portfolio.portfolio_selected hchosen
  unfold componentTrial at htrial
  obtain ⟨run, hrun, _⟩ := bind_ok htrial
  exact ⟨index, run, hi, hrun⟩

theorem componentPortfolio_cost_le_default {P : Params} {inp : Input} {o : Options}
    {g : Graph} {acc acc' : Acc} {comp : List Nat} {labels : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp labels = .ok acc') :
    ∃ chosen first initial final,
      Portfolio.portfolio o.thoroughness (componentTrial P inp o g comp labels) = .ok chosen ∧
      componentTrial P inp o g comp labels 0 = .ok first ∧
      softCost first.scene = .ok initial ∧ softCost chosen.scene = .ok final ∧ final ≤ initial := by

  unfold layoutComponent at h
  obtain ⟨chosen, hc, _⟩ := bind_ok h
  obtain ⟨first, initial, final, hf, hi, ho, hle⟩ :=
    Portfolio.portfolio_cost_le_default hc
  exact ⟨chosen, first, initial, final, hc, hf, hi, ho, hle⟩

theorem componentRun_spec {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    ∃ ranks p0 labeled q0, normalize cg ranks = .ok p0 ∧
      Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      (∃ ord, orderWithBudget run.coordinateProper orderOptions = .ok ord ∧
        ord.layers = run.layers) ∧
      crossCoordsClusterWith P.nodeGap P.clusterPad run.coordinateProper run.layers =
        .ok run.coordinateXs ∧
      proxyWidths run.coordinateProper run.coordinateXs = .ok (q0, run.xs) ∧
      OrderImpl.dropSynthetic q0 = run.proper ∧
      RouteImpl.routeWithLanes P.slot run.proper run.layers run.xs
        (cg.edges.map (·.reversed))
        (cg.edges.map fun edge => (stackSize cg.slot (routeLabels labels edge.decl)).width) =
          .ok run.lanes ∧ run.lanes.routing = run.routing ∧
      rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)) = .ok (run.coordinateYs, run.top) ∧
      proxyYs run.coordinateProper run.layers run.top run.coordinateYs = run.ys ∧
      RouteImpl.routePointsWithLanes P.slot run.proper run.layers run.xs run.ys run.top run.lanes =
        .ok run.routes := by
  unfold componentRun at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, hp0, h⟩ := bind_ok h
  obtain ⟨p, hp, h⟩ := bind_ok h
  obtain ⟨ord, hord, h⟩ := bind_ok h
  obtain ⟨xs, hxs, h⟩ := bind_ok h
  obtain ⟨routed, hprojection, h⟩ := bind_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨yt, hy, h⟩ := bind_ok h
  obtain ⟨routes, hroutes, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  exact ⟨rr.ranks, p0, p, routed.1, hp0, hp, rfl, ⟨ord, hord, rfl⟩,
    hxs, hprojection, rfl, hr, rfl, hy, rfl, hroutes⟩
/-- Successful normalization only appends nodes to its original input prefix. -/
theorem normalize_nodes_length_le {cg : Graph} {ranks : List Int} {p0 : Proper}
    (hn : normalize cg ranks = .ok p0) :
    cg.nodes.length ≤ p0.nodes.length := by
  have edge_growth : ∀ {slot : Int} {p q : Proper} {e : Edge} {idx : Nat},
      NormalizeImpl.normalizeEdge slot p e idx = .ok q →
      p.nodes.length ≤ q.nodes.length := by
    intro slot p q e idx he
    unfold NormalizeImpl.normalizeEdge at he
    split at he
    · have he := Except.ok.inj he
      subst q
      exact Nat.le_refl _
    · split at he
      · simp at he
      · split at he
        · simp at he
        · have he := Except.ok.inj he
          subst q
          simp [NormalizeImpl.appendChain]
  have loop_growth : ∀ (slot : Int) (es : List (Edge × Nat)) (p q : Proper),
      NormalizeImpl.normalizeLoop slot es p = .ok q →
      p.nodes.length ≤ q.nodes.length := by
    intro slot es
    induction es with
    | nil =>
      intro p q he
      have he : p = q := Except.ok.inj he
      subst q
      exact Nat.le_refl _
    | cons e es ih =>
      intro p q he
      unfold NormalizeImpl.normalizeLoop at he
      split at he
      · simp at he
      · rename_i next hn
        exact Nat.le_trans (edge_growth hn) (ih next q he)
  unfold NormalizeImpl.normalize at hn
  split at hn
  · simp at hn
  · split at hn
    · simpa only [List.length_map] using loop_growth _ _ _ _ hn
    · simp at hn

theorem normalize_node_rank_alignment {cg : Graph} {ranks : List Int} {p : Proper}
    (h : normalize cg ranks = .ok p) :
    p.nodes.length = p.rank.length ∧ cg.wellformed = true := by
  unfold NormalizeImpl.normalize at h
  split at h
  · simp at h
  · rename_i slot hs
    split at h
    · rename_i hc
      have hmem : ∀ edge ∈ cg.edges.zipIdx,
          edge.1.tail < cg.nodes.length ∧ edge.1.head < cg.nodes.length ∧
            1 ≤ edge.1.minLen := by
        intro edge he
        exact RankImpl.wellformed_spec hc.1 edge.1 (RankImpl.mem_of_mem_zipIdx he)
      have hp : NormalizeImpl.PInv
          { nodes := cg.nodes.map fun nd => ⟨nd, false, none, false⟩,
            edges := [], rank := ranks, chains := [] } := by
        refine ⟨by simp [hc.2.1], ?_⟩
        intro edge he
        simp at he
      have hinv := NormalizeImpl.normalizeLoop_inv slot cg.nodes.length
        _ _ p hmem (by simp [hc.2.1]) hp h
      exact ⟨hinv.1, hc.1⟩
    · simp at h

/-- A successful run retains an index for every original component node through
the label, coordinate, and proxy-materialization phases. -/
theorem componentRun_original_nodes_covered {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    ∀ i, i < cg.nodes.length → i < run.proper.nodes.length := by
  obtain ⟨ranks, p0, labeled, q, hn, hl, hcoord, _, _, hproxy, hdrop,
    _, _, _, _, _⟩ := componentRun_spec h
  have hnlen := normalize_nodes_length_le hn
  have hllen : p0.nodes.length ≤ labeled.nodes.length := by
    by_cases hle : p0.nodes.length ≤ labeled.nodes.length
    · exact hle
    · have hi : labeled.nodes.length < p0.nodes.length := by omega
      have hmap := (Labels.addLabelNodes_metadata hl).2.2.2 labeled.nodes.length
      have hget : p0.nodes[labeled.nodes.length]? =
          some p0.nodes[labeled.nodes.length] := by simp [hi]
      simp [hget] at hmap
  let titled := titleReservations (sizeProperPorts P labeled)
  obtain ⟨_, _, extra, hextra, _⟩ :=
    OrderImpl.addClusterBorders_metadata titled P.clusterBorderW
  have hclen : labeled.nodes.length ≤ run.coordinateProper.nodes.length := by
    rw [← hcoord]
    unfold coordinateGraph materializeDummyPaths clearProxyExtents
    simp only [List.length_map]
    rw [hextra]
    dsimp only [titled, titleReservations]
    simp only [List.length_zipIdx, List.length_map, List.length_append,
      sizeProperPorts_length]
    omega
  have hplen := (proxyWidths_rel hproxy).2.2.1
  intro i hi
  rw [← hdrop]
  change i < q.nodes.length
  omega

/-- Successful normalization rejects a negative component label-stack slot. -/
theorem componentRun_slot_nonneg {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    0 ≤ cg.slot := by
  obtain ⟨_, _, _, _, hn, _⟩ := componentRun_spec h
  unfold NormalizeImpl.normalize at hn
  split at hn
  · simp at hn
  · rename_i slot hs
    split at hn
    · rename_i hc
      by_cases hz : cg.slot = 0
      · omega
      · have he : cg.slot = slot := by
          simpa [NormalizeImpl.slotOf, hz] using hs
        rw [he]
        exact hc.2.2

    · simp at hn
/-- Index of the first label anchor. Only edge identity and rank participate:
measuring a label changes neither, even when it changes the selected node's size. -/
def labelAnchorIndex (p : Proper) (edge : Nat) (rank : Int) : Option Nat :=
  (((p.nodes.map ProperNode.edge).zipIdx).find? fun q =>
    q.1 == some edge && rk p.rank q.2 == rank).map (·.2)

theorem labelAnchorIndex_eq (p : Proper) (edge : Nat) (rank : Int) :
    labelAnchorIndex p edge rank =
      (p.nodes.zipIdx.find? fun q =>
        q.1.edge == some edge && rk p.rank q.2 == rank).map (·.2) := by
  simp only [labelAnchorIndex, List.zipIdx_map, List.find?_map,
    Option.map_map, Function.comp_def, Prod.map, id_eq]

/-- The executable label update retains the exact edge-key sequence as well as
the rank sequence. Thus later labels cannot change first-anchor selection. -/
theorem addLabelNode_anchor_keys {g : Graph} {p q : Proper} {label : EdgeLabelSize}
    (h : Labels.addLabelNode g p label = .ok q) :
    q.rank = p.rank ∧ q.nodes.map ProperNode.edge = p.nodes.map ProperNode.edge := by
  unfold Labels.addLabelNode at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · have he := Except.ok.inj h
          subst q
          exact ⟨rfl, rfl⟩
        · dsimp only at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · rename_i anchor ha
              split at h
              · simp at h
              · rename_i nd hnd
                have he := Except.ok.inj h
                subst q
                refine ⟨rfl, ?_⟩
                simp only [List.map_set]
                have hi := (List.getElem?_eq_some_iff.mp hnd).1
                have him : anchor.2 < (p.nodes.map ProperNode.edge).length := by
                  simpa only [List.length_map] using hi
                have helem : (p.nodes.map ProperNode.edge)[anchor.2] = nd.edge := by
                  have hm : (p.nodes.map ProperNode.edge)[anchor.2]? = some nd.edge := by
                    simp only [List.getElem?_map, hnd, Option.map_some]
                  exact (List.getElem?_eq_some_iff.mp hm).2
                change (p.nodes.map ProperNode.edge).set anchor.2 nd.edge =
                  p.nodes.map ProperNode.edge
                rw [← helem]
                exact List.set_getElem_self him

theorem addLabelNodes_anchor_keys {g : Graph} {p q : Proper}
    {labels : List EdgeLabelSize} (h : Labels.addLabelNodes g p labels = .ok q) :
    q.rank = p.rank ∧ q.nodes.map ProperNode.edge = p.nodes.map ProperNode.edge := by
  induction labels generalizing p with
  | nil =>
    have he : p = q := Except.ok.inj h
    subst q
    exact ⟨rfl, rfl⟩
  | cons label rest ih =>
    simp only [Labels.addLabelNodes] at h
    obtain ⟨next, hn, h⟩ := bind_ok h
    obtain ⟨hr, he⟩ := addLabelNode_anchor_keys hn
    obtain ⟨hr', he'⟩ := ih h
    exact ⟨hr'.trans hr, he'.trans he⟩

theorem labelAnchorIndex_addLabelNode {g : Graph} {p q : Proper}
    {label : EdgeLabelSize} (h : Labels.addLabelNode g p label = .ok q)
    (edge : Nat) (rank : Int) :
    labelAnchorIndex q edge rank = labelAnchorIndex p edge rank := by
  obtain ⟨hr, he⟩ := addLabelNode_anchor_keys h
  unfold labelAnchorIndex
  rw [hr, he]

/-- A successful non-loop label update sizes the very first anchor that the
renderer will later select, not merely some node with the same edge identity. -/
theorem addLabelNode_selected_size {g : Graph} {p q : Proper}
    {label : EdgeLabelSize} {edge : Edge}
    (hg : g.edges[label.edge]? = some edge) (hne : edge.tail ≠ edge.head)
    (h : Labels.addLabelNode g p label = .ok q) :
    ∃ index nd,
      labelAnchorIndex p label.edge
        (rk p.rank edge.tail + Int.fdiv (rk p.rank edge.head - rk p.rank edge.tail) 2) =
          some index ∧
      q.nodes[index]? = some nd ∧
      nd.node.w = label.width ∧ nd.node.h = label.height := by
  unfold Labels.addLabelNode at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [hg, hne, ↓reduceIte] at h
      split at h
      · simp at h
      · cases ha : p.nodes.zipIdx.find? (fun a =>
          a.1.edge == some label.edge &&
            rk p.rank a.2 ==
              rk p.rank edge.tail + Int.fdiv (rk p.rank edge.head - rk p.rank edge.tail) 2) with
        | none => simp [ha] at h
        | some anchor =>
          simp only [ha] at h
          cases hnd : p.nodes[anchor.2]? with
          | none => simp [hnd] at h
          | some old =>
            simp only [hnd] at h
            have he := Except.ok.inj h
            subst q
            refine ⟨anchor.2, { old with
              node := { old.node with w := label.width, h := label.height }, label := true },
              ?_, ?_, rfl, rfl⟩
            · rw [labelAnchorIndex_eq, ha]
              rfl
            · exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp hnd).1

theorem labelAnchorIndex_node_edge {p : Proper} {edge index : Nat} {rank : Int}
    {nd : ProperNode} (hi : labelAnchorIndex p edge rank = some index)
    (hn : p.nodes[index]? = some nd) :
    nd.edge = some edge := by
  rw [labelAnchorIndex_eq] at hi
  cases hf : p.nodes.zipIdx.find? (fun q =>
      q.1.edge == some edge && rk p.rank q.2 == rank) with
  | none => simp [hf] at hi
  | some found =>
    simp only [hf, Option.map_some, Option.some.injEq] at hi
    have hget := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
    rw [hi, hn] at hget
    have he : nd = found.1 := Option.some.inj hget
    have hp := List.find?_some hf
    rw [← he] at hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact hp.1

/-- An update for another edge cannot overwrite a previously assigned label
anchor: the selected node itself records the updated edge identity. -/
theorem addLabelNode_preserves_other_edge {g : Graph} {p q : Proper}
    {label : EdgeLabelSize} {index : Nat} {nd : ProperNode}
    (hn : p.nodes[index]? = some nd) (hne : nd.edge ≠ some label.edge)
    (h : Labels.addLabelNode g p label = .ok q) :
    q.nodes[index]? = some nd := by
  unfold Labels.addLabelNode at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · have he := Except.ok.inj h
          subst q
          exact hn
        · dsimp only at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · rename_i anchor ha
              split at h
              · simp at h
              · rename_i old hold
                have hindex : anchor.2 ≠ index := by
                  intro he
                  have hget := List.mem_zipIdx_iff_getElem?.mp
                    (List.mem_of_find?_eq_some ha)
                  rw [he, hn] at hget
                  have hnode : nd = anchor.1 := Option.some.inj hget
                  have hp := List.find?_some ha
                  simp only [Bool.and_eq_true, beq_iff_eq] at hp
                  apply hne
                  rw [hnode]
                  exact hp.1
                have he := Except.ok.inj h
                subst q
                simpa [hindex] using hn

theorem addLabelNodes_preserves_other_edge {g : Graph} {p q : Proper}
    {labels : List EdgeLabelSize} {index edge : Nat} {nd : ProperNode}
    (hn : p.nodes[index]? = some nd) (he : nd.edge = some edge)
    (hother : ∀ label ∈ labels, label.edge ≠ edge)
    (h : Labels.addLabelNodes g p labels = .ok q) :
    q.nodes[index]? = some nd := by
  induction labels generalizing p with
  | nil =>
    have heq : p = q := Except.ok.inj h
    subst q
    exact hn
  | cons label rest ih =>
    simp only [Labels.addLabelNodes] at h
    obtain ⟨next, hnext, h⟩ := bind_ok h
    have hne : nd.edge ≠ some label.edge := by
      rw [he]
      intro heq
      exact hother label List.mem_cons_self (Option.some.inj heq).symm
    have hn' := addLabelNode_preserves_other_edge hn hne hnext
    exact ih hn' (fun label hl => hother label (List.mem_cons_of_mem _ hl)) h

/-- The label fold retains the measured size of every distinct-edge declaration
at the exact first anchor selected by the successful update. -/
theorem addLabelNodes_selected_size {g : Graph} {p q : Proper}
    {labels : List EdgeLabelSize} {label : EdgeLabelSize} {edge : Edge}
    (hnd : (labels.map EdgeLabelSize.edge).Nodup) (hmem : label ∈ labels)
    (hg : g.edges[label.edge]? = some edge) (hne : edge.tail ≠ edge.head)
    (h : Labels.addLabelNodes g p labels = .ok q) :
    ∃ index nd,
      labelAnchorIndex q label.edge
        (rk q.rank edge.tail + Int.fdiv (rk q.rank edge.head - rk q.rank edge.tail) 2) =
          some index ∧
      q.nodes[index]? = some nd ∧
      nd.node.w = label.width ∧ nd.node.h = label.height := by
  induction labels generalizing p with
  | nil => simp at hmem
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [Labels.addLabelNodes] at h
    obtain ⟨next, hn, htail⟩ := bind_ok h
    rcases List.mem_cons.mp hmem with heq | hrest
    · subst first
      obtain ⟨index, nd, hi, hnode, hw, hh⟩ := addLabelNode_selected_size hg hne hn
      have hkeys := addLabelNode_anchor_keys hn
      have hi' : labelAnchorIndex next label.edge
          (rk next.rank edge.tail + Int.fdiv (rk next.rank edge.head - rk next.rank edge.tail) 2) =
            some index := by
        rw [hkeys.1, labelAnchorIndex_addLabelNode hn]
        exact hi
      have hedge := labelAnchorIndex_node_edge hi' hnode
      have hout := addLabelNodes_preserves_other_edge hnode hedge
        (fun other ho he => hnd.1 (List.mem_map.mpr ⟨other, ho, he⟩)) htail
      obtain ⟨hr, he⟩ := addLabelNodes_anchor_keys htail
      refine ⟨index, nd, ?_, hout, hw, hh⟩
      unfold labelAnchorIndex at hi' ⊢
      rw [hr, he]
      exact hi'
    · exact ih hnd.2 hrest htail

/-- Component measurement emits at most one stack size per edge-array index,
even if distinct graph edges share a source declaration identity. -/
theorem componentLabels_edges_nodup (cg : Graph) (labels : List MeasuredLabel) :
    ((componentLabels cg labels).map EdgeLabelSize.edge).Nodup := by
  have hindices : (cg.edges.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hp : cg.edges.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) :=
    List.pairwise_map.mp hindices
  let emit : Edge × Nat → Option EdgeLabelSize := fun q =>
    match routeLabels labels q.1.decl with
    | [] => none
    | first :: rest =>
      let size := stackSize cg.slot (first :: rest)
      some ⟨q.2, size.width + first.gutter, size.height⟩
  have identity : ∀ q size, emit q = some size → size.edge = q.2 := by
    intro q size he
    cases hr : routeLabels labels q.1.decl with
    | nil => simp [emit, hr] at he
    | cons first rest =>
      simp only [emit, hr] at he
      have he := Option.some.inj he
      rw [← he]
  change ((componentLabels cg labels).map EdgeLabelSize.edge).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  change (cg.edges.zipIdx.filterMap emit).Pairwise (fun a b => a.edge ≠ b.edge)
  apply List.Pairwise.filterMap emit _ hp
  intro a b hne sa hsa sb hsb
  rw [identity a sa hsa, identity b sb hsb]
  exact hne

theorem componentLabels_selected_size {cg : Graph} {p q : Proper}
    {labels : List MeasuredLabel} {k : Nat} {edge : Edge} {first : MeasuredLabel}
    (hk : cg.edges[k]? = some edge) (hne : edge.tail ≠ edge.head)
    (hfirst : (routeLabels labels edge.decl).head? = some first)
    (h : Labels.addLabelNodes cg p (componentLabels cg labels) = .ok q) :
    ∃ index nd,
      labelAnchorIndex q k
        (rk q.rank edge.tail + Int.fdiv (rk q.rank edge.head - rk q.rank edge.tail) 2) =
          some index ∧
      q.nodes[index]? = some nd ∧
      nd.node.w = (stackSize cg.slot (routeLabels labels edge.decl)).width + first.gutter ∧
      nd.node.h = (stackSize cg.slot (routeLabels labels edge.decl)).height := by
  let size : EdgeLabelSize :=
    ⟨k, (stackSize cg.slot (routeLabels labels edge.decl)).width + first.gutter,
      (stackSize cg.slot (routeLabels labels edge.decl)).height⟩
  have hmem : size ∈ componentLabels cg labels := by
    unfold componentLabels
    apply List.mem_filterMap.mpr
    refine ⟨(edge, k), List.mem_zipIdx_iff_getElem?.mpr hk, ?_⟩
    cases hr : routeLabels labels edge.decl with
    | nil => simp [hr] at hfirst
    | cons head rest =>
      have he : head = first := by simpa [hr] using hfirst
      subst head
      simp only [size, hr]
  exact addLabelNodes_selected_size (componentLabels_edges_nodup cg labels)
    hmem hk hne h

def EdgeAnchorsPlain (p : Proper) : Prop :=
  ∀ nd ∈ p.nodes, nd.edge ≠ none → nd.node.border = 0

/-- Only ordinary dummy nodes receive an edge-anchor identity during
normalization. Group title and frame anchors never receive one. -/
theorem normalize_edgeAnchorsPlain {cg : Graph} {ranks : List Int} {p : Proper}
    (h : normalize cg ranks = .ok p) : EdgeAnchorsPlain p := by
  have step : ∀ {slot : Int} {a b : Proper} {edge : Edge} {index : Nat},
      EdgeAnchorsPlain a →
      NormalizeImpl.normalizeEdge slot a edge index = .ok b →
      EdgeAnchorsPlain b := by
    intro slot a b edge index ha hb
    unfold NormalizeImpl.normalizeEdge at hb
    split at hb
    · have he := Except.ok.inj hb
      subst b
      exact ha
    · split at hb
      · simp at hb
      · split at hb
        · simp at hb
        · have he := Except.ok.inj hb
          subst b
          intro nd hn hedge
          change nd ∈ a.nodes ++ _ at hn
          rcases List.mem_append.mp hn with hn | hn
          · exact ha nd hn hedge
          · have he := List.eq_of_mem_replicate hn
            subst nd
            rfl
  have loop : ∀ (slot : Int) (edges : List (Edge × Nat)) (a b : Proper),
      EdgeAnchorsPlain a →
      NormalizeImpl.normalizeLoop slot edges a = .ok b →
      EdgeAnchorsPlain b := by
    intro slot edges
    induction edges with
    | nil =>
      intro a b ha hb
      have he : a = b := Except.ok.inj hb
      subst b
      exact ha
    | cons edge rest ih =>
      intro a b ha hb
      unfold NormalizeImpl.normalizeLoop at hb
      split at hb
      · simp at hb
      · rename_i next hn
        exact ih next b (step ha hn) hb
  unfold NormalizeImpl.normalize at h
  split at h
  · simp at h
  · split at h
    · apply loop _ _ _ _ ?_ h
      intro nd hn hedge
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp hn
      exact False.elim (hedge rfl)
    · simp at h

theorem addLabelNodes_edgeAnchorsPlain {cg : Graph} {p q : Proper}
    {labels : List EdgeLabelSize} (hp : EdgeAnchorsPlain p)
    (h : Labels.addLabelNodes cg p labels = .ok q) : EdgeAnchorsPlain q := by
  have step : ∀ {a b : Proper} {label : EdgeLabelSize},
      EdgeAnchorsPlain a → Labels.addLabelNode cg a label = .ok b →
      EdgeAnchorsPlain b := by
    intro a b label ha hb
    unfold Labels.addLabelNode at hb
    split at hb
    · simp at hb
    · split at hb
      · simp at hb
      · split at hb
        · simp at hb
        · split at hb
          · have he := Except.ok.inj hb
            subst b
            exact ha
          · dsimp only at hb
            split at hb
            · simp at hb
            · split at hb
              · simp at hb
              · split at hb
                · simp at hb
                · rename_i old hold
                  have he := Except.ok.inj hb
                  subst b
                  intro nd hn hedge
                  rcases List.mem_or_eq_of_mem_set hn with hmem | heq
                  · exact ha nd hmem hedge
                  · subst nd
                    exact ha old (List.mem_of_getElem? hold) hedge
  induction labels generalizing p with
  | nil =>
    have he : p = q := Except.ok.inj h
    subst q
    exact hp
  | cons label rest ih =>
    simp only [Labels.addLabelNodes] at h
    obtain ⟨next, hn, htail⟩ := bind_ok h
    exact ih (step hp hn) htail

private theorem find_eq_of_mem_congr {α : Type} (f g : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.find? f = xs.find? g := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have hx := h x List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [List.find?_cons, hx, ht]

/-- Appending coordinate-only nodes and ranks cannot change a first anchor
already found in the original, rank-aligned prefix. -/
theorem labelAnchorIndex_prefix {p q : Proper} {edge index : Nat} {rank : Int}
    (halign : p.nodes.length = p.rank.length)
    (hkeys : ∃ extra, q.nodes.map ProperNode.edge = p.nodes.map ProperNode.edge ++ extra)
    (hranks : ∃ extra, q.rank = p.rank ++ extra)
    (hi : labelAnchorIndex p edge rank = some index) :
    labelAnchorIndex q edge rank = some index := by
  obtain ⟨extraKeys, hk⟩ := hkeys
  obtain ⟨extraRanks, hr⟩ := hranks
  unfold labelAnchorIndex at hi ⊢
  rw [hk, hr, List.zipIdx_append, List.find?_append]
  have hf :
      ((p.nodes.map ProperNode.edge).zipIdx.find? fun a =>
        a.1 == some edge && rk (p.rank ++ extraRanks) a.2 == rank) =
      ((p.nodes.map ProperNode.edge).zipIdx.find? fun a =>
        a.1 == some edge && rk p.rank a.2 == rank) := by
    apply find_eq_of_mem_congr
    intro a ha
    have hb := List.snd_lt_of_mem_zipIdx ha
    have hv : a.2 < p.rank.length := by
      simp only [List.length_map, Nat.add_zero] at hb
      omega
    rw [NormalizeImpl.rk_append_left hv]
  rw [hf]
  cases hfound : (p.nodes.map ProperNode.edge).zipIdx.find? (fun a =>
      a.1 == some edge && rk p.rank a.2 == rank) with
  | none => simp [hfound] at hi
  | some found => simpa [hfound] using hi

theorem addClusterBorders_rank_prefix (p : Proper) (width : Int) :
    ∃ extra, (OrderImpl.addClusterBorders p width).rank = p.rank ++ extra := by
  unfold OrderImpl.addClusterBorders
  apply OrderImpl.foldl_inv
    (fun out => ∃ extra, out.rank = p.rank ++ extra) _ _ p ⟨[], by simp⟩
  intro out hout anchor _
  dsimp only
  split
  · exact hout
  · apply OrderImpl.foldl_inv
      (fun out => ∃ extra, out.rank = p.rank ++ extra) _ _ out hout
    intro state hstate offset _
    obtain ⟨extra, he⟩ := hstate
    let level : Int := (((rk p.rank anchor.2).toNat + offset : Nat) : Int)
    refine ⟨extra ++ [level, level], ?_⟩
    simp only [he, List.append_assoc, level]

theorem coordinateGraph_anchor_prefix (P : Params) (p : Proper) :
    (∃ extra, (coordinateGraph P p).nodes.map ProperNode.edge =
      p.nodes.map ProperNode.edge ++ extra) ∧
    (∃ extra, (coordinateGraph P p).rank = p.rank ++ extra) := by
  have mapped : ∀ (nodes : List ProperNode) (f : ProperNode → ProperNode),
      (∀ n, (f n).edge = n.edge) →
      (nodes.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
    intro nodes f hf
    simp only [List.map_map]
    apply congrArg (fun g => nodes.map g)
    funext n
    exact hf n
  have indexed : ∀ (nodes : List ProperNode) (f : ProperNode × Nat → ProperNode),
      (∀ n, (f n).edge = n.1.edge) →
      (nodes.zipIdx.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
    intro nodes f hf
    calc
      (nodes.zipIdx.map f).map ProperNode.edge =
          (nodes.zipIdx.map Prod.fst).map ProperNode.edge := by
        simp only [List.map_map]
        apply congrArg (fun g => nodes.zipIdx.map g)
        funext n
        exact hf n
      _ = nodes.map ProperNode.edge := by rw [List.zipIdx_map_fst]
  have hs : (sizeProperPorts P p).nodes.map ProperNode.edge = p.nodes.map ProperNode.edge := by
    unfold sizeProperPorts
    apply indexed
    intro n
    split <;> rfl
  have ht : ∀ nodes : List ProperNode,
      (nodes.map titleF).map ProperNode.edge = nodes.map ProperNode.edge := by
    intro nodes
    apply mapped
    intro n
    unfold titleF
    split <;> rfl
  have hc : ∀ q : Proper,
      (clearProxyExtents q).nodes.map ProperNode.edge = q.nodes.map ProperNode.edge := by
    intro q
    rw [clearProxyExtents_nodes]
    apply mapped
    intro n
    unfold clearF
    split <;> rfl
  have hm : ∀ q : Proper,
      (materializeDummyPaths q).nodes.map ProperNode.edge = q.nodes.map ProperNode.edge := by
    intro q
    unfold materializeDummyPaths
    apply indexed
    intro n
    split <;> rfl
  obtain ⟨extraNodes, hn, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  constructor
  · unfold coordinateGraph
    rw [hm, hc, hn, List.map_append, titleReservations_nodes, List.map_append, ht, hs]
    refine ⟨((titleNodes (sizeProperPorts P p)).map copyF).map ProperNode.edge ++
      extraNodes.map ProperNode.edge, ?_⟩
    rw [List.append_assoc]
  · obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW
    have htitle : ∃ tail, (titleReservations (sizeProperPorts P p)).rank = p.rank ++ tail :=
      ⟨_, rfl⟩
    obtain ⟨tail, htitle⟩ := htitle
    refine ⟨tail ++ extraRanks, ?_⟩
    change (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).rank = _
    rw [hr, htitle, List.append_assoc]

/-- Port sizing can widen a plain anchor, but title reservation, border
insertion, and display-path materialization cannot shrink its measured stack. -/
theorem coordinateGraph_plain_anchor_dims (P : Params) {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraph P p).nodes[i]? = some out ∧

      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨sized, hs, he, hb', hw, hh⟩ :
      ∃ sized, (sizeProperPorts P p).nodes[i]? = some sized ∧
        sized.edge = nd.edge ∧ sized.node.border = 0 ∧
        nd.node.w ≤ sized.node.w ∧ sized.node.h = nd.node.h := by
    unfold sizeProperPorts
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, rfl, hb, Int.le_refl _, rfl⟩
    · refine ⟨_, rfl, rfl, hb, ?_, rfl⟩
      exact Int.le_max_left _ _
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPorts P p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[i]? = some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split <;> exact ⟨_, rfl, he, hb', hw, hh⟩
/-- Proxy materialization changes checked widths and x coordinates, never the
edge-key sequence used to select the first forward label anchor. -/
theorem proxyWidths_edge_keys {p q : Proper} {xs ys : List Int}
    (h : proxyWidths p xs = .ok (q, ys)) :
    q.nodes.map ProperNode.edge = p.nodes.map ProperNode.edge := by
  unfold proxyWidths at h
  obtain ⟨updated, hu, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hq : q = { p with nodes := updated.map (·.1) } := (Prod.mk.inj he).1.symm
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ hu
  have hlen' : updated.length = p.nodes.length := by
    simpa only [List.length_zipIdx] using hlen
  subst q
  apply List.ext_getElem?
  intro v
  simp only [List.getElem?_map]
  cases hv : p.nodes[v]? with
  | none =>
    have hb : p.nodes.length ≤ v := List.getElem?_eq_none_iff.mp hv
    have hn : updated[v]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp [hn]
  | some nd =>
    obtain ⟨b, hb, hget⟩ := hidx v (nd, v)
      (by simp only [List.getElem?_zipIdx, hv, Option.map_some, Nat.zero_add])
    simp only [hget, Option.map_some]
    dsimp only at hb
    split at hb
    · cases hl : nd.node.clusterPath.getLast? with
      | none => simp [hl] at hb
      | some owner =>
        simp only [hl] at hb
        obtain ⟨span, _, hb⟩ := bind_ok hb
        obtain ⟨width, _, hb⟩ := bind_ok hb
        split at hb
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hb
        · obtain ⟨center, _, hb⟩ := bind_ok hb
          have he := Except.ok.inj hb
          rw [← he]
    · have he := Except.ok.inj hb
      rw [← he]

theorem proxyWidths_plain_node {p q : Proper} {xs ys : List Int}
    {i : Nat} {nd : ProperNode}
    (h : proxyWidths p xs = .ok (q, ys))
    (hp : p.nodes[i]? = some nd) (hb : nd.node.border = 0) :
    q.nodes[i]? = some nd := by
  unfold proxyWidths at h
  obtain ⟨updated, hu, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hq : q = { p with nodes := updated.map (·.1) } := (Prod.mk.inj he).1.symm
  obtain ⟨_, hidx⟩ := mapM_getElem? _ _ _ hu
  obtain ⟨entry, hentry, hget⟩ := hidx i (nd, i)
    (by simp only [List.getElem?_zipIdx, hp, Option.map_some, Nat.zero_add])
  dsimp only at hentry
  simp only [hb, show ((0 : Int) == -2) = false from rfl,
    show ((0 : Int) == 2) = false from rfl, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte] at hentry
  have hentryEq := Except.ok.inj hentry
  subst q
  simp only [List.getElem?_map, hget, Option.map_some]
  rw [← hentryEq]

theorem coordinateGraph_proxyWidths_plain_node_dims (P : Params)
    {p q : Proper} {xs ys : List Int} {i : Nat} {nd : ProperNode}
    (hp : p.nodes[i]? = some nd) (hb : nd.node.border = 0)
    (hproxy : proxyWidths (coordinateGraph P p) xs = .ok (q, ys)) :
    ∃ out, q.nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨out, hout, hedge, hborder, hw, hh⟩ :=
    coordinateGraph_plain_anchor_dims P hp hb
  exact ⟨out, proxyWidths_plain_node hproxy hout hborder, hedge, hborder, hw, hh⟩

theorem componentRun_plain_node_dims {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, projected, _, _, _, _, _, hproxy, hdrop,
    _, _, _, _, _⟩ := componentRun_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

theorem componentRun_coordinateGraph_plain_node_dims
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {p : Proper} (hcoordinate : coordinateGraph P p = run.coordinateProper)
    {i : Nat} {nd : ProperNode}
    (hnode : p.nodes[i]? = some nd) (hborder : nd.node.border = 0) :
    ∃ out, run.proper.nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨out, hout, hedge, hplain, hw, hh⟩ :=
    coordinateGraph_plain_anchor_dims P hnode hborder
  rw [hcoordinate] at hout
  exact ⟨out, componentRun_plain_node_dims h hout hplain, hedge, hplain, hw, hh⟩

/-- The actual component pipeline carries the selected measured stack through
coordinate construction and checked proxy materialization to the exact anchor
that forward label rendering will use. -/
theorem componentRun_forward_anchor_size {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {k : Nat} {edge : Edge} {first : MeasuredLabel}
    (h : componentRun P cg labels orderOptions = .ok run)
    (hk : cg.edges[k]? = some edge) (hne : edge.tail ≠ edge.head)
    (hfirst : (routeLabels labels edge.decl).head? = some first) :
    ∃ index nd,
      labelAnchorIndex run.proper k
        (rk run.proper.rank edge.tail +
          Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) =
            some index ∧
      run.proper.nodes[index]? = some nd ∧
      (stackSize cg.slot (routeLabels labels edge.decl)).width + first.gutter ≤ nd.node.w ∧
      nd.node.h = (stackSize cg.slot (routeLabels labels edge.decl)).height := by
  obtain ⟨ranks, p0, labeled, projected, hn, hl, hc, _, _, hproxy, hdrop,
    _, _, _, _, _⟩ := componentRun_spec h
  obtain ⟨halign0, hwf⟩ := normalize_node_rank_alignment hn
  obtain ⟨hlrank, hlkeys⟩ := addLabelNodes_anchor_keys hl
  have hllen : labeled.nodes.length = p0.nodes.length := by
    have he := congrArg List.length hlkeys
    simpa only [List.length_map] using he
  have halign : labeled.nodes.length = labeled.rank.length := by
    rw [hllen, hlrank, halign0]
  have hnodes := normalize_nodes_length_le hn
  have hedgeBounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hk)
  have htailBound : edge.tail < labeled.rank.length := by
    rw [hlrank]
    omega
  have hheadBound : edge.head < labeled.rank.length := by
    rw [hlrank]
    omega
  obtain ⟨index, nd, hi, hnode, hw, hh⟩ :=
    componentLabels_selected_size hk hne hfirst hl
  have hedge := labelAnchorIndex_node_edge hi hnode
  have hplain := addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain hn) hl
  have hborder : nd.node.border = 0 :=
    hplain nd (List.mem_of_getElem? hnode) (by simp [hedge])
  obtain ⟨out, hout, _, hborderOut, hwidth, hheight⟩ :=
    coordinateGraph_plain_anchor_dims P hnode hborder
  obtain ⟨hkeysPrefix, hrankPrefix⟩ := coordinateGraph_anchor_prefix P labeled
  have hicoord := labelAnchorIndex_prefix halign hkeysPrefix hrankPrefix hi
  rw [hc] at hout hicoord hrankPrefix
  obtain ⟨_, hprank, _, _, _, hpreserve⟩ := proxyWidths_rel hproxy
  have hpnode := (hpreserve index out hout (by rw [hborderOut]; omega)).1
  have hlookup : run.proper.nodes[index]? = some out := by
    rw [← hdrop]
    exact hpnode
  obtain ⟨extraRanks, hcrank⟩ := hrankPrefix
  have hfinalrank : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]
    exact hprank
  have htail : rk run.proper.rank edge.tail = rk labeled.rank edge.tail := by
    rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left htailBound]
  have hhead : rk run.proper.rank edge.head = rk labeled.rank edge.head := by
    rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left hheadBound]
  refine ⟨index, out, ?_, hlookup, ?_, hheight.trans hh⟩
  · rw [htail, hhead, ← hdrop]
    change labelAnchorIndex projected k _ = some index
    unfold labelAnchorIndex
    rw [proxyWidths_edge_keys hproxy, hprank]
    exact hicoord
  · rw [hw] at hwidth
    exact hwidth

def DeclInv (gedges : List Edge) (q : Proper) : Prop :=
  ∀ e ∈ q.edges, ∃ ge, gedges[e.original]? = some ge ∧ e.decl = ge.decl

theorem normalizeEdge_declInv {gedges : List Edge} {slot : Int} {q q' : Proper} {e : Edge}
    {idx : Nat} (hge : gedges[idx]? = some e) (hI : DeclInv gedges q)
    (h : NormalizeImpl.normalizeEdge slot q e idx = .ok q') : DeclInv gedges q' := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact hI
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        intro e' he'
        simp only [NormalizeImpl.appendChain] at he'
        rcases List.mem_append.mp he' with he' | he'
        · exact hI e' he'
        · simp only [NormalizeImpl.chainEdges, List.mem_map, List.mem_range] at he'
          obtain ⟨k, _, rfl⟩ := he'
          exact ⟨e, hge, rfl⟩

theorem normalizeLoop_declInv {gedges : List Edge} {slot : Int} :
    ∀ (l : List (Edge × Nat)) (q q' : Proper), (∀ x ∈ l, gedges[x.2]? = some x.1) →
      DeclInv gedges q → NormalizeImpl.normalizeLoop slot l q = .ok q' → DeclInv gedges q'
  | [], q, q', _, hI, h => by
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hI
  | x :: xs, q, q', hl, hI, h => by
    obtain ⟨e, i⟩ := x
    unfold NormalizeImpl.normalizeLoop at h
    split at h
    · simp at h
    · next q1 h1 =>
      exact normalizeLoop_declInv xs q1 q' (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        (normalizeEdge_declInv (hl (e, i) (List.mem_cons_self ..)) hI h1) h

theorem normalize_declInv {g : Graph} {rank : List Int} {p : Proper}
    (h : normalize g rank = .ok p) : DeclInv g.edges p := by
  unfold NormalizeImpl.normalize at h
  split at h
  · simp at h
  · next slot hs =>
    split at h
    · refine normalizeLoop_declInv _ _ _ (fun x hx => List.mem_zipIdx_iff_getElem?.mp hx)
        (fun e he => ?_) h
      simp at he
    · simp at h

theorem nodup_map_inj {α : Type} (f : α → Nat) {l : List α} (hn : (l.map f).Nodup) {a b : Nat}
    {x y : α} (ha : l[a]? = some x) (hb : l[b]? = some y) (h : f x = f y) : a = b := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨hai, hax⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hbi, hbx⟩ := List.getElem?_eq_some_iff.mp hb
  have hpa := List.pairwise_iff_getElem.mp hn
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hpa a b (by simpa using hai) (by simpa using hbi) hlt
    simp [hax, hbx, h] at this
  · have := hpa b a (by simpa using hbi) (by simpa using hai) hlt
    simp [hax, hbx, h] at this

theorem pairwise_inj {α : Type} (g : α → Nat) :
    ∀ l : List α, l.Pairwise (fun a b => g a < g b) →
      ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b
  | [], _, a, ha, _, _, _ => by simp at ha
  | c :: l, hp, a, ha, b, hb, hab => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · have := h1 b hb'
        omega
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have := h1 a ha'
        omega
      · exact pairwise_inj g l h2 a ha' b hb' hab

theorem chain_pairwise {R : Nat → Nat → Prop} (g : Nat → Nat) (hR : ∀ a b, R a b → g a < g b) :
    ∀ es : List Nat, RouteImpl.chainRel R es → es.Pairwise (fun a b => g a < g b)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [RouteImpl.chainRel] at h
    have ih := chain_pairwise g hR (b :: rest) h.2
    refine List.pairwise_cons.mpr ⟨fun c hc => ?_, ih⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hR a c h.1
    · have h1 := (List.pairwise_cons.mp ih).1 c hc'
      have h2 := hR a b h.1
      omega

theorem edgeAt_mem {p : Proper} {i : Nat} (hi : i < p.edges.length) :
    RouteImpl.edgeAt p i ∈ p.edges := by
  have : RouteImpl.edgeAt p i = p.edges[i] := by
    simp [RouteImpl.edgeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [this]
  exact List.getElem_mem hi

theorem mem_edgesOf {p : Proper} {o i : Nat} :
    i ∈ RouteImpl.edgesOf p o ↔ i < p.edges.length ∧ (RouteImpl.edgeAt p i).original = o := by
  simp [RouteImpl.edgesOf, List.mem_filter, List.mem_range]

theorem chain_gap_lt {p : Proper} {layers : List (List Nat)}
    (hl : RouteImpl.layersOk p layers = true) {i j : Nat} (h : RouteImpl.ChainLink p i j) :
    RouteImpl.gapOf p i < RouteImpl.gapOf p j := by
  obtain ⟨hi, _, hhead, _⟩ := h
  obtain ⟨_, _, _, hcov, hedge⟩ := RouteImpl.layersOk_spec hl
  obtain ⟨ht, _, hsp⟩ := hedge i hi
  obtain ⟨l, _, _, hnn⟩ := hcov _ ht
  unfold RouteImpl.gapOf
  rw [← hhead]
  omega

theorem gapDeclsDistinct_of_normalize {g : Graph} {rank : List Int} {p : Proper}
    {layers : List (List Nat)} (hd : (g.edges.map (·.decl)).Nodup)
    (hn : normalize g rank = .ok p) (hl : RouteImpl.layersOk p layers = true) :
    RouteImpl.GapDeclsDistinct p := by
  intro i j hi hj hgap hdecl
  obtain ⟨gi, hgi, hdi⟩ := normalize_declInv hn _ (edgeAt_mem hi)
  obtain ⟨gj, hgj, hdj⟩ := normalize_declInv hn _ (edgeAt_mem hj)
  have ho : (RouteImpl.edgeAt p i).original = (RouteImpl.edgeAt p j).original :=
    nodup_map_inj (·.decl) hd hgi hgj (by rw [← hdi, ← hdj, hdecl])
  have hch := normalize_shape hn (RouteImpl.edgeAt p i).original
  have hpw := chain_pairwise (RouteImpl.gapOf p) (fun a b hab => chain_gap_lt hl hab) _ hch
  exact pairwise_inj (RouteImpl.gapOf p) _ hpw i (mem_edgesOf.mpr ⟨hi, rfl⟩) j
    (mem_edgesOf.mpr ⟨hj, ho.symm⟩) hgap

theorem gapDeclsDistinct_of_shape {g : Graph} {p : Proper} {layers : List (List Nat)}
    (hd : (g.edges.map (·.decl)).Nodup) (hI : DeclInv g.edges p)
    (hshape : RouteImpl.ProperShape p) (hl : RouteImpl.layersOk p layers = true) :
    RouteImpl.GapDeclsDistinct p := by
  intro i j hi hj hgap hdecl
  obtain ⟨gi, hgi, hdi⟩ := hI _ (edgeAt_mem hi)
  obtain ⟨gj, hgj, hdj⟩ := hI _ (edgeAt_mem hj)
  have ho : (RouteImpl.edgeAt p i).original = (RouteImpl.edgeAt p j).original :=
    nodup_map_inj (·.decl) hd hgi hgj (by rw [← hdi, ← hdj, hdecl])
  have hpw := chain_pairwise (RouteImpl.gapOf p) (fun a b hab => chain_gap_lt hl hab) _
    (hshape (RouteImpl.edgeAt p i).original)
  exact pairwise_inj (RouteImpl.gapOf p) _ hpw i (mem_edgesOf.mpr ⟨hi, rfl⟩) j
    (mem_edgesOf.mpr ⟨hj, ho.symm⟩) hgap

theorem normalizeEdge_clean {slot : Int} {q q' : Proper} {e : Edge} {idx : Nat}
    (hI : ∀ x ∈ q.edges, x.synthetic = false)
    (h : NormalizeImpl.normalizeEdge slot q e idx = .ok q') :
    ∀ x ∈ q'.edges, x.synthetic = false := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact hI
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        intro x hx
        simp only [NormalizeImpl.appendChain] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hI x hx
        · simp only [NormalizeImpl.chainEdges, List.mem_map, List.mem_range] at hx
          obtain ⟨k, _, rfl⟩ := hx
          rfl

theorem normalizeLoop_clean {slot : Int} :
    ∀ (l : List (Edge × Nat)) (q q' : Proper), (∀ x ∈ q.edges, x.synthetic = false) →
      NormalizeImpl.normalizeLoop slot l q = .ok q' → ∀ x ∈ q'.edges, x.synthetic = false
  | [], q, q', hI, h => by
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hI
  | x :: xs, q, q', hI, h => by
    obtain ⟨e, i⟩ := x
    unfold NormalizeImpl.normalizeLoop at h
    split at h
    · simp at h
    · next q1 h1 =>
      exact normalizeLoop_clean xs q1 q' (normalizeEdge_clean hI h1) h

theorem normalize_clean {g : Graph} {rank : List Int} {p : Proper}
    (h : normalize g rank = .ok p) : ∀ x ∈ p.edges, x.synthetic = false := by
  unfold NormalizeImpl.normalize at h
  split at h
  · simp at h
  · split at h
    · refine normalizeLoop_clean _ _ _ (fun x hx => ?_) h
      simp at hx
    · simp at h

/-- Adjacent separations of one layer give separations of every ordered pair. -/
theorem coordSep_chain {gap : Int} (hg : 1 ≤ gap) {p : Proper} {layer : List Nat}
    {x : List Int} (hnn : ∀ v, 0 ≤ CoordsImpl.nodeW p v)
    (hadj : ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
      CoordsImpl.coordSep gap p a b ≤ x.getD b 0 - x.getD a 0) :
    ∀ (d i j : Nat) (a b : Nat), j = i + 1 + d → layer[i]? = some a → layer[j]? = some b →
      CoordsImpl.coordSep gap p a b ≤ x.getD b 0 - x.getD a 0 := by
  intro d
  induction d with
  | zero =>
    intro i j a b hj ha hb
    subst hj
    exact hadj i a b ha hb
  | succ d ih =>
    intro i j a b hj ha hb
    have hjl : j - 1 < layer.length := by
      have := (List.getElem?_eq_some_iff.mp hb).1
      omega
    obtain ⟨m, hm⟩ : ∃ m, layer[j - 1]? = some m := ⟨_, List.getElem?_eq_getElem hjl⟩
    have h1 := ih i (j - 1) a m (by omega) ha hm
    have h2 := hadj (j - 1) m b hm (by rw [show j - 1 + 1 = j by omega]; exact hb)
    have hmm := hnn m
    unfold CoordsImpl.coordSep at h1 h2 ⊢
    rw [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at h1 h2 ⊢
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at h1 h2 ⊢
    omega

/-- Flat coordinate phases, for proper graphs without frame anchors. -/
theorem coordFacts_of_pipeline {P : Params} (hP : P.Valid) {p : Proper}
    {layers : List (List Nat)} {xs ys top : List Int} {r : Routing}
    (hnf : ∀ v, ¬ RouteImpl.IsFrame p v)
    (hx : crossCoordsWith P.nodeGap p layers = .ok xs) (hr : route p layers xs = .ok r)
    (hy : rankCoordsWith P.rankGap P.slot p layers (r.gaps.map (·.slots)) = .ok (ys, top)) :
    CoordFacts p layers xs ys top r P.nodeGap (CoordsImpl.rankGapAt P.rankGap p layers) P.slot := by
  obtain ⟨hg, hrg, hs, hh⟩ := hP
  obtain ⟨_, _, hsz, _⟩ := CoordsImpl.crossCoordsWith_spec hx
  refine ⟨hg, fun k => CoordsImpl.rankGapAt_nonneg (by omega) p layers k, hs,
    fun k => CoordsImpl.half_slot_le_rankGapAt hrg hh p layers k,
    ?_, fun v hv => absurd hv (hnf v),
    fun k l v _ _ hT => absurd (Or.inl hT) (hnf v),
    fun layer _ t v _ _ hT => absurd (Or.inl hT) (hnf t),
    fun layer _ t v _ _ hB => absurd (Or.inr hB) (hnf t), ?_, ?_⟩
  · intro layer hl i j a b hij ha hb _ _ _
    have hsep := coordSep_chain hg (p := p) (layer := layer) (x := xs)
      (fun v => CoordsImpl.nodeW_nonneg hsz v)
      (fun i a b ha hb => balance_separated hx layer hl i a b ha hb) (j - i - 1) i j a b
      (by omega) ha hb
    have hwa : RouteImpl.nodeW p a ≤ CoordsImpl.nodeW p a := CoordsImpl.nodeW_ge_width p a
    have hwb : RouteImpl.nodeW p b ≤ CoordsImpl.nodeW p b := CoordsImpl.nodeW_ge_width p b
    unfold CoordsImpl.coordSep at hsep
    unfold RouteImpl.coordSep
    unfold RouteImpl.xAt
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega
  · intro k l v hkl hv hvn hrk
    exact rankAxis_node_in_band hy hkl hv hvn hrk
  · intro k l hkl hk
    obtain ⟨_, _, hlen, _, _, htop, _⟩ := CoordsImpl.rankCoordsWith_spec hy
    obtain ⟨_, _, _, _, _, hgaps, _⟩ := RouteImpl.route_spec hr
    subst htop
    have hgl : r.gaps.length = layers.length - 1 := by
      rw [hgaps]
      simp
    have hk' : k < r.gaps.length := by omega
    have hh : (layers.map (CoordsImpl.layerHeight p)).getD k 0 = CoordsImpl.layerHeight p l := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hkl]
    have hs' : (r.gaps.map (·.slots)).getD k 0 = (r.gaps.getD k default).slots := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk']
    rw [rankSteps_topsFrom_step P.rankGap P.slot p layers (r.gaps.map (·.slots))
      0 k (by simp; omega) (by simpa using hk), hh, hs']
    rfl

theorem componentRun_facts {P : Params} (hP : P.Valid) {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hd : (cg.edges.map (·.decl)).Nodup) (hS : CgShape cg)
    (h : componentRun P cg labels orderOptions = .ok run) :
    RouteImpl.ProperShape run.proper ∧ RouteImpl.GapDeclsDistinct run.proper ∧
      (FrameClearance run.proper run.layers run.xs →
        CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
          (min P.nodeGap P.clusterPad)
          (CoordsImpl.rankGapAt P.rankGap run.proper run.layers) P.slot) := by
  obtain ⟨ranks, p0, labeled, q0, hn, hlabels, hproper, _, hx, hprox, hdrop, hr, hroute, hy,
    hys, _⟩ := componentRun_spec h
  obtain ⟨he, _, _, hdummy⟩ := Labels.addLabelNodes_metadata hlabels
  have hK : NodeKeys cg labeled := addLabelNodes_keys _ _ _ (normalize_keys hn) hlabels
  have hlabeled : RouteImpl.ProperShape labeled :=
    RouteImpl.properShape_of_metadata he hdummy (normalize_shape hn)
  have hsized : Metadata.NodeMetadata labeled (sizeProperPorts P labeled) := by
    apply Metadata.nodeMetadata_of_lookup_maps
    intro v
    have hk := congrArg (Option.map (fun t : Bool × Int × List Nat => t.1))
      (sizeProperPorts_key P labeled v)
    simpa [Option.map_map, Function.comp_def] using hk
  have hs1 : RouteImpl.ProperShape (sizeProperPorts P labeled) :=
    Metadata.properShape_transfer (p := labeled) (q := sizeProperPorts P labeled)
      rfl hsized hlabeled
  have hT : RouteImpl.ProperShape (titleReservations (sizeProperPorts P labeled)) :=
    Metadata.properShape_transfer (p := sizeProperPorts P labeled) rfl
      (Metadata.nodeMetadata_map_append titleF (fun n => (titleF_keys n).1) _
        (titleReservations_nodes _)) hs1
  have hclean : ∀ e ∈ (titleReservations (sizeProperPorts P labeled)).edges,
      e.synthetic = false := by
    intro e he'
    have hTe : (titleReservations (sizeProperPorts P labeled)).edges = p0.edges := he
    rw [hTe] at he'
    exact normalize_clean hn e he'
  have hext := OrderImpl.addClusterBorders_metadata
    (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW
  have hAdd := Metadata.properShape_borderExtension hext hclean hT
  obtain ⟨hrE, hrR, hlen, hxlen, hP1, hP2⟩ := proxyWidths_rel hprox
  have hdropE : (OrderImpl.dropSynthetic q0).edges = (OrderImpl.dropSynthetic
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW)).edges := by
    show q0.edges.filter (fun e => !e.synthetic) = _
    rw [hrE, ← hproper]
    rfl
  have hmeta : Metadata.NodeMetadata (OrderImpl.dropSynthetic
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW)) (OrderImpl.dropSynthetic q0) := by
    intro v nd hv
    have hv' : (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW).nodes[v]? = some nd := hv
    have h1 : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes[v]? =
          some (clearF nd) := by
      rw [clearProxyExtents_nodes]
      simp only [List.getElem?_map, hv']
      rfl
    obtain ⟨n2, hn2, hd2⟩ := materialize_exists _ h1
    have hc : (coordinateGraph P labeled).nodes[v]? = some n2 := hn2
    rw [hproper] at hc
    obtain ⟨nd', hq', hd', _, _⟩ := hP1 v _ hc
    exact ⟨nd', hq', hd'.trans (hd2.trans (clearF_keys nd).1)⟩
  have hshape : RouteImpl.ProperShape run.proper := by
    rw [← hdrop]
    exact Metadata.properShape_transfer hdropE hmeta hAdd
  have hlabeledE : (OrderImpl.dropSynthetic q0).edges = labeled.edges := by
    rw [hdropE]
    exact OrderImpl.dropSynthetic_addClusterBorders_edges _ _ hclean
  have hI : DeclInv cg.edges run.proper := by
    rw [← hdrop]
    intro e he'
    rw [hlabeledE, he] at he'
    exact normalize_declInv hn e he'
  have hl := (RouteImpl.routeWithLanes_geometry hr).1
  refine ⟨hshape, gapDeclsDistinct_of_shape hd hI hshape hl, fun hclear => ?_⟩
  have hy' : rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
      (run.lanes.routing.gaps.map (·.slots)) = .ok (run.coordinateYs, run.top) := by
    rw [hroute]
    exact hy
  have hF := coordFacts_of_parts hP hK hS hproper hdrop hx hprox hr hy' hys hclear
  rw [hroute] at hF
  exact hF

theorem checkedParams_valid {profile : Profile} {P : Params}
    (h : checkedParams profile = .ok P) : P.Valid := by
  unfold checkedParams at h
  split at h
  · simp at h
  · next Q hQ =>
    split at h
    · next hv =>
      simp only [Except.ok.injEq] at h
      subst h
      exact hv
    · simp at h

def ComponentFacts (inp : Input) (o : Options) : Prop :=
  ∃ P lines measured g0, checkedParams o.profile = .ok P ∧ measuredGraph P inp o lines = .ok g0 ∧
    ∀ comp ∈ components g0, ∃ index run, index < 5 ∧
      componentRun P (componentCandidate g0 comp index) measured (candidateOrder index) =
        .ok run ∧
      RouteImpl.ProperShape run.proper ∧ RouteImpl.GapDeclsDistinct run.proper ∧
      (FrameClearance run.proper run.layers run.xs →
        CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
          (min P.nodeGap P.clusterPad)
          (CoordsImpl.rankGapAt P.rankGap run.proper run.layers) P.slot)

theorem layout_component_facts {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) : ComponentFacts inp o := by
  unfold layout at h
  dsimp only at h
  obtain ⟨P, hP, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨lines, _, h⟩ := bind_ok h
  obtain ⟨measured, _, h⟩ := bind_ok h
  obtain ⟨g0, hg0, h⟩ := bind_ok h
  obtain ⟨acc, hacc, _⟩ := bind_ok h
  refine ⟨P, lines, measured, g0, hP, hg0, fun comp hcomp => ?_⟩
  obtain ⟨a', b', hab⟩ := foldlM_ok_mem _ _ _ _ hacc comp hcomp
  obtain ⟨index, run, hi, hrun⟩ := layoutComponent_run hab
  refine ⟨index, run, hi, hrun, ?_⟩
  refine componentRun_facts (checkedParams_valid hP) ?_
    (componentCandidate_shape (components_nodup g0 comp hcomp) (measuredGraph_shape hg0) index)
    hrun
  rw [componentCandidate_decls]
  exact componentGraph_decls_nodup _ _ (measuredGraph_decls_nodup hg0)

theorem zipIdx_map_comp {α β : Type} (f : α → β) :
    ∀ (l : List α) (k : Nat), (l.zipIdx k).map (fun q => f q.1) = l.map f
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, zipIdx_map_comp f l (k + 1)]

theorem layout_ids {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  unfold layout at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf, List.map_map]
    exact ⟨zipIdx_map_comp (·.id) inp.boxes 0, zipIdx_map_comp (·.id) inp.routes 0⟩

end PipelineImpl

theorem layoutFamily_geometry_ok {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) :
    PipelineImpl.layoutRecursive (inp.boxes.length + 1) inp o = .ok res := by
  by_cases hn : o.limits.maxNodes < inp.boxes.length <;>
    by_cases he : o.limits.maxEdges < inp.routes.length <;>
    by_cases ht : o.limits.maxTextBytes < inputTextBytes inp <;>
    by_cases hw : modelWellFormed (inputModel inp o) <;>
    cases hg : PipelineImpl.layoutRecursive (inp.boxes.length + 1) inp o <;>
    simp_all [layoutFamily]

theorem layoutFamily_wellFormed {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) : WellFormed (inputModel inp o) := by
  by_cases hn : o.limits.maxNodes < inp.boxes.length <;>
    by_cases he : o.limits.maxEdges < inp.routes.length <;>
    by_cases ht : o.limits.maxTextBytes < inputTextBytes inp <;>
    by_cases hw : modelWellFormed (inputModel inp o) <;>
    simp_all [layoutFamily, WellFormed]

theorem normalize_gapDeclsDistinct {g : Graph} {rank : List Int} {p : Proper}
    {layers : List (List Nat)} (hd : (g.edges.map (·.decl)).Nodup)
    (hn : normalize g rank = .ok p) (hl : RouteImpl.layersOk p layers = true) :
    GapDeclsDistinct p :=
  PipelineImpl.gapDeclsDistinct_of_normalize hd hn hl

theorem coordPhases_coordFacts {P : PipelineImpl.Params} (hP : P.Valid) {p : Proper}
    {layers : List (List Nat)} {xs ys top : List Int} {r : Routing}
    (hnf : ∀ v, ¬ RouteImpl.IsFrame p v)
    (hx : crossCoordsWith P.nodeGap p layers = .ok xs) (hr : route p layers xs = .ok r)
    (hy : rankCoordsWith P.rankGap P.slot p layers (r.gaps.map (·.slots)) = .ok (ys, top)) :
    CoordFacts p layers xs ys top r P.nodeGap (CoordsImpl.rankGapAt P.rankGap p layers) P.slot :=
  PipelineImpl.coordFacts_of_pipeline hP hnf hx hr hy

theorem layoutFamily_component_facts {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) :
    PipelineImpl.TraceOf PipelineImpl.ComponentFacts (inp.boxes.length + 1) inp o :=
  PipelineImpl.layoutRecursive_trace
    (fun _ _ _ hl => PipelineImpl.layout_component_facts hl) _ _ _ _
    (layoutFamily_geometry_ok h)

theorem componentRun_route_avoids_nodes {P : PipelineImpl.Params} (hP : P.Valid)
    {cg : Graph} {run : PipelineImpl.Run} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions}
    (hd : (cg.edges.map (·.decl)).Nodup) (hS : PipelineImpl.CgShape cg)
    (hclear : PipelineImpl.FrameClearance run.proper run.layers run.xs)
    (h : PipelineImpl.componentRun P cg labels orderOptions = .ok run) :
    ∀ rt ∈ run.routes, ∀ i₀ i₁, (edgesOf run.proper rt.original).head? = some i₀ →
      (edgesOf run.proper rt.original).getLast? = some i₁ →
      ∀ v, v < run.proper.nodes.length → IsReal run.proper v →
        v ≠ (edgeAt run.proper i₀).tail → v ≠ (edgeAt run.proper i₁).head →
        ¬ Polyline.hitsRect rt.points (boxRect run.proper run.xs run.ys v) := by
  obtain ⟨hshape, _, hcoords⟩ := PipelineImpl.componentRun_facts hP hd hS h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, hroute, _, _, hpoints⟩ :=
    PipelineImpl.componentRun_spec h
  have hF := hcoords hclear
  rw [← hroute] at hF
  exact route_avoids_nodes hshape hr hpoints hF

/-- Distinct executed midpoint label nodes in one rank have disjoint rectangles. -/
theorem componentRun_labels_disjoint {P : PipelineImpl.Params} (hP : P.Valid)
    {cg : Graph} {run : PipelineImpl.Run} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions}
    (hd : (cg.edges.map (·.decl)).Nodup) (hS : PipelineImpl.CgShape cg)
    (hclear : PipelineImpl.FrameClearance run.proper run.layers run.xs)
    (h : PipelineImpl.componentRun P cg labels orderOptions = .ok run)
    {u v : Nat} (hu : u < run.proper.nodes.length) (hv : v < run.proper.nodes.length)
    (hrank : rk run.proper.rank u = rk run.proper.rank v) (hne : u ≠ v) :
    ¬ Rect.meetsInterior (Labels.rectAt run.proper run.xs run.ys u)
      (Labels.rectAt run.proper run.xs run.ys v) := by
  obtain ⟨_, _, hcoords⟩ := PipelineImpl.componentRun_facts hP hd hS h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, _, _, _⟩ := PipelineImpl.componentRun_spec h
  exact labels_disjoint (RouteImpl.routeWithLanes_geometry hr).1 (hcoords hclear) hu hv hrank hne

theorem componentRun_slots_separate_overlapping_segments {P : PipelineImpl.Params}
    {cg : Graph} {run : PipelineImpl.Run} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : PipelineImpl.componentRun P cg labels orderOptions = .ok run) :
    ∀ g ∈ run.routing.gaps, ∀ s ∈ g.segments, ∀ t ∈ g.segments,
      (s.tail ≠ t.tail ∨ s.head ≠ t.head) →
        segConflict s t = true → s.slot ≠ t.slot := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, hroute, _, _, _⟩ := PipelineImpl.componentRun_spec h
  rw [← hroute]
  exact slots_separate_overlapping_segments hr

theorem layoutFamily_ids {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  have hw := layoutFamily_wellFormed h
  refine PipelineImpl.layoutRecursive_ids (fun _ _ _ hl => PipelineImpl.layout_ids hl) _ _ _ _
    ?_ (layoutFamily_geometry_ok h)
  intro r hr
  have hwf : modelWellFormed (inputModel inp o) = true := hw
  unfold modelWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hroutes⟩, _⟩, _⟩ := hwf
  have hr' := List.all_eq_true.mp hroutes r hr
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at hr'
  exact ⟨hr'.1, hr'.2⟩

/-- Every point actually emitted by component placement belongs to the bounds
used for that placement. The non-loop case uses the successful route-array
correspondence, rather than assuming that `edgePoints` selected a real route. -/
theorem placeComponent_routes_bounds_of_run
    {P : PipelineImpl.Params} {cg : Graph} {run : PipelineImpl.Run}
    {labels : List PipelineImpl.MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : PipelineImpl.componentRun P cg labels orderOptions = .ok run)
    (loops : List (Nat × LoopPlacement)) :
    ∀ route ∈ (PipelineImpl.placeComponent P cg run 0 labels loops).routes,
      ∀ p ∈ route.2,
        0 ≤ p.x ∧ p.x ≤ (PipelineImpl.placeComponent P cg run 0 labels loops).width ∧
        0 ≤ p.y ∧ p.y ≤ (PipelineImpl.placeComponent P cg run 0 labels loops).height := by
  intro route hroute p hp
  change route ∈ cg.edges.zipIdx.map _ at hroute
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hroute
  dsimp only at hp
  obtain ⟨point, hpoint, rfl⟩ := List.mem_map.mp hp
  have hcovered :
      point ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points) := by
    cases hloop : loops.find? (fun l => l.1 == q.1.decl) with
    | some loop =>
      have hl : loop ∈ loops := List.mem_of_find?_eq_some hloop
      have hp' : point ∈ loop.2.points := by
        simpa only [hloop, Option.map_some, Option.getD_some] using hpoint
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨loop, hl, hp'⟩)
    | none =>
      have hget : cg.edges[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
      have hi := (List.getElem?_eq_some_iff.mp hget).1
      have hp' : point ∈ PipelineImpl.edgePoints run q.2 q.1 := by
        simpa only [hloop, Option.map_none, Option.getD_none] using hpoint
      rw [PipelineImpl.componentRun_edgePoints_of_index hrun hi] at hp'
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨_, List.getElem_mem _, hp'⟩)
  exact PipelineImpl.placeComponent_shifted_point_bounds_zero P cg run labels loops point hcovered

/-- Recover the executed phases, including the exact packed accumulator used by
`sceneOf`; no placement or scene-validity hypothesis is supplied by the caller. -/
theorem layout_success_phases {inp : Input} {o : Options} {result : FamilyResult}
    (h : PipelineImpl.layout inp o = .ok result) :
    ∃ P metric lines measured graph mid packed,
      PipelineImpl.checkedParams o.profile inp.kind = .ok P ∧
      PipelineImpl.metricOf o.profile = .ok metric ∧
      PipelineImpl.boxLines metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp = .ok lines ∧
      PipelineImpl.measureLabels P metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp o.direction = .ok measured ∧
      PipelineImpl.measuredGraph P inp o lines = .ok graph ∧
      (PipelineImpl.components graph).foldlM
        (fun acc comp => PipelineImpl.layoutComponent P inp o graph acc comp measured)
        ⟨0, 0, 0, Array.replicate inp.boxes.length default,
          Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
          false, [], []⟩ = .ok mid ∧
      PipelineImpl.packAcc P o mid = .ok packed ∧
      result.scene = PipelineImpl.sceneOf P inp o lines packed measured ∧
      result.budgetExhausted = packed.budget ∧
      result.itemArea = packed.parts.foldl (fun area part => area + part.2.area) 0 := by
  unfold PipelineImpl.layout at h
  obtain ⟨P, hP, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨metric, hm, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨lines, hl, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨measured, hmeasured, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨graph, hg, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨mid, hmid, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨packed, hpacked, h⟩ := PipelineImpl.bind_ok h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · have he := Except.ok.inj h
    subst result
    exact ⟨P, metric, lines, measured, graph, mid, packed,
      hP, hm, hl, hmeasured, hg, hmid, hpacked, rfl, rfl, rfl⟩

/-- The public family gate admits precisely an actual successful recursive run
on the supplied input, and its successful branch establishes model admission. -/
theorem layoutFamily_success {inp : Input} {o : Options} {result : FamilyResult}
    (h : layoutFamily inp o = .ok result) :
    WellFormed (inputModel inp o) ∧
      PipelineImpl.layoutRecursive (inp.boxes.length + 1) inp o = .ok result := by
  unfold layoutFamily at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next hadmitted =>
          have hwf : WellFormed (inputModel inp o) := by
            unfold WellFormed
            cases hb : modelWellFormed (inputModel inp o) with
            | false => simp [hb] at hadmitted
            | true => rfl
          cases hr : PipelineImpl.layoutRecursive (inp.boxes.length + 1) inp o with
          | error error => simp [hr] at h
          | ok out =>
            simp only [hr, Except.ok.injEq] at h
            subst result
            exact ⟨hwf, rfl⟩

/-- Successful base execution supplies both global route-declaration ownership
and the disjoint component packing used to assemble its final scene. -/
theorem layout_success_component_packing {inp : Input} {o : Options}
    {result : FamilyResult} (h : PipelineImpl.layout inp o = .ok result) :
    ∃ P lines measured graph mid out packed,
      PipelineImpl.measuredGraph P inp o lines = .ok graph ∧
      (graph.edges.map (·.decl)).Nodup ∧
      (PipelineImpl.components graph).foldlM
        (fun acc comp => PipelineImpl.layoutComponent P inp o graph acc comp measured)
        ⟨0, 0, 0, Array.replicate inp.boxes.length default,
          Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
          false, [], []⟩ = .ok mid ∧
      PipelineImpl.packAcc P o mid = .ok out ∧
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (mid.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed ∧
      packed.boxes.Pairwise Disjoint ∧
      result.scene = PipelineImpl.sceneOf P inp o lines out measured := by
  obtain ⟨P, metric, lines, measured, graph, mid, out,
    _, _, _, _, hg, hfold, hpack, hscene, _, _⟩ := layout_success_phases h
  obtain ⟨packed, hpacked, hdisjoint⟩ := PipelineImpl.packAcc_components_disjoint hpack
  exact ⟨P, lines, measured, graph, mid, out, packed, hg,
    PipelineImpl.measuredGraph_decls_nodup hg, hfold, hpack, hpacked, hdisjoint, hscene⟩

/-- With no recursively laid-out independent group, the public successful run
uses the same base pipeline whose phase witnesses are recovered above. -/
theorem layoutFamily_success_base {inp : Input} {o : Options} {result : FamilyResult}
    (h : layoutFamily inp o = .ok result)
    (hflat : inp.boxes.find? (fun box =>
      Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none) :
    PipelineImpl.layout inp o = .ok result := by
  have hr := (layoutFamily_success h).2
  simpa only [PipelineImpl.layoutRecursive, hflat] using hr

theorem placeComponent_rect_dimensions (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (cursor : Int)
    (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    ((PipelineImpl.placeComponent P cg run cursor labels loops).rects.map
      (fun rect => (rect.w, rect.h))) =
      (List.range cg.nodes.length).map (fun i =>
        ((PipelineImpl.frameRect P cg run i).w,
          (PipelineImpl.frameRect P cg run i).h)) := by
  unfold PipelineImpl.placeComponent
  simp [PipelineImpl.shiftRect, Function.comp_def]

end Layered
end Elegant
