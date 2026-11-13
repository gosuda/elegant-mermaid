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

end Layered
end Elegant
