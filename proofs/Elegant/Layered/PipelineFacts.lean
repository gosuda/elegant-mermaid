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

private theorem mapM_index_record {α β : Type} (f : α → Except LayoutError β) :
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

private theorem sizedNodes_index_metadata {P : Params}
    {lines : List (List Measure.Line)} {nodes : List Node}
    (h : sizedNodes P lines = .ok nodes) :
    nodes.length = lines.length ∧
      ∀ (i : Nat) (n : Node), nodes[i]? = some n → n.decl = i ∧ n.border = 0 := by
  unfold sizedNodes at h
  obtain ⟨hlen, hget⟩ := mapM_index_record
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

private theorem componentCandidate_nodes_record (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes =
      comp.map (fun v => g.nodes.getD v default) := by
  unfold componentCandidate
  dsimp only
  split
  · split
    · rfl
    · rfl
  · unfold cycleGraph
    split <;> rfl

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
    ∀ p ∈ out, ¬ Polyline.hitsRect p.points (nodeRect cg run v) := by
  unfold nodeLoops at h
  split at h
  · exact Loops.exactLoops_result_outside_node h
  · exact Loops.loops_result_outside_node h

theorem bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem packAcc_components_disjoint {P : Params} {o : Options} {acc out : Acc}
    (h : packAcc P o acc = .ok out) :
    ∃ packed, Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
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
private theorem measuredGraph_title_metadata {P : Params} {inp : Input} {o : Options}
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
  obtain ⟨hlen, hinit⟩ := sizedNodes_index_metadata hinitial
  obtain ⟨hprocessed, hget⟩ := mapM_index_record _ _ _ hnodes
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

theorem actual_title_metadata {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    {comp : List Nat} {index i : Nat} {top : Node} {box : ModelBox}
    (htop : (componentCandidate g comp index).nodes[i]? = some top)
    (hborder : top.border = -2)
    (hbox : inp.boxes[comp.getD i 0]? = some box) :
    ∃ j, comp[i]? = some j ∧ comp.getD i 0 = j ∧
      g.nodes[j]? = some top ∧ top.decl = j ∧ j < lines.length ∧
      box.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false ∧
      top.w = (match o.direction with
        | .LR | .RL => (max 1 (lines.getD j []).length : Int) * P.lineH
        | .TB | .BT => (lines.getD j []).foldl (fun w line => max w line.width) 0) ∧
      (match o.direction with
        | .LR | .RL => (lines.getD j []).foldl (fun w line => max w line.width) 0
        | .TB | .BT => (max 1 (lines.getD j []).length : Int) * P.lineH) +
          P.clusterPad ≤ top.h := by
  rw [componentCandidate_nodes_record] at htop
  cases hc : comp[i]? with
  | none => simp [List.getElem?_map, hc] at htop
  | some j =>
    have hcD : comp.getD i 0 = j := by simp [List.getD, hc]
    have hv : g.nodes.getD j default = top := by
      simpa [List.getElem?_map, hc] using htop
    have hj : j < g.nodes.length := by
      by_cases hj : j < g.nodes.length
      · exact hj
      · have hnone : g.nodes[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        have hdefault : (default : Node) = top := by simpa [List.getD, hnone] using hv
        rw [← hdefault] at hborder
        have hz : (default : Node).border = 0 := rfl
        rw [hz] at hborder
        omega
    have hget : g.nodes[j]? = some top := by
      have he : g.nodes[j] = top := by simpa [List.getD, hj] using hv
      simpa [hj] using congrArg some he
    obtain ⟨hlt, hdecl, original, horiginal, hrole, hfixed, hw, hh⟩ :=
      measuredGraph_title_metadata hg hget hborder
    rw [hcD] at hbox
    have hsame : original = box := Option.some.inj (horiginal.symm.trans hbox)
    subst original
    exact ⟨j, rfl, hcD, hget, hdecl, hlt, hrole, hfixed, hw, hh⟩

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

theorem checkedParams_valid {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : P.Valid := by
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
  ∃ P lines measured g0, checkedParams o.profile inp.kind = .ok P ∧ measuredGraph P inp o lines = .ok g0 ∧
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
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf, List.map_map]
    exact ⟨zipIdx_map_comp (·.id) inp.boxes 0, zipIdx_map_comp (·.id) inp.routes 0⟩

/-! ### Bounds fold and component placement geometry -/

theorem foldl_stepRect_minX_le :
    ∀ (rects : List Rect) (b : Bounds),
      (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).minX ≤ b.minX
  | [], b => Int.le_refl b.minX
  | r :: rs, b => by
    simp only [List.foldl_cons]
    have h := foldl_stepRect_minX_le rs ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩
    exact Int.le_trans h (Int.min_le_left b.minX r.x)

theorem foldl_stepRect_minY_le :
    ∀ (rects : List Rect) (b : Bounds),
      (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).minY ≤ b.minY
  | [], b => Int.le_refl b.minY
  | r :: rs, b => by
    simp only [List.foldl_cons]
    have h := foldl_stepRect_minY_le rs ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩
    exact Int.le_trans h (Int.min_le_left b.minY r.y)

theorem foldl_stepRect_le_right :
    ∀ (rects : List Rect) (b : Bounds),
      b.right ≤ (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).right
  | [], b => Int.le_refl b.right
  | r :: rs, b => by
    simp only [List.foldl_cons]
    have h := foldl_stepRect_le_right rs ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩
    exact Int.le_trans (Int.le_max_left b.right (r.x + r.w)) h

theorem foldl_stepRect_le_bottom :
    ∀ (rects : List Rect) (b : Bounds),
      b.bottom ≤ (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).bottom
  | [], b => Int.le_refl b.bottom
  | r :: rs, b => by
    simp only [List.foldl_cons]
    have h := foldl_stepRect_le_bottom rs ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩
    exact Int.le_trans (Int.le_max_left b.bottom (r.y + r.h)) h

theorem foldl_stepRect_minX_le_mem :
    ∀ (rects : List Rect) (b : Bounds) (r : Rect),
      r ∈ rects →
        (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).minX ≤ r.x
  | [], b, r, hr => by simp at hr
  | r0 :: rs, b, r, hr => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · have h := foldl_stepRect_minX_le rs ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩
      exact Int.le_trans h (Int.min_le_right b.minX r.x)
    · exact foldl_stepRect_minX_le_mem rs ⟨min b.minX r0.x, min b.minY r0.y, max b.right (r0.x + r0.w), max b.bottom (r0.y + r0.h)⟩ r hr'

theorem foldl_stepRect_minY_le_mem :
    ∀ (rects : List Rect) (b : Bounds) (r : Rect),
      r ∈ rects →
        (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).minY ≤ r.y
  | [], b, r, hr => by simp at hr
  | r0 :: rs, b, r, hr => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · have h := foldl_stepRect_minY_le rs ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩
      exact Int.le_trans h (Int.min_le_right b.minY r.y)
    · exact foldl_stepRect_minY_le_mem rs ⟨min b.minX r0.x, min b.minY r0.y, max b.right (r0.x + r0.w), max b.bottom (r0.y + r0.h)⟩ r hr'

theorem foldl_stepRect_right_ge_mem :
    ∀ (rects : List Rect) (b : Bounds) (r : Rect),
      r ∈ rects →
        r.x + r.w ≤ (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).right
  | [], b, r, hr => by simp at hr
  | r0 :: rs, b, r, hr => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · have h := foldl_stepRect_le_right rs ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩
      exact Int.le_trans (Int.le_max_right b.right (r.x + r.w)) h
    · exact foldl_stepRect_right_ge_mem rs ⟨min b.minX r0.x, min b.minY r0.y, max b.right (r0.x + r0.w), max b.bottom (r0.y + r0.h)⟩ r hr'

theorem foldl_stepRect_bottom_ge_mem :
    ∀ (rects : List Rect) (b : Bounds) (r : Rect),
      r ∈ rects →
        r.y + r.h ≤ (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).bottom
  | [], b, r, hr => by simp at hr
  | r0 :: rs, b, r, hr => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · have h := foldl_stepRect_le_bottom rs ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩
      exact Int.le_trans (Int.le_max_right b.bottom (r.y + r.h)) h
    · exact foldl_stepRect_bottom_ge_mem rs ⟨min b.minX r0.x, min b.minY r0.y, max b.right (r0.x + r0.w), max b.bottom (r0.y + r0.h)⟩ r hr'

theorem foldl_stepPoint_minX_le :
    ∀ (pts : List Point) (b : Bounds),
      (pts.foldl (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b).minX ≤ b.minX
  | [], b => Int.le_refl b.minX
  | p :: ps, b => by
    simp only [List.foldl_cons]
    have h := foldl_stepPoint_minX_le ps ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩
    exact Int.le_trans h (Int.min_le_left b.minX p.x)

theorem foldl_stepPoint_minY_le :
    ∀ (pts : List Point) (b : Bounds),
      (pts.foldl (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b).minY ≤ b.minY
  | [], b => Int.le_refl b.minY
  | p :: ps, b => by
    simp only [List.foldl_cons]
    have h := foldl_stepPoint_minY_le ps ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩
    exact Int.le_trans h (Int.min_le_left b.minY p.y)

theorem foldl_stepPoint_le_right :
    ∀ (pts : List Point) (b : Bounds),
      b.right ≤ (pts.foldl (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b).right
  | [], b => Int.le_refl b.right
  | p :: ps, b => by
    simp only [List.foldl_cons]
    have h := foldl_stepPoint_le_right ps ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩
    exact Int.le_trans (Int.le_max_left b.right p.x) h

theorem foldl_stepPoint_le_bottom :
    ∀ (pts : List Point) (b : Bounds),
      b.bottom ≤ (pts.foldl (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b).bottom
  | [], b => Int.le_refl b.bottom
  | p :: ps, b => by
    simp only [List.foldl_cons]
    have h := foldl_stepPoint_le_bottom ps ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩
    exact Int.le_trans (Int.le_max_left b.bottom p.y) h

theorem foldl_stepPoint_minX_le_mem :
    ∀ (pts : List Point) (b : Bounds) (p : Point),
      p ∈ pts →
        (pts.foldl (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b).minX ≤ p.x
  | [], b, p, hp => by simp at hp
  | p0 :: ps, b, p, hp => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · have h := foldl_stepPoint_minX_le ps ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩
      exact Int.le_trans h (Int.min_le_right b.minX p.x)
    · exact foldl_stepPoint_minX_le_mem ps ⟨min b.minX p0.x, min b.minY p0.y, max b.right p0.x, max b.bottom p0.y⟩ p hp'

theorem foldl_stepPoint_minY_le_mem :
    ∀ (pts : List Point) (b : Bounds) (p : Point),
      p ∈ pts →
        (pts.foldl (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b).minY ≤ p.y
  | [], b, p, hp => by simp at hp
  | p0 :: ps, b, p, hp => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · have h := foldl_stepPoint_minY_le ps ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩
      exact Int.le_trans h (Int.min_le_right b.minY p.y)
    · exact foldl_stepPoint_minY_le_mem ps ⟨min b.minX p0.x, min b.minY p0.y, max b.right p0.x, max b.bottom p0.y⟩ p hp'

theorem foldl_stepPoint_right_ge_mem :
    ∀ (pts : List Point) (b : Bounds) (p : Point),
      p ∈ pts →
        p.x ≤ (pts.foldl (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b).right
  | [], b, p, hp => by simp at hp
  | p0 :: ps, b, p, hp => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · have h := foldl_stepPoint_le_right ps ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩
      exact Int.le_trans (Int.le_max_right b.right p.x) h
    · exact foldl_stepPoint_right_ge_mem ps ⟨min b.minX p0.x, min b.minY p0.y, max b.right p0.x, max b.bottom p0.y⟩ p hp'

theorem foldl_stepPoint_bottom_ge_mem :
    ∀ (pts : List Point) (b : Bounds) (p : Point),
      p ∈ pts →
        p.y ≤ (pts.foldl (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b).bottom
  | [], b, p, hp => by simp at hp
  | p0 :: ps, b, p, hp => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · have h := foldl_stepPoint_le_bottom ps ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩
      exact Int.le_trans (Int.le_max_right b.bottom p.y) h
    · exact foldl_stepPoint_bottom_ge_mem ps ⟨min b.minX p0.x, min b.minY p0.y, max b.right p0.x, max b.bottom p0.y⟩ p hp'

theorem boundsOf_minX_le_rect_x (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) :
    (boundsOf rects pts).minX ≤ r.x := by
  unfold boundsOf
  dsimp only
  exact Int.le_trans (foldl_stepPoint_minX_le pts _) (foldl_stepRect_minX_le_mem rects _ r hr)

theorem boundsOf_minY_le_rect_y (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) :
    (boundsOf rects pts).minY ≤ r.y := by
  unfold boundsOf
  dsimp only
  exact Int.le_trans (foldl_stepPoint_minY_le pts _) (foldl_stepRect_minY_le_mem rects _ r hr)

theorem rect_right_le_boundsOf_right (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) :
    r.x + r.w ≤ (boundsOf rects pts).right := by
  unfold boundsOf
  dsimp only
  exact Int.le_trans (foldl_stepRect_right_ge_mem rects _ r hr) (foldl_stepPoint_le_right pts _)

theorem rect_bottom_le_boundsOf_bottom (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) :
    r.y + r.h ≤ (boundsOf rects pts).bottom := by
  unfold boundsOf
  dsimp only
  exact Int.le_trans (foldl_stepRect_bottom_ge_mem rects _ r hr) (foldl_stepPoint_le_bottom pts _)

theorem boundsOf_contains_rect (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) :
    (boundsOf rects pts).minX ≤ r.x ∧
    r.x + r.w ≤ (boundsOf rects pts).right ∧
    (boundsOf rects pts).minY ≤ r.y ∧
    r.y + r.h ≤ (boundsOf rects pts).bottom :=
  ⟨boundsOf_minX_le_rect_x rects pts r hr,
   rect_right_le_boundsOf_right rects pts r hr,
   boundsOf_minY_le_rect_y rects pts r hr,
   rect_bottom_le_boundsOf_bottom rects pts r hr⟩

theorem boundsOf_minX_le_point_x (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) :
    (boundsOf rects pts).minX ≤ p.x := by
  unfold boundsOf
  dsimp only
  exact foldl_stepPoint_minX_le_mem pts _ p hp

theorem point_x_le_boundsOf_right (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) :
    p.x ≤ (boundsOf rects pts).right := by
  unfold boundsOf
  dsimp only
  exact foldl_stepPoint_right_ge_mem pts _ p hp

theorem boundsOf_minY_le_point_y (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) :
    (boundsOf rects pts).minY ≤ p.y := by
  unfold boundsOf
  dsimp only
  exact foldl_stepPoint_minY_le_mem pts _ p hp

theorem point_y_le_boundsOf_bottom (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) :
    p.y ≤ (boundsOf rects pts).bottom := by
  unfold boundsOf
  dsimp only
  exact foldl_stepPoint_bottom_ge_mem pts _ p hp

theorem boundsOf_contains_point (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) :
    (boundsOf rects pts).minX ≤ p.x ∧
    p.x ≤ (boundsOf rects pts).right ∧
    (boundsOf rects pts).minY ≤ p.y ∧
    p.y ≤ (boundsOf rects pts).bottom :=
  ⟨boundsOf_minX_le_point_x rects pts p hp,
   point_x_le_boundsOf_right rects pts p hp,
   boundsOf_minY_le_point_y rects pts p hp,
   point_y_le_boundsOf_bottom rects pts p hp⟩

theorem boundsOf_minX_le_right_of_rect {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) (hw : 0 ≤ r.w) :
    (boundsOf rects pts).minX ≤ (boundsOf rects pts).right := by
  have h1 := boundsOf_minX_le_rect_x rects pts r hr
  have h2 := rect_right_le_boundsOf_right rects pts r hr
  omega

theorem boundsOf_minY_le_bottom_of_rect {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) (hh : 0 ≤ r.h) :
    (boundsOf rects pts).minY ≤ (boundsOf rects pts).bottom := by
  have h1 := boundsOf_minY_le_rect_y rects pts r hr
  have h2 := rect_bottom_le_boundsOf_bottom rects pts r hr
  omega

theorem boundsOf_minX_le_right_of_point {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) :
    (boundsOf rects pts).minX ≤ (boundsOf rects pts).right := by
  have h1 := boundsOf_minX_le_point_x rects pts p hp
  have h2 := point_x_le_boundsOf_right rects pts p hp
  omega

theorem boundsOf_minY_le_bottom_of_point {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) :
    (boundsOf rects pts).minY ≤ (boundsOf rects pts).bottom := by
  have h1 := boundsOf_minY_le_point_y rects pts p hp
  have h2 := point_y_le_boundsOf_bottom rects pts p hp
  omega

theorem boundsOf_nil_nil : boundsOf [] [] = ⟨0, 0, 0, 0⟩ :=
  rfl

theorem boundsOf_width_nonneg_of_rect {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) (hw : 0 ≤ r.w) :
    0 ≤ (boundsOf rects pts).right - (boundsOf rects pts).minX := by
  have := boundsOf_minX_le_right_of_rect (pts := pts) hr hw
  omega

theorem boundsOf_height_nonneg_of_rect {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) (hh : 0 ≤ r.h) :
    0 ≤ (boundsOf rects pts).bottom - (boundsOf rects pts).minY := by
  have := boundsOf_minY_le_bottom_of_rect (pts := pts) hr hh
  omega

theorem boundsOf_width_nonneg_of_point {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) :
    0 ≤ (boundsOf rects pts).right - (boundsOf rects pts).minX := by
  have := boundsOf_minX_le_right_of_point (rects := rects) hp
  omega

theorem boundsOf_height_nonneg_of_point {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) :
    0 ≤ (boundsOf rects pts).bottom - (boundsOf rects pts).minY := by
  have := boundsOf_minY_le_bottom_of_point (rects := rects) hp
  omega

theorem boundsOf_width_nonneg_of_empty :
    0 ≤ (boundsOf [] []).right - (boundsOf [] []).minX :=
  Int.le_refl _

theorem boundsOf_height_nonneg_of_empty :
    0 ≤ (boundsOf [] []).bottom - (boundsOf [] []).minY :=
  Int.le_refl _

theorem boundsOf_width_nonneg {rects : List Rect} {pts : List Point}
    (h : (∃ r ∈ rects, 0 ≤ r.w) ∨ pts ≠ [] ∨ (rects = [] ∧ pts = [])) :
    0 ≤ (boundsOf rects pts).right - (boundsOf rects pts).minX := by
  rcases h with ⟨r, hr, hw⟩ | hpts | ⟨rfl, rfl⟩
  · exact boundsOf_width_nonneg_of_rect hr hw
  · cases pts with
    | nil => contradiction
    | cons p ps => exact boundsOf_width_nonneg_of_point List.mem_cons_self
  · exact boundsOf_width_nonneg_of_empty

theorem boundsOf_height_nonneg {rects : List Rect} {pts : List Point}
    (h : (∃ r ∈ rects, 0 ≤ r.h) ∨ pts ≠ [] ∨ (rects = [] ∧ pts = [])) :
    0 ≤ (boundsOf rects pts).bottom - (boundsOf rects pts).minY := by
  rcases h with ⟨r, hr, hh⟩ | hpts | ⟨rfl, rfl⟩
  · exact boundsOf_height_nonneg_of_rect hr hh
  · cases pts with
    | nil => contradiction
    | cons p ps => exact boundsOf_height_nonneg_of_point List.mem_cons_self
  · exact boundsOf_height_nonneg_of_empty

theorem shiftRect_cursor_bounds (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) (cursor : Int) :
    cursor ≤ (shiftRect (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) r).x ∧
    (shiftRect (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) r).x +
        (shiftRect (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) r).w ≤
      cursor + ((boundsOf rects pts).right - (boundsOf rects pts).minX) ∧
    0 ≤ (shiftRect (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) r).y ∧
    (shiftRect (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) r).y +
        (shiftRect (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) r).h ≤
      (boundsOf rects pts).bottom - (boundsOf rects pts).minY := by
  have hx := boundsOf_minX_le_rect_x rects pts r hr
  have hrw := rect_right_le_boundsOf_right rects pts r hr
  have hy := boundsOf_minY_le_rect_y rects pts r hr
  have hrh := rect_bottom_le_boundsOf_bottom rects pts r hr
  dsimp only [shiftRect]
  omega

theorem shiftPoint_cursor_bounds (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) (cursor : Int) :
    cursor ≤ (shiftPoint (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) p).x ∧
    (shiftPoint (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) p).x ≤
      cursor + ((boundsOf rects pts).right - (boundsOf rects pts).minX) ∧
    0 ≤ (shiftPoint (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) p).y ∧
    (shiftPoint (cursor - (boundsOf rects pts).minX) (0 - (boundsOf rects pts).minY) p).y ≤
      (boundsOf rects pts).bottom - (boundsOf rects pts).minY := by
  have hx := boundsOf_minX_le_point_x rects pts p hp
  have hxr := point_x_le_boundsOf_right rects pts p hp
  have hy := boundsOf_minY_le_point_y rects pts p hp
  have hyb := point_y_le_boundsOf_bottom rects pts p hp
  dsimp only [shiftPoint]
  omega

theorem shiftRect_origin_bounds (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) :
    0 ≤ (shiftRect (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) r).x ∧
    (shiftRect (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) r).x +
        (shiftRect (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) r).w ≤
      (boundsOf rects pts).right - (boundsOf rects pts).minX ∧
    0 ≤ (shiftRect (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) r).y ∧
    (shiftRect (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) r).y +
        (shiftRect (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) r).h ≤
      (boundsOf rects pts).bottom - (boundsOf rects pts).minY := by
  have hx := boundsOf_minX_le_rect_x rects pts r hr
  have hrw := rect_right_le_boundsOf_right rects pts r hr
  have hy := boundsOf_minY_le_rect_y rects pts r hr
  have hrh := rect_bottom_le_boundsOf_bottom rects pts r hr
  dsimp only [shiftRect]
  omega

theorem shiftPoint_origin_bounds (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) :
    0 ≤ (shiftPoint (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) p).x ∧
    (shiftPoint (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) p).x ≤
      (boundsOf rects pts).right - (boundsOf rects pts).minX ∧
    0 ≤ (shiftPoint (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) p).y ∧
    (shiftPoint (-(boundsOf rects pts).minX) (-(boundsOf rects pts).minY) p).y ≤
      (boundsOf rects pts).bottom - (boundsOf rects pts).minY := by
  have hx := boundsOf_minX_le_point_x rects pts p hp
  have hxr := point_x_le_boundsOf_right rects pts p hp
  have hy := boundsOf_minY_le_point_y rects pts p hp
  have hyb := point_y_le_boundsOf_bottom rects pts p hp
  dsimp only [shiftPoint]
  omega

theorem placeComponent_rects_bounds (P : Params) (cg : Graph) (run : Run) (cursor : Int)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    ∀ r' ∈ (placeComponent P cg run cursor labels loops).rects,
      cursor ≤ r'.x ∧
      r'.x + r'.w ≤ cursor + (placeComponent P cg run cursor labels loops).width ∧
      0 ≤ r'.y ∧
      r'.y + r'.h ≤ (placeComponent P cg run cursor labels loops).height := by
  intro r' hr'
  unfold placeComponent at hr' ⊢
  dsimp only at hr' ⊢
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  have hmem : r ∈ ((List.range cg.nodes.length).map (frameRect P cg run) ++
      ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
        ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
      labelBounds P cg run labels ++
      (componentTitles P cg run).map (·.2)) :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))
  exact shiftRect_cursor_bounds _ _ r hmem cursor

theorem placeComponent_titles_bounds (P : Params) (cg : Graph) (run : Run) (cursor : Int)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    ∀ t' ∈ (placeComponent P cg run cursor labels loops).titles,
      cursor ≤ t'.2.x ∧
      t'.2.x + t'.2.w ≤ cursor + (placeComponent P cg run cursor labels loops).width ∧
      0 ≤ t'.2.y ∧
      t'.2.y + t'.2.h ≤ (placeComponent P cg run cursor labels loops).height := by
  intro t' ht'
  unfold placeComponent at ht' ⊢
  dsimp only at ht' ⊢
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht'
  dsimp only
  have hmem : q.2 ∈ ((List.range cg.nodes.length).map (frameRect P cg run) ++
      ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
        ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
      labelBounds P cg run labels ++
      (componentTitles P cg run).map (·.2)) :=
    List.mem_append_right _ (List.mem_map_of_mem hq)
  exact shiftRect_cursor_bounds _ _ q.2 hmem cursor

theorem placeComponent_rects_bounds_zero (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    ∀ r' ∈ (placeComponent P cg run 0 labels loops).rects,
      0 ≤ r'.x ∧
      r'.x + r'.w ≤ (placeComponent P cg run 0 labels loops).width ∧
      0 ≤ r'.y ∧
      r'.y + r'.h ≤ (placeComponent P cg run 0 labels loops).height := by
  intro r' hr'
  have h := placeComponent_rects_bounds P cg run 0 labels loops r' hr'
  omega

theorem placeComponent_titles_bounds_zero (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    ∀ t' ∈ (placeComponent P cg run 0 labels loops).titles,
      0 ≤ t'.2.x ∧
      t'.2.x + t'.2.w ≤ (placeComponent P cg run 0 labels loops).width ∧
      0 ≤ t'.2.y ∧
      t'.2.y + t'.2.h ≤ (placeComponent P cg run 0 labels loops).height := by
  intro t' ht'
  have h := placeComponent_titles_bounds P cg run 0 labels loops t' ht'
  omega

theorem placeComponent_shifted_point_bounds (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (p : Point)
    (hp : p ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) :
    cursor ≤ (shiftPoint (cursor - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
      (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).x ∧
    (shiftPoint (cursor - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
      (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).x ≤
      cursor + (placeComponent P cg run cursor labels loops).width ∧
    0 ≤ (shiftPoint (cursor - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
      (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).y ∧
    (shiftPoint (cursor - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
      (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).y ≤
      (placeComponent P cg run cursor labels loops).height := by
  have h := shiftPoint_cursor_bounds ((List.range cg.nodes.length).map (frameRect P cg run) ++
      ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
        ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
      labelBounds P cg run labels ++
      (componentTitles P cg run).map (·.2))
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) p hp cursor
  unfold placeComponent
  dsimp only
  exact h

theorem placeComponent_shifted_point_bounds_zero (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (p : Point)
    (hp : p ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) :
    0 ≤ (shiftPoint (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
      (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).x ∧
    (shiftPoint (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
      (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).x ≤
      (placeComponent P cg run 0 labels loops).width ∧
    0 ≤ (shiftPoint (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
      (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).y ∧
    (shiftPoint (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
      (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
            ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
          labelBounds P cg run labels ++
          (componentTitles P cg run).map (·.2))
        (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).y ≤
      (placeComponent P cg run 0 labels loops).height := by
  have h := placeComponent_shifted_point_bounds P cg run 0 labels loops p hp
  omega

theorem placeComponent_width_nonneg_of_nodeIdx (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (v : Nat) (hv : v < cg.nodes.length) (hw : 0 ≤ (frameRect P cg run v).w) :
    0 ≤ (placeComponent P cg run cursor labels loops).width := by
  unfold placeComponent
  dsimp only
  have h0 : v ∈ List.range cg.nodes.length := List.mem_range.mpr hv
  have hr : frameRect P cg run v ∈ (List.range cg.nodes.length).map (frameRect P cg run) :=
    List.mem_map_of_mem h0
  have hmem : frameRect P cg run v ∈ ((List.range cg.nodes.length).map (frameRect P cg run) ++
      ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
        ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
      labelBounds P cg run labels ++
      (componentTitles P cg run).map (·.2)) :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))
  exact boundsOf_width_nonneg_of_rect hmem hw

theorem placeComponent_height_nonneg_of_nodeIdx (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (v : Nat) (hv : v < cg.nodes.length) (hh : 0 ≤ (frameRect P cg run v).h) :
    0 ≤ (placeComponent P cg run cursor labels loops).height := by
  unfold placeComponent
  dsimp only
  have h0 : v ∈ List.range cg.nodes.length := List.mem_range.mpr hv
  have hr : frameRect P cg run v ∈ (List.range cg.nodes.length).map (frameRect P cg run) :=
    List.mem_map_of_mem h0
  have hmem : frameRect P cg run v ∈ ((List.range cg.nodes.length).map (frameRect P cg run) ++
      ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
        ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
      labelBounds P cg run labels ++
      (componentTitles P cg run).map (·.2)) :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))
  exact boundsOf_height_nonneg_of_rect hmem hh

theorem placeComponent_width_nonneg_of_node (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (hn : 0 < cg.nodes.length) (hw : 0 ≤ (frameRect P cg run 0).w) :
    0 ≤ (placeComponent P cg run cursor labels loops).width :=
  placeComponent_width_nonneg_of_nodeIdx P cg run cursor labels loops 0 hn hw

theorem placeComponent_height_nonneg_of_node (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (hn : 0 < cg.nodes.length) (hh : 0 ≤ (frameRect P cg run 0).h) :
    0 ≤ (placeComponent P cg run cursor labels loops).height :=
  placeComponent_height_nonneg_of_nodeIdx P cg run cursor labels loops 0 hn hh

theorem placeComponent_width_nonneg_of_point (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (p : Point)
    (hp : p ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) :
    0 ≤ (placeComponent P cg run cursor labels loops).width := by
  unfold placeComponent
  dsimp only
  exact boundsOf_width_nonneg_of_point hp

theorem placeComponent_height_nonneg_of_point (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (p : Point)
    (hp : p ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) :
    0 ≤ (placeComponent P cg run cursor labels loops).height := by
  unfold placeComponent
  dsimp only
  exact boundsOf_height_nonneg_of_point hp

/-! ### Producer identity bridge

`componentRun` produces `run.routes` through `RouteImpl.routePointsWithLanes`, which maps
`RouteImpl.laneRouteOf` over `List.range run.proper.chains.length`. The theorems below
derive the positional identity of that produced list from the producer expression itself:
its length, the route at each covered position together with its original index, the
`edgePoints` positional lookup without the default, and the decl-keyed `placeComponent`
route entry that consumes the produced points. Coverage of every `cg.edges` index
(`i < cg.edges.length → i < run.proper.chains.length`) is derived by `componentRun_proper_chains_length`
via `normalize_chains_length`. -/

theorem zipIdx_getElem? {α : Type} :
    ∀ (l : List α) (k i : Nat), (l.zipIdx k)[i]? = (l[i]?).map (fun a => (a, k + i))
  | [], _, _ => rfl
  | _ :: _, _, 0 => rfl
  | _ :: _, k, i + 1 => by
    rw [List.zipIdx_cons, List.getElem?_cons_succ]
    simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using
      zipIdx_getElem? _ (k + 1) i

theorem loops_find?_none_of_ne {loops : List (Nat × LoopPlacement)} {d : Nat}
    (h : ∀ l ∈ loops, l.1 ≠ d) :
    loops.find? (fun l => l.1 == d) = none := by
  cases hl : loops.find? (fun l => l.1 == d) with
  | none => rfl
  | some l =>
    have hmem : l ∈ loops := List.mem_of_find?_eq_some hl
    have hval : l.1 = d := by simpa using List.find?_some hl
    exact absurd hval (h l hmem)

/-- The placement bounds of `placeComponent`, named so that route-entry statements stay
readable. This is exactly the `boundsOf` argument that `placeComponent` itself builds. -/
def placeBounds (P : Params) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) : Bounds :=
  boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
      ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
        ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩) ++
      labelBounds P cg run labels ++
      (componentTitles P cg run).map (·.2))
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))

theorem proxyWidths_chains {p q : Proper} {xs xs' : List Int}
    (h : proxyWidths p xs = .ok (q, xs')) : q.chains = p.chains := by
  unfold proxyWidths at h
  obtain ⟨updated, _, h⟩ := bind_ok h
  have h := Except.ok.inj h
  injection h with hq _
  have hq' : q = { p with nodes := updated.map (·.1) } := hq.symm
  rw [hq']

theorem coordinateGraph_chains (P : Params) (p : Proper) :
    (coordinateGraph P p).chains = p.chains := by
  unfold coordinateGraph materializeDummyPaths clearProxyExtents
  exact (OrderImpl.addClusterBorders_metadata (titleReservations (sizeProperPorts P p)) P.clusterBorderW).2.1

theorem componentRun_proper_chains_length {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    run.proper.chains.length = cg.edges.length := by
  obtain ⟨ranks, p0, labeled, q0, hn, hlabels, hproper, _, _, hprox, hdrop, _⟩ :=
    componentRun_spec h
  have hdropC : run.proper.chains = q0.chains := by
    rw [← hdrop, OrderImpl.dropSynthetic_chains]
  have hproxC : q0.chains = run.coordinateProper.chains := proxyWidths_chains hprox
  have hcoordC : run.coordinateProper.chains = labeled.chains := by
    rw [← hproper]
    exact coordinateGraph_chains P labeled
  obtain ⟨_, _, hlblC, _⟩ := Labels.addLabelNodes_metadata hlabels
  have hnorm : p0.chains.length = cg.edges.length := normalize_chains_length hn
  rw [hdropC, hproxC, hcoordC, hlblC, hnorm]

theorem componentRun_routes_length {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    run.routes.length = run.proper.chains.length := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hroutes⟩ := componentRun_spec h
  unfold RouteImpl.routePointsWithLanes at hroutes
  split at hroutes
  · simp at hroutes
  · simpa using RouteImpl.mapOk_length _ _ _ hroutes

theorem componentRun_route_of_index {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) {i : Nat}
    (hi : i < cg.edges.length) :
    ∃ rt : EdgeRoute, run.routes[i]? = some rt ∧ rt.original = i ∧
      RouteImpl.laneRouteOf P.slot run.proper run.ys run.top
        (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes i = .ok rt := by
  have hcov : i < run.proper.chains.length := by
    rw [componentRun_proper_chains_length h]
    exact hi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hroutes⟩ := componentRun_spec h
  unfold RouteImpl.routePointsWithLanes at hroutes
  split at hroutes
  · simp at hroutes
  · have hrange : i < (List.range run.proper.chains.length).length := by
      simpa only [List.length_range] using hcov
    obtain ⟨rt, hget, hok⟩ := RouteImpl.mapOk_getElem _ _ _ hroutes i hrange
    have hri : (List.range run.proper.chains.length)[i] = i := by simp
    rw [hri] at hok
    exact ⟨rt, hget, RouteImpl.laneRouteOf_original hok, hok⟩

theorem componentRun_edgePoints_of_index {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {e : Edge}
    (h : componentRun P cg labels orderOptions = .ok run) {i : Nat}
    (hi : i < cg.edges.length) :
    edgePoints run i e = (run.routes[i]'(by
      rw [componentRun_routes_length h, componentRun_proper_chains_length h]
      exact hi)).points := by
  obtain ⟨rt, hget, _, _⟩ := componentRun_route_of_index h hi
  have hir : i < run.routes.length := (List.getElem?_eq_some_iff.mp hget).1
  have hrt : run.routes[i]'hir = rt := (List.getElem?_eq_some_iff.mp hget).2
  simp only [edgePoints, List.getD_eq_getElem?_getD, hget, Option.getD_some, hrt]

theorem placeComponent_route_key_decl (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (i : Nat) (hi : i < cg.edges.length) :
    ((placeComponent P cg run cursor labels loops).routes[i]?).map (·.1) =
      some (cg.edges[i]).decl := by
  unfold placeComponent
  dsimp only
  simp only [List.getElem?_map, zipIdx_getElem?, List.getElem?_eq_getElem hi,
    Option.map_some]

theorem placeComponent_route_points_of_noLoop (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (i : Nat) (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl) :
    ((placeComponent P cg run cursor labels loops).routes[i]?).map (·.2) =
      some ((edgePoints run i (cg.edges[i])).map
        (shiftPoint (cursor - (placeBounds P cg run labels loops).minX)
          (0 - (placeBounds P cg run labels loops).minY))) := by
  have hfind := loops_find?_none_of_ne hloop
  unfold placeComponent placeBounds
  dsimp only
  simp only [List.getElem?_map, zipIdx_getElem?, List.getElem?_eq_getElem hi,
    Option.map_some, hfind, Option.map_none, Option.getD_none, Nat.zero_add]

theorem placeComponent_route_entry_of_producer {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    (cursor : Int) (loops : List (Nat × LoopPlacement)) (i : Nat)
    (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl) :
    (placeComponent P cg run cursor labels loops).routes[i]? =
      some ((cg.edges[i]).decl,
        (run.routes[i]'(by
          rw [componentRun_routes_length h, componentRun_proper_chains_length h]
          exact hi)).points.map
          (shiftPoint (cursor - (placeBounds P cg run labels loops).minX)
            (0 - (placeBounds P cg run labels loops).minY))) := by
  have hk := placeComponent_route_key_decl P cg run cursor labels loops i hi
  have hp := placeComponent_route_points_of_noLoop P cg run cursor labels loops i hi hloop
  cases hri : (placeComponent P cg run cursor labels loops).routes[i]? with
  | none => rw [hri] at hk; simp at hk
  | some entry =>
    obtain ⟨k, pts⟩ := entry
    have hk' : k = (cg.edges[i]).decl := by
      simpa only [hri, Option.map_some, Option.some.injEq] using hk
    have hp' : pts = (edgePoints run i (cg.edges[i])).map
        (shiftPoint (cursor - (placeBounds P cg run labels loops).minX)
          (0 - (placeBounds P cg run labels loops).minY)) := by
      simpa only [hri, Option.map_some, Option.some.injEq] using hp
    rw [hk', hp', componentRun_edgePoints_of_index h hi]

theorem mem_range'_lt : ∀ {k n x : Nat}, x ∈ List.range' k n → x < k + n
  | _, 0, _, h => by simp at h
  | k, n + 1, x, h => by
    rw [List.range'_succ] at h
    rcases List.mem_cons.mp h with rfl | hm
    · omega
    · have := mem_range'_lt hm
      omega

theorem graphEdges_edge_decl_lt {inp : Input} {es : List Edge}
    (h : graphEdges inp = .ok es) {e : Edge} (he : e ∈ es) :
    e.decl < inp.routes.length := by
  unfold graphEdges at h
  have hd := graphEdgesFrom_decls inp inp.routes 0 es h
  have hmem : e.decl ∈ es.map (·.decl) := List.mem_map_of_mem he
  rw [hd] at hmem
  have hlt := mem_range'_lt hmem
  omega

theorem measuredGraph_edge_decl_lt {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (h : measuredGraph P inp o lines = .ok g0) {e : Edge} (he : e ∈ g0.edges) :
    e.decl < inp.routes.length := by
  unfold measuredGraph at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨edges, he_edges, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  unfold Compound.prepare at he
  dsimp only at he
  obtain ⟨orig, horig, rfl⟩ := List.mem_map.mp he
  rw [Compound.aliasEdge_decl]
  exact graphEdges_edge_decl_lt he_edges horig

theorem componentGraph_edge_decl_lt (g : Graph) (comp : List Nat) {N : Nat}
    (hlt : ∀ e ∈ g.edges, e.decl < N) {e : Edge}
    (he : e ∈ (componentGraph g comp).edges) : e.decl < N := by
  unfold componentGraph at he
  dsimp only at he
  obtain ⟨orig, horig, rfl⟩ := List.mem_map.mp he
  simp only [List.mem_filter] at horig
  exact hlt orig horig.1

theorem componentCandidate_edge_decl_lt (g : Graph) (comp : List Nat) (index : Nat) {N : Nat}
    (hlt : ∀ e ∈ g.edges, e.decl < N) {e : Edge}
    (he : e ∈ (componentCandidate g comp index).edges) : e.decl < N := by
  have hd : (componentCandidate g comp index).edges.map (·.decl) =
      (componentGraph g comp).edges.map (·.decl) :=
    componentCandidate_decls g comp index
  have hmem : e.decl ∈ (componentCandidate g comp index).edges.map (·.decl) :=
    List.mem_map_of_mem he
  rw [hd] at hmem
  obtain ⟨e', he', he_decl⟩ := List.mem_map.mp hmem
  rw [← he_decl]
  exact componentGraph_edge_decl_lt g comp hlt he'

theorem componentCandidate_edge_index_decl_lt {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (hg0 : measuredGraph P inp o lines = .ok g0)
    (comp : List Nat) (index : Nat) {i : Nat}
    (hi : i < (componentCandidate g0 comp index).edges.length) :
    ((componentCandidate g0 comp index).edges[i]).decl < inp.routes.length := by
  have he : (componentCandidate g0 comp index).edges[i] ∈ (componentCandidate g0 comp index).edges :=
    List.getElem_mem hi
  exact componentCandidate_edge_decl_lt g0 comp index (fun e he => measuredGraph_edge_decl_lt hg0 he) he

theorem routes_foldl_size {α β : Type} (f : β → α) (entries : List (Nat × β)) (a : Array α) :
    (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a).size = a.size := by
  induction entries generalizing a with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih (a.set! q.1 (f q.2))]
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem routes_foldl_getD_ne {α β : Type} (f : β → α) (entries : List (Nat × β)) (a : Array α)
    (k : Nat) (d : α) (hk : k ∉ entries.map (·.1)) :
    (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a).getD k d = a.getD k d := by
  induction entries generalizing a with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    have hne : k ≠ q.1 := by
      intro h
      subst h
      exact hk List.mem_cons_self
    have hrest : k ∉ rest.map (·.1) := by
      intro h
      exact hk (List.mem_cons_of_mem _ h)
    rw [ih (a.set! q.1 (f q.2)) hrest]
    rw [RankImpl.getD_set!]
    have hcond : ¬ (q.1 = k ∧ q.1 < a.size) := fun h => hne h.1.symm
    simp only [hcond, ite_false]

theorem routes_foldl_getD_mem {α β : Type} (f : β → α) (entries : List (Nat × β)) (a : Array α)
    (i : Nat) (k : Nat) (v : β) (d : α)
    (hget : entries[i]? = some (k, v))
    (hnodup : (entries.map (·.1)).Nodup)
    (hsize : k < a.size) :
    (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a).getD k d = f v := by
  induction entries generalizing a i with
  | nil => simp at hget
  | cons q rest ih =>
    simp only [List.foldl_cons]
    simp only [List.map_cons, List.nodup_cons] at hnodup
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      have hnot : k ∉ rest.map (·.1) := hnodup.1
      rw [routes_foldl_getD_ne f rest (a.set! k (f v)) k d hnot]
      rw [RankImpl.getD_set!]
      simp [hsize]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      have hsize' : k < (a.set! q.1 (f q.2)).size := by
        rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact hsize
      exact ih (a.set! q.1 (f q.2)) j hget hnodup.2 hsize'

theorem placeComponent_routes_length (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run cursor labels loops).routes.length = cg.edges.length := by
  unfold placeComponent
  dsimp only
  simp only [List.length_map, List.length_zipIdx]

theorem placeComponent_routes_decls (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run cursor labels loops).routes.map (·.1) = cg.edges.map (·.decl) := by
  unfold placeComponent
  dsimp only
  rw [List.map_map]
  exact zipIdx_map_comp (·.decl) cg.edges 0

theorem placeComponent_routes_decls_nodup (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (hnd : (cg.edges.map (·.decl)).Nodup) :
    ((placeComponent P cg run cursor labels loops).routes.map (·.1)).Nodup := by
  rw [placeComponent_routes_decls]
  exact hnd

theorem placePart_routes_size {comp : List Nat} {cg : Graph} {run : Run}
    {P : Params} {acc res : Acc} {labels : List MeasuredLabel}
    (hplace : placePart comp cg run P acc labels = .ok res) :
    res.routes.size = acc.routes.size := by
  unfold placePart at hplace
  dsimp only at hplace
  obtain ⟨loops, _, hplace⟩ := bind_ok hplace
  split at hplace
  · simp at hplace
  · have hres := Except.ok.inj hplace
    subst hres
    dsimp only
    exact routes_foldl_size id _ acc.routes

theorem placePart_routes_getD {comp : List Nat} {cg : Graph} {run : Run}
    {P : Params} {acc res : Acc} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)}
    (hplace : placePart comp cg run P acc labels = .ok res)
    (hloops : componentLoops P cg run labels = .ok loops)
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget : (placeComponent P cg run 0 labels loops).routes[i]? = some (k, pts))
    (hnd : (cg.edges.map (·.decl)).Nodup)
    (hsize : k < acc.routes.size) :
    res.routes.getD k d = pts := by
  unfold placePart at hplace
  dsimp only at hplace
  obtain ⟨loops', hl', hplace⟩ := bind_ok hplace
  have heq_loops : loops' = loops := by
    rw [hloops] at hl'
    exact (Except.ok.inj hl').symm
  subst loops'
  split at hplace
  · simp at hplace
  · have hres := Except.ok.inj hplace
    subst hres
    dsimp only
    have hnd_routes := placeComponent_routes_decls_nodup P cg run 0 labels loops hnd
    have hget_id : (placeComponent P cg run 0 labels loops).routes[i]? = some (k, id pts) := hget
    exact routes_foldl_getD_mem id (placeComponent P cg run 0 labels loops).routes acc.routes i k pts d hget_id hnd_routes hsize

theorem placePart_route_points_of_producer {comp : List Nat} {cg : Graph} {run : Run}
    {P : Params} {acc res : Acc} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {loops : List (Nat × LoopPlacement)}
    (hplace : placePart comp cg run P acc labels = .ok res)
    (hloops : componentLoops P cg run labels = .ok loops)
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hnd : (cg.edges.map (·.decl)).Nodup)
    {i : Nat} (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (hsize : (cg.edges[i]).decl < acc.routes.size)
    (d : List Point) :
    res.routes.getD (cg.edges[i]).decl d =
      (run.routes[i]'(by
        rw [componentRun_routes_length hrun, componentRun_proper_chains_length hrun]
        exact hi)).points.map
        (shiftPoint (0 - (placeBounds P cg run labels loops).minX)
          (0 - (placeBounds P cg run labels loops).minY)) := by
  have hget := placeComponent_route_entry_of_producer hrun 0 loops i hi hloop
  exact placePart_routes_getD hplace hloops i (cg.edges[i]).decl _ d hget hnd hsize

theorem packAcc_routes_eq_foldl (pairs : List ((List Nat × Part) × Rect)) (init : Acc) :
    (pairs.foldl (fun out q =>
      let comp := q.1.1
      let part := q.1.2
      let dx := q.2.x
      let dy := q.2.y
      { out with
        rects := (comp.zip part.rects).foldl
          (fun a r => if r.1 < a.size then a.set! r.1 (shiftRect dx dy r.2) else a) out.rects
        routes := part.routes.foldl
          (fun a r => a.set! r.1 (r.2.map (shiftPoint dx dy))) out.routes
        labels := part.labels.foldl
          (fun a r => a.set! r.1 (shiftRect dx dy r.2)) out.labels
        titles := out.titles ++ part.titles.map
          (fun r => (comp.getD r.1 0, shiftRect dx dy r.2)) }) init).routes =
    pairs.foldl (fun arr q => q.1.2.routes.foldl
      (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) arr) init.routes := by
  induction pairs generalizing init with
  | nil => rfl
  | cons q pairs ih =>
    simp only [List.foldl_cons]
    rw [ih]

theorem packRoutes_foldl_size (pairs : List ((List Nat × Part) × Rect)) (arr : Array (List Point)) :
    (pairs.foldl (fun arr q => q.1.2.routes.foldl
      (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) arr) arr).size = arr.size := by
  induction pairs generalizing arr with
  | nil => rfl
  | cons q pairs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact routes_foldl_size (fun r2 => r2.map (shiftPoint q.2.x q.2.y)) q.1.2.routes arr

theorem packRoutes_foldl_getD_ne (pairs : List ((List Nat × Part) × Rect)) (arr : Array (List Point))
    (k : Nat) (d : List Point)
    (hnot : ∀ q ∈ pairs, k ∉ q.1.2.routes.map (·.1)) :
    (pairs.foldl (fun arr q => q.1.2.routes.foldl
      (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) arr) arr).getD k d = arr.getD k d := by
  induction pairs generalizing arr with
  | nil => rfl
  | cons q pairs ih =>
    simp only [List.foldl_cons]
    have hq_not : k ∉ q.1.2.routes.map (·.1) := hnot q List.mem_cons_self
    have hrest_not : ∀ q' ∈ pairs, k ∉ q'.1.2.routes.map (·.1) :=
      fun q' hq' => hnot q' (List.mem_cons_of_mem _ hq')
    rw [ih _ hrest_not]
    exact routes_foldl_getD_ne (fun r2 => r2.map (shiftPoint q.2.x q.2.y)) q.1.2.routes arr k d hq_not

theorem packRoutes_foldl_getD_mem (pairs : List ((List Nat × Part) × Rect)) (arr : Array (List Point))
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hget_pair : pairs[c]? = some q)
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget_route : q.1.2.routes[i]? = some (k, pts))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    (hsize : k < arr.size)
    (hnot_after : ∀ q' ∈ pairs.drop (c + 1), k ∉ q'.1.2.routes.map (·.1)) :
    (pairs.foldl (fun arr q => q.1.2.routes.foldl
      (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) arr) arr).getD k d =
      pts.map (shiftPoint q.2.x q.2.y) := by
  induction pairs generalizing arr c with
  | nil => simp at hget_pair
  | cons p rest ih =>
    simp only [List.foldl_cons]
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget_pair
      subst p
      simp only [List.drop_succ_cons, List.drop_zero] at hnot_after
      rw [packRoutes_foldl_getD_ne rest _ k d hnot_after]
      exact routes_foldl_getD_mem (fun r2 => r2.map (shiftPoint q.2.x q.2.y))
        q.1.2.routes arr i k pts d hget_route hnodup hsize
    | succ c' =>
      simp only [List.getElem?_cons_succ] at hget_pair
      simp only [List.drop_succ_cons] at hnot_after
      have hsize' : k < (p.1.2.routes.foldl (fun a r => a.set! r.1 (r.2.map (shiftPoint p.2.x p.2.y))) arr).size := by
        rw [routes_foldl_size]
        exact hsize
      exact ih _ c' hget_pair hsize' hnot_after

theorem packAcc_routes_size {P : Params} {o : Options} {acc out : Acc}
    (hpack : packAcc P o acc = .ok out) :
    out.routes.size = acc.routes.size := by
  unfold packAcc at hpack
  obtain ⟨packed, _, hpack⟩ := bind_ok hpack
  have h := Except.ok.inj hpack
  subst h
  rw [packAcc_routes_eq_foldl]
  dsimp only
  exact packRoutes_foldl_size _ _

theorem packAcc_routes_getD {P : Params} {o : Options} {acc out : Acc}
    (hpack : packAcc P o acc = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (acc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hget_pair : (acc.parts.zip packed.boxes)[c]? = some q)
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget_route : q.1.2.routes[i]? = some (k, pts))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    (hsize : k < acc.routes.size)
    (hnot_after : ∀ q' ∈ (acc.parts.zip packed.boxes).drop (c + 1), k ∉ q'.1.2.routes.map (·.1)) :
    out.routes.getD k d = pts.map (shiftPoint q.2.x q.2.y) := by
  unfold packAcc at hpack
  obtain ⟨packed', hp', hpack⟩ := bind_ok hpack
  have heq : packed' = packed := by
    rw [hpacked] at hp'
    exact (Except.ok.inj hp').symm
  subst packed'
  have h := Except.ok.inj hpack
  subst h
  rw [packAcc_routes_eq_foldl]
  dsimp only
  exact packRoutes_foldl_getD_mem (acc.parts.zip packed.boxes) acc.routes c q hget_pair i k pts d hget_route hnodup hsize hnot_after

theorem packAcc_routes_getD_single {P : Params} {o : Options} {acc out : Acc}
    (hpack : packAcc P o acc = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (acc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (q : (List Nat × Part) × Rect)
    (hpairs : acc.parts.zip packed.boxes = [q])
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget_route : q.1.2.routes[i]? = some (k, pts))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    (hsize : k < acc.routes.size) :
    out.routes.getD k d = pts.map (shiftPoint q.2.x q.2.y) := by
  have hget : (acc.parts.zip packed.boxes)[0]? = some q := by rw [hpairs]; rfl
  have hnot : ∀ q' ∈ (acc.parts.zip packed.boxes).drop 1, k ∉ q'.1.2.routes.map (·.1) := by
    rw [hpairs]
    intro q' hq'
    simp at hq'
  exact packAcc_routes_getD hpack packed hpacked 0 q hget i k pts d hget_route hnodup hsize hnot

def routePointTransport (margin : Int) (d : Direction) (h : Int) (boxX boxY minX minY : Int) (p : Point) : Point :=
  shiftPoint margin margin (orientPoint d h (shiftPoint (boxX - minX) (boxY - minY) p))

theorem routePointTransport_eq (margin : Int) (d : Direction) (h : Int) (boxX boxY minX minY : Int) (pts : List Point) :
    ((pts.map (shiftPoint (0 - minX) (0 - minY))).map (shiftPoint boxX boxY)).map
      (fun p => shiftPoint margin margin (orientPoint d h p)) =
    pts.map (routePointTransport margin d h boxX boxY minX minY) := by
  simp only [List.map_map]
  congr 1
  funext p
  have hs : shiftPoint boxX boxY (shiftPoint (0 - minX) (0 - minY) p) =
      shiftPoint (boxX - minX) (boxY - minY) p := by
    cases p
    simp only [shiftPoint, Point.mk.injEq]
    constructor <;> omega
  exact congrArg (fun q => shiftPoint margin margin (orientPoint d h q)) hs

theorem sceneOf_routes_length (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel) :
    (sceneOf P inp o lines acc measured).routes.length = inp.routes.length := by
  unfold sceneOf
  dsimp only
  simp only [List.length_map, List.length_zipIdx]

theorem sceneOf_routes_getElem? (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (k : Nat) (hk : k < inp.routes.length) :
    (sceneOf P inp o lines acc measured).routes[k]? =
      some ⟨(inp.routes[k]).id, (inp.routes[k]).fromId, (inp.routes[k]).toId, (inp.routes[k]).orthogonal,
        (acc.routes.getD k []).map (fun p =>
          shiftPoint P.canvasMargin
            P.canvasMargin
            (orientPoint o.direction acc.canvasH p))⟩ := by
  unfold sceneOf
  dsimp only
  simp only [List.getElem?_map, zipIdx_getElem?, List.getElem?_eq_getElem hk,
    Option.map_some, Nat.zero_add]

theorem sceneOf_route_id (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (k : Nat) (hk : k < inp.routes.length) :
    ((sceneOf P inp o lines acc measured).routes[k]?).map (·.id) =
      some (inp.routes[k]).id := by
  rw [sceneOf_routes_getElem? P inp o lines acc measured k hk]
  rfl

theorem sceneOf_route_points (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (k : Nat) (hk : k < inp.routes.length) :
    ((sceneOf P inp o lines acc measured).routes[k]?).map (·.points) =
      some ((acc.routes.getD k []).map (fun p =>
        shiftPoint P.canvasMargin
          P.canvasMargin
          (orientPoint o.direction acc.canvasH p))) := by
  rw [sceneOf_routes_getElem? P inp o lines acc measured k hk]
  rfl

theorem sceneOf_routes_ids (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel) :
    (sceneOf P inp o lines acc measured).routes.map (·.id) = inp.routes.map (·.id) := by
  unfold sceneOf
  dsimp only
  rw [List.map_map]
  exact zipIdx_map_comp (·.id) inp.routes 0

theorem sceneOf_route_of_pack (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (out : Acc) (measured : List MeasuredLabel)
    (k : Nat) (hk : k < inp.routes.length)
    (pts : List Point)
    (hroutes : out.routes.getD k [] = pts) :
    (sceneOf P inp o lines out measured).routes[k]? =
      some ⟨(inp.routes[k]).id, (inp.routes[k]).fromId, (inp.routes[k]).toId, (inp.routes[k]).orthogonal,
        pts.map (fun p =>
          shiftPoint P.canvasMargin
            P.canvasMargin
            (orientPoint o.direction out.canvasH p))⟩ := by
  rw [sceneOf_routes_getElem? P inp o lines out measured k hk, hroutes]

theorem sceneOf_route_entry_of_producer {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {loops : List (Nat × LoopPlacement)}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (i : Nat) (hi : i < cg.edges.length)
    (_hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (out : Acc) (measured : List MeasuredLabel)
    (b : Bounds) (hb : b = placeBounds P cg run labels loops)
    (box : Rect)
    (hroutes : out.routes.getD (cg.edges[i]).decl [] =
      ((run.routes[i]'(by
        rw [componentRun_routes_length hrun, componentRun_proper_chains_length hrun]
        exact hi)).points.map
        (shiftPoint (0 - b.minX) (0 - b.minY))).map (shiftPoint box.x box.y))
    (hk : (cg.edges[i]).decl < inp.routes.length) :
    let margin := P.canvasMargin
    (sceneOf P inp o lines out measured).routes[(cg.edges[i]).decl]? =
      some ⟨(inp.routes[(cg.edges[i]).decl]).id,
        (inp.routes[(cg.edges[i]).decl]).fromId,
        (inp.routes[(cg.edges[i]).decl]).toId,
        (inp.routes[(cg.edges[i]).decl]).orthogonal,
        (run.routes[i]'(by
          rw [componentRun_routes_length hrun, componentRun_proper_chains_length hrun]
          exact hi)).points.map
          (routePointTransport margin o.direction out.canvasH box.x box.y b.minX b.minY)⟩ := by
  have hscene := sceneOf_routes_getElem? P inp o lines out measured (cg.edges[i]).decl hk
  rw [hscene]
  dsimp only
  rw [hroutes, hb]
  rw [routePointTransport_eq]

theorem sceneOf_route_entry_of_single_part {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {comp : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {loops : List (Nat × LoopPlacement)}
    {acc out : Acc} (packed : Pack.State)
    (box : Rect)
    (hpack : packAcc P o acc = .ok out)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (acc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (part : Part)
    (hpairs : acc.parts.zip packed.boxes = [((comp, part), box)])
    (hpart_routes : part.routes = (placeComponent P cg run 0 labels loops).routes)
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hnd : (cg.edges.map (·.decl)).Nodup)
    (i : Nat) (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (hsize : (cg.edges[i]).decl < acc.routes.size)
    (hk : (cg.edges[i]).decl < inp.routes.length)
    (measured : List MeasuredLabel) :
    let margin := P.canvasMargin
    let b := placeBounds P cg run labels loops
    (sceneOf P inp o lines out measured).routes[(cg.edges[i]).decl]? =
      some ⟨(inp.routes[(cg.edges[i]).decl]).id,
        (inp.routes[(cg.edges[i]).decl]).fromId,
        (inp.routes[(cg.edges[i]).decl]).toId,
        (inp.routes[(cg.edges[i]).decl]).orthogonal,
        (run.routes[i]'(by
          rw [componentRun_routes_length hrun, componentRun_proper_chains_length hrun]
          exact hi)).points.map
          (routePointTransport margin o.direction out.canvasH box.x box.y b.minX b.minY)⟩ := by
  have hget_entry := placeComponent_route_entry_of_producer hrun 0 loops i hi hloop
  rw [← hpart_routes] at hget_entry
  have hnd_part : (part.routes.map (·.1)).Nodup := by
    rw [hpart_routes]
    exact placeComponent_routes_decls_nodup P cg run 0 labels loops hnd
  have hget_out := packAcc_routes_getD_single hpack packed hpacked ((comp, part), box)
    hpairs i (cg.edges[i]).decl _ [] hget_entry hnd_part hsize
  exact sceneOf_route_entry_of_producer hrun i hi hloop out measured (placeBounds P cg run labels loops) rfl box hget_out hk

/-! ### Actual components: partition, noninterference, and declaration ownership

`components g` partitions the node indices by the union-find labels of
`labelsFix (g.edges ++ Compound.constraints g)`; `componentGraph g comp` filters `g.edges` by
tail membership only, so every candidate edge of `comp` is an original edge whose tail lies in
`comp`. These facts give cross-component route-key ownership from the declaration `Nodup` of
`measuredGraph`, without assuming label convergence, output lookup, or singleton components. -/

/-- The union-find label array `components` builds, stated once so every component fact reuses
the runtime label expression instead of restating the fixpoint. -/
def componentLab (g : Graph) : Array Nat :=
  labelsFix (g.edges ++ Compound.constraints g) (g.nodes.length + 1) (Array.range g.nodes.length)

theorem components_eq (g : Graph) :
    components g =
      ((List.range g.nodes.length).filter (fun v => (componentLab g)[v]! == v)).map
        (fun r => (List.range g.nodes.length).filter (fun v => (componentLab g)[v]! == r)) := by
  unfold components componentLab
  rfl

theorem mem_componentRoots {g : Graph} {r : Nat} :
    r ∈ (List.range g.nodes.length).filter (fun v => (componentLab g)[v]! == v) ↔
      r < g.nodes.length ∧ (componentLab g)[r]! = r := by
  rw [List.mem_filter, List.mem_range]
  simp

theorem mem_componentOf {g : Graph} {r v : Nat} :
    v ∈ (List.range g.nodes.length).filter (fun w => (componentLab g)[w]! == r) ↔
      v < g.nodes.length ∧ (componentLab g)[v]! = r := by
  rw [List.mem_filter, List.mem_range]
  simp

theorem mem_components_eq {g : Graph} {comp : List Nat} (hcomp : comp ∈ components g) :
    ∃ r, comp = (List.range g.nodes.length).filter (fun w => (componentLab g)[w]! == r) := by
  unfold components at hcomp
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hcomp
  exact ⟨r, rfl⟩

theorem nodup_map_eq_of_mem {α : Type} {f : α → Nat} {l : List α}
    (hn : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (h : f x = f y) : x = y := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
  have hij := nodup_map_inj f hn hi hj h
  subst hij
  rw [hi] at hj
  exact Option.some.inj hj

theorem components_entries_nodup (g : Graph) : (components g).Nodup := by
  rw [components_eq g, List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_
    (List.Pairwise.sublist List.filter_sublist List.nodup_range)
  intro a b ha hb hne hcon
  obtain ⟨ha1, ha2⟩ := (mem_componentRoots (g := g)).mp ha
  have hmem_fa : a ∈ (List.range g.nodes.length).filter (fun v => (componentLab g)[v]! == a) :=
    (mem_componentOf).mpr ⟨ha1, ha2⟩
  rw [hcon] at hmem_fa
  exact hne (ha2.symm.trans ((mem_componentOf).mp hmem_fa).2)

theorem components_shared_member_eq {g : Graph} {a b : List Nat}
    (ha : a ∈ components g) (hb : b ∈ components g) {v : Nat} (hva : v ∈ a) (hvb : v ∈ b) :
    a = b := by
  obtain ⟨r, rfl⟩ := mem_components_eq ha
  obtain ⟨s, rfl⟩ := mem_components_eq hb
  have hr : (componentLab g)[v]! = r := ((mem_componentOf).mp hva).2
  have hs : (componentLab g)[v]! = s := ((mem_componentOf).mp hvb).2
  have hrs : r = s := hr.symm.trans hs
  subst hrs
  rfl

theorem components_disjoint {g : Graph} {a b : List Nat} (ha : a ∈ components g)
    (hb : b ∈ components g) (hne : a ≠ b) {v : Nat} (hv : v ∈ a) : v ∉ b := by
  intro hvb
  obtain ⟨r, rfl⟩ := mem_components_eq ha
  obtain ⟨s, rfl⟩ := mem_components_eq hb
  have hr : (componentLab g)[v]! = r := ((mem_componentOf).mp hv).2
  have hs : (componentLab g)[v]! = s := ((mem_componentOf).mp hvb).2
  have hrs : r = s := hr.symm.trans hs
  subst hrs
  exact hne rfl

theorem componentGraph_edge_decl (e : Edge) (t h : Nat) :
    ({ e with tail := t, head := h }).decl = e.decl := rfl

/-- Composition of `componentCandidate_decls` and `componentGraph_decls_nodup`. -/
theorem componentCandidate_decls_nodup (g : Graph) (comp : List Nat) (index : Nat)
    (h : (g.edges.map (·.decl)).Nodup) :
    ((componentCandidate g comp index).edges.map (·.decl)).Nodup := by
  rw [componentCandidate_decls]
  exact componentGraph_decls_nodup _ _ h

/-- Declaration ownership: an original `g.edges` entry whose tail lies in `comp` carries
declaration `d`. -/
def ownsDecl (g : Graph) (comp : List Nat) (d : Nat) : Prop :=
  ∃ e ∈ g.edges, e.tail ∈ comp ∧ e.decl = d

/-- Every candidate edge of an actual filter component owns its declaration: derived from the
decl-list equality of `componentCandidate_decls` and the tail filter of `componentGraph`. -/
theorem componentCandidate_edge_owns {g : Graph} {comp : List Nat} {index : Nat} {e : Edge}
    (he : e ∈ (componentCandidate g comp index).edges) : ownsDecl g comp e.decl := by
  have hd : (componentCandidate g comp index).edges.map (·.decl) =
      (componentGraph g comp).edges.map (·.decl) := componentCandidate_decls g comp index
  have hmem : e.decl ∈ (componentGraph g comp).edges.map (·.decl) := by
    rw [← hd]
    exact List.mem_map_of_mem he
  unfold componentGraph at hmem
  dsimp only at hmem
  obtain ⟨x, hxmem, hxdecl⟩ := List.mem_map.mp hmem
  obtain ⟨e', he'ge, hfx⟩ := List.mem_map.mp hxmem
  subst hfx
  dsimp only at hxdecl
  obtain ⟨he'ge, htail⟩ := List.mem_filter.mp he'ge
  exact ⟨e', he'ge, List.contains_iff_mem.mp htail, hxdecl⟩

/-- Ownership uniqueness across actual components: the declaring edge is pinned by declaration
`Nodup`, and its tail then pins the component. -/
theorem ownsDecl_unique {g : Graph} {a b : List Nat} {d : Nat}
    (hnd : (g.edges.map (·.decl)).Nodup)
    (ha : a ∈ components g) (hb : b ∈ components g)
    (h1 : ownsDecl g a d) (h2 : ownsDecl g b d) : a = b := by
  unfold ownsDecl at h1 h2
  obtain ⟨e1, he1, ht1, hd1⟩ := h1
  obtain ⟨e2, he2, ht2, hd2⟩ := h2
  have hsame : e1 = e2 := nodup_map_eq_of_mem hnd he1 he2 (hd1.trans hd2.symm)
  subst hsame
  exact components_shared_member_eq ha hb ht1 ht2

/-- Route-key noninterference: distinct actual components never share a declaration owner. -/
theorem components_ownsDecl_disjoint {g : Graph} {a b : List Nat} {d : Nat}
    (hnd : (g.edges.map (·.decl)).Nodup)
    (ha : a ∈ components g) (hb : b ∈ components g) (hne : a ≠ b)
    (h1 : ownsDecl g a d) : ¬ ownsDecl g b d := by
  intro h2
  exact hne (ownsDecl_unique hnd ha hb h1 h2)

/-- The composition instantiated at `measuredGraph` success. -/
theorem componentCandidate_decls_nodup_of_measuredGraph {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (h : measuredGraph P inp o lines = .ok g0) (comp : List Nat) (index : Nat) :
    ((componentCandidate g0 comp index).edges.map (·.decl)).Nodup :=
  componentCandidate_decls_nodup g0 comp index (measuredGraph_decls_nodup h)

def ActualPart (P : Params) (inp : Input) (o : Options) (g : Graph)
    (labels : List MeasuredLabel) (q : List Nat × Part) : Prop :=
  ∃ index chosen run loops,
    index < 5 ∧
    Portfolio.portfolio o.thoroughness (componentTrial P inp o g q.1 labels) = .ok chosen ∧
    chosen.value = (componentCandidate g q.1 index, run) ∧
    componentRun P (componentCandidate g q.1 index) labels (candidateOrder index) = .ok run ∧
    componentLoops P (componentCandidate g q.1 index) run labels = .ok loops ∧
    q.2.routes = (placeComponent P (componentCandidate g q.1 index) run 0 labels loops).routes

theorem placePart_parts {comp : List Nat} {cg : Graph} {run : Run}
    {P : Params} {acc out : Acc} {labels : List MeasuredLabel}
    (h : placePart comp cg run P acc labels = .ok out) :
    ∃ loops part, componentLoops P cg run labels = .ok loops ∧
      out.parts = acc.parts ++ [(comp, part)] ∧
      part.routes = (placeComponent P cg run 0 labels loops).routes := by
  unfold placePart at h
  obtain ⟨loops, hl, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp at h
  · have he := Except.ok.inj h
    subst out
    exact ⟨loops, _, hl, rfl, rfl⟩

theorem layoutComponent_parts {P : Params} {inp : Input} {o : Options} {g : Graph}
    {acc out : Acc} {comp : List Nat} {labels : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp labels = .ok out) :
    ∃ part, out.parts = acc.parts ++ [(comp, part)] ∧
      ActualPart P inp o g labels (comp, part) := by
  unfold layoutComponent at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨metric, _, h⟩ := bind_ok h
  obtain ⟨areas, _, h⟩ := bind_ok h
  obtain ⟨loops, part, hl, hparts, hroutes⟩ := placePart_parts hp
  obtain ⟨index, trial, hi, ht, hv, _⟩ := Portfolio.portfolio_selected hc
  unfold componentTrial at ht
  obtain ⟨run, hrun, ht⟩ := bind_ok ht
  obtain ⟨scene, _, ht⟩ := bind_ok ht
  have htrial := Except.ok.inj ht
  subst trial
  dsimp only at hv
  have he := Except.ok.inj h
  subst out
  let childArea := inp.fixedAreas.foldl (fun total child =>
    if chosen.scene.boxes.any (fun box => box.id == child.1) then total + child.2 else total) 0
  let augmented := { part with area := part.area + childArea + areas.sum }
  refine ⟨augmented, ?_, ?_⟩
  · simp [hparts, augmented, childArea]
  · unfold ActualPart
    refine ⟨index, chosen, run, loops, hi, hc, hv, hrun, ?_, ?_⟩
    · simpa only [hv] using hl
    · simpa only [hv] using hroutes

theorem actualPart_owns {P : Params} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {q : List Nat × Part}
    (h : ActualPart P inp o g labels q) :
    ∀ d ∈ q.2.routes.map (·.1), ownsDecl g q.1 d := by
  obtain ⟨index, _, run, loops, _, _, _, _, _, hr⟩ := h
  rw [hr, placeComponent_routes_decls]
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  exact componentCandidate_edge_owns he

theorem foldlM_layout_components_parts (P : Params) (inp : Input) (o : Options)
    (g : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out →
      ∃ parts, out.parts = start.parts ++ parts ∧ parts.map (·.1) = comps ∧
        ∀ q ∈ parts, ActualPart P inp o g labels q := by
  intro comps
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil] at h
    have hout : start = out := Except.ok.inj h
    subst out
    exact ⟨[], by simp, rfl, by simp⟩
  | cons comp comps ih =>
    intro start out h
    rw [List.foldlM_cons] at h
    obtain ⟨next, hn, hrest⟩ := bind_ok h
    obtain ⟨part, hp, hprod⟩ := layoutComponent_parts hn
    obtain ⟨parts, hout, hmap, hall⟩ := ih next out hrest
    refine ⟨(comp, part) :: parts, ?_, ?_, ?_⟩
    · rw [hout, hp]
      simp only [List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, hmap]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hprod
      · exact hall q hq

theorem actual_components_parts {P : Params} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {start out : Acc} (hempty : start.parts = [])
    (h : (components g).foldlM
      (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out) :
    out.parts.map (·.1) = components g ∧
      ∀ q ∈ out.parts, ActualPart P inp o g labels q := by
  obtain ⟨parts, hp, hm, hall⟩ := foldlM_layout_components_parts P inp o g labels _ _ _ h
  simp only [hempty, List.nil_append] at hp
  subst parts
  exact ⟨hm, hall⟩

private def ActualPartGeometry (P : Params) (inp : Input) (o : Options) (g : Graph)
    (labels : List MeasuredLabel) (q : List Nat × Part) : Prop :=
  ∃ index chosen run loops area,
    index < 5 ∧
    Portfolio.portfolio o.thoroughness (componentTrial P inp o g q.1 labels) = .ok chosen ∧
    chosen.value = (componentCandidate g q.1 index, run) ∧
    componentRun P (componentCandidate g q.1 index) labels (candidateOrder index) = .ok run ∧
    componentLoops P (componentCandidate g q.1 index) run labels = .ok loops ∧
    q.2 = { placeComponent P (componentCandidate g q.1 index) run 0 labels loops
      with area := area }

private theorem placePart_parts_geometry {comp : List Nat} {cg : Graph} {run : Run}
    {P : Params} {acc out : Acc} {labels : List MeasuredLabel}
    (h : placePart comp cg run P acc labels = .ok out) :
    ∃ loops area,
      componentLoops P cg run labels = .ok loops ∧
      out.parts = acc.parts ++ [(comp,
        { placeComponent P cg run 0 labels loops with area := area })] := by
  unfold placePart at h
  obtain ⟨loops, hl, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp at h
  · have he := Except.ok.inj h
    subst out
    exact ⟨loops, _, hl, rfl⟩

private theorem layoutComponent_parts_geometry {P : Params} {inp : Input} {o : Options}
    {g : Graph} {acc out : Acc} {comp : List Nat} {labels : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp labels = .ok out) :
    ∃ part, out.parts = acc.parts ++ [(comp, part)] ∧
      ActualPartGeometry P inp o g labels (comp, part) := by
  unfold layoutComponent at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨metric, _, h⟩ := bind_ok h
  obtain ⟨areas, _, h⟩ := bind_ok h
  obtain ⟨loops, area, hl, hparts⟩ := placePart_parts_geometry hp
  obtain ⟨index, trial, hi, ht, hv, _⟩ := Portfolio.portfolio_selected hc
  unfold componentTrial at ht
  obtain ⟨run, hrun, ht⟩ := bind_ok ht
  obtain ⟨scene, _, ht⟩ := bind_ok ht
  have htrial := Except.ok.inj ht
  subst trial
  dsimp only at hv
  have he := Except.ok.inj h
  subst out
  let childArea := inp.fixedAreas.foldl (fun total child =>
    if chosen.scene.boxes.any (fun box => box.id == child.1) then total + child.2 else total) 0
  let base := placeComponent P chosen.value.1 chosen.value.2 0 labels loops
  let augmented := { base with area := area + childArea + areas.sum }
  refine ⟨augmented, ?_, ?_⟩
  · simp [hparts, augmented, base, childArea]
  · unfold ActualPartGeometry
    refine ⟨index, chosen, run, loops, area + childArea + areas.sum,
      hi, hc, hv, hrun, ?_, ?_⟩
    · simpa only [hv] using hl
    · simp only [augmented, base, hv]

private theorem foldlM_layout_components_parts_geometry
    (P : Params) (inp : Input) (o : Options) (g : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out →
      ∃ parts, out.parts = start.parts ++ parts ∧ parts.map (·.1) = comps ∧
        ∀ q ∈ parts, ActualPartGeometry P inp o g labels q := by
  intro comps
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil] at h
    have hout : start = out := Except.ok.inj h
    subst out
    exact ⟨[], by simp, rfl, by simp⟩
  | cons comp comps ih =>
    intro start out h
    rw [List.foldlM_cons] at h
    obtain ⟨next, hn, hrest⟩ := bind_ok h
    obtain ⟨part, hp, hprod⟩ := layoutComponent_parts_geometry hn
    obtain ⟨parts, hout, hmap, hall⟩ := ih next out hrest
    refine ⟨(comp, part) :: parts, ?_, ?_, ?_⟩
    · rw [hout, hp]
      simp only [List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, hmap]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hprod
      · exact hall q hq

theorem actual_components_parts_geometry {P : Params} {inp : Input} {o : Options}
    {g : Graph} {labels : List MeasuredLabel} {start out : Acc}
    (hempty : start.parts = [])
    (h : (components g).foldlM
      (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out) :
    out.parts.map (·.1) = components g ∧
      ∀ q ∈ out.parts, ∃ index chosen run loops area,
        index < 5 ∧
        Portfolio.portfolio o.thoroughness (componentTrial P inp o g q.1 labels) = .ok chosen ∧
        chosen.value = (componentCandidate g q.1 index, run) ∧
        componentRun P (componentCandidate g q.1 index) labels (candidateOrder index) = .ok run ∧
        componentLoops P (componentCandidate g q.1 index) run labels = .ok loops ∧
        q.2 = { placeComponent P (componentCandidate g q.1 index) run 0 labels loops
          with area := area } := by
  obtain ⟨parts, hp, hm, hall⟩ :=
    foldlM_layout_components_parts_geometry P inp o g labels _ _ _ h
  simp only [hempty, List.nil_append] at hp
  subst parts
  exact ⟨hm, hall⟩

theorem actual_components_route_keys_disjoint {P : Params} {inp : Input} {o : Options}
    {g : Graph} {labels : List MeasuredLabel} {start out : Acc}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {a b : List Nat × Part} (ha : a ∈ out.parts) (hb : b ∈ out.parts)
    (hne : a.1 ≠ b.1) {d : Nat} (hd : d ∈ a.2.routes.map (·.1)) :
    d ∉ b.2.routes.map (·.1) := by
  obtain ⟨hm, hall⟩ := actual_components_parts hempty hfold
  have hca : a.1 ∈ components g := by
    rw [← hm]
    exact List.mem_map_of_mem ha
  have hcb : b.1 ∈ components g := by
    rw [← hm]
    exact List.mem_map_of_mem hb
  intro hd'
  exact components_ownsDecl_disjoint hnd hca hcb hne
    (actualPart_owns (hall a ha) d hd) (actualPart_owns (hall b hb) d hd')

theorem actual_components_later_route_key_ne {P : Params} {inp : Input} {o : Options}
    {g : Graph} {labels : List MeasuredLabel} {start out : Acc}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {i j : Nat} {a b : List Nat × Part}
    (ha : out.parts[i]? = some a) (hb : out.parts[j]? = some b) (hij : i < j)
    {d : Nat} (hd : d ∈ a.2.routes.map (·.1)) :
    d ∉ b.2.routes.map (·.1) := by
  obtain ⟨hm, _⟩ := actual_components_parts hempty hfold
  have hn : (out.parts.map (·.1)).Nodup := by
    rw [hm]
    exact components_entries_nodup g
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, hbj⟩ := List.getElem?_eq_some_iff.mp hb
  have hne : a.1 ≠ b.1 := by
    have hpair := List.pairwise_iff_getElem.mp hn
    have hnij := hpair i j (by simpa using hi) (by simpa using hj) hij
    simpa [hai, hbj] using hnij
  exact actual_components_route_keys_disjoint hempty hfold hnd
    (List.mem_iff_getElem?.mpr ⟨i, ha⟩) (List.mem_iff_getElem?.mpr ⟨j, hb⟩) hne hd

/-- Structural transport: a pair selected from the packed zip projects to the part selected
from `parts` at the same index. Zip truncation is honest: the hypothesis is about the zip
itself, so a pair at index `c` exists only when `c` is in range for both sides. -/
theorem zip_getElem?_left {α β : Type} {xs : List α} {ys : List β}
    {c : Nat} {x : α} {y : β} (h : (xs.zip ys)[c]? = some (x, y)) :
    xs[c]? = some x :=
  (List.getElem?_zip_eq_some.mp h).1

/-- Structural transport: a member of the packed zip strictly after index `c` projects to a
part at a strictly later index. Duplicate parts are handled by indexed membership: the index
`j` comes from the concrete occurrence of `q` in the zip, so no uniqueness of part values is
assumed. Truncation of `ys` is honest: `q` occurs in the zip only where both lists have an
entry at that index. -/
theorem zip_drop_mem_later_getElem? {α β : Type} {xs : List α} {ys : List β}
    {c : Nat} {q : α × β} (h : q ∈ (xs.zip ys).drop (c + 1)) :
    ∃ j, c < j ∧ xs[j]? = some q.1 := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp h
  rw [List.getElem?_drop] at hn
  exact ⟨c + 1 + n, by omega, (List.getElem?_zip_eq_some.mp hn).1⟩

/-- For the actual component fold output, a route declaration owned by the part selected from
the packed zip cannot occur in any part occurring strictly later in the same zip. This turns
the fold, the edge declaration Nodup, and the selected zip pair into the `hnot_after` premise
of `PipelineImpl.packAcc_routes_getD`; no bound or overwrite assumption is added. -/
theorem actual_components_zip_later_route_key_ne
    {P : Params} {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel}
    {start out : Acc} {positions : List Rect}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {c : Nat} {a : List Nat × Part} {pos : Rect}
    (hsel : (out.parts.zip positions)[c]? = some (a, pos))
    {d : Nat} (hd : d ∈ a.2.routes.map (·.1))
    {q' : (List Nat × Part) × Rect}
    (hq' : q' ∈ (out.parts.zip positions).drop (c + 1)) :
    d ∉ q'.1.2.routes.map (·.1) := by
  obtain ⟨j, hjlt, hjget⟩ :=
    zip_drop_mem_later_getElem? (xs := out.parts) (ys := positions) hq'
  exact actual_components_later_route_key_ne hempty hfold hnd
    (zip_getElem?_left hsel) hjget hjlt hd

end PipelineImpl

theorem layoutFamily_geometry_ok {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) :
    PipelineImpl.layoutRecursive (inp.boxes.length + 1) inp o = .ok res := by
  by_cases hn : o.limits.maxNodes < inp.boxes.length <;>
    by_cases he : o.limits.maxEdges < inp.routes.length <;>
    by_cases ht : o.limits.maxTextBytes < inputTextBytes inp <;>
    by_cases hw : modelWellFormed (inputModel inp o) <;>
    by_cases hf : framedParents inp <;>
    by_cases ha : attachedNoteParents inp <;>
    cases hg : PipelineImpl.layoutRecursive (inp.boxes.length + 1) inp o <;>
    simp_all [layoutFamily]

theorem layoutFamily_wellFormed {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) : WellFormed (inputModel inp o) := by
  by_cases hn : o.limits.maxNodes < inp.boxes.length <;>
    by_cases he : o.limits.maxEdges < inp.routes.length <;>
    by_cases ht : o.limits.maxTextBytes < inputTextBytes inp <;>
    by_cases hw : modelWellFormed (inputModel inp o) <;>
    by_cases hf : framedParents inp <;>
    by_cases ha : attachedNoteParents inp <;>
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

theorem boundsOf_contains_rect {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) :
    (PipelineImpl.boundsOf rects pts).minX ≤ r.x ∧
    r.x + r.w ≤ (PipelineImpl.boundsOf rects pts).right ∧
    (PipelineImpl.boundsOf rects pts).minY ≤ r.y ∧
    r.y + r.h ≤ (PipelineImpl.boundsOf rects pts).bottom :=
  PipelineImpl.boundsOf_contains_rect rects pts r hr

theorem boundsOf_contains_point {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) :
    (PipelineImpl.boundsOf rects pts).minX ≤ p.x ∧
    p.x ≤ (PipelineImpl.boundsOf rects pts).right ∧
    (PipelineImpl.boundsOf rects pts).minY ≤ p.y ∧
    p.y ≤ (PipelineImpl.boundsOf rects pts).bottom :=
  PipelineImpl.boundsOf_contains_point rects pts p hp

theorem boundsOf_minX_le_rect_x {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) : (PipelineImpl.boundsOf rects pts).minX ≤ r.x :=
  PipelineImpl.boundsOf_minX_le_rect_x rects pts r hr

theorem rect_right_le_boundsOf_right {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) : r.x + r.w ≤ (PipelineImpl.boundsOf rects pts).right :=
  PipelineImpl.rect_right_le_boundsOf_right rects pts r hr

theorem boundsOf_minY_le_rect_y {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) : (PipelineImpl.boundsOf rects pts).minY ≤ r.y :=
  PipelineImpl.boundsOf_minY_le_rect_y rects pts r hr

theorem rect_bottom_le_boundsOf_bottom {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) : r.y + r.h ≤ (PipelineImpl.boundsOf rects pts).bottom :=
  PipelineImpl.rect_bottom_le_boundsOf_bottom rects pts r hr

theorem boundsOf_minX_le_point_x {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) : (PipelineImpl.boundsOf rects pts).minX ≤ p.x :=
  PipelineImpl.boundsOf_minX_le_point_x rects pts p hp

theorem point_x_le_boundsOf_right {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) : p.x ≤ (PipelineImpl.boundsOf rects pts).right :=
  PipelineImpl.point_x_le_boundsOf_right rects pts p hp

theorem boundsOf_minY_le_point_y {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) : (PipelineImpl.boundsOf rects pts).minY ≤ p.y :=
  PipelineImpl.boundsOf_minY_le_point_y rects pts p hp

theorem point_y_le_boundsOf_bottom {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) : p.y ≤ (PipelineImpl.boundsOf rects pts).bottom :=
  PipelineImpl.point_y_le_boundsOf_bottom rects pts p hp

theorem boundsOf_width_nonneg_of_rect {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) (hw : 0 ≤ r.w) :
    0 ≤ (PipelineImpl.boundsOf rects pts).right - (PipelineImpl.boundsOf rects pts).minX :=
  PipelineImpl.boundsOf_width_nonneg_of_rect hr hw

theorem boundsOf_height_nonneg_of_rect {rects : List Rect} {pts : List Point} {r : Rect}
    (hr : r ∈ rects) (hh : 0 ≤ r.h) :
    0 ≤ (PipelineImpl.boundsOf rects pts).bottom - (PipelineImpl.boundsOf rects pts).minY :=
  PipelineImpl.boundsOf_height_nonneg_of_rect hr hh

theorem boundsOf_width_nonneg_of_point {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) :
    0 ≤ (PipelineImpl.boundsOf rects pts).right - (PipelineImpl.boundsOf rects pts).minX :=
  PipelineImpl.boundsOf_width_nonneg_of_point hp

theorem boundsOf_height_nonneg_of_point {rects : List Rect} {pts : List Point} {p : Point}
    (hp : p ∈ pts) :
    0 ≤ (PipelineImpl.boundsOf rects pts).bottom - (PipelineImpl.boundsOf rects pts).minY :=
  PipelineImpl.boundsOf_height_nonneg_of_point hp

theorem shiftRect_cursor_bounds (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) (cursor : Int) :
    cursor ≤ (PipelineImpl.shiftRect (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) r).x ∧
    (PipelineImpl.shiftRect (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) r).x +
        (PipelineImpl.shiftRect (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) r).w ≤
      cursor + ((PipelineImpl.boundsOf rects pts).right - (PipelineImpl.boundsOf rects pts).minX) ∧
    0 ≤ (PipelineImpl.shiftRect (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) r).y ∧
    (PipelineImpl.shiftRect (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) r).y +
        (PipelineImpl.shiftRect (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) r).h ≤
      (PipelineImpl.boundsOf rects pts).bottom - (PipelineImpl.boundsOf rects pts).minY :=
  PipelineImpl.shiftRect_cursor_bounds rects pts r hr cursor

theorem shiftPoint_cursor_bounds (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) (cursor : Int) :
    cursor ≤ (PipelineImpl.shiftPoint (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) p).x ∧
    (PipelineImpl.shiftPoint (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) p).x ≤
      cursor + ((PipelineImpl.boundsOf rects pts).right - (PipelineImpl.boundsOf rects pts).minX) ∧
    0 ≤ (PipelineImpl.shiftPoint (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) p).y ∧
    (PipelineImpl.shiftPoint (cursor - (PipelineImpl.boundsOf rects pts).minX)
        (0 - (PipelineImpl.boundsOf rects pts).minY) p).y ≤
      (PipelineImpl.boundsOf rects pts).bottom - (PipelineImpl.boundsOf rects pts).minY :=
  PipelineImpl.shiftPoint_cursor_bounds rects pts p hp cursor

theorem shiftRect_origin_bounds (rects : List Rect) (pts : List Point) (r : Rect)
    (hr : r ∈ rects) :
    0 ≤ (PipelineImpl.shiftRect (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) r).x ∧
    (PipelineImpl.shiftRect (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) r).x +
        (PipelineImpl.shiftRect (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) r).w ≤
      (PipelineImpl.boundsOf rects pts).right - (PipelineImpl.boundsOf rects pts).minX ∧
    0 ≤ (PipelineImpl.shiftRect (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) r).y ∧
    (PipelineImpl.shiftRect (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) r).y +
        (PipelineImpl.shiftRect (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) r).h ≤
      (PipelineImpl.boundsOf rects pts).bottom - (PipelineImpl.boundsOf rects pts).minY :=
  PipelineImpl.shiftRect_origin_bounds rects pts r hr

theorem shiftPoint_origin_bounds (rects : List Rect) (pts : List Point) (p : Point)
    (hp : p ∈ pts) :
    0 ≤ (PipelineImpl.shiftPoint (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) p).x ∧
    (PipelineImpl.shiftPoint (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) p).x ≤
      (PipelineImpl.boundsOf rects pts).right - (PipelineImpl.boundsOf rects pts).minX ∧
    0 ≤ (PipelineImpl.shiftPoint (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) p).y ∧
    (PipelineImpl.shiftPoint (-(PipelineImpl.boundsOf rects pts).minX)
        (-(PipelineImpl.boundsOf rects pts).minY) p).y ≤
      (PipelineImpl.boundsOf rects pts).bottom - (PipelineImpl.boundsOf rects pts).minY :=
  PipelineImpl.shiftPoint_origin_bounds rects pts p hp

theorem placeComponent_rects_bounds (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (cursor : Int) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    ∀ r' ∈ (PipelineImpl.placeComponent P cg run cursor labels loops).rects,
      cursor ≤ r'.x ∧
      r'.x + r'.w ≤ cursor + (PipelineImpl.placeComponent P cg run cursor labels loops).width ∧
      0 ≤ r'.y ∧
      r'.y + r'.h ≤ (PipelineImpl.placeComponent P cg run cursor labels loops).height :=
  PipelineImpl.placeComponent_rects_bounds P cg run cursor labels loops

theorem placeComponent_titles_bounds (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (cursor : Int) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    ∀ t' ∈ (PipelineImpl.placeComponent P cg run cursor labels loops).titles,
      cursor ≤ t'.2.x ∧
      t'.2.x + t'.2.w ≤ cursor + (PipelineImpl.placeComponent P cg run cursor labels loops).width ∧
      0 ≤ t'.2.y ∧
      t'.2.y + t'.2.h ≤ (PipelineImpl.placeComponent P cg run cursor labels loops).height :=
  PipelineImpl.placeComponent_titles_bounds P cg run cursor labels loops

theorem placeComponent_rects_bounds_zero (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    ∀ r' ∈ (PipelineImpl.placeComponent P cg run 0 labels loops).rects,
      0 ≤ r'.x ∧
      r'.x + r'.w ≤ (PipelineImpl.placeComponent P cg run 0 labels loops).width ∧
      0 ≤ r'.y ∧
      r'.y + r'.h ≤ (PipelineImpl.placeComponent P cg run 0 labels loops).height :=
  PipelineImpl.placeComponent_rects_bounds_zero P cg run labels loops

theorem placeComponent_titles_bounds_zero (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    ∀ t' ∈ (PipelineImpl.placeComponent P cg run 0 labels loops).titles,
      0 ≤ t'.2.x ∧
      t'.2.x + t'.2.w ≤ (PipelineImpl.placeComponent P cg run 0 labels loops).width ∧
      0 ≤ t'.2.y ∧
      t'.2.y + t'.2.h ≤ (PipelineImpl.placeComponent P cg run 0 labels loops).height :=
  PipelineImpl.placeComponent_titles_bounds_zero P cg run labels loops

theorem componentRun_routes_length {P : PipelineImpl.Params} {cg : Graph}
    {run : PipelineImpl.Run} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : PipelineImpl.componentRun P cg labels orderOptions = .ok run) :
    run.routes.length = run.proper.chains.length :=
  PipelineImpl.componentRun_routes_length h

theorem componentRun_proper_chains_length {P : PipelineImpl.Params} {cg : Graph}
    {run : PipelineImpl.Run} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : PipelineImpl.componentRun P cg labels orderOptions = .ok run) :
    run.proper.chains.length = cg.edges.length :=
  PipelineImpl.componentRun_proper_chains_length h

theorem componentRun_route_of_index {P : PipelineImpl.Params} {cg : Graph}
    {run : PipelineImpl.Run} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : PipelineImpl.componentRun P cg labels orderOptions = .ok run) {i : Nat}
    (hi : i < cg.edges.length) :
    ∃ rt : EdgeRoute, run.routes[i]? = some rt ∧ rt.original = i ∧
      RouteImpl.laneRouteOf P.slot run.proper run.ys run.top
        (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes i = .ok rt :=
  PipelineImpl.componentRun_route_of_index h hi

theorem componentRun_edgePoints_of_index {P : PipelineImpl.Params} {cg : Graph}
    {run : PipelineImpl.Run} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions} {e : Edge}
    (h : PipelineImpl.componentRun P cg labels orderOptions = .ok run) {i : Nat}
    (hi : i < cg.edges.length) :
    PipelineImpl.edgePoints run i e = (run.routes[i]'(by
      rw [PipelineImpl.componentRun_routes_length h, PipelineImpl.componentRun_proper_chains_length h]
      exact hi)).points :=
  PipelineImpl.componentRun_edgePoints_of_index h hi

theorem placeComponent_route_key_decl {P : PipelineImpl.Params} (cg : Graph)
    (run : PipelineImpl.Run) (cursor : Int) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) (i : Nat) (hi : i < cg.edges.length) :
    ((PipelineImpl.placeComponent P cg run cursor labels loops).routes[i]?).map (·.1) =
      some (cg.edges[i]).decl :=
  PipelineImpl.placeComponent_route_key_decl P cg run cursor labels loops i hi

theorem placeComponent_route_points_of_noLoop {P : PipelineImpl.Params} (cg : Graph)
    (run : PipelineImpl.Run) (cursor : Int) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) (i : Nat) (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl) :
    ((PipelineImpl.placeComponent P cg run cursor labels loops).routes[i]?).map (·.2) =
      some ((PipelineImpl.edgePoints run i (cg.edges[i])).map
        (PipelineImpl.shiftPoint (cursor - (PipelineImpl.placeBounds P cg run labels loops).minX)
          (0 - (PipelineImpl.placeBounds P cg run labels loops).minY))) :=
  PipelineImpl.placeComponent_route_points_of_noLoop P cg run cursor labels loops i hi
    hloop

theorem placeComponent_route_entry_of_producer {P : PipelineImpl.Params} {cg : Graph}
    {run : PipelineImpl.Run} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : PipelineImpl.componentRun P cg labels orderOptions = .ok run)
    (cursor : Int) (loops : List (Nat × LoopPlacement)) (i : Nat)
    (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl) :
    (PipelineImpl.placeComponent P cg run cursor labels loops).routes[i]? =
      some ((cg.edges[i]).decl,
        (run.routes[i]'(by
          rw [PipelineImpl.componentRun_routes_length h, PipelineImpl.componentRun_proper_chains_length h]
          exact hi)).points.map
          (PipelineImpl.shiftPoint (cursor - (PipelineImpl.placeBounds P cg run labels loops).minX)
            (0 - (PipelineImpl.placeBounds P cg run labels loops).minY))) :=
  PipelineImpl.placeComponent_route_entry_of_producer h cursor loops i hi hloop

theorem componentCandidate_edge_index_decl_lt {P : PipelineImpl.Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (hg0 : PipelineImpl.measuredGraph P inp o lines = .ok g0)
    (comp : List Nat) (index : Nat) {i : Nat}
    (hi : i < (PipelineImpl.componentCandidate g0 comp index).edges.length) :
    ((PipelineImpl.componentCandidate g0 comp index).edges[i]).decl < inp.routes.length :=
  PipelineImpl.componentCandidate_edge_index_decl_lt hg0 comp index hi

theorem routes_foldl_size {α β : Type} (f : β → α) (entries : List (Nat × β)) (a : Array α) :
    (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a).size = a.size :=
  PipelineImpl.routes_foldl_size f entries a

theorem routes_foldl_getD_ne {α β : Type} (f : β → α) (entries : List (Nat × β)) (a : Array α)
    (k : Nat) (d : α) (hk : k ∉ entries.map (·.1)) :
    (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a).getD k d = a.getD k d :=
  PipelineImpl.routes_foldl_getD_ne f entries a k d hk

theorem routes_foldl_getD_mem {α β : Type} (f : β → α) (entries : List (Nat × β)) (a : Array α)
    (i : Nat) (k : Nat) (v : β) (d : α)
    (hget : entries[i]? = some (k, v))
    (hnodup : (entries.map (·.1)).Nodup)
    (hsize : k < a.size) :
    (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a).getD k d = f v :=
  PipelineImpl.routes_foldl_getD_mem f entries a i k v d hget hnodup hsize

theorem placeComponent_routes_length (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (cursor : Int) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    (PipelineImpl.placeComponent P cg run cursor labels loops).routes.length = cg.edges.length :=
  PipelineImpl.placeComponent_routes_length P cg run cursor labels loops

theorem placeComponent_routes_decls (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (cursor : Int) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    (PipelineImpl.placeComponent P cg run cursor labels loops).routes.map (·.1) = cg.edges.map (·.decl) :=
  PipelineImpl.placeComponent_routes_decls P cg run cursor labels loops

theorem placeComponent_routes_decls_nodup (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (cursor : Int) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement))
    (hnd : (cg.edges.map (·.decl)).Nodup) :
    ((PipelineImpl.placeComponent P cg run cursor labels loops).routes.map (·.1)).Nodup :=
  PipelineImpl.placeComponent_routes_decls_nodup P cg run cursor labels loops hnd

theorem placePart_routes_size {comp : List Nat} {cg : Graph} {run : PipelineImpl.Run}
    {P : PipelineImpl.Params} {acc res : PipelineImpl.Acc} {labels : List PipelineImpl.MeasuredLabel}
    (hplace : PipelineImpl.placePart comp cg run P acc labels = .ok res) :
    res.routes.size = acc.routes.size :=
  PipelineImpl.placePart_routes_size hplace

theorem placePart_routes_getD {comp : List Nat} {cg : Graph} {run : PipelineImpl.Run}
    {P : PipelineImpl.Params} {acc res : PipelineImpl.Acc} {labels : List PipelineImpl.MeasuredLabel}
    {loops : List (Nat × LoopPlacement)}
    (hplace : PipelineImpl.placePart comp cg run P acc labels = .ok res)
    (hloops : PipelineImpl.componentLoops P cg run labels = .ok loops)
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget : (PipelineImpl.placeComponent P cg run 0 labels loops).routes[i]? = some (k, pts))
    (hnd : (cg.edges.map (·.decl)).Nodup)
    (hsize : k < acc.routes.size) :
    res.routes.getD k d = pts :=
  PipelineImpl.placePart_routes_getD hplace hloops i k pts d hget hnd hsize

theorem placePart_route_points_of_producer {comp : List Nat} {cg : Graph} {run : PipelineImpl.Run}
    {P : PipelineImpl.Params} {acc res : PipelineImpl.Acc} {labels : List PipelineImpl.MeasuredLabel}
    {orderOptions : OrderOptions} {loops : List (Nat × LoopPlacement)}
    (hplace : PipelineImpl.placePart comp cg run P acc labels = .ok res)
    (hloops : PipelineImpl.componentLoops P cg run labels = .ok loops)
    (hrun : PipelineImpl.componentRun P cg labels orderOptions = .ok run)
    (hnd : (cg.edges.map (·.decl)).Nodup)
    {i : Nat} (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (hsize : (cg.edges[i]).decl < acc.routes.size)
    (d : List Point) :
    res.routes.getD (cg.edges[i]).decl d =
      (run.routes[i]'(by
        rw [PipelineImpl.componentRun_routes_length hrun, PipelineImpl.componentRun_proper_chains_length hrun]
        exact hi)).points.map
        (PipelineImpl.shiftPoint (0 - (PipelineImpl.placeBounds P cg run labels loops).minX)
          (0 - (PipelineImpl.placeBounds P cg run labels loops).minY)) :=
  PipelineImpl.placePart_route_points_of_producer hplace hloops hrun hnd hi hloop hsize d

theorem packAcc_routes_size {P : PipelineImpl.Params} {o : Options} {acc out : PipelineImpl.Acc}
    (hpack : PipelineImpl.packAcc P o acc = .ok out) :
    out.routes.size = acc.routes.size :=
  PipelineImpl.packAcc_routes_size hpack

theorem packAcc_routes_getD {P : PipelineImpl.Params} {o : Options} {acc out : PipelineImpl.Acc}
    (hpack : PipelineImpl.packAcc P o acc = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (acc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × PipelineImpl.Part) × Rect)
    (hget_pair : (acc.parts.zip packed.boxes)[c]? = some q)
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget_route : q.1.2.routes[i]? = some (k, pts))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    (hsize : k < acc.routes.size)
    (hnot_after : ∀ q' ∈ (acc.parts.zip packed.boxes).drop (c + 1), k ∉ q'.1.2.routes.map (·.1)) :
    out.routes.getD k d = pts.map (PipelineImpl.shiftPoint q.2.x q.2.y) :=
  PipelineImpl.packAcc_routes_getD hpack packed hpacked c q hget_pair i k pts d hget_route hnodup hsize hnot_after

theorem packAcc_routes_getD_single {P : PipelineImpl.Params} {o : Options} {acc out : PipelineImpl.Acc}
    (hpack : PipelineImpl.packAcc P o acc = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (acc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (q : (List Nat × PipelineImpl.Part) × Rect)
    (hpairs : acc.parts.zip packed.boxes = [q])
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget_route : q.1.2.routes[i]? = some (k, pts))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    (hsize : k < acc.routes.size) :
    out.routes.getD k d = pts.map (PipelineImpl.shiftPoint q.2.x q.2.y) :=
  PipelineImpl.packAcc_routes_getD_single hpack packed hpacked q hpairs i k pts d hget_route hnodup hsize

/-- Corollary of `packAcc_routes_getD`: the `hnot_after` premise is discharged from the actual
component fold, the edge declaration Nodup, and the selected zip pair, via
`PipelineImpl.actual_components_zip_later_route_key_ne`. The packed positions list may be
shorter than the parts; the derivation uses indexed membership and assumes no overwrite or
ownership premise. -/
theorem actual_components_packAcc_routes_getD
    {P : PipelineImpl.Params} {inp : Input} {o : Options} {g : Graph}
    {labels : List PipelineImpl.MeasuredLabel} {start mid out : PipelineImpl.Acc}
    (hempty : start.parts = [])
    (hfold : (PipelineImpl.components g).foldlM
      (fun acc comp => PipelineImpl.layoutComponent P inp o g acc comp labels) start = .ok mid)
    (hnd : (g.edges.map (·.decl)).Nodup)
    (packed : Pack.State)
    (hpack : PipelineImpl.packAcc P o mid = .ok out)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × PipelineImpl.Part) × Rect)
    (hget_pair : (mid.parts.zip packed.boxes)[c]? = some q)
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget_route : q.1.2.routes[i]? = some (k, pts))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    (hsize : k < mid.routes.size) :
    out.routes.getD k d = pts.map (PipelineImpl.shiftPoint q.2.x q.2.y) := by
  have hsel : (mid.parts.zip packed.boxes)[c]? = some (q.1, q.2) := hget_pair
  have hmem : k ∈ q.1.2.routes.map (·.1) := by
    have hp : (k, pts) ∈ q.1.2.routes := List.mem_iff_getElem?.mpr ⟨i, hget_route⟩
    exact List.mem_map_of_mem hp
  refine packAcc_routes_getD hpack packed hpacked c q hget_pair i k pts d hget_route hnodup hsize ?_
  intro q' hq'
  exact PipelineImpl.actual_components_zip_later_route_key_ne hempty hfold hnd hsel hmem hq'

def routePointTransport := PipelineImpl.routePointTransport

theorem routePointTransport_eq (margin : Int) (d : Direction) (h : Int) (boxX boxY minX minY : Int) (pts : List Point) :
    ((pts.map (PipelineImpl.shiftPoint (0 - minX) (0 - minY))).map (PipelineImpl.shiftPoint boxX boxY)).map
      (fun p => PipelineImpl.shiftPoint margin margin (PipelineImpl.orientPoint d h p)) =
    pts.map (routePointTransport margin d h boxX boxY minX minY) :=
  PipelineImpl.routePointTransport_eq margin d h boxX boxY minX minY pts

theorem sceneOf_routes_length (P : PipelineImpl.Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : PipelineImpl.Acc) (measured : List PipelineImpl.MeasuredLabel) :
    (PipelineImpl.sceneOf P inp o lines acc measured).routes.length = inp.routes.length :=
  PipelineImpl.sceneOf_routes_length P inp o lines acc measured

theorem sceneOf_routes_getElem? (P : PipelineImpl.Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : PipelineImpl.Acc) (measured : List PipelineImpl.MeasuredLabel)
    (k : Nat) (hk : k < inp.routes.length) :
    (PipelineImpl.sceneOf P inp o lines acc measured).routes[k]? =
      some ⟨(inp.routes[k]).id, (inp.routes[k]).fromId, (inp.routes[k]).toId, (inp.routes[k]).orthogonal,
        (acc.routes.getD k []).map (fun p =>
          PipelineImpl.shiftPoint P.canvasMargin
            P.canvasMargin
            (PipelineImpl.orientPoint o.direction acc.canvasH p))⟩ :=
  PipelineImpl.sceneOf_routes_getElem? P inp o lines acc measured k hk

theorem sceneOf_route_id (P : PipelineImpl.Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : PipelineImpl.Acc) (measured : List PipelineImpl.MeasuredLabel)
    (k : Nat) (hk : k < inp.routes.length) :
    ((PipelineImpl.sceneOf P inp o lines acc measured).routes[k]?).map (·.id) =
      some (inp.routes[k]).id :=
  PipelineImpl.sceneOf_route_id P inp o lines acc measured k hk

theorem sceneOf_route_points (P : PipelineImpl.Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : PipelineImpl.Acc) (measured : List PipelineImpl.MeasuredLabel)
    (k : Nat) (hk : k < inp.routes.length) :
    ((PipelineImpl.sceneOf P inp o lines acc measured).routes[k]?).map (·.points) =
      some ((acc.routes.getD k []).map (fun p =>
        PipelineImpl.shiftPoint P.canvasMargin
          P.canvasMargin
          (PipelineImpl.orientPoint o.direction acc.canvasH p))) :=
  PipelineImpl.sceneOf_route_points P inp o lines acc measured k hk

theorem sceneOf_routes_ids (P : PipelineImpl.Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : PipelineImpl.Acc) (measured : List PipelineImpl.MeasuredLabel) :
    (PipelineImpl.sceneOf P inp o lines acc measured).routes.map (·.id) = inp.routes.map (·.id) :=
  PipelineImpl.sceneOf_routes_ids P inp o lines acc measured

theorem sceneOf_route_of_pack (P : PipelineImpl.Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (out : PipelineImpl.Acc) (measured : List PipelineImpl.MeasuredLabel)
    (k : Nat) (hk : k < inp.routes.length)
    (pts : List Point)
    (hroutes : out.routes.getD k [] = pts) :
    (PipelineImpl.sceneOf P inp o lines out measured).routes[k]? =
      some ⟨(inp.routes[k]).id, (inp.routes[k]).fromId, (inp.routes[k]).toId, (inp.routes[k]).orthogonal,
        pts.map (fun p =>
          PipelineImpl.shiftPoint P.canvasMargin
            P.canvasMargin
            (PipelineImpl.orientPoint o.direction out.canvasH p))⟩ :=
  PipelineImpl.sceneOf_route_of_pack P inp o lines out measured k hk pts hroutes

theorem sceneOf_route_entry_of_producer {P : PipelineImpl.Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {cg : Graph} {run : PipelineImpl.Run}
    {labels : List PipelineImpl.MeasuredLabel} {orderOptions : OrderOptions}
    {loops : List (Nat × LoopPlacement)}
    (hrun : PipelineImpl.componentRun P cg labels orderOptions = .ok run)
    (i : Nat) (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (out : PipelineImpl.Acc) (measured : List PipelineImpl.MeasuredLabel)
    (b : PipelineImpl.Bounds) (hb : b = PipelineImpl.placeBounds P cg run labels loops)
    (box : Rect)
    (hroutes : out.routes.getD (cg.edges[i]).decl [] =
      ((run.routes[i]'(by
        rw [PipelineImpl.componentRun_routes_length hrun, PipelineImpl.componentRun_proper_chains_length hrun]
        exact hi)).points.map
        (PipelineImpl.shiftPoint (0 - b.minX) (0 - b.minY))).map (PipelineImpl.shiftPoint box.x box.y))
    (hk : (cg.edges[i]).decl < inp.routes.length) :
    let margin := P.canvasMargin
    (PipelineImpl.sceneOf P inp o lines out measured).routes[(cg.edges[i]).decl]? =
      some ⟨(inp.routes[(cg.edges[i]).decl]).id,
        (inp.routes[(cg.edges[i]).decl]).fromId,
        (inp.routes[(cg.edges[i]).decl]).toId,
        (inp.routes[(cg.edges[i]).decl]).orthogonal,
        (run.routes[i]'(by
          rw [PipelineImpl.componentRun_routes_length hrun, PipelineImpl.componentRun_proper_chains_length hrun]
          exact hi)).points.map
          (routePointTransport margin o.direction out.canvasH box.x box.y b.minX b.minY)⟩ :=
  PipelineImpl.sceneOf_route_entry_of_producer hrun i hi hloop out measured b hb box hroutes hk

theorem sceneOf_route_entry_of_single_part {P : PipelineImpl.Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {comp : List Nat} {cg : Graph} {run : PipelineImpl.Run}
    {labels : List PipelineImpl.MeasuredLabel} {orderOptions : OrderOptions}
    {loops : List (Nat × LoopPlacement)}
    {acc out : PipelineImpl.Acc} (packed : Pack.State)
    (box : Rect)
    (hpack : PipelineImpl.packAcc P o acc = .ok out)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (acc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (part : PipelineImpl.Part)
    (hpairs : acc.parts.zip packed.boxes = [((comp, part), box)])
    (hpart_routes : part.routes = (PipelineImpl.placeComponent P cg run 0 labels loops).routes)
    (hrun : PipelineImpl.componentRun P cg labels orderOptions = .ok run)
    (hnd : (cg.edges.map (·.decl)).Nodup)
    (i : Nat) (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (hsize : (cg.edges[i]).decl < acc.routes.size)
    (hk : (cg.edges[i]).decl < inp.routes.length)
    (measured : List PipelineImpl.MeasuredLabel) :
    let margin := P.canvasMargin
    let b := PipelineImpl.placeBounds P cg run labels loops
    (PipelineImpl.sceneOf P inp o lines out measured).routes[(cg.edges[i]).decl]? =
      some ⟨(inp.routes[(cg.edges[i]).decl]).id,
        (inp.routes[(cg.edges[i]).decl]).fromId,
        (inp.routes[(cg.edges[i]).decl]).toId,
        (inp.routes[(cg.edges[i]).decl]).orthogonal,
        (run.routes[i]'(by
          rw [PipelineImpl.componentRun_routes_length hrun, PipelineImpl.componentRun_proper_chains_length hrun]
          exact hi)).points.map
          (routePointTransport margin o.direction out.canvasH box.x box.y b.minX b.minY)⟩ :=
  PipelineImpl.sceneOf_route_entry_of_single_part packed box hpack hpacked part hpairs hpart_routes hrun hnd i hi hloop hsize hk measured

/-- Actual multi-part scene entry. For the part selected from the packed zip of the actual
component fold output, `ActualPart` supplies the run and loop witnesses of the candidate that
the portfolio selected for that part's own component, together with the equality between the
selected part's routes and that run's placed routes. The packed route array entry of a queried
component edge is that placed route shifted by the part's packed position, so the emitted scene
route entry carries the actual run's points under `routePointTransport`. The inner `∀` retains
exactly the conditions of `sceneOf_route_entry_of_single_part`: the component-edge index bound,
the non-loop condition of the queried edge, the packed route-array bound, and the input
route-array bound. The selected part's route-key `Nodup` is derived from the actual candidate
construction and the global edge declaration `Nodup`, and later noninterference is discharged by
the actual fold, so no singleton zip premise, no assumed `out.routes` lookup, and no
`hnot_after` premise is used. -/
theorem actual_components_sceneOf_route_entry
    {P : PipelineImpl.Params} {inp : Input} {o : Options} {g : Graph}
    {labels : List PipelineImpl.MeasuredLabel} {start mid out : PipelineImpl.Acc}
    (hempty : start.parts = [])
    (hfold : (PipelineImpl.components g).foldlM
      (fun acc comp => PipelineImpl.layoutComponent P inp o g acc comp labels) start = .ok mid)
    (hnd : (g.edges.map (·.decl)).Nodup)
    (packed : Pack.State)
    (hpack : PipelineImpl.packAcc P o mid = .ok out)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × PipelineImpl.Part) × Rect)
    (hget_pair : (mid.parts.zip packed.boxes)[c]? = some q)
    (lines : List (List Measure.Line))
    (measured : List PipelineImpl.MeasuredLabel) :
    ∃ index run loops,
      PipelineImpl.componentRun P (PipelineImpl.componentCandidate g q.1.1 index) labels
          (candidateOrder index) = .ok run ∧
      PipelineImpl.componentLoops P (PipelineImpl.componentCandidate g q.1.1 index) run labels
          = .ok loops ∧
      q.1.2.routes =
        (PipelineImpl.placeComponent P (PipelineImpl.componentCandidate g q.1.1 index) run 0
          labels loops).routes ∧
      ∀ (i : Nat) (hi : i < (PipelineImpl.componentCandidate g q.1.1 index).edges.length),
        (∀ l ∈ loops,
          l.1 ≠ ((PipelineImpl.componentCandidate g q.1.1 index).edges[i]).decl) →
        ((PipelineImpl.componentCandidate g q.1.1 index).edges[i]).decl < mid.routes.size →
        ∀ (hk : ((PipelineImpl.componentCandidate g q.1.1 index).edges[i]).decl <
          inp.routes.length),
        let margin := P.canvasMargin
        let b := PipelineImpl.placeBounds P (PipelineImpl.componentCandidate g q.1.1 index)
          run labels loops
        (PipelineImpl.sceneOf P inp o lines out measured).routes[
            ((PipelineImpl.componentCandidate g q.1.1 index).edges[i]).decl]? =
          some ⟨(inp.routes[((PipelineImpl.componentCandidate g q.1.1 index).edges[i]).decl]'hk).id,
            (inp.routes[((PipelineImpl.componentCandidate g q.1.1 index).edges[i]).decl]'hk).fromId,
            (inp.routes[((PipelineImpl.componentCandidate g q.1.1 index).edges[i]).decl]'hk).toId,
            (inp.routes[
              ((PipelineImpl.componentCandidate g q.1.1 index).edges[i]).decl]'hk).orthogonal,
            (PipelineImpl.edgePoints run i
              ((PipelineImpl.componentCandidate g q.1.1 index).edges[i])).map
              (routePointTransport margin o.direction out.canvasH q.2.x q.2.y b.minX b.minY)⟩ := by
  obtain ⟨_, hall⟩ := PipelineImpl.actual_components_parts hempty hfold
  have hparts : mid.parts[c]? = some q.1 := PipelineImpl.zip_getElem?_left hget_pair
  have hactual : PipelineImpl.ActualPart P inp o g labels q.1 :=
    hall q.1 (List.mem_iff_getElem?.mpr ⟨c, hparts⟩)
  obtain ⟨index, _, run, loops, _, _, _, hrun, hloops, hproutes⟩ := hactual
  refine ⟨index, run, loops, hrun, hloops, hproutes, ?_⟩
  intro i hi hloop hsize hk
  dsimp only
  have hnd_cand : ((PipelineImpl.componentCandidate g q.1.1 index).edges.map (·.decl)).Nodup :=
    PipelineImpl.componentCandidate_decls_nodup g q.1.1 index hnd
  have hnd_part : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hproutes]
    exact PipelineImpl.placeComponent_routes_decls_nodup P
      (PipelineImpl.componentCandidate g q.1.1 index) run 0 labels loops hnd_cand
  have hget_entry :=
    PipelineImpl.placeComponent_route_entry_of_producer hrun 0 loops i hi hloop
  rw [← hproutes] at hget_entry
  have hout := actual_components_packAcc_routes_getD hempty hfold hnd packed hpack hpacked
    c q hget_pair i _ _ [] hget_entry hnd_part hsize
  simpa only [PipelineImpl.componentRun_edgePoints_of_index hrun hi] using
    (sceneOf_route_entry_of_producer hrun i hi hloop out measured
      (PipelineImpl.placeBounds P (PipelineImpl.componentCandidate g q.1.1 index) run labels loops)
      rfl q.2 hout hk)
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
    ∃ P metric lines measured graph mid packed straight,
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
      PipelineImpl.straightenAcc inp packed = .ok straight ∧
      result.scene = PipelineImpl.sceneOf P inp o lines straight measured ∧
      result.budgetExhausted = straight.budget ∧
    result.itemArea = straight.parts.foldl (fun area part => area + part.2.area) 0 := by
  unfold PipelineImpl.layout at h
  obtain ⟨P, hP, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨metric, hm, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨lines, hl, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨measured, hmeasured, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨graph, hg, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨mid, hmid, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨packed, hpacked, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨straight, hstraight, h⟩ := PipelineImpl.bind_ok h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · have he := Except.ok.inj h
    subst result
    exact ⟨P, metric, lines, measured, graph, mid, packed, straight,
      hP, hm, hl, hmeasured, hg, hmid, hpacked, hstraight, rfl, rfl, rfl⟩

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
          split at h
          · cases h
          · split at h
            · cases h
            · have hwf : WellFormed (inputModel inp o) := by
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
    ∃ P lines measured graph mid out packed straight,
      PipelineImpl.measuredGraph P inp o lines = .ok graph ∧
      (graph.edges.map (·.decl)).Nodup ∧
      (PipelineImpl.components graph).foldlM
        (fun acc comp => PipelineImpl.layoutComponent P inp o graph acc comp measured)
        ⟨0, 0, 0, Array.replicate inp.boxes.length default,
          Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
          false, [], []⟩ = .ok mid ∧
      PipelineImpl.packAcc P o mid = .ok out ∧
      PipelineImpl.straightenAcc inp out = .ok straight ∧
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (mid.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed ∧
      packed.boxes.Pairwise Disjoint ∧
      result.scene = PipelineImpl.sceneOf P inp o lines straight measured := by
  obtain ⟨P, metric, lines, measured, graph, mid, out, straight,
    _, _, _, _, hg, hfold, hpack, hstraight, hscene, _, _⟩ := layout_success_phases h
  obtain ⟨packed, hpacked, hdisjoint⟩ := PipelineImpl.packAcc_components_disjoint hpack
  exact ⟨P, lines, measured, graph, mid, out, packed, straight, hg,
    PipelineImpl.measuredGraph_decls_nodup hg, hfold, hpack, hstraight, hpacked, hdisjoint, hscene⟩

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

theorem framedParents_parent {inp : Input} (h : framedParents inp = true)
    {box : ModelBox} (hbox : box ∈ inp.boxes) (hne : box.parent ≠ "") :
    ∃ parent ∈ inp.boxes, parent.id = box.parent ∧ parent.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == parent.id) = false := by
  unfold framedParents at h
  have hbox' := List.all_eq_true.mp h box hbox
  simp only [Bool.or_eq_true, beq_iff_eq] at hbox'
  rcases hbox' with hroot | hparent
  · exact absurd hroot hne
  · obtain ⟨parent, hmem, hcondition⟩ := List.any_eq_true.mp hparent
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcondition
    exact ⟨parent, hmem, hcondition.1.1, by simpa using hcondition.1.2, hcondition.2⟩

theorem layoutFamily_framed_parents {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) : framedParents inp = true := by
  by_cases hn : o.limits.maxNodes < inp.boxes.length <;>
    by_cases he : o.limits.maxEdges < inp.routes.length <;>
    by_cases ht : o.limits.maxTextBytes < inputTextBytes inp <;>
    by_cases hw : modelWellFormed (inputModel inp o) <;>
    by_cases hf : framedParents inp <;>
    simp_all [layoutFamily]

end Layered
end Elegant
