import Elegant.Layered.LabelsC7Bridges
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.ExecutedPortsFacts

set_option autoImplicit false

/-! # Executed label-run bridges

`LabelsC7Bridges.LabelBelongsToRun` is proved here outright from the executed
record `PipelineImpl.SceneExecution`: a measured scene label's rect is the
common transport (canvas margin, orientation, pack shelf shift, component
placement shift) of the placed rect `LabelsC7.routeLabelRect` of its own edge
in the executed component run of the component that owns the edge.

`LabelsC7Bridges.ExclusiveBoxInLabelRun` (the box half of the bridge, with
the same-run scope stated through the label's own edge) remains the one open
box residual: the free proper-edge-index form was false (see
`proofs/wip/Layered/ExclusiveBoxInLabelRunRefuted.lean`), and the
pinned-index variant once recorded at the bottom of this file is superseded
by the restated seam.
 -/

namespace Elegant.Layered

namespace PipelineImpl

/-! ## Small helpers -/

theorem findIdx?_lt {α : Type} {p : α → Bool} :
    ∀ (l : List α) (i : Nat), l.findIdx? p = some i → i < l.length := by
  intro l
  induction l with
  | nil =>
    intro i h
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons x xs ih =>
    intro i h
    rw [List.findIdx?_cons] at h
    split at h
    · simp at h
      subst h
      simp
    · cases hx : xs.findIdx? p with
      | none => rw [hx] at h; simp at h
      | some j =>
        rw [hx] at h
        simp at h
        have hbound := ih j hx
        have hlen : (x :: xs).length = xs.length + 1 := List.length_cons ..
        omega

theorem shiftRect_shiftRect (a b c d : Int) (r : Rect) :
    shiftRect a b (shiftRect c d r) = shiftRect (a + c) (b + d) r := by
  unfold shiftRect
  cases r
  simp only [Rect.mk.injEq]
  exact ⟨by ac_rfl, by ac_rfl, by trivial, by trivial⟩

/-! ## Measured-label source facts -/

/-- A measured label carries the position of its source label, so its index
bounds the source list and its edge bounds the route list. -/
theorem measureLabels_source {P : Params} {m : Measure.Metric} {target : Int}
    {inp : Input} {direction : Direction} {labels : List MeasuredLabel}
    (h : measureLabels P m target inp direction = .ok labels)
    {l : MeasuredLabel} (hl : l ∈ labels) :
    l.index < inp.labels.length ∧ l.edge < inp.routes.length := by
  unfold measureLabels at h
  obtain ⟨options, ho, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst labels
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ ho
  obtain ⟨opt, hopt, hlb⟩ := List.mem_filterMap.mp hl
  have hopt : some l ∈ options := by
    have he : opt = some l := by simpa using hlb
    exact he ▸ hopt
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hopt
  have hil : i < options.length := (List.getElem?_eq_some_iff.mp hi).1
  have his : i < inp.labels.zipIdx.length := by rw [← hlen]; exact hil
  have hget : inp.labels.zipIdx[i]? = some (inp.labels[i]'(by simpa using his), i) := by
    simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem (by simpa using his),
      Nat.zero_add, Option.map_some]
  obtain ⟨result, hr, hresult⟩ := hidx i _ hget
  rw [hi] at hresult
  have hrl : result = some l := (Option.some.inj hresult).symm
  subst hrl
  dsimp only at hr
  split at hr
  · change Except.ok none = Except.ok (some l) at hr
    cases hr
  · next edge heq =>
    obtain ⟨lines, _, hr⟩ := bind_ok hr
    have hilt := findIdx?_lt inp.routes edge heq
    by_cases hover :
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 ∨
        I32_MAX < (lines.length : Int) * P.lineH ∨
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 +
          (if m.profile == .cell then P.slot else 0) ∨
        I32_MAX < (lines.length : Int) * P.lineH +
          (if m.profile == .cell then P.slot else 0)
    · simp only [hover, ↓reduceIte] at hr
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hr
    · simp only [hover, ↓reduceIte] at hr
      cases direction <;>
        dsimp only at hr <;>
        have he := Option.some.inj (Except.ok.inj hr) <;>
        subst l
      all_goals exact ⟨by simpa using his, hilt⟩

/-- The measured list is the some-part of an option list aligned with the
label positions: each measured label records its position and route bound. -/
theorem measureLabels_position {P : Params} {m : Measure.Metric} {target : Int}
    {inp : Input} {direction : Direction} {labels : List MeasuredLabel}
    (h : measureLabels P m target inp direction = .ok labels) :
    ∃ options : List (Option MeasuredLabel),
      labels = options.filterMap id ∧
      (∀ (j : Nat) (x : MeasuredLabel), options[j]? = some x →
        x.index = j ∧ x.edge < inp.routes.length) := by
  unfold measureLabels at h
  obtain ⟨options, ho, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst labels
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ ho
  refine ⟨options, rfl, ?_⟩
  intro (j : Nat) (x : MeasuredLabel) hj
  have hjl : j < options.length := (List.getElem?_eq_some_iff.mp hj).1
  have his : j < inp.labels.zipIdx.length := hlen ▸ hjl
  have hget : inp.labels.zipIdx[j]? = some (inp.labels[j]'(by simpa using his), j) := by
    simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem (by simpa using his),
      Nat.zero_add, Option.map_some]
  obtain ⟨result, hr, hresult⟩ := hidx j (inp.labels[j]'(by simpa using his), j) hget
  rw [hj] at hresult
  have hrl : result = some x := (Option.some.inj hresult).symm
  subst hrl
  dsimp only at hr
  split at hr
  · change Except.ok none = Except.ok (some x) at hr
    cases hr
  · next edge heq =>
    obtain ⟨lines, _, hr⟩ := bind_ok hr
    have hilt := findIdx?_lt inp.routes edge heq
    by_cases hover :
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 ∨
        I32_MAX < (lines.length : Int) * P.lineH ∨
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 +
          (if m.profile == .cell then P.slot else 0) ∨
        I32_MAX < (lines.length : Int) * P.lineH +
          (if m.profile == .cell then P.slot else 0)
    · simp only [hover, ↓reduceIte] at hr
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hr
    · simp only [hover, ↓reduceIte] at hr
      cases direction <;>
        dsimp only at hr <;>
        have he := Option.some.inj (Except.ok.inj hr) <;>
        subst x
      all_goals exact ⟨rfl, hilt⟩

/-- Distinct measured labels carry distinct indices. -/
private theorem filterMap_id_index_nodup (k : Nat) :
    ∀ (options : List (Option MeasuredLabel)),
      (∀ (j : Nat) (x : MeasuredLabel), options[j]? = some x → x.index = j + k) →
      ((options.filterMap id).map (·.index)).Nodup := by
  intro options
  induction options generalizing k with
  | nil => intro _; simp
  | cons opt rest ih =>
    intro hpos
    have hpos' : ∀ (j : Nat) (x : MeasuredLabel), rest[j]? = some x →
        x.index = j + (k + 1) := by
      intro (j : Nat) (x : MeasuredLabel) hj
      have h := hpos (j + 1) x (by rw [List.getElem?_cons_succ]; exact hj)
      omega
    have hrest := ih (k + 1) hpos'
    match hopt : opt with
    | none =>
      exact hrest
    | some x =>
      have hxk : x.index = k := by
        have h0 : (some x :: rest)[0]? = some (some x) := by
          rw [List.getElem?_cons_zero]
        have hh := hpos 0 x h0
        omega
      have hxmem : ∀ y ∈ rest.filterMap id, y.index ≠ x.index := by
        intro y hy hxy
        obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.mp hy
        have hwx : w = some y := by simpa using hwe
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hwx ▸ hw)
        have hyj : y.index = j + (k + 1) := hpos' j y hj
        omega
      refine List.nodup_cons.mpr ⟨?_, hrest⟩
      intro hmem
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
      exact (hxmem y hy) hyx

theorem measureLabels_index_nodup {P : Params} {m : Measure.Metric} {target : Int}
    {inp : Input} {direction : Direction} {labels : List MeasuredLabel}
    (h : measureLabels P m target inp direction = .ok labels) :
    (labels.map (·.index)).Nodup := by
  obtain ⟨options, hdef, hpos⟩ := measureLabels_position h
  subst labels
  exact filterMap_id_index_nodup 0 options (by
    intro (j : Nat) (x : MeasuredLabel) hj
    simpa using (hpos j x hj).1)


/-! ## Graph-edge and scene-emission transport -/

/-- Every measured label's edge is the declaration of a measured-graph edge:
routes map one-to-one onto prepared graph edges. -/
theorem measuredGraph_edge_decl {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (h : measuredGraph P inp o lines = .ok g)
    {ml : MeasuredLabel} (hedge : ml.edge < inp.routes.length) :
    ∃ ge ∈ g.edges, ge.decl = ml.edge := by
  unfold measuredGraph at h
  obtain ⟨nodes0, _, h⟩ := bind_ok h
  obtain ⟨edges, hedges, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨nodes, _, h⟩ := bind_ok h
  have hg := Except.ok.inj h
  have hdecls : g.edges.map (·.decl) = edges.map (·.decl) := by
    rw [hg.symm]
    exact Compound.prepare_decls _ _ _ _
  have hmem : ml.edge ∈ g.edges.map (·.decl) := by
    rw [hdecls, graphEdgesFrom_decls inp inp.routes 0 edges hedges]
    exact List.mem_range'.mpr ⟨ml.edge, hedge, by omega⟩
  obtain ⟨ge, hge, hde⟩ := List.mem_map.mp hmem
  exact ⟨ge, hge, hde⟩

/-- A measured scene label's rect is the canvas transport of the packed
label-array entry at its measured index. -/
theorem scene_label_rect {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {l : SceneLabel} {index : Nat}
    {source : ModelLabel} {measured : MeasuredLabel}
    (hwf : WellFormed (inputModel inp o))
    (hl : l ∈ res.scene.labels) (hin : inp.labels[index]? = some source)
    (hid : l.id = source.id)
    (hmeasured : execution.measured.find? (fun label => label.index == index) = some measured) :
    l.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.labels.getD measured.index default)) := by
  have hids : (inp.labels.map (·.id)).Nodup := labelIds_nodup hwf
  have hindex : index < inp.labels.length := (List.getElem?_eq_some_iff.mp hin).1
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  obtain ⟨q1, q2⟩ := q
  have hp : inp.labels[q2]? = some q1 := List.mem_zipIdx_iff_getElem?.mp hq
  have hq2l : q2 < inp.labels.length := (List.getElem?_eq_some_iff.mp hp).1
  rw [List.getElem?_eq_getElem hq2l] at hp
  rw [List.getElem?_eq_getElem hindex] at hin
  have hp : inp.labels[q2] = q1 := Option.some.inj hp
  have hin : inp.labels[index] = source := Option.some.inj hin
  have hkey : l.id = q1.id → q2 = index := by
    intro lid
    refine hids.eq_of_getElem_eq
      (by simpa only [List.length_map] using hq2l)
      (by simpa only [List.length_map] using hindex) ?_
    rw [List.getElem_map, List.getElem_map, hp, hin]
    exact lid.symm.trans hid
  dsimp only at hemitted
  split at hemitted
  · simp at hemitted
  · split at hemitted
    · next label hfind =>
      have lid : l.id = q1.id :=
        (congrArg (fun s => s.toLabel.id) (Option.some.inj hemitted)).symm
      have hq2 : q2 = index := hkey lid
      rw [hq2] at hfind
      have hlm : label = measured :=
        Option.some.inj (hfind.symm.trans hmeasured)
      have hr := (congrArg (fun s => s.toLabel.rect) (Option.some.inj hemitted)).symm
      dsimp only at hr
      rw [hlm] at hr
      exact hr
    · next hfind =>
      split at hemitted
      · simp at hemitted
      · next idx hidx =>
        have lid : l.id = q1.id :=
          (congrArg (fun s => s.toLabel.id) (Option.some.inj hemitted)).symm
        have hq2 : q2 = index := hkey lid
        rw [hq2] at hfind
        rw [hmeasured] at hfind
        cases hfind


/-! ## Component subgraphs, executed parts, and placed-label structure -/

/-- A graph edge whose tail lies in a reported component survives into that
component's subgraph with its declaration unchanged. -/
theorem componentGraph_decl_edge {g : Graph} {comp : List Nat} {ge : Edge}
    (hge : ge ∈ g.edges) (htail : comp.contains ge.tail = true) :
    ∃ ce ∈ (componentGraph g comp).edges, ce.decl = ge.decl := by
  unfold componentGraph
  refine ⟨{ ge with tail := comp.idxOf ge.tail, head := comp.idxOf ge.head },
    List.mem_map.mpr ⟨ge, List.mem_filter.mpr ⟨hge, by simpa using htail⟩, rfl⟩, rfl⟩

/-- Every declaration of a component subgraph edge survives into every
candidate graph, with an edge index. -/
theorem componentCandidate_decl_edge {g : Graph} {comp : List Nat} {index : Nat}
    {decl : Nat} (hmem : decl ∈ (componentGraph g comp).edges.map (·.decl)) :
    ∃ (i : Nat) (e : Edge), (componentCandidate g comp index).edges[i]? = some e ∧
      e.decl = decl := by
  have hmem' : decl ∈ (componentCandidate g comp index).edges.map (·.decl) := by
    rw [componentCandidate_decls]
    exact hmem
  obtain ⟨e, he, hde⟩ := List.mem_map.mp hmem'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
  exact ⟨i, e, hi, hde⟩

/-- Executed parts carry their component and run. -/
theorem execution_part_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {part : List Nat × Part}
    (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ (index : Nat) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int),
      part.1 ∈ components execution.graph ∧
      componentRun execution.params (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area } := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hm, hall⟩ := actual_components_parts_geometry hempty execution.components_eq
  obtain ⟨index, chosen, run, loops, area, _, _, _, hrun, _, heq⟩ := hall part hpart
  refine ⟨index, run, loops, area, ?_, hrun, heq⟩
  rw [← hm]
  exact List.mem_map_of_mem hpart

/-- Measured labels with equal indices are equal. -/
theorem measured_eq_of_index_eq : ∀ (labels : List MeasuredLabel),
    (labels.map (·.index)).Nodup → ∀ (a b : MeasuredLabel),
    a ∈ labels → b ∈ labels → a.index = b.index → a = b := by
  intro labels
  induction labels with
  | nil => intro _ a b ha; cases ha
  | cons m ms ih =>
    intro hnd a b ha hb hidx
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · have hbidx : b.index ∈ ms.map (·.index) := by
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb'
          exact List.mem_map_of_mem (f := (·.index)) (List.mem_of_getElem? hi)
        exact absurd hidx (fun h => (List.nodup_cons.mp hnd).1
          (by show a.index ∈ ms.map (·.index); rw [h]; exact hbidx))
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have haidx : a.index ∈ ms.map (·.index) := by
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha'
          exact List.mem_map_of_mem (f := (·.index)) (List.mem_of_getElem? hi)
        exact absurd hidx.symm (fun h => (List.nodup_cons.mp hnd).1
          (by show b.index ∈ ms.map (·.index); rw [h]; exact haidx))
      · exact ih (List.nodup_cons.mp hnd).2 a b ha' hb' hidx

/-- A placed pair comes from a measured label of its own edge, through the
executed find/lookup/envelope/stack chain. -/
theorem placedLabels_pair_inv {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} (hnd : (labels.map (·.index)).Nodup)
    {k : Nat} {r : Rect} (hmem : (k, r) ∈ placedLabels P cg run labels) :
    ∃ (ml : MeasuredLabel) (edge : Nat) (e : Edge) (env : Rect) (rect : Rect),
      ml ∈ labels ∧ ml.index = k ∧
      cg.edges.findIdx? (fun e => e.decl == ml.edge) = some edge ∧
      cg.edges[edge]? = some e ∧
      labelEnvelope P cg run labels edge e = some env ∧
      ((routeLabels labels e.decl).zip
        (Labels.stackRects env.x env.y cg.slot
          ((routeLabels labels e.decl).map fun q => (q.width, q.height)))).find?
        (fun q => q.1.index == ml.index) = some (ml, rect) ∧
      r = rect := by
  unfold placedLabels at hmem
  obtain ⟨ml, hml, hbind⟩ := List.mem_filterMap.mp hmem
  dsimp only at hbind
  obtain ⟨edge, h1, h2⟩ := Option.bind_eq_some_iff.mp hbind
  obtain ⟨e, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨env, h5, h6⟩ := Option.bind_eq_some_iff.mp h4
  obtain ⟨placed, h7, h8⟩ := Option.bind_eq_some_iff.mp h6
  have hpair : (ml.index, placed.2) = (k, r) := by
    simpa using h8
  have hinj : ml.index = k ∧ placed.2 = r := by simpa using hpair
  obtain ⟨hk, hr⟩ := hinj
  obtain ⟨ml', rect⟩ := placed
  have hfind : ((routeLabels labels e.decl).zip
      (Labels.stackRects env.x env.y cg.slot
        ((routeLabels labels e.decl).map fun q => (q.width, q.height)))).find?
      (fun q => q.1.index == ml.index) = some (ml', rect) := h7
  have hml' : ml' = ml := by
    have hpred := List.find?_some hfind
    have hmem' : (ml', rect) ∈ (routeLabels labels e.decl).zip
      (Labels.stackRects env.x env.y cg.slot
        ((routeLabels labels e.decl).map fun q => (q.width, q.height))) :=
      List.mem_of_find?_eq_some hfind
    have hml'mem : ml' ∈ labels :=
      mem_measured_of_mem_routeLabels (List.of_mem_zip hmem').1
    exact measured_eq_of_index_eq labels hnd ml' ml hml'mem hml (by
        simpa using hpred)
  subst hml'
  exact ⟨ml', edge, e, env, rect, hml, hk, h1, h3, h5, hfind, hr.symm⟩


/-! ## Label-array transport through the two folds -/

theorem labels_arr_getD_set!_self {arr : Array Rect} {i : Nat} {v : Rect}
    (h : i < arr.size) : (arr.set! i v).getD i default = v := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

theorem labels_arr_getD_set!_ne {arr : Array Rect} {i j : Nat} {v : Rect}
    (h : i ≠ j) : (arr.set! i v).getD j default = arr.getD j default := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne h]

/-- Folding writes that never target `k` leaves the entry unchanged. -/
theorem labels_set_foldl_getD_ne : ∀ (vals : List (Nat × Rect)) (arr : Array Rect)
    (k : Nat), (∀ p ∈ vals, p.1 ≠ k) →
    (vals.foldl (fun a q => a.set! q.1 q.2) arr).getD k default = arr.getD k default := by
  intro vals
  induction vals with
  | nil => intro arr k _; rfl
  | cons q vs ih =>
    intro arr k hne
    rw [List.foldl_cons,
      ih _ k (fun p hp => hne p (List.mem_cons_of_mem _ hp)),
      labels_arr_getD_set!_ne (hne q List.mem_cons_self)]

/-- Folding writes whose key-`k` pairs all carry `v` keeps the entry at `v`. -/
private theorem labels_set_foldl_keep : ∀ (vals : List (Nat × Rect)) (arr : Array Rect)
    (k : Nat) (v : Rect), k < arr.size → arr.getD k default = v →
    (∀ q ∈ vals, q.1 = k → q.2 = v) →
    (vals.foldl (fun a q => a.set! q.1 q.2) arr).getD k default = v := by
  intro vals
  induction vals with
  | nil => intro arr k v _ harr _; exact harr
  | cons q vs ih =>
    intro arr k v hk harr hval
    rw [List.foldl_cons]
    by_cases hqk : q.1 = k
    · refine ih _ k v ?_ ?_ (fun p hp => hval p (List.mem_cons_of_mem _ hp))
      · rw [Array.size_set!]; exact hk
      · rw [hqk, labels_arr_getD_set!_self hk]; exact hval q List.mem_cons_self hqk
    · refine ih _ k v ?_ ?_ (fun p hp => hval p (List.mem_cons_of_mem _ hp))
      · rw [Array.size_set!]; exact hk
      · rw [labels_arr_getD_set!_ne hqk]; exact harr

/-- One part's plain label writes install the pair value of any present key. -/
theorem labels_set_foldl_getD_mem : ∀ (vals : List (Nat × Rect)) (arr : Array Rect)
    (k : Nat) (r0 : Rect), (k, r0) ∈ vals →
    (∀ q₁ ∈ vals, ∀ q₂ ∈ vals, q₁.1 = k → q₂.1 = k → q₁.2 = q₂.2) →
    k < arr.size →
    (vals.foldl (fun a q => a.set! q.1 q.2) arr).getD k default = r0 := by
  intro vals
  induction vals with
  | nil => intro arr k r0 hmem; cases hmem
  | cons q vs ih =>
    intro arr k r0 hmem hdet hk
    rw [List.foldl_cons]
    by_cases hqk : q.1 = k
    · have hqr0 : q.2 = r0 := by
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact congrArg Prod.snd hhead.symm
        · exact (hdet (k, r0) (List.mem_cons.mpr (Or.inr htail)) q List.mem_cons_self rfl
            hqk).symm
      refine labels_set_foldl_keep vs _ k r0 ?_ ?_ ?_
      · rw [Array.size_set!]; exact hk
      · rw [hqk, labels_arr_getD_set!_self hk]; exact hqr0
      · intro p hp hpk
        exact ((hdet q List.mem_cons_self p (List.mem_cons_of_mem _ hp) hqk hpk).symm).trans
          hqr0
    · rcases List.mem_cons.mp hmem with hhead | htail
      · exact absurd (congrArg Prod.fst hhead.symm) hqk
      · refine ih _ k r0 ?_ ?_ ?_
        · exact htail
        · intro q₁ h₁ q₂ h₂ e₁ e₂
          exact hdet q₁ (List.mem_cons_of_mem _ h₁) q₂ (List.mem_cons_of_mem _ h₂) e₁ e₂
        · rw [Array.size_set!]; exact hk

/-- Folding translated writes that never target `k` leaves the entry. -/
theorem labels_shift_foldl_getD_ne (dx dy : Int) : ∀ (vals : List (Nat × Rect))
    (arr : Array Rect) (k : Nat), (∀ p ∈ vals, p.1 ≠ k) →
    (vals.foldl (fun a r => a.set! r.1 (shiftRect dx dy r.2)) arr).getD k default =
      arr.getD k default := by
  intro vals
  induction vals with
  | nil => intro arr k _; rfl
  | cons q vs ih =>
    intro arr k hne
    rw [List.foldl_cons,
      ih _ k (fun p hp => hne p (List.mem_cons_of_mem _ hp)),
      labels_arr_getD_set!_ne (hne q List.mem_cons_self)]

private theorem labels_shift_foldl_keep (dx dy : Int) : ∀ (vals : List (Nat × Rect))
    (arr : Array Rect) (k : Nat) (v : Rect), k < arr.size → arr.getD k default = v →
    (∀ q ∈ vals, q.1 = k → shiftRect dx dy q.2 = v) →
    (vals.foldl (fun a r => a.set! r.1 (shiftRect dx dy r.2)) arr).getD k default = v := by
  intro vals
  induction vals with
  | nil => intro arr k v _ harr _; exact harr
  | cons q vs ih =>
    intro arr k v hk harr hval
    rw [List.foldl_cons]
    by_cases hqk : q.1 = k
    · refine ih _ k v ?_ ?_ (fun p hp => hval p (List.mem_cons_of_mem _ hp))
      · rw [Array.size_set!]; exact hk
      · rw [hqk, labels_arr_getD_set!_self hk]; exact hval q List.mem_cons_self hqk
    · refine ih _ k v ?_ ?_ (fun p hp => hval p (List.mem_cons_of_mem _ hp))
      · rw [Array.size_set!]; exact hk
      · rw [labels_arr_getD_set!_ne hqk]; exact harr

/-- One part's pack-shifted label writes install the translated pair value. -/
theorem labels_shift_foldl_getD_mem (dx dy : Int) : ∀ (vals : List (Nat × Rect))
    (arr : Array Rect) (k : Nat) (r0 : Rect), (k, r0) ∈ vals →
    (∀ q₁ ∈ vals, ∀ q₂ ∈ vals, q₁.1 = k → q₂.1 = k → q₁.2 = q₂.2) →
    k < arr.size →
    (vals.foldl (fun a r => a.set! r.1 (shiftRect dx dy r.2)) arr).getD k default =
      shiftRect dx dy r0 := by
  intro vals
  induction vals with
  | nil => intro arr k r0 hmem; cases hmem
  | cons q vs ih =>
    intro arr k r0 hmem hdet hk
    rw [List.foldl_cons]
    by_cases hqk : q.1 = k
    · have hqr0 : q.2 = r0 := by
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact congrArg Prod.snd hhead.symm
        · exact (hdet (k, r0) (List.mem_cons.mpr (Or.inr htail)) q List.mem_cons_self rfl
            hqk).symm
      refine labels_shift_foldl_keep dx dy vs _ k (shiftRect dx dy r0) ?_ ?_ ?_
      · rw [Array.size_set!]; exact hk
      · rw [hqk, labels_arr_getD_set!_self hk, hqr0]
      · intro p hp hpk
        exact (((hdet q List.mem_cons_self p (List.mem_cons_of_mem _ hp) hqk hpk).symm).trans
          hqr0) ▸ rfl
    · rcases List.mem_cons.mp hmem with hhead | htail
      · exact absurd (congrArg Prod.fst hhead.symm) hqk
      · refine ih _ k r0 ?_ ?_ ?_
        · exact htail
        · intro q₁ h₁ q₂ h₂ e₁ e₂
          exact hdet q₁ (List.mem_cons_of_mem _ h₁) q₂ (List.mem_cons_of_mem _ h₂) e₁ e₂
        · rw [Array.size_set!]; exact hk



/-! ## The component-fold label transport -/

/-- One `placePart` appends exactly one part and folds its label pairs into
the accumulator. -/
theorem placePart_labels_step {P : Params} {comp : List Nat} {cg : Graph} {run : Run}
    {acc acc' : Acc} {labels : List MeasuredLabel}
    (h : placePart comp cg run P acc labels = .ok acc') :
    ∃ part : Part,
      acc'.parts = acc.parts ++ [(comp, part)] ∧
      acc'.labels = part.labels.foldl (fun a q => a.set! q.1 q.2) acc.labels := by
  unfold placePart at h
  obtain ⟨loops, hloops, hres⟩ := bind_ok h
  dsimp only at hres
  split at hres
  · simp at hres
  · have hok := Except.ok.inj hres
    apply Exists.intro
    exact ⟨Eq.symm (congrArg Acc.parts hok), Eq.symm (congrArg Acc.labels hok)⟩

/-- One `layoutComponent` step appends exactly one part (with only its
bookkeeping area changed) and folds its label pairs into the accumulator. -/
theorem layoutComponent_labels_step {P : Params} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp measured = .ok acc') :
    ∃ (part : Part) (area : Int),
      acc'.labels = part.labels.foldl (fun a q => a.set! q.1 q.2) acc.labels ∧
      acc'.parts = acc.parts ++ [(comp, { part with area := area })] ∧
      acc.labels.size = acc'.labels.size := by
  have hsizes := (layoutComponent_sizes h).2.2
  unfold layoutComponent at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨result, hres, h⟩ := bind_ok h
  obtain ⟨part, hparts, hlab⟩ := placePart_labels_step hres
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hdrop : result.parts.drop acc.parts.length = [(comp, part)] := by
    rw [hparts]; simp
  have hpp := (congrArg Acc.parts he).symm
  dsimp only at hpp
  rw [hdrop, List.map_cons, List.map_nil] at hpp
  have hll := (congrArg Acc.labels he).symm
  dsimp only at hll
  exact ⟨part, _, hll.trans hlab, hpp, hsizes⟩

private theorem fold_parts_structure {P : Params} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out →
      ∃ parts, out.parts = start.parts ++ parts ∧ parts.map (·.1) = comps := by
  intro comps
  induction comps with
  | nil =>
    intro start out h
    rw [List.foldlM_nil] at h
    have houtEq : start = out := Except.ok.inj h
    refine ⟨[], ?_, rfl⟩
    rw [← houtEq, List.append_nil]
  | cons comp comps ih =>
    intro start out h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    obtain ⟨part0, area0, _, hmidParts, _⟩ := layoutComponent_labels_step hmid
    obtain ⟨parts, hout, hmap⟩ := ih mid out hrest
    refine ⟨(comp, { part0 with area := area0 }) :: parts, ?_, ?_⟩
    · rw [hout, hmidParts, List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, hmap]

/-- The iterated component fold: with cross-part and within-part label-key
uniqueness, the final label array carries the pair value of the unique
carrying part at a position after which no other carrier appears; when no
part of this fold's components carries the key, the initial entry survives. -/
theorem fold_labels_value {P : Params} {inp : Input} {o : Options} {g : Graph}
    {measured : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc) (k : Nat),
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp measured) start = .ok out →
      k < start.labels.size →
      (∀ p ∈ start.parts, p.1 ∉ comps) →
      comps.Nodup →
      (∀ (p₁ p₂ : List Nat × Part) (r₁ r₂ : Rect),
        (k, r₁) ∈ p₁.2.labels → (k, r₂) ∈ p₂.2.labels → p₁.1 ≠ p₂.1 → False) →
      (∀ (p : List Nat × Part) (r₁ r₂ : Rect),
        (k, r₁) ∈ p.2.labels → (k, r₂) ∈ p.2.labels → r₁ = r₂) →
      ((∃ (r0 : Rect), ∃ p ∈ out.parts, (k, r0) ∈ p.2.labels ∧ p.1 ∈ comps) →
        ∃ (c : Nat) (part : List Nat × Part) (r0 : Rect),
          out.parts[c]? = some part ∧ (k, r0) ∈ part.2.labels ∧
          out.labels.getD k default = r0 ∧
          (∀ q ∈ out.parts.drop (c + 1), ∀ r, (k, r) ∉ q.2.labels)) ∧
      ((∀ p ∈ out.parts, p.1 ∈ comps → ∀ r, (k, r) ∉ p.2.labels) →
        out.labels.getD k default = start.labels.getD k default) := by
  intro comps
  induction comps with
  | nil =>
    intro start out k hfold _ _ _ _ _
    rw [List.foldlM_nil] at hfold
    have houtEq : start = out := Except.ok.inj hfold
    refine ⟨fun hcar => ?_, fun _ => ?_⟩
    · obtain ⟨r0, p, hp, hkr, hpin⟩ := hcar
      exact absurd hpin (by simp)
    · rw [← houtEq]
  | cons comp comps ih =>
    intro start out k hfold hsize hstart hnd huni hpartdet
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := bind_ok hfold
    obtain ⟨part0, area0, hmidLabels, hmidParts, hmidSize⟩ :=
      layoutComponent_labels_step hmid
    have hpnewlabels : ({ part0 with area := area0 } : Part).labels = part0.labels := rfl
    obtain ⟨appended', houtparts', happended'⟩ :=
      fold_parts_structure comps mid out hrest
    have hcomptail : comp ∉ comps := (List.nodup_cons.mp hnd).1
    have hnd' : comps.Nodup := (List.nodup_cons.mp hnd).2
    have hsizeMid : k < mid.labels.size := by rw [← hmidSize]; exact hsize
    have houtstruct : out.parts = start.parts ++ ((comp, { part0 with area := area0 }) :: appended') := by
      rw [houtparts', hmidParts, List.append_assoc, List.singleton_append]
    have hstart' : ∀ p ∈ mid.parts, p.1 ∉ comps := by
      intro p hp
      rw [hmidParts] at hp
      rcases List.mem_append.mp hp with hp' | hp'
      · intro hcin
        exact hstart p hp' (List.mem_cons_of_mem _ hcin)
      · have hp1 : p.1 = comp := by rw [List.mem_singleton.mp hp']
        intro hcin
        exact hcomptail (hp1 ▸ hcin)
    have hih := ih mid out k hrest hsizeMid hstart' hnd' huni hpartdet
    by_cases hcarnew : ∃ r, (k, r) ∈ part0.labels
    · obtain ⟨rnew, hrnew⟩ := hcarnew
      have htailclean : ∀ p ∈ out.parts, p.1 ∈ comps → ∀ r, (k, r) ∉ p.2.labels := by
        intro p hp hpin r hkr
        have hpne : p.1 ≠ comp := fun h => hcomptail (h ▸ hpin)
        exact huni p (comp, { part0 with area := area0 }) r rnew hkr
          (by rw [hpnewlabels]; exact hrnew) hpne
      have hdetp : ∀ q₁ ∈ part0.labels, ∀ q₂ ∈ part0.labels, q₁.1 = k → q₂.1 = k →
          q₁.2 = q₂.2 := by
        intro q₁ h₁ q₂ h₂ e₁ e₂
        have ha : (k, q₁.2) ∈ (comp, part0).2.labels := by
          have hq : (q₁.1, q₁.2) ∈ part0.labels := h₁
          rw [e₁] at hq
          exact hq
        have hb : (k, q₂.2) ∈ (comp, part0).2.labels := by
          have hq : (q₂.1, q₂.2) ∈ part0.labels := h₂
          rw [e₂] at hq
          exact hq
        exact hpartdet (comp, part0) q₁.2 q₂.2 ha hb
      have hval : out.labels.getD k default = rnew := by
        rw [hih.2 htailclean, hmidLabels,
          labels_set_foldl_getD_mem part0.labels start.labels k rnew hrnew hdetp hsize]
      refine ⟨fun _ => ⟨start.parts.length, (comp, { part0 with area := area0 }), rnew,
        ?_, ?_, hval, ?_⟩, fun hall =>
          (hall (comp, { part0 with area := area0 })
            (by rw [houtstruct]; exact List.mem_append.mpr (Or.inr List.mem_cons_self))
            List.mem_cons_self rnew (by rw [hpnewlabels]; exact hrnew)).elim⟩
      · rw [houtstruct, List.getElem?_append]
        by_cases hlt : start.parts.length < start.parts.length
        · omega
        · simp only [hlt, ite_false, Nat.sub_self, List.getElem?_cons_zero]
      · rw [hpnewlabels]; exact hrnew
      · intro q hq r hkr
        have hqapp : q ∈ appended' := by
          have hdrop : out.parts.drop (start.parts.length + 1) = appended' := by
            rw [houtstruct, List.drop_append]
            have h1 : start.parts.drop (start.parts.length + 1) = [] := by simp
            rw [h1, Nat.add_sub_cancel_left, List.nil_append]
            simp
          rw [hdrop] at hq
          exact hq
        exact htailclean q (by
          rw [houtstruct]
          exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hqapp)))
          (by rw [← happended']; exact List.mem_map_of_mem (f := (·.1)) hqapp) r hkr
    · have hpnewclean : ∀ r, (k, r) ∉ part0.labels := by
        intro r hkr
        exact hcarnew ⟨r, hkr⟩
      refine ⟨?_, ?_⟩
      · intro hcar
        obtain ⟨r0, p, hp, hkr, hpin⟩ := hcar
        rcases List.mem_cons.mp hpin with h | h
        · exfalso
          have hpnotstart : p ∉ start.parts := fun hpst =>
            hstart p hpst (h ▸ List.mem_cons_self)
          rw [houtstruct] at hp
          rcases List.mem_append.mp hp with hst | hnew
          · exact hpnotstart hst
          · rcases List.mem_cons.mp hnew with h' | hmem
            · subst h'
              have hkr' : (k, r0) ∈ ({ part0 with area := area0 } : Part).labels := hkr
              rw [hpnewlabels] at hkr'
              exact hpnewclean r0 hkr'
            · have hpin2 : p.1 ∈ comps := by
                rw [← happended']
                exact List.mem_map_of_mem (f := (·.1)) hmem
              rw [h] at hpin2
              exact hcomptail hpin2
        · exact hih.1 ⟨r0, p, hp, hkr, h⟩
      · intro hall
        rw [hih.2 (fun p hp hpin => hall p hp (List.mem_cons_of_mem _ hpin)),
          hmidLabels, labels_set_foldl_getD_ne part0.labels start.labels k
            (fun p hp he => hpnewclean p.2 (by rw [← he]; exact hp))]


/-- Placed pairs with the same index carry the same rect: the measured label
is unique by index, and every later stage of the pairing is a function. -/
theorem placedLabels_det {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} (hnd : (labels.map (·.index)).Nodup)
    {k : Nat} {r₁ r₂ : Rect}
    (h₁ : (k, r₁) ∈ placedLabels P cg run labels)
    (h₂ : (k, r₂) ∈ placedLabels P cg run labels) : r₁ = r₂ := by
  obtain ⟨ml₁, edge₁, e₁, env₁, rect₁, hm₁, hk₁, hf₁, he₁, henv₁, hfind₁, hr₁⟩ :=
    placedLabels_pair_inv hnd h₁
  obtain ⟨ml₂, edge₂, e₂, env₂, rect₂, hm₂, hk₂, hf₂, he₂, henv₂, hfind₂, hr₂⟩ :=
    placedLabels_pair_inv hnd h₂
  have hml : ml₁ = ml₂ :=
    measured_eq_of_index_eq labels hnd ml₁ ml₂ hm₁ hm₂ (by rw [hk₁, hk₂])
  subst hml
  have hedge : edge₁ = edge₂ := Option.some.inj (hf₁.symm.trans hf₂)
  subst hedge
  have he : e₁ = e₂ := Option.some.inj (he₁.symm.trans he₂)
  subst he
  have henv : env₁ = env₂ := Option.some.inj (henv₁.symm.trans henv₂)
  subst henv
  have hrect : rect₁ = rect₂ :=
    congrArg Prod.snd (Option.some.inj (hfind₁.symm.trans hfind₂))
  rw [hr₁, hr₂, hrect]

/-- `routeLabelRect` of a placed measured label. -/
theorem routeLabelRect_of_mem {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} (hnd : (labels.map (·.index)).Nodup)
    {l : MeasuredLabel} {rect : Rect}
    (hmem : (l.index, rect) ∈ placedLabels P cg run labels) :
    routeLabelRect P cg run labels l = rect :=
  routeLabelRect_eq hmem (fun q hq hq1 => by
    have hq2 : (q.1, q.2) ∈ placedLabels P cg run labels := by simpa using hq
    rw [hq1] at hq2
    exact (placedLabels_det hnd hmem hq2).symm)

/-- The labels a part stores are the placed pairs shifted by the placement
bounds negated (cursor `0`). -/
theorem placeComponent_labels_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} :
    (placeComponent P cg run 0 labels loops).labels =
      (placedLabels P cg run labels).map (fun q =>
        (q.1, shiftRect (0 - (placeBounds P cg run labels loops).minX)
          (0 - (placeBounds P cg run labels loops).minY) q.2)) := rfl


/-- A shifted write fold either writes the entry from one of its pairs or
leaves it untouched. -/
theorem labels_shift_foldl_getD (dx dy : Int) : ∀ (vals : List (Nat × Rect))
    (arr : Array Rect) (i : Nat) (r : Rect), i < arr.size →
    (vals.foldl (fun a e => a.set! e.1 (shiftRect dx dy e.2)) arr).getD i default = r →
    (∃ e ∈ vals, e.1 = i ∧ r = shiftRect dx dy e.2) ∨
      ((∀ e ∈ vals, e.1 ≠ i) ∧ arr.getD i default = r) := by
  intro vals
  induction vals with
  | nil =>
    intro arr i r _ h
    exact Or.inr ⟨by simp, h⟩
  | cons q vs ih =>
    intro arr i r hi h
    rw [List.foldl_cons] at h
    have hi' : i < (arr.set! q.1 (shiftRect dx dy q.2)).size := by
      rw [Array.size_set!]; exact hi
    rcases ih _ i r hi' h with ⟨e, he, h1, h2⟩ | ⟨hno, harr⟩
    · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩
    · by_cases hqi : q.1 = i
      · subst hqi
        have hshift : shiftRect dx dy q.2 = r := by
          rw [labels_arr_getD_set!_self hi] at harr
          exact harr
        exact Or.inl ⟨q, List.mem_cons_self, rfl, hshift.symm⟩
      · refine Or.inr ⟨?_, ?_⟩
        · intro e he h1
          rcases List.mem_cons.mp he with h | h
          · exact hqi (h ▸ h1)
          · exact hno e h h1
        · rw [labels_arr_getD_set!_ne hqi] at harr
          exact harr

/-- The packing fold's label array is the fold of the per-part shifted label
writes, in part order. -/
theorem pack_labels_eq_fold (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).labels =
      pairs.foldl (fun a q => q.1.2.labels.foldl
        (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) a) start.labels := by
  induction pairs generalizing start with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rfl

/-- Pack provenance for a label entry: it either comes from one part's
stored pair shifted by that part's shelf origin, or no part carries the
key and the pre-pack entry survives. -/
theorem packFold_labels_provenance : ∀ (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) (i : Nat) (r : Rect), i < start.labels.size →
    (pairs.foldl packStep start).labels.getD i default = r →
    (∃ q ∈ pairs, ∃ r0 : Rect, (i, r0) ∈ q.1.2.labels ∧
        r = shiftRect q.2.x q.2.y r0) ∨
      ((∀ q ∈ pairs, ∀ r0 : Rect, (i, r0) ∉ q.1.2.labels) ∧
        start.labels.getD i default = r) := by
  intro pairs
  induction pairs with
  | nil =>
    intro start i r _ h
    exact Or.inr ⟨by simp, h⟩
  | cons q rest ih =>
    intro start i r hi h
    rw [List.foldl_cons] at h
    have hi' : i < (packStep start q).labels.size := by
      rw [(packStep_sizes start q).2.2]; exact hi
    rcases ih _ i r hi' h with ⟨q', hq', r0, hmem, hr⟩ | ⟨hnorest, hstart⟩
    · exact Or.inl ⟨q', List.mem_cons_of_mem _ hq', r0, hmem, hr⟩
    · have hstep : (packStep start q).labels.getD i default = r := hstart
      change (q.1.2.labels.foldl (fun a e => a.set! e.1 (shiftRect q.2.x q.2.y e.2))
        start.labels).getD i default = r at hstep
      rcases labels_shift_foldl_getD q.2.x q.2.y q.1.2.labels start.labels i r hi hstep with
        ⟨e, he, h1, h2⟩ | ⟨hnoq, harr⟩
      · refine Or.inl ⟨q, List.mem_cons_self, e.2, ?_, ?_⟩
        · have hmem : (e.1, e.2) ∈ q.1.2.labels := he
          rw [h1] at hmem
          exact hmem
        · rw [h2]
      · refine Or.inr ⟨?_, harr⟩
        intro q' hq' r0 hmem
        rcases List.mem_cons.mp hq' with h | h
        · subst h
          apply hnoq (i, r0) hmem rfl
        · exact hnorest q' h r0 hmem

/-- The component fold preserves the label array size. -/
theorem components_fold_labels_size {P : Params} {inp : Input} {o : Options}
    {g : Graph} {labels : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp labels) start =
        .ok out → out.labels.size = start.labels.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    rw [components_fold_labels_size comps mid out hrest]
    exact (layoutComponent_sizes hmid).2.2.symm

/-- If no part of the fold output carries a key, the fold leaves that entry
at its starting value. -/
theorem fold_labels_getD_of_no_carry {P : Params} {inp : Input} {o : Options}
    {g : Graph} {labels : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc) (i : Nat),
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp labels) start =
        .ok out →
      (∀ p ∈ out.parts, ∀ r : Rect, (i, r) ∉ p.2.labels) →
      out.labels.getD i default = start.labels.getD i default := by
  intro comps
  induction comps with
  | nil =>
    intro start out i h _
    have he : start = out := Except.ok.inj h
    rw [he]
  | cons comp comps ih =>
    intro start out i h hno
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    obtain ⟨part0, area0, hmidLabels, hmidParts, _⟩ := layoutComponent_labels_step hmid
    obtain ⟨appended', houtparts', _⟩ := fold_parts_structure comps mid out hrest
    have hpartmem : (comp, { part0 with area := area0 }) ∈ out.parts := by
      rw [houtparts', hmidParts]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr List.mem_cons_self)))
    rw [ih mid out i hrest hno, hmidLabels,
      labels_set_foldl_getD_ne part0.labels start.labels i
        (fun p hp he => hno (comp, { part0 with area := area0 }) hpartmem p.2
          (by rw [← he]; exact hp))]

/-- Residual: route labels are placed in successful runs (one phase: the
executed `placedLabels` pairing is complete). For every successful component
run, each measured label on an edge present in the candidate graph has a
placed entry. True for executed layouts (the run builds label nodes for
every nonempty route edge and envelopes for every placed edge), strictly
simpler than the bridge goal, about the placement phase only, and pinned by
the `SceneExecution` run equation. Probed in
`proofs/wip/Probe/RouteLabelsPlacedProbe.lean`. -/
def RouteLabelsPlaced : Prop :=
  ∀ (P : Params) (cg : Graph) (labels : List MeasuredLabel)
    (orderOptions : OrderOptions) (run : Run) (l : MeasuredLabel)
    (edge : Nat) (e : Edge),
    componentRun P cg labels orderOptions = .ok run →
    cg.edges[edge]? = some e → l ∈ routeLabels labels e.decl →
    ∃ rect, (l.index, rect) ∈ placedLabels P cg run labels

/-- The executed label bridge: every measured scene label's rect is the
common transport of the placed rect of its own edge in the executed
component run of the component that owns the edge, pinned to the executed
pack shelf and placement shift. The no-carry case is vacuous by
`RouteLabelsPlaced`. -/
theorem labelBelongsToRun {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hroute_placed : RouteLabelsPlaced) : LabelBelongsToRun inp o res := by
  intro execution l index source measured hl hin hid hmeasured
  have hfindmem : measured ∈ execution.measured := List.mem_of_find?_eq_some hmeasured
  have hidxeq : measured.index = index := by
    simpa using List.find?_some hmeasured
  obtain ⟨hidxlt, hedgrt⟩ := measureLabels_source execution.measured_eq hfindmem
  have hnd : (execution.measured.map (·.index)).Nodup :=
    measureLabels_index_nodup execution.measured_eq
  have hscene := scene_label_rect execution hwf hl hin hid hmeasured
  have hpk := execution.packed_eq
  unfold packAcc at hpk
  obtain ⟨packedSt, hpack, hfold⟩ := bind_ok hpk
  have hpackedAcc : execution.packedAcc =
      (execution.componentsAcc.parts.zip packedSt.boxes).foldl packStep
        ({ execution.componentsAcc with canvasW := packedSt.width, canvasH := packedSt.height, titles := [] } : Acc) := (Except.ok.inj hfold).symm
  have hsizeComp : execution.componentsAcc.labels.size = inp.labels.length := by
    have h := components_fold_labels_size (components execution.graph) _ _
      execution.components_eq
    rw [h]
    simp
  have hprov := packFold_labels_provenance
    (execution.componentsAcc.parts.zip packedSt.boxes)
    ({ execution.componentsAcc with canvasW := packedSt.width, canvasH := packedSt.height, titles := [] } : Acc)
    measured.index (execution.packedAcc.labels.getD measured.index default)
    (by change measured.index < execution.componentsAcc.labels.size; rw [hsizeComp]; exact hidxlt)
    (by rw [hpackedAcc])
  rcases hprov with ⟨q, hqzip, r0, hmemlabels, hrpacked⟩ | ⟨hnocarryzip, hstartval⟩
  · have hqpart : q.1 ∈ execution.componentsAcc.parts := (List.of_mem_zip hqzip).1
    obtain ⟨cand, run, loops, area, hcomp, hrun, hpartdef⟩ :=
      execution_part_run execution hqpart
    have hplacedmem : (measured.index, r0) ∈
        (placeComponent execution.params (componentCandidate execution.graph q.1.1 cand)
          run 0 execution.measured loops).labels := by
      rw [hpartdef] at hmemlabels
      exact hmemlabels
    rw [placeComponent_labels_eq] at hplacedmem
    obtain ⟨pair, hpair, hpairEq⟩ := List.mem_map.mp hplacedmem
    have hpair1 : pair.1 = measured.index := congrArg Prod.fst hpairEq
    have hpair2 : shiftRect (0 - (placeBounds execution.params
          (componentCandidate execution.graph q.1.1 cand) run execution.measured
          loops).minX)
        (0 - (placeBounds execution.params
          (componentCandidate execution.graph q.1.1 cand) run execution.measured
          loops).minY) pair.2 = r0 := congrArg Prod.snd hpairEq
    have hplaced : (measured.index, pair.2) ∈
        placedLabels execution.params (componentCandidate execution.graph q.1.1 cand)
          run execution.measured := by
      have h : (pair.1, pair.2) ∈ placedLabels execution.params
          (componentCandidate execution.graph q.1.1 cand) run execution.measured := hpair
      rw [hpair1] at h
      exact h
    obtain ⟨ml, edge, e, env, rect, hmlmem, hmlidx, hfindex, hgetedge, henv,
      hfindstack, hreq⟩ := placedLabels_pair_inv hnd hplaced
    have hml : ml = measured :=
      measured_eq_of_index_eq execution.measured hnd ml measured hmlmem hfindmem
        (by rw [hmlidx])
    subst hml
    have hroutemem : ml ∈ routeLabels execution.measured e.decl :=
      (List.of_mem_zip (List.mem_of_find?_eq_some hfindstack)).1
    have hrouteRect : routeLabelRect execution.params
        (componentCandidate execution.graph q.1.1 cand) run execution.measured ml =
        pair.2 := routeLabelRect_of_mem hnd hplaced
    obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hqzip
    have hrect1 : l.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect (q.2.x + (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 cand) run execution.measured
            loops).minX))
            (q.2.y + (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 cand) run execution.measured
              loops).minY))
            (routeLabelRect execution.params
              (componentCandidate execution.graph q.1.1 cand) run execution.measured
              ml))) := by
      rw [hscene, hrouteRect, hrpacked, ← hpair2, shiftRect_shiftRect]
    have hlrect2 : l.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y r0)) := by
      rw [hscene, hrpacked]
    refine ⟨q.1.1, cand, run, candidateOrder cand,
      componentCandidate execution.graph q.1.1 cand, edge, e.decl,
      q.2.x + (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 cand) run execution.measured
        loops).minX),
      q.2.y + (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 cand) run execution.measured
        loops).minY),
      execution.params.canvasMargin, execution.packedAcc.canvasH, o.direction,
      packedSt, c, q.1, q.2, loops, area, (ml.index, r0),
      hcomp, rfl, hrun, rfl, by simp [hgetedge], hroutemem, hrect1,
      rfl, rfl, rfl, hpack, hc, rfl, hpartdef, rfl, rfl, hmemlabels, hlrect2⟩
  · have hnocarry : ∀ part ∈ execution.componentsAcc.parts, ∀ r : Rect,
        (measured.index, r) ∉ part.2.labels := by
      intro part hpart r hmem
      obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpart
      have hclen : c < execution.componentsAcc.parts.length :=
        (List.getElem?_eq_some_iff.mp hc).1
      have hboxlen : packedSt.boxes.length = execution.componentsAcc.parts.length := by
        rw [Pack.pack_count hpack, List.length_map]
      have hcbox : packedSt.boxes[c]? = some packedSt.boxes[c] :=
        List.getElem?_eq_getElem (by rw [hboxlen]; exact hclen)
      have hpair : (execution.componentsAcc.parts.zip packedSt.boxes)[c]? =
          some (part, packedSt.boxes[c]) := List.getElem?_zip_eq_some.mpr ⟨hc, hcbox⟩
      exact hnocarryzip (part, packedSt.boxes[c]) (List.mem_of_getElem? hpair) r hmem
    have hcompdef : execution.componentsAcc.labels.getD measured.index default = default := by
      rw [fold_labels_getD_of_no_carry (components execution.graph) _ _ _
        execution.components_eq hnocarry]
      change (Array.replicate inp.labels.length default).getD measured.index default = default
      unfold Array.getD
      split <;> simp
    have hpackeddef : execution.packedAcc.labels.getD measured.index default = default := by
      rw [← hstartval]
      exact hcompdef
    obtain ⟨ge, hge, hgedcl⟩ := measuredGraph_edge_decl execution.graph_eq hedgrt
    have htailbound : ge.tail < execution.graph.nodes.length :=
      (sceneExecution_edges_bounded execution ge
        (List.mem_append.mpr (Or.inl hge))).1
    obtain ⟨comp, hcomp, htailmem⟩ :=
      components_cover htailbound (sceneExecution_edges_bounded execution)
    have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ : Acc).parts = [] := rfl
    obtain ⟨hm, _⟩ := actual_components_parts_geometry hempty execution.components_eq
    have hcompmap : comp ∈ execution.componentsAcc.parts.map (·.1) := by
      rw [hm]; exact hcomp
    obtain ⟨part, hpartmem, hpartcomp⟩ := List.mem_map.mp hcompmap
    obtain ⟨cand, run, loops, area, _, hrun, hpartdef⟩ :=
      execution_part_run execution hpartmem
    have htailmem' : ge.tail ∈ part.1 := hpartcomp ▸ htailmem
    have htailcontains : part.1.contains ge.tail = true := by simpa using htailmem'
    obtain ⟨ce, hce, hcedcl⟩ := componentGraph_decl_edge hge htailcontains
    have hdeclmem : measured.edge ∈
        (componentGraph execution.graph part.1).edges.map (·.decl) :=
      List.mem_map.mpr ⟨ce, hce, hcedcl.trans hgedcl⟩
    obtain ⟨edge, e, hgetedge, hedef⟩ :=
      componentCandidate_decl_edge (index := cand) hdeclmem
    have hroutemem : measured ∈ routeLabels execution.measured e.decl :=
      List.mem_filter.mpr ⟨hfindmem, by simp [hedef]⟩
    have hnoplaced : ∀ qq ∈ placedLabels execution.params
        (componentCandidate execution.graph part.1 cand) run execution.measured,
        qq.1 ≠ measured.index := by
      intro qq hqq hq1
      have hpartqq : (measured.index, shiftRect (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 cand) run execution.measured
            loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 cand) run execution.measured
            loops).minY) qq.2) ∈ part.2.labels := by
        rw [hpartdef, placeComponent_labels_eq]
        exact List.mem_map.mpr ⟨qq, hqq, by rw [hq1]⟩
      exact hnocarry part hpartmem _ hpartqq
    have hroute0 : routeLabelRect execution.params
        (componentCandidate execution.graph part.1 cand) run execution.measured measured =
        ⟨0, 0, 0, 0⟩ := by
      unfold routeLabelRect
      have hfilter : (placedLabels execution.params
          (componentCandidate execution.graph part.1 cand) run execution.measured).filter
          (fun qq => qq.1 == measured.index) = [] := by
        rw [List.filter_eq_nil_iff]
        intro qq hqq hcond
        simp only [beq_iff_eq] at hcond
        exact hnoplaced qq hqq hcond
      rw [hfilter]
      rfl
    obtain ⟨rect, hmem⟩ := hroute_placed execution.params
      (componentCandidate execution.graph part.1 cand) execution.measured
      (candidateOrder cand) run measured edge e hrun hgetedge hroutemem
    exact False.elim (hnoplaced _ hmem rfl)

end PipelineImpl
end Elegant.Layered
