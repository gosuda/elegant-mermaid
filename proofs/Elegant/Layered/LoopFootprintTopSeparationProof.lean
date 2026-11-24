import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Coords
import Elegant.Layered.Labels
import Elegant.Layered.SceneBounds
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.ForeignNonGroupSpansProof

import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.LoopFootprintFactsProof
import Elegant.Layered.Route

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Loop footprint top separation

The footprint of a self-loop owned by a group top node (`border = -2`)
separates from every plain box frame. The proof works uniformly for all
plain-like frames (in-candidate plains, title copies, side markers,
routing dummies): with markers at the frame's rank (supplied by the closed
`bracketMarkersAtRank'`), a layer-index trichotomy puts the frame left of,
inside, or right of the marker pair; left/inside clear the hull's right
edge directly, and right clears it via the Coords-level gap (which reserves
the marker-carried loop extent) plus the right-marker alignment residual.

-/
/-- Local re-proof of the private `ComponentCoverage.componentCandidate_nodes_length`. -/
private theorem tsep_candidate_nodes_length (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Local copy of the private general `bind_ok`. -/
private theorem tsep_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => simp [hx, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [hx, Except.bind] using h⟩

/-- Local copy of the private `componentRun_exact_nil_general`. -/
private theorem tsep_exact_nil {P : Params} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (h : componentRun P cg labels orderOptions = .ok run) : run.exact = [] := by
  unfold componentRun at h
  obtain ⟨rr, _, h⟩ := tsep_bind_ok h
  obtain ⟨p0, _, h⟩ := tsep_bind_ok h
  obtain ⟨p, _, h⟩ := tsep_bind_ok h
  obtain ⟨ord, _, h⟩ := tsep_bind_ok h
  obtain ⟨xs, _, h⟩ := tsep_bind_ok h
  obtain ⟨routed, _, h⟩ := tsep_bind_ok h
  obtain ⟨lanes, _, h⟩ := tsep_bind_ok h
  obtain ⟨yt, _, h⟩ := tsep_bind_ok h
  obtain ⟨routes, _, h⟩ := tsep_bind_ok h
  have hfin := Except.ok.inj h
  subst hfin
  rfl

/-- Local copy of the private `componentCandidate_slot_general`. -/
private theorem tsep_slot (g : Graph) (component : List Nat)
    (candidate : Nat) :
    (componentCandidate g component candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

/-- Local copy of the private `lines_len_general`. -/
private theorem tsep_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- A degenerate-width frame is disjoint from every loop footprint. -/
private theorem tsep_sep_of_frame_oob {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hw : (frameRect default cg run b).w = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  omega

/-- A degenerate-height footprint is disjoint from every frame. -/
private theorem tsep_sep_of_foot_oob {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hh : (loopFootprint cg run labels v).h = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨-, hy⟩
  omega

/-- `fdiv` shifts over an added even part. -/
private theorem tsep_ediv_shift (w k : Int) :
    Int.fdiv (w + 2 * k) 2 = Int.fdiv w 2 + k := by
  have h2 : (0 : Int) ≤ 2 := by decide
  have hkk : (2 : Int) * k = k * 2 := by omega
  rw [hkk, Int.fdiv_eq_ediv_of_nonneg _ h2, Int.fdiv_eq_ediv_of_nonneg _ h2]
  exact Int.add_mul_ediv_right w k (by decide)

/-- Loop extents are nonnegative for nonnegative slots. -/
private theorem tsep_extent_nonneg {slot : Int} (hs : 0 ≤ slot)
    {sizes : List LoopLabel} (hw : ∀ l ∈ sizes, 0 ≤ l.width) :
    0 ≤ Loops.extent slot sizes := by
  have hsum : ∀ (xs : List Int) (z : Int), 0 ≤ z → (∀ x ∈ xs, 0 ≤ x) →
      0 ≤ xs.foldl (· + ·) z := by
    intro xs
    induction xs with
    | nil => intro z hz h; simpa using hz
    | cons y ys ih =>
      intro z hz h
      simp only [List.foldl_cons]
      have hy : 0 ≤ y := h y (List.mem_cons.mpr (Or.inl rfl))
      have hys : ∀ x ∈ ys, 0 ≤ x :=
        fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      exact ih (z + y) (by omega) hys
  unfold Loops.extent
  apply hsum _ 0 (by omega)
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨l, idx⟩ := p
  have hl : sizes[idx]? = some l :=
    List.mem_zipIdx_iff_getElem?.mp hp
  have h1 : 0 ≤ slot * ((idx : Int) + 2) :=
    Int.mul_nonneg hs (by omega)
  have h2 := hw l (List.mem_of_getElem? hl)
  simpa using Int.add_nonneg h1 h2
/-! ## Hull bounds -/

private theorem tsep_fold_right_mono (rs : List Rect) (b : Bounds) :
    b.right ≤ (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).right := by
  induction rs generalizing b with
  | nil => simp
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (by simp only; omega) (ih _)

private theorem tsep_fold_bottom_mono (rs : List Rect) (b : Bounds) :
    b.bottom ≤ (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).bottom := by
  induction rs generalizing b with
  | nil => simp
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (by simp only; omega) (ih _)

private theorem tsep_fold_miny_anti (rs : List Rect) (b : Bounds) :
    (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).minY ≤ b.minY := by
  induction rs generalizing b with
  | nil => simp
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (ih _) (by simp only; omega)

private theorem tsep_fold_right_mem (rs : List Rect) (b : Bounds) {r : Rect}
    (hmem : r ∈ rs) :
    r.x + r.w ≤ (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).right := by
  induction rs generalizing b with
  | nil => simp at hmem
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Int.le_trans (by simp only; omega) (tsep_fold_right_mono rest _)
    · exact ih _ hmem

private theorem tsep_fold_bottom_mem (rs : List Rect) (b : Bounds) {r : Rect}
    (hmem : r ∈ rs) :
    r.y + r.h ≤ (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).bottom := by
  induction rs generalizing b with
  | nil => simp at hmem
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Int.le_trans (by simp only; omega) (tsep_fold_bottom_mono rest _)
    · exact ih _ hmem

private theorem tsep_fold_miny_mem (rs : List Rect) (b : Bounds) {r : Rect}
    (hmem : r ∈ rs) :
    (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).minY ≤ r.y := by
  induction rs generalizing b with
  | nil => simp at hmem
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Int.le_trans (tsep_fold_miny_anti rest _) (by simp only; omega)
    · exact ih _ hmem

/-- Every border rectangle's right edge is at most the hull's right edge. -/
private theorem tsep_borders_right_ge {rs : List Rect} {r : Rect}
    (hmem : r ∈ rs) :
    r.x + r.w ≤ (boundsOf rs []).right := by
  cases rs with
  | nil => simp at hmem
  | cons r0 rest =>
    show r.x + r.w ≤ (((r0 :: rest).foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩)) (⟨r0.x, r0.y, 0, 0⟩ : Bounds)).right
    exact tsep_fold_right_mem _ _ hmem
/-- The folded bottom is at most `T` when every rectangle and the start are. -/
private theorem tsep_fold_bottom_le (rs : List Rect) (b : Bounds) {T : Int}
    (hbs : b.bottom ≤ T) (hall : ∀ r ∈ rs, r.y + r.h ≤ T) :
    (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).bottom ≤ T := by
  induction rs generalizing b with
  | nil => simpa using hbs
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    have hr0 := hall r0 (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ r ∈ rest, r.y + r.h ≤ T :=
      fun r hr => hall r (List.mem_cons.mpr (Or.inr hr))
    have hbs' : (⟨min b.minX r0.x, min b.minY r0.y, max b.right (r0.x + r0.w),
        max b.bottom (r0.y + r0.h)⟩ : Bounds).bottom ≤ T := by
      simp only
      omega
    exact ih _ hbs' hrest

/-- The folded top is at least `T` when every rectangle and the start are. -/
private theorem tsep_fold_miny_ge (rs : List Rect) (b : Bounds) {T : Int}
    (hbs : T ≤ b.minY) (hall : ∀ r ∈ rs, T ≤ r.y) :
    T ≤ (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).minY := by
  induction rs generalizing b with
  | nil => simpa using hbs
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    have hr0 := hall r0 (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ r ∈ rest, T ≤ r.y :=
      fun r hr => hall r (List.mem_cons.mpr (Or.inr hr))
    have hbs' : T ≤ (⟨min b.minX r0.x, min b.minY r0.y,
        max b.right (r0.x + r0.w),
        max b.bottom (r0.y + r0.h)⟩ : Bounds).minY := by
      simp only
      omega
    exact ih _ hbs' hrest

/-! ## Sizing value and frame equations -/

/-- Local copy of the private `graph_node_loopExtent_general`: an executed
graph node stores the exact loop extent of its own loop sizes. -/
private theorem tsep_graph_node_loopExtent {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecution inp o res) {m : Nat}
    (hm : m < e.lines.length) {gnode : Node}
    (hg : e.graph.nodes[m]? = some gnode) :
    gnode.loopExtent = (Loops.extent e.graph.slot
      (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
  have hlines : e.lines.length = inp.boxes.length := tsep_lines_len e
  have hmB : m < inp.boxes.length := by rw [← hlines]; exact hm
  obtain ⟨box, hbox⟩ : ∃ box, inp.boxes[m]? = some box :=
    ⟨_, List.getElem?_eq_getElem hmB⟩
  have hgE := e.graph_eq
  unfold measuredGraph at hgE
  obtain ⟨initial, hinitial, hgE⟩ := tsep_bind_ok hgE
  obtain ⟨edges, _, hgE⟩ := tsep_bind_ok hgE
  obtain ⟨metric, hmM, hgE⟩ := tsep_bind_ok hgE
  obtain ⟨labels, hlL, hgE⟩ := tsep_bind_ok hgE
  obtain ⟨nodes, hnodes, hgE⟩ := tsep_bind_ok hgE
  have hprepare := (Except.ok.inj hgE).symm
  let raw : Graph := { nodes := nodes, edges := edges, slot := e.params.slot }
  change e.graph = Compound.prepare _ e.params.clusterPad _ raw at hprepare
  have hemetric : metric = e.metric := Except.ok.inj (hmM.symm.trans e.metric_eq)
  subst hemetric
  have helabels : labels = e.measured :=
    Except.ok.inj (hlL.symm.trans e.measured_eq)
  subst helabels
  have hslotG : e.graph.slot = e.params.slot := by rw [hprepare]; exact rfl
  have hslotnn : 0 ≤ e.params.slot := by
    have hvalid := checkedParams_valid e.checked
    have h1 : 1 ≤ e.params.slot := hvalid.2.2.1
    omega
  have hwidths : ∀ l ∈ loopSizes edges e.measured m e.params.slot, 0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hextnn : 0 ≤ Loops.extent e.params.slot
      (loopSizes edges e.measured m e.params.slot) :=
    tsep_extent_nonneg hslotnn hwidths
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, _, hbefore⟩ :=
    hinit m (e.lines[m], m)
      (by simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hm,
        Option.map_some, Nat.zero_add])
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ :=
    hprocessed m (orientNode o.direction before, m)
      (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
        Option.map_some, Nat.zero_add])
  have hloop : after.loopExtent =
      (Loops.extent e.params.slot
        (loopSizes edges e.measured m e.params.slot)).toNat := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hstep
    by_cases hfixed : inp.fixedSizes.any
        (fun fixed => fixed.1 == box.id) = true
    · obtain ⟨entry, hfindE⟩ : ∃ entry, inp.fixedSizes.find?
          (fun fixed => fixed.1 == box.id) = some entry := by
        cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
        | none =>
          obtain ⟨e2, hmF, hid⟩ := List.any_eq_true.mp hfixed
          exact absurd (List.find?_eq_none.mp hf e2 hmF) (by rw [hid]; decide)
        | some e2 => exact ⟨e2, rfl⟩
      have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true :=
        hfixed
      simp [hbox, hfindE, hany] at hstep
      split at hstep
      · cases hstep
      · split at hstep
        · cases hstep
        · have he := Except.ok.inj hstep
          subst after
          rfl
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hfindN : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
        List.find?_eq_none.mpr (List.any_eq_false.mp hfixedF)
      by_cases hrole : box.role = .group
      · simp [hbox, hfindN, hrole, hfixedF] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · have he := Except.ok.inj hstep
            subst after
            rfl
      · have hroleN : box.role = .node := by
          match h : box.role with
          | .node => rfl
          | .group => exact absurd h hrole
        simp [hbox, hfindN, hroleN, hfixedF] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · have he := Except.ok.inj hstep
            subst after
            rfl
  have hinodes : m < nodes.length := (List.getElem?_eq_some_iff.mp hafter).1
  have hget : nodes[m]'hinodes = after := (List.getElem?_eq_some_iff.mp hafter).2
  have hraw : raw.nodes[m]? = some after := by
    simpa only [raw, List.getElem?_eq_getElem hinodes] using congrArg some hget
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := e.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * e.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  have hprepEq : e.graph = Compound.prepare boxes e.params.clusterPad titles raw :=
    hprepare
  have hbound : m < boxes.length := by
    simpa only [boxes, List.length_map] using hmB
  have hpe := prepare_loopSizes_preserved boxes e.params.clusterPad titles raw m
    hbound e.measured e.params.slot
  have heg : (Compound.prepare boxes e.params.clusterPad titles raw).edges =
      e.graph.edges := by
    rw [hprepEq]
  rw [heg] at hpe
  have hrawE : raw.edges = edges := rfl
  have hsizeq : loopSizes edges e.measured m e.params.slot =
      loopSizes e.graph.edges e.measured m e.graph.slot := by
    rw [hrawE] at hpe
    rw [← hpe, hslotG]
  have hloopG : after.loopExtent = (Loops.extent e.graph.slot
      (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
    rw [hloop, hsizeq, hslotG]
  have hclose : gnode.loopExtent = after.loopExtent →
      gnode.loopExtent = (Loops.extent e.graph.slot
        (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
    intro hll
    rw [hll, hloopG]
  by_cases hrole : box.role = .group
  · by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
    · have hmapped : boxes[m]? = some { box with role := .node } := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixed,
          ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hmapped rfl
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hboxM : boxes[m]? = some box := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      have hrec := Compound.prepare_group_title_record boxes e.params.clusterPad
        titles raw hinodes hboxM hrole
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = (raw.nodes[m]'hinodes).loopExtent := by
        rw [h2]
      have hRl : (raw.nodes[m]'hinodes).loopExtent = after.loopExtent := by
        simp only [raw, hget]
      exact hclose (hloopR.trans hRl)
  · have hroleN : box.role = .node := by
      match h : box.role with
      | .node => rfl
      | .group => exact absurd h hrole
    by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
    · have hmapped : boxes[m]? = some { box with role := .node } := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixed,
          ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hmapped rfl
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hboxM : boxes[m]? = some box := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hboxM hroleN
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR

/-! ## Frame equations and marker brackets -/

/-- The frame of a top node is its member/marker hull. -/
private theorem tsep_frame_hull {P : Params} {cg : Graph} {run : Run}
    {v : Nat} {nodeV : Node}
    (hget : cg.nodes.getD v default = nodeV) (hvB : nodeV.border = -2) :
    frameRect P cg run v =
      ⟨(boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some nodeV.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minX,
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains nodeV.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minY,
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some nodeV.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).right -
        (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some nodeV.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minX,
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains nodeV.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).bottom -
        (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains nodeV.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minY⟩ := by
  unfold frameRect
  simp only [hget, hvB, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]

/-- A candidate frame at a `border = 0` position is its node rect
(local copy; `LoopRectRealQProof` is currently unbuildable in this tree). -/
private theorem tsep_frame_node {P : Params} {cg : Graph} {run : Run}
    {v : Nat} {node : Node}
    (hget : cg.nodes.getD v default = node) (hb : node.border = 0) :
    frameRect P cg run v = nodeRect cg run v := by
  unfold frameRect
  simp only []
  rw [hget, hb]
  rfl

/-- The footprint of any node in an exact-free run. -/
private theorem tsep_foot_eq {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v : Nat}

    (hexact : run.exact = []) :
    loopFootprint cg run labels v =
      ⟨(frameRect default cg run v).x + (frameRect default cg run v).w,
        (frameRect default cg run v).y,
        Loops.extent cg.slot (loopSizes cg.edges labels v cg.slot),
        (frameRect default cg run v).h⟩ := by
  unfold loopFootprint
  have hcon : run.exact.contains v = false := by simp [hexact]
  simp only [hcon, Bool.false_eq_true, ↓reduceIte]


/-- Main theorem: the footprint of a group-top self-loop separates from every
plain box frame, modulo the open border-chain alignment seam `hx` (accepted:
the consumer already holds it) and the sliver residual above. Stated first
against transient case hypotheses; each is discharged below. -/
-- Good-position case: the plain box sits at or before the group's right
-- marker in its layer. Its frame then ends left of the marker's right edge by
-- the coordinate gap (which reserves the marker-carried loop extent), and the
-- marker rect lies inside the group's border hull. No alignment needed.
private theorem tsep_good_case
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
    (actualB : ProperNode) (mR : Nat) (nR : ProperNode)
    (hcomp : comp ∈ components e.graph)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop' : nodeV.border = -2)
    (hnodeB : (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB)
    (hb0' : nodeB.border = 0)
    (hbB0 : actualB.node.border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (hpropB : run.proper.nodes[b]? = some actualB)
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hxeqB : run.xs.getD b 0 = run.coordinateXs.getD b 0)
    (hcpmR : run.coordinateProper.nodes[mR]? = some nR)
    (hborderR : nR.node.border = 1)
    (hlastR : nR.node.clusterPath.getLast? = some nodeV.decl)
    (layer : List Nat) (hlayerMem : layer ∈ run.layers)
    (iv j : Nat) (hiv : layer[iv]? = some b) (hj : layer[j]? = some mR)
    (hlt : iv < j) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hexact := tsep_exact_nil hrun
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      nodeB := by
    simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
  have hframeV := frameRect_group_span (P := default) (run := run) hnodeV hvtop'
  have hframeB := tsep_frame_node (P := default) (run := run) hgetB hb0'
  have hfoot := tsep_foot_eq (cg := componentCandidate e.graph comp candidate)
    (run := run) (labels := e.measured) (v := v) hexact
  have hrb := rectAt_eq run.proper run.xs run.ys b
  have hrm := rectAt_eq run.proper run.xs run.ys mR
  obtain ⟨_, _, _, q0, _, _, _, _, hcross, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, hnp⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hnotProxyR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by
    rw [hborderR]; omega
  obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
  have hmarkRunR : run.proper.nodes[mR]? = some nR := by
    rw [hnodes]; exact hnpRecR
  have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
      groupBorderRects (componentCandidate e.graph comp candidate) run
        nodeV.decl :=
    groupBorderRects_mem_of_record hmarkRunR (Or.inr hborderR) hlastR
  obtain ⟨_, _, _, hcoordinate, hkeys, _, _, _⟩ :=
    componentRun_prepared_titled_source e.graph_eq hcomp hrun
  have hshape := componentCandidate_shape (components_nodup e.graph comp hcomp)
    (measuredGraph_shape e.graph_eq) candidate
  have huniq : ∀ (u w : Nat) (left right : ProperNode),
      run.coordinateProper.nodes[u]? = some left →
      run.coordinateProper.nodes[w]? = some right →
      left.node.border = 3 → right.node.border = 3 →
      left.node.clusterPath = right.node.clusterPath → u = w := by
    intro u w left right hleft hright hleftBorder hrightBorder hpath
    apply pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact hleft)
      (by rw [hcoordinate]; exact hright) hleftBorder hrightBorder hpath
  have hsep := CoordsImpl.cluster_all_pairs_separated hcross huniq layer
    hlayerMem iv j b mR actualB nR hlt hiv hj hcoordB hcpmR
    (by rw [hbB0]; omega) (by rw [hbB0]; omega)
    (by rw [hborderR]; omega) (by rw [hborderR]; omega)
  obtain ⟨hng, hcp, _, hsizesNN, _⟩ :=
    CoordsImpl.crossCoordsClusterWith_spec hcross
  have hgap : 1 ≤ min e.params.nodeGap e.params.clusterPad := by omega
  have hwbNN : (0 : Int) ≤ actualB.node.w :=
    (sizesNonneg_lookup hsizesNN b actualB hcoordB).1
  have hwmNN : (0 : Int) ≤ nR.node.w :=
    (sizesNonneg_lookup hsizesNN mR nR hcpmR).1
  obtain ⟨_, hxM⟩ := componentRun_border_record hrun hcpmR (Or.inr hborderR)
  have hstep : RouteImpl.leftOf run.proper run.xs b +
      RouteImpl.nodeW run.proper b ≤
      RouteImpl.leftOf run.proper run.xs mR +
        RouteImpl.nodeW run.proper mR := by
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordB, hcpmR,
      RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hpropB, hmarkRunR,
      hxeqB, hxM,
      Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hpropB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hpropB]
  have h1 : (Labels.rectAt run.proper run.xs run.ys b).x +
      (Labels.rectAt run.proper run.xs run.ys b).w =
      RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b := by
    simp only [hrb]
  have h2 : (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
    simp only [hrm]
  have hle : RouteImpl.leftOf run.proper run.xs b +
      RouteImpl.nodeW run.proper b ≤
      (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate) run
        nodeV.decl) []).right :=
    Int.le_trans hstep (by rw [← h2]; exact tsep_borders_right_ge hmemR)
  unfold LoopFootprintSeparation
  rw [hfoot, hframeV, hframeB, hrectB]
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  dsimp only at hx
  simp only [h1] at hx
  omega

/-! ## Y-band cases: the other box lies strictly above or below all members -/

/-- The plain box sits strictly above every member rank: its frame bottom
lies at or above the member hull top, hence above the footprint. -/
private theorem tsep_above_case
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
    (actualB : ProperNode)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2)
    (hnodeB : (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB)
    (hb0 : nodeB.border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (hpropB : run.proper.nodes[b]? = some actualB)
    (haboveFacts : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
      nd.node.clusterPath.contains nodeV.decl = true →
      (rk run.proper.rank b).toNat < (rk run.proper.rank q).toNat) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hexact := tsep_exact_nil hrun
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      nodeB := by
    simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
  have hframeV := frameRect_group_span (P := default) (run := run) hnodeV hvtop
  have hframeB := tsep_frame_node (P := default) (run := run) hgetB hb0
  have hfoot := tsep_foot_eq (cg := componentCandidate e.graph comp candidate)
    (run := run) (labels := e.measured) (v := v) hexact
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hpropB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hpropB]
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, hry, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  obtain ⟨lB, hlyB, _, hbBot⟩ := run_node_band hrun hpropB
  have hmem : ∀ r ∈ groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl,
      run.ys.getD b 0 + RouteImpl.nodeH run.proper b ≤ r.y := by
    intro r hr
    obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
    obtain ⟨l, hly, hqTop, _⟩ := run_node_band hrun hq
    have hlt : (rk run.coordinateProper.rank b).toNat <
        (rk run.coordinateProper.rank q).toNat := by
      rw [← hranks]
      exact haboveFacts q nd hq hcon
    have hband := CoordsImpl.rankAxis_bands_disjoint hry _ _ _ _ hlt hlyB hly
    rw [hrq, rectAt_eq]
    dsimp only
    simp only [RouteImpl.yAt]
    omega
  by_cases hnil : groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl = []
  · have hh : (loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).h = 0 := by
      rw [hfoot, hframeV, hnil]
      rfl
    exact tsep_sep_of_foot_oob hh
  · have htop := boundsOf_minY_ge_of_all hnil hmem
    have hnH : RouteImpl.nodeH run.proper b = actualB.node.h := by
      simp only [RouteImpl.nodeH, hpropB]
    unfold LoopFootprintSeparation
    rw [hfoot, hframeV, hframeB, hrectB, rectAt_eq run.proper run.xs run.ys b]
    refine rect_disjoint_of_y (Or.inr ?_)
    dsimp only
    simp only [RouteImpl.yAt]
    omega

/-- The plain box sits strictly below every member rank: the member hull
bottom (hence the footprint bottom) lies at or above the frame top. -/
private theorem tsep_below_case
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
    (actualB : ProperNode)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2)
    (hnodeB : (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB)
    (hb0 : nodeB.border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (hpropB : run.proper.nodes[b]? = some actualB)
    (hbelowFacts : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
      nd.node.clusterPath.contains nodeV.decl = true →
      (rk run.proper.rank q).toNat < (rk run.proper.rank b).toNat) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hexact := tsep_exact_nil hrun
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      nodeB := by
    simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
  have hframeV := frameRect_group_span (P := default) (run := run) hnodeV hvtop
  have hframeB := tsep_frame_node (P := default) (run := run) hgetB hb0
  have hfoot := tsep_foot_eq (cg := componentCandidate e.graph comp candidate)
    (run := run) (labels := e.measured) (v := v) hexact
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hpropB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hpropB]
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, hry, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  obtain ⟨lB, hlyB, hbTop, _⟩ := run_node_band hrun hpropB
  have htopNN := fbs_run_top_nonneg hrun
  have hysWNN : (0 : Int) ≤ run.ys.getD b 0 :=
    Int.le_trans (htopNN _) hbTop
  have hmem : ∀ r ∈ groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl,
      r.y + r.h ≤ run.ys.getD b 0 := by
    intro r hr
    obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
    obtain ⟨l, hly, _, hqBot⟩ := run_node_band hrun hq
    have hlt : (rk run.coordinateProper.rank q).toNat <
        (rk run.coordinateProper.rank b).toNat := by
      rw [← hranks]
      exact hbelowFacts q nd hq hcon
    have hband := CoordsImpl.rankAxis_bands_disjoint hry _ _ _ _ hlt hly hlyB
    rw [hrq, rectAt_eq]
    dsimp only
    simp only [RouteImpl.yAt]
    omega
  by_cases hnil : groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl = []
  · have hh : (loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).h = 0 := by
      rw [hfoot, hframeV, hnil]
      rfl
    exact tsep_sep_of_foot_oob hh
  · have hbot := boundsOf_bottom_le_of_all hysWNN hmem
    unfold LoopFootprintSeparation
    rw [hfoot, hframeV, hframeB, hrectB, rectAt_eq run.proper run.xs run.ys b]
    refine rect_disjoint_of_y (Or.inl ?_)
    dsimp only
    simp only [RouteImpl.yAt]
    omega

/-! ## Marker extent: the right marker copies the top's loop extent -/

/-- A candidate top node stores the exact loop extent of its own loop sizes.
Local candidate-level copy of `tsep_graph_node_loopExtent`: candidate nodes
are `componentGraph` copies of executed-graph nodes
(`componentCandidate_nodes`), so the executed-graph equation transports along
the loop-size preservation (`componentCandidate_loopSizes_preserved`). -/
private theorem tsep_cg_node_loopExtent {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecution inp o res) (comp : List Nat)
    (candidate v : Nat) {nodeV : Node}
    (hcomp : comp ∈ components e.graph)
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2) :
    nodeV.loopExtent = (Loops.extent (componentCandidate e.graph comp candidate).slot
      (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot)).toNat := by
  have hlen : (componentCandidate e.graph comp candidate).nodes.length =
      comp.length :=
    tsep_candidate_nodes_length _ _ _
  have hvcomp : v < comp.length := by rw [← hlen]; exact hvlen
  obtain ⟨u, huv, hnodeU⟩ :=
    componentCandidate_nonplain_source hnodeV (by omega : nodeV.border ≠ 0)
  obtain ⟨hdeclEq, _, hbox, _, _⟩ :=
    measuredGraph_group_origin e.graph_eq hnodeU hvtop
  have huLines : u < e.lines.length := by
    have h1 : nodeV.decl < inp.boxes.length := by
      have hmem := (List.getElem?_eq_some_iff.mp hbox).1
      simpa only [List.length_map] using hmem
    have h2 : e.lines.length = inp.boxes.length := tsep_lines_len e
    omega
  have hextU := tsep_graph_node_loopExtent e huLines hnodeU
  have hslot : (componentCandidate e.graph comp candidate).slot = e.graph.slot := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  have hnd : comp.Nodup := components_nodup e.graph comp hcomp
  have hloop := componentCandidate_loopSizes_preserved e.graph comp hnd candidate
    v hvcomp e.measured (componentCandidate e.graph comp candidate).slot
  have hcompv : comp[v]'hvcomp = u := by
    have h1 : comp[v]? = some (comp[v]'hvcomp) := List.getElem?_eq_getElem hvcomp
    exact Option.some.inj (h1.symm.trans huv)
  rw [hcompv] at hloop
  rw [hextU, ← hslot, ← hloop]

/-! ## Right-outsider case: alignment, marker extent, and the cluster gap -/

/-- A same-rank marker pair pins the border hull's right edge to the right
marker: every border marker shares its side's placed span (`SideMarkerSpanAligned`
from `hx`), and the same-rank pair orders the left span below the right span. -/
private theorem tsep_hull_eq_of_pair (hx : ForeignBorderChainXAligned)
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v : Nat) (nodeV : Node)
    (hcomp : comp ∈ components e.graph)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (mL mR : Nat) (nL nR : ProperNode)
    (hL : run.proper.nodes[mL]? = some nL) (hbL : nL.node.border = -1)
    (hlL : nL.node.clusterPath.getLast? = some nodeV.decl)
    (hR : run.proper.nodes[mR]? = some nR) (hbR : nR.node.border = 1)
    (hlR : nR.node.clusterPath.getLast? = some nodeV.decl)
    (hrank : rk run.proper.rank mL = rk run.proper.rank mR) :
    (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      (frameRect default (componentCandidate e.graph comp candidate) run v).x +
        (frameRect default (componentCandidate e.graph comp candidate) run v).w := by
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  have hframe := frameRect_group_span (P := default) (run := run) hnodeV hvtop
  have hall : ∀ r ∈ groupBorderRects (componentCandidate e.graph comp candidate)
      run nodeV.decl,
      r.x + r.w ≤ (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w := by
    intro r hr
    obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
    rcases hbq with hbqL | hbqR
    · obtain ⟨heq1, heq2⟩ := (halign e.graph_eq (tsep_lines_len e) hwf hfp
        hcomp hrun hq (Or.inl hbqL) hlastq hL (Or.inl hbL) hlL).1
        (by rw [hbL, hbqL])
      have hcross := (halign e.graph_eq (tsep_lines_len e) hwf hfp hcomp hrun
        hL (Or.inl hbL) hlL hR (Or.inr hbR) hlR).2.2 ⟨hbL, hbR, hrank⟩
      rw [hrq, rectAt_eq run.proper run.xs run.ys q,
        rectAt_eq run.proper run.xs run.ys mR]
      dsimp only
      omega
    · obtain ⟨heq1, heq2⟩ := (halign e.graph_eq (tsep_lines_len e) hwf hfp
        hcomp hrun hq (Or.inr hbqR) hlastq hR (Or.inr hbR) hlR).1
        (by rw [hbR, hbqR])
      rw [hrq, rectAt_eq run.proper run.xs run.ys q,
        rectAt_eq run.proper run.xs run.ys mR]
      dsimp only
      omega
  have hnonnegR := (halign e.graph_eq (tsep_lines_len e) hwf hfp hcomp hrun
    hR (Or.inr hbR) hlR hR (Or.inr hbR) hlR).2.1
  have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
      groupBorderRects (componentCandidate e.graph comp candidate) run
        nodeV.decl :=
    groupBorderRects_mem_of_record hR (Or.inr hbR) hlR
  have hRw : (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
    rw [rectAt_eq]
  have hzero : (0 : Int) ≤ (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w := by
    rw [hRw]
    exact hnonnegR
  have hright := boundsOf_right_le_of_all hzero hall
  have hge := tsep_borders_right_ge hmemR
  have hframeRW : (frameRect default (componentCandidate e.graph comp candidate)
      run v).x +
      (frameRect default (componentCandidate e.graph comp candidate) run v).w =
      (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate) run
        nodeV.decl) []).right := by
    rw [hframe]
    dsimp only
    omega
  omega

/-! ## Rank transports for the reconstructed pair -/

/-- Prefixed copy of the private `smc_top_getLast` in
`SideMarkerAnchorCoverProof`: a candidate `-2` node ends its cluster path in
its declaration. -/
private theorem tsep_top_getLast {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hb : uNode.border = -2) :
    uNode.clusterPath.getLast? = some uNode.decl := by
  obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hu (by omega)
  obtain ⟨_, _, _, _, hpath⟩ := measuredGraph_group_origin hgraph hsource hb
  rw [hpath]
  simp

/-- Prefixed copy of the private `smc_rkToNat_le` in
`SideMarkerAnchorCoverProof`: `toNat` is monotone on nonnegative ranks. -/
private theorem tsep_rkToNat_le {a b : Int} (ha : 0 ≤ a) (h : a ≤ b) :
    a.toNat ≤ b.toNat := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg (Int.le_trans ha h)
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by omega
  exact Int.ofNat_le.mp h3


theorem loopFootprintTopSeparation_holds (hx : ForeignBorderChainXAligned)
    (hbeyond : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      LoopFootprintBeyondProper inp o res)
    (hright : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (e : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat)
      (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
      (actualB : ProperNode) (mR : Nat) (nR : ProperNode),
      comp ∈ components e.graph →
      (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV →
      nodeV.border = -2 →
      (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB →
      nodeB.border = 0 →
      actualB.node.border = 0 →
      componentRun e.params (componentCandidate e.graph comp candidate) e.measured
        oo = .ok run →
      run.proper.nodes[b]? = some actualB →
      run.coordinateProper.nodes[b]? = some actualB →
      run.coordinateProper.nodes[mR]? = some nR →
      nR.node.border = 1 →
      nR.node.clusterPath.getLast? = some nodeV.decl →
      SideMarkerSpanAligned →
      ((nR.node.loopExtent : Int) ≥ Loops.extent
        (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot)) →
      ∀ (layer : List Nat), layer ∈ run.layers →
        ∀ (iv j : Nat), layer[iv]? = some b → layer[j]? = some mR → j < iv →
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x +
          (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≤
          (frameRect default (componentCandidate e.graph comp candidate) run b).x)
    (hext_all : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
      (run : Run) (oo : OrderOptions) (v m : Nat) (nodeV : Node) (mk : ProperNode),
      comp ∈ components e.graph →
      (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV →
      nodeV.border = -2 →
      componentRun e.params (componentCandidate e.graph comp candidate) e.measured
        oo = .ok run →
      run.coordinateProper.nodes[m]? = some mk →
      mk.node.border = 1 →
      mk.node.clusterPath.getLast? = some nodeV.decl →
      (mk.node.loopExtent : Int) ≥ Loops.extent
        (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot)) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    LoopFootprintTopSeparation inp o res := by
  intro inp o res hwf hfp e comp candidate run oo v b hcomp hb0 hrun hvlen hvtop
  by_cases hblen : b < (componentCandidate e.graph comp candidate).nodes.length
  · obtain ⟨nodeV, hnodeV⟩ : ∃ n,
        (componentCandidate e.graph comp candidate).nodes[v]? = some n :=
      ⟨_, List.getElem?_eq_getElem hvlen⟩
    obtain ⟨nodeB, hnodeB⟩ : ∃ n,
        (componentCandidate e.graph comp candidate).nodes[b]? = some n :=
      ⟨_, List.getElem?_eq_getElem hblen⟩
    have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
        nodeV := by
      simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
    have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
        nodeB := by
      simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
    have hvtop' : nodeV.border = -2 := by rw [← hgetV]; exact hvtop
    have hb0' : nodeB.border = 0 := by rw [← hgetB]; exact hb0
    obtain ⟨actualB, hcoordB, hpropB, _, hbB0, hpathB, _, _, _, hxeqB⟩ :=
      componentRun_original_plain_record hrun hnodeB hb0'
    obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, hroute, _, _, _, _⟩ :=
      componentRun_spec hrun
    obtain ⟨_, hrankEq, _, _, _, hnp⟩ := proxyWidths_rel hproxy
    have hranks : run.proper.rank = run.coordinateProper.rank := by
      rw [← hdrop, OrderImpl.dropSynthetic_rank]; exact hrankEq
    have hnodes : run.proper.nodes = q0.nodes := by
      rw [← hdrop, OrderImpl.dropSynthetic_nodes]
    obtain ⟨_, _, _, hcov, _⟩ :=
      RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
    have hwP : b < run.proper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hpropB).1
    obtain ⟨lB, hlyB, hmemB, hrkBNN⟩ := hcov b hwP
    have hrkWNN : 0 ≤ rk run.coordinateProper.rank b := by
      rw [← hranks]; exact hrkBNN
    have hlayerMem : lB ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyB
      rw [← hmemEq]; exact List.getElem_mem hmemLT
    obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hmemB
    have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
    -- Right-marker acquisition: a member brackets itself; an outsider uses
    -- the low/high member witnesses.
    by_cases hmemC : actualB.node.clusterPath.contains nodeV.decl = true
    · obtain ⟨_, mR, _, nR, _, _, _, _, hcpmR, hborderR, hlastR, hrankR⟩ :=
        bracketMarkersAtRank' e.graph_eq (tsep_lines_len e) hwf hfp hcomp
          hrun (rk run.proper.rank b).toNat hpropB hmemC (Nat.le_refl _)
          hpropB hmemC (Nat.le_refl _)
      have hnotProxyR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by
        rw [hborderR]; omega
      obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
      have hmarkRunR : run.proper.nodes[mR]? = some nR := by
        rw [hnodes]; exact hnpRecR
      have hrankmWR : rk run.proper.rank mR = rk run.proper.rank b := by
        rw [hranks, hrankR, hranks]; exact Int.toNat_of_nonneg hrkWNN
      have hwM : mR < run.proper.nodes.length :=
        (List.getElem?_eq_some_iff.mp hmarkRunR).1
      obtain ⟨lM, hlyM, hmemM, -⟩ := hcov mR hwM
      have hlyEq : lM = lB := by
        rw [hrankmWR] at hlyM
        exact Option.some.inj (hlyM.symm.trans hlyB)
      rw [hlyEq] at hmemM
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemM
      rcases Nat.lt_or_ge iv j with hlt | hge
      · exact tsep_good_case e comp candidate run oo v b nodeV nodeB actualB
          mR nR hcomp hnodeV hvtop' hnodeB hb0' hbB0 hrun hpropB hcoordB hxeqB hcpmR
          hborderR hlastR lB hlayerMem iv j hiv hj hlt
      · rcases Nat.eq_or_lt_of_le hge with heq | hgt
        · have hbm : b = mR := Option.some.inj (hiv.symm.trans (heq ▸ hj))
          subst hbm
          have heq2 := Option.some.inj (hpropB.symm.trans hmarkRunR)
          rw [heq2] at hbB0; omega
        · exact rect_disjoint_of_x (Or.inl (hright inp o res e hwf hfp comp
            candidate run oo v b nodeV nodeB actualB mR nR hcomp hnodeV hvtop'
            hnodeB hb0' hbB0 hrun hpropB hcoordB hcpmR hborderR hlastR halign
            (hext_all inp o res e comp candidate run oo v mR nodeV nR hcomp
            hnodeV hvtop' hrun hcpmR hborderR hlastR) lB hlayerMem iv j hiv hj
            hgt))
    · by_cases hLow : ∃ (q : Nat) (nd : ProperNode),
          run.proper.nodes[q]? = some nd ∧
          nd.node.clusterPath.contains nodeV.decl = true ∧
          (rk run.proper.rank q).toNat ≤ (rk run.proper.rank b).toNat
      · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode),
            run.proper.nodes[q]? = some nd ∧
            nd.node.clusterPath.contains nodeV.decl = true ∧
            (rk run.proper.rank b).toNat ≤ (rk run.proper.rank q).toNat
        · obtain ⟨low, lowNd, hlowRec, hlowCon, hlowLe⟩ := hLow
          obtain ⟨high, highNd, hhighRec, hhighCon, hhighGe⟩ := hHigh
          obtain ⟨_, mR, _, nR, _, _, _, _, hcpmR, hborderR, hlastR, hrankR⟩ :=
            bracketMarkersAtRank' e.graph_eq (tsep_lines_len e) hwf hfp hcomp
              hrun (rk run.proper.rank b).toNat hlowRec hlowCon hlowLe
              hhighRec hhighCon hhighGe
          have hnotProxyR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by
            rw [hborderR]; omega
          obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
          have hmarkRunR : run.proper.nodes[mR]? = some nR := by
            rw [hnodes]; exact hnpRecR
          have hrankmWR : rk run.proper.rank mR = rk run.proper.rank b := by
            rw [hranks, hrankR, hranks]; exact Int.toNat_of_nonneg hrkWNN
          have hwM : mR < run.proper.nodes.length :=
            (List.getElem?_eq_some_iff.mp hmarkRunR).1
          obtain ⟨lM, hlyM, hmemM, -⟩ := hcov mR hwM
          have hlyEq : lM = lB := by
            rw [hrankmWR] at hlyM
            exact Option.some.inj (hlyM.symm.trans hlyB)
          rw [hlyEq] at hmemM
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemM
          rcases Nat.lt_or_ge iv j with hlt | hge
          · exact tsep_good_case e comp candidate run oo v b nodeV nodeB
              actualB mR nR hcomp hnodeV hvtop' hnodeB hb0' hbB0 hrun hpropB
              hcoordB hxeqB hcpmR hborderR hlastR lB hlayerMem iv j hiv hj hlt
          · rcases Nat.eq_or_lt_of_le hge with heq | hgt
            · have hbm : b = mR := Option.some.inj (hiv.symm.trans (heq ▸ hj))
              subst hbm
              have heq2 := Option.some.inj (hpropB.symm.trans hmarkRunR)
              rw [heq2] at hbB0; omega
            · exact rect_disjoint_of_x (Or.inl (hright inp o res e hwf hfp comp
                candidate run oo v b nodeV nodeB actualB mR nR hcomp hnodeV
                hvtop' hnodeB hb0' hbB0 hrun hpropB hcoordB hcpmR hborderR
                hlastR halign (hext_all inp o res e comp candidate run oo v mR
                nodeV nR hcomp hnodeV hvtop' hrun hcpmR hborderR hlastR)
                lB hlayerMem iv j hiv hj hgt))
        · have hbelowFacts : ∀ (q : Nat) (nd : ProperNode),
              run.proper.nodes[q]? = some nd →
              nd.node.clusterPath.contains nodeV.decl = true →
              (rk run.proper.rank q).toNat < (rk run.proper.rank b).toNat := by
            intro q nd hq hc
            refine Classical.byContradiction (fun hle => ?_)
            exact hHigh ⟨q, nd, hq, hc, by omega⟩
          exact tsep_below_case e comp candidate run oo v b nodeV nodeB actualB
            hnodeV hvtop' hnodeB hb0' hrun hpropB hbelowFacts
      · have haboveFacts : ∀ (q : Nat) (nd : ProperNode),
            run.proper.nodes[q]? = some nd →
            nd.node.clusterPath.contains nodeV.decl = true →
            (rk run.proper.rank b).toNat < (rk run.proper.rank q).toNat := by
          intro q nd hq hc
          refine Classical.byContradiction (fun hle => ?_)
          exact hLow ⟨q, nd, hq, hc, by omega⟩
        exact tsep_above_case e comp candidate run oo v b nodeV nodeB actualB
          hnodeV hvtop' hnodeB hb0' hrun hpropB haboveFacts
  · by_cases hbproper : b < run.proper.nodes.length
    · exact hbeyond inp o res e comp candidate run oo v b hcomp hrun hvlen
        (Nat.le_of_not_gt hblen) hbproper
    · have hnone : (componentCandidate e.graph comp candidate).nodes[b]? = none :=
        List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hblen)
      have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
          default := by
        simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
      have hframeB : frameRect default (componentCandidate e.graph comp candidate)
          run b = nodeRect (componentCandidate e.graph comp candidate) run b :=
        tsep_frame_node hgetB rfl
      have hproperB : run.proper.nodes.getD b default = default := by
        have hnoneP : run.proper.nodes[b]? = none :=
          List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hbproper)
        simp only [List.getD_eq_getElem?_getD, hnoneP, Option.getD_none]
      have hdefW : (default : ProperNode).node.w = 0 := rfl
      have hwB : (frameRect default (componentCandidate e.graph comp candidate)
          run b).w = 0 := by
        simp only [hframeB, nodeRect, hproperB, hdefW]
      exact tsep_sep_of_frame_oob hwB
end PipelineImpl
end Layered
end Elegant
