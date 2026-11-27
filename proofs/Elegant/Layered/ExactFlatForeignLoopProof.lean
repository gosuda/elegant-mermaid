import Elegant.Layered.ExactBottomLoopTransportProof
import Elegant.Layered.ExactFlatC5SelfRoutes
import Elegant.Layered.ExactFlatC7ExclusiveKey
import Elegant.Layered.ExactForeignFrameClearProof
import Elegant.Layered.ExactLoopEnvelopeGroupMissProof
import Elegant.Layered.ExactLoopEnvelopeReserveProof
import Elegant.Layered.ExactLoopEnvelopeRightProof
import Elegant.Layered.ExactLoopMarkerCoreProof
import Elegant.Layered.ExactLoopMarkerLayerOrderProof
import Elegant.Layered.ExactLoopMarkerSpanProof
import Elegant.Layered.ExactLoopRectFactsProof
import Elegant.Layered.ExactRunFrameNestingProof
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.ExactStraightenFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private def shelfBefore (a b : Rect) : Prop :=
  a.x + a.w ≤ b.x ∨ a.y + a.h ≤ b.y

private theorem append_shelfBefore {target gap : Int} {s out : Pack.State} {item : Pack.Item}
    (hg : 0 ≤ gap) (hs : Pack.Inv s) (hp : s.boxes.Pairwise shelfBefore)
    (h : Pack.append target gap s item = .ok out) : out.boxes.Pairwise shelfBefore := by
  unfold Pack.append at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals simp at h
  all_goals try contradiction
  all_goals subst out
  all_goals obtain ⟨_, _, _, _, _, hempty, _, hb⟩ := hs
  all_goals have hx : s.occupied ≠ true → s.x = 0 :=
    fun hn => hempty (Bool.eq_false_iff.mpr hn)
  all_goals simp only [List.pairwise_append, List.pairwise_singleton, true_and, hp,
    List.mem_singleton, forall_eq]
  all_goals intro old hold
  all_goals obtain ⟨_, _, _, _, _, _, hbottom, hrow⟩ := hb old hold
  all_goals try have hx0 : s.x = 0 := hx (by assumption)
  all_goals simp only [shelfBefore]
  all_goals omega

private theorem fold_shelfBefore {target gap : Int} (hg : 0 ≤ gap) (items : List Pack.Item)
    {s out : Pack.State} (hs : Pack.Inv s) (hp : s.boxes.Pairwise shelfBefore)
    (h : items.foldlM (Pack.append target gap) s = .ok out) :
    out.boxes.Pairwise shelfBefore := by
  induction items generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst out
    exact hp
  | cons item rest ih =>
    simp only [List.foldlM_cons] at h
    cases ha : Pack.append target gap s item with
    | error e => simp [ha, bind, Except.bind] at h
    | ok next =>
      simp only [ha, bind, Except.bind] at h
      exact ih (Pack.append_inv hg hs ha) (append_shelfBefore hg hs hp ha) h

private theorem pack_shelfBefore {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out) :
    out.boxes.Pairwise shelfBefore := by
  unfold Pack.pack at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · cases ht : Pack.packingTarget maxWidth gap aspectNum aspectDen items with
    | error e => simp [ht] at h
    | ok target =>
      simp only [ht] at h
      cases hf : items.foldlM (Pack.append target gap) {} with
      | error e => simp [hf] at h
      | ok result =>
        simp only [hf] at h
        split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          subst out
          have hp := fold_shelfBefore (by omega : 0 ≤ gap) items
            (s := {}) (by simp [Pack.Inv]) (by simp) hf
          exact List.Pairwise.map (S := shelfBefore)
            (fun r => { r with x := r.x + margin, y := r.y + margin })
            (by intro a b hab; simp only [shelfBefore] at hab ⊢; omega) hp

/-- Distinct shelves remain axis-separated even when a shelf has zero width or height. -/
theorem pack_shelves_axisSeparatedX {maxWidth : Nat}
    {gap margin aspectNum aspectDen : Int} {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out)
    {i j : Nat} (hne : i ≠ j) {a b : Rect}
    (ha : out.boxes[i]? = some a) (hb : out.boxes[j]? = some b) :
    RectAxisSeparated a b := by
  obtain ⟨hi, ha'⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, hb'⟩ := List.getElem?_eq_some_iff.mp hb
  have hp := List.pairwise_iff_getElem.mp (pack_shelfBefore h)
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · have hsep := hp i j hi hj hij
    rw [ha', hb'] at hsep
    simp only [shelfBefore, RectAxisSeparated] at hsep ⊢
    omega
  · have hsep := hp j i hj hi hji
    rw [hb', ha'] at hsep
    simp only [shelfBefore, RectAxisSeparated] at hsep ⊢
    omega

private theorem maxFold_ge (f : LoopLabel → Int) (sizes : List LoopLabel) (start : Int) :
    start ≤ sizes.foldl (fun n l => max n (f l)) start := by
  induction sizes generalizing start with
  | nil => exact Int.le_refl _
  | cons l rest ih =>
    exact Int.le_trans (Int.le_max_left start (f l)) (ih _)

private theorem nativeLoop_points_in_reserved_band {node : Rect} {slot : Int}
    {sizes : List LoopLabel} {placements : List LoopPlacement} {exact : Bool}
    (h : (if exact then Loops.exactLoops else Loops.loops) node slot sizes = .ok placements)
    (hslot : 0 < slot) (hw : ∀ l ∈ sizes, 0 ≤ l.width)
    {placement : LoopPlacement} (hmem : placement ∈ placements) :
    let width := (if exact then Loops.exactExtent else Loops.extent) slot sizes
    let height := max node.h ((sizes.length : Int) * Loops.band slot sizes)
    0 < width ∧ 0 < height ∧
      ∀ p ∈ placement.points, PointIn ⟨node.x + node.w, node.y, width, height⟩ p := by
  have hforms : node.Valid ∧ ∃ entry ∈ sizes.zipIdx,
      placement = (if exact then Loops.exactPlacement else Loops.placement) node slot
        (Loops.band slot sizes) sizes.length entry.2 entry.1 := by
    cases exact <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    all_goals first | unfold Loops.loops at h | unfold Loops.exactLoops at h
    all_goals dsimp only at h
    all_goals split at h
    all_goals try contradiction
    all_goals rename_i hvalid
    all_goals split at h
    all_goals try contradiction
    all_goals split at h
    all_goals try contradiction
    all_goals split at h
    all_goals try contradiction
    all_goals cases h
    all_goals obtain ⟨entry, hentry, he⟩ := List.mem_map.mp hmem
    all_goals exact ⟨by omega, entry, hentry, he.symm⟩
  obtain ⟨hvalid, ⟨label, index⟩, hentry, rfl⟩ := hforms
  have hindexed : sizes[index]? = some label := List.mem_zipIdx_iff_getElem?.mp hentry
  have hi := (List.getElem?_eq_some_iff.mp hindexed).1
  have hlabel := List.mem_of_getElem? hindexed
  let band := Loops.band slot sizes
  have hband : 2 * slot ≤ band := maxFold_ge LoopLabel.height sizes (2 * slot)
  have hb : 0 ≤ band := by omega
  have hstack : 0 < (sizes.length : Int) * band := Int.mul_pos (by omega) (by omega)
  have hheight : 0 < max node.h ((sizes.length : Int) * band) :=
    Int.lt_of_lt_of_le hstack (Int.le_max_right _ _)
  have hrow : (index : Int) * band + band ≤ (sizes.length : Int) * band := by
    simpa only [Int.add_mul, Int.one_mul] using
      (Int.mul_le_mul_of_nonneg_right (show (index : Int) + 1 ≤ sizes.length by omega) hb)
  have hbase : 0 ≤ (index : Int) * band := Int.mul_nonneg (by omega) hb
  have hhalf : slot ≤ Int.fdiv band 2 ∧ Int.fdiv band 2 + slot ≤ band := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    omega
  have hmax := Int.le_max_right node.h ((sizes.length : Int) * band)
  cases exact
  · have hlane : 0 < slot * ((index : Int) + 1) := Int.mul_pos hslot (by omega)
    have hle : slot * ((index : Int) + 1) ≤ slot * ((sizes.length : Int) + 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have he := Loops.outer_label_extent slot sizes (by omega) hw label hlabel
    have hwLabel := hw label hlabel
    have hpos : 0 < Loops.extent slot sizes := by omega
    refine ⟨hpos, hheight, ?_⟩
    intro p hp
    change p ∈ (Loops.placement node slot band sizes.length index label).points at hp
    change PointIn ⟨node.x + node.w, node.y, Loops.extent slot sizes,
      max node.h ((sizes.length : Int) * band)⟩ p
    simp only [Loops.placement, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      simp only [PointIn] <;> omega
  · have hne : sizes.isEmpty = false := by
      cases hs : sizes with
      | nil => simp [hs] at hi
      | cons => rfl
    have he : Loops.exactExtent slot sizes = slot * (2 * (sizes.length : Int) + 1) +
        sizes.foldl (fun n l => max n l.width) 0 := by simp [Loops.exactExtent, hne]
    have hwide : 0 ≤ sizes.foldl (fun n l => max n l.width) 0 := maxFold_ge _ _ _
    have hpos : 0 < Loops.exactExtent slot sizes := by
      have hp : 0 < slot * (2 * (sizes.length : Int) + 1) := Int.mul_pos hslot (by omega)
      omega
    have ha : 0 ≤ slot * (2 * (index : Int) + 1) := Int.mul_nonneg (by omega) (by omega)
    have hab : slot * (2 * (index : Int) + 1) ≤ slot * (2 * (index : Int) + 2) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hbe : slot * (2 * (index : Int) + 2) ≤ slot * (2 * (sizes.length : Int) + 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hports (k : Int) (hk : 1 ≤ k ∧ k ≤ 2) :
        0 ≤ Int.fdiv ((2 * (index : Int) + k) * node.h) (2 * (sizes.length : Int) + 1) ∧
        Int.fdiv ((2 * (index : Int) + k) * node.h) (2 * (sizes.length : Int) + 1) ≤ node.h := by
      have hd : 0 < 2 * (sizes.length : Int) + 1 := by omega
      rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
      constructor
      · exact Int.ediv_nonneg (Int.mul_nonneg (by omega) hvalid.2.1) (by omega)
      · have hm := Int.mul_le_mul_of_nonneg_right
          (show 2 * (index : Int) + k ≤ 2 * (sizes.length : Int) + 1 by omega) hvalid.2.1
        have hl := Int.ediv_le_ediv (c := 2 * (sizes.length : Int) + 1) hd hm
        simpa only [Int.mul_comm (2 * (sizes.length : Int) + 1) node.h,
          Int.mul_ediv_cancel _ (by omega : 2 * (sizes.length : Int) + 1 ≠ 0)] using hl
    have hpA := hports 1 (by omega)
    have hpB := hports 2 (by omega)
    have hnode := Int.le_max_left node.h ((sizes.length : Int) * band)
    refine ⟨hpos, hheight, ?_⟩
    intro p hp
    change p ∈ (Loops.exactPlacement node slot band sizes.length index label).points at hp
    change PointIn ⟨node.x + node.w, node.y, Loops.exactExtent slot sizes,
      max node.h ((sizes.length : Int) * band)⟩ p
    simp only [Loops.exactPlacement, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [PointIn] <;> omega

/-- Each actual loop placement is confined by its full reservation, including
    exact ports on a frame shorter than the loop's bend stack. -/
theorem componentLoops_entry_in_footprintExt
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)} (hloops : componentLoops P cg run labels = .ok loops)
    (hslot : 0 < cg.slot) {entry : Nat × LoopPlacement} (hentry : entry ∈ loops) :
    ∃ v, v < cg.nodes.length ∧ ∃ edge ∈ loopEdges cg.edges v,
      entry.1 = edge.decl ∧ edge.tail = v ∧ edge.head = v ∧
      0 < (loopFootprintExt cg run labels v).w ∧ 0 < (loopFootprintExt cg run labels v).h ∧
      ∀ p ∈ entry.2.points, PointIn (loopFootprintExt cg run labels v) p := by
  obtain ⟨v, hv, placements, hp, edge, hzip, hdecl, htail, hhead⟩ :=
    componentLoops_entry_origin hloops hentry
  obtain ⟨hedge, hmem⟩ := List.of_mem_zip hzip
  have hw : ∀ l ∈ loopSizes cg.edges labels v cg.slot, 0 ≤ l.width := by
    intro l hl
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hbounds := nativeLoop_points_in_reserved_band hp hslot hw hmem
  exact ⟨v, hv, edge, hedge, hdecl, htail, hhead, hbounds⟩

private theorem chosen_shelf_dims
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q) :
    q.2.w = q.1.2.width ∧ q.2.h = q.1.2.height := by
  obtain ⟨hpart, hshelf⟩ := List.getElem?_zip_eq_some.mp hselected
  have hdim := congrArg (fun dims : List (Int × Int) => dims[c]?) (Pack.pack_dimensions hpacked)
  simpa only [Pack.dimensions, List.getElem?_map, hpart, hshelf, Option.map_some,
    Option.some.injEq, Prod.mk.injEq] using hdim

private theorem chosen_frame_packed
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {v key : Nat} (hv : q.1.1[v]? = some key) (hk : key < inp.boxes.length) :
    let cg := componentCandidate execution.graph q.1.1 candidate
    let bounds := placeBoundsX execution.params cg run execution.measured loops
    let localRect := shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect execution.params cg run v)
    execution.packedAcc.rects.getD key default = shiftRect q.2.x q.2.y localRect ∧
      q.2.Contained (shiftRect q.2.x q.2.y localRect) := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  let localRect := shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect execution.params cg run v)
  have hlen : v < cg.nodes.length := by
    dsimp only [cg]
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using (List.getElem?_eq_some_iff.mp hv).1
  have hrect : q.1.2.rects[v]? = some localRect := by
    rw [hpart]
    change (((List.range cg.nodes.length).map (frameRect execution.params cg run)).map
      (shiftRect (0 - bounds.minX) (-bounds.minY)))[v]? = some localRect
    simp only [List.getElem?_map, List.getElem?_range hlen, Option.map_some]
    rfl
  have hentry : (q.1.1.zip q.1.2.rects)[v]? = some (key, localRect) :=
    List.getElem?_zip_eq_some.mpr ⟨hv, hrect⟩
  have hsize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hk
  have hread := actual_components_packed_rect_valueX (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hsize default
  have hd := chosen_shelf_dims execution hpacked hselected
  have hm := List.mem_of_getElem? (zip_getElem?_left hselected)
  have hb := (exactPartsBounded' execution q.1 hm).2.2.1 localRect (List.mem_of_getElem? hrect)
  refine ⟨hread, ?_⟩
  change q.2.Contained (shiftRect q.2.x q.2.y localRect)
  simp only [Rect.Contained, shiftRect, hd.1, hd.2]
  omega

private theorem chosen_route_packed_points
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {k : Nat} {points : List Point} {minX minY : Int}
    (hp : (k, points.map (shiftPoint (0 - minX) (-minY))) ∈ q.1.2.routes) :
    ∀ p ∈ points.map (shiftPoint (q.2.x - minX) (q.2.y - minY)), PointIn q.2 p := by
  have hd := chosen_shelf_dims execution hpacked hselected
  have hm := List.mem_of_getElem? (zip_getElem?_left hselected)
  intro p hp'
  obtain ⟨native, hn, rfl⟩ := List.mem_map.mp hp'
  have hlocal := (exactPartsBounded' execution q.1 hm).2.2.2.2.1 _ hp
    (shiftPoint (0 - minX) (-minY) native) (List.mem_map_of_mem hn)
  simp only [PointIn, shiftPoint, hd.1, hd.2] at hlocal ⊢
  omega

private theorem selected_loop_points
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)} (hloops : componentLoops P cg run labels = .ok loops)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hv : edge.tail < cg.nodes.length) (hself : edge.tail = edge.head) :
    ∃ native ∈ loops,
      (placeComponentExact P cg run 0 labels loops).routes[i]? =
        some (edge.decl, native.2.points.map
          (shiftPoint (0 - (placeBoundsX P cg run labels loops).minX)
            (-(placeBoundsX P cg run labels loops).minY))) ∧ native.1 = edge.decl := by
  obtain ⟨placement, hplacement⟩ := componentLoops_entry_of_self_edge hloops
    (List.mem_of_getElem? hedge) hv hself
  cases hfind : loops.find? (fun loop => loop.1 == edge.decl) with
  | none =>
    have hn := List.find?_eq_none.mp hfind (edge.decl, placement) hplacement
    simp only [beq_self_eq_true, not_true_eq_false] at hn
  | some native =>
    refine ⟨native, List.mem_of_find?_eq_some hfind, ?_, ?_⟩
    · unfold placeComponentExact placeBoundsX
      dsimp only
      simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some,
        hfind, Option.getD_some]
    · simpa only [beq_iff_eq] using List.find?_some hfind

private theorem chosen_route_decls
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {part : List Nat × Part} {candidate : Nat} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int}
    (hpart : part.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops
      with area := area }) :
    (part.2.routes.map (·.1)).Nodup := by
  rw [hpart]
  unfold placeComponentExact
  dsimp only
  rw [List.map_map]
  change (((componentCandidate execution.graph part.1 candidate).edges.zipIdx).map
    (fun q => q.1.decl)).Nodup
  rw [zipIdx_map_comp (fun edge : Edge => edge.decl)]
  exact componentCandidate_decls_nodup execution.graph part.1 candidate
    (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)

private theorem scene_selfLoop_candidate
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    {route : Route} (hroute : res.scene.routes[edge.decl]? = some route)
    (hself : route.fromId = route.toId) :
    (∃ model, inp.routes[edge.decl]? = some model) ∧ edge.tail = edge.head := by
  obtain ⟨index, model, raw, _, _, hm, hraw, hindex, _, _, _, _, hsemantic⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq (List.mem_of_getElem? hedge)
  have hm' : inp.routes[edge.decl]? = some model := by rwa [hindex]
  have hk := (List.getElem?_eq_some_iff.mp hm').1
  have hs := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured edge.decl hk
  have hmodel : inp.routes[edge.decl]'hk = model := (List.getElem?_eq_some_iff.mp hm').2
  rw [← execution.scene_eq, hmodel] at hs
  have heq := Option.some.inj (hroute.symm.trans hs)
  have hmself : model.fromId = model.toId :=
    (congrArg Route.fromId heq).symm.trans (hself.trans (congrArg Route.toId heq))
  have hrawSelf : raw.tail = raw.head := by
    unfold edgeOf at hraw
    rw [hmself] at hraw
    cases hf : inp.boxes.findIdx? (fun b => b.id == model.toId) with
    | none => simp [hf] at hraw
    | some k =>
      simp only [hf, Except.ok.injEq] at hraw
      rw [← hraw]
  have halias (boxes : List ModelBox) :
      (Compound.aliasEdge boxes raw).tail = (Compound.aliasEdge boxes raw).head := by
    change Compound.endpoint boxes true raw.tail raw.head =
      Compound.endpoint boxes false raw.head raw.tail
    rw [hrawSelf]
    unfold Compound.endpoint
    cases boxes[raw.head]? <;> simp
  let prepared := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
    else box
  let aliased := Compound.aliasEdge prepared raw
  have he : edge.original.tail = comp.idxOf aliased.tail := congrArg Edge.tail hsemantic
  have hh : edge.original.head = comp.idxOf aliased.head := congrArg Edge.head hsemantic
  have ho : edge.original.tail = edge.original.head :=
    he.trans ((congrArg comp.idxOf (halias prepared)).trans hh.symm)
  exact ⟨⟨model, hm'⟩, by cases hr : edge.reversed <;> simpa [Edge.original, hr, eq_comm] using ho⟩

private theorem chosen_candidate_slot_pos
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) (comp : List Nat) (candidate : Nat) :
    0 < (componentCandidate execution.graph comp candidate).slot := by
  have hc : (componentCandidate execution.graph comp candidate).slot = execution.graph.slot := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  have hg := execution.graph_eq
  unfold exactGraph at hg
  obtain ⟨_, _, hg⟩ := bind_ok hg
  have hs : execution.graph.slot = execution.graph0.slot := by rw [← Except.ok.inj hg]
  obtain ⟨_, _, _, _, _, _, hslot, hprep, _⟩ :=
    measuredGraph_loop_reservation_before_prepare execution.graph0_eq
  have hslot0 : execution.graph0.slot = execution.params.slot := by rw [hprep]; exact hslot
  have hvalid := (checkedParams_valid execution.checked).2.2.1
  rw [hc, hs, hslot0]
  omega

private theorem fixed_graph_border
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {k : Nat} {source : ModelBox} {entry : String × Size}
    (hsource : inp.boxes[k]? = some source)
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry) :
    ∃ node, execution.graph.nodes[k]? = some node ∧ node.border = 0 := by
  have hlinesEq := execution.lines_eq
  unfold boxLines at hlinesEq
  have hlines : execution.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlinesEq).1
  have hk : k < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨_, _, _, _, _, hnode, hzero, _⟩ :=
    measuredGraph_fixed_loop_reservation execution.graph0_eq hk hsource hfixed
  obtain ⟨node, hlookup, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hnode
  exact ⟨node, hlookup, hborder.trans hzero⟩

private theorem plain_coord_node {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : Node} (hv : cg.nodes[v]? = some node) (hplain : node.border = 0) :
    ∃ actual : ProperNode, run.coordinateProper.nodes[v]? = some actual ∧
      actual.node.border = 0 := by
  obtain ⟨_, _, _, _, hn, hl, hc, _, _, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨actual, ha, _, hb, _, _⟩ := coordinateGraphX_plain_anchor_dims P
    (addLabelNodes_untouched_node hl (normalize_node_record hn hv) rfl) hplain
  refine ⟨actual, ?_, hb⟩
  rwa [← hc]

set_option maxHeartbeats 800000 in
/-- In one exact component, an ordinary-node loop's full reservation misses
    every original plain frame. That includes a fixed group demoted to a plain
    node, regardless of its scene exclusivity flag. -/
theorem componentRunX_plainLoop_footprint_misses_plain_frame
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head)
    {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[edge.tail]? = some owner)
    (hplain : owner.border = 0) {v : Nat} {target : Node}
    (htarget : (componentCandidate execution.graph comp candidate).nodes[v]? = some target)
    (hzero : target.border = 0) :
    Disjoint (loopFootprintExt (componentCandidate execution.graph comp candidate)
        run execution.measured edge.tail)
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run v) := by
  let cg := componentCandidate execution.graph comp candidate
  let foot := loopFootprintExt cg run execution.measured edge.tail
  have ht := componentRunX_original_nodes_covered hrun edge.tail
    (List.getElem?_eq_some_iff.mp howner).1
  have hv := componentRunX_original_nodes_covered hrun v (List.getElem?_eq_some_iff.mp htarget).1
  have hbOwn : (cg.nodes.getD edge.tail default).border = 0 := by
    simp only [cg, List.getD_eq_getElem?_getD, howner, Option.getD_some, hplain]
  have hbTarget : (cg.nodes.getD v default).border ≠ -2 := by
    simpa only [cg, List.getD_eq_getElem?_getD, htarget, Option.getD_some, hzero] using
      (by decide : (0 : Int) ≠ -2)
  have hframe := plain_frame_eq_boxRect execution.params cg run v hv hbTarget
  have hframeOwn := plain_frame_eq_boxRect execution.params cg run edge.tail ht (by omega)
  have hx : foot.x = RouteImpl.leftOf run.proper run.xs edge.tail +
      RouteImpl.nodeW run.proper edge.tail := by
    change (frameRect execution.params cg run edge.tail).x +
      (frameRect execution.params cg run edge.tail).w = _
    rw [hframeOwn] <;> rfl
  change Disjoint foot (frameRect execution.params cg run v)
  rw [hframe]
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hlanes, _, _⟩ := componentRunX_spec hrun
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel hproxy).2.1
  obtain ⟨_, hnonneg, _, hcovered, _⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hlanes).1
  let ownRank := (rk run.proper.rank edge.tail).toNat
  let boxRank := (rk run.proper.rank v).toNat
  obtain ⟨ownLayer, hownLayer, hmemOwn, _⟩ := hcovered edge.tail ht
  obtain ⟨boxLayer, hboxLayer, hmemBox, _⟩ := hcovered v hv
  change run.layers[ownRank]? = some ownLayer at hownLayer
  change run.layers[boxRank]? = some boxLayer at hboxLayer
  rcases Nat.lt_trichotomy ownRank boxRank with hlt | heq | hgt
  · obtain ⟨_, _, _, hbelow⟩ :=
      XLEM_footBelow_holds exactIds (XLEM_plainReserve_holds exactIds)
        inp o res execution comp candidate run (candidateOrder candidate) cg i edge
        hcomp rfl hrun hedge hself (by omega)
    have hsep := hbelow boxRank boxLayer (by rw [← hrankEq]; exact hlt) hboxLayer
    obtain ⟨_, _, _, hlo, _⟩ := componentRunX_node_rank_band hrun hv
    change run.top.getD boxRank 0 ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).y at hlo
    unfold Disjoint Rect.meetsInterior
    change foot.y + foot.h ≤ run.top.getD boxRank 0 at hsep
    omega
  · have hsame := hboxLayer
    rw [← heq, hownLayer] at hsame
    have hsame' : ownLayer = boxLayer := Option.some.inj hsame
    rw [← hsame'] at hmemBox
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hmemOwn
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hmemBox
    have hmem := List.mem_of_getElem? hownLayer
    obtain ⟨pt, hpt, hbpt⟩ := plain_coord_node hrun htarget hzero
    rcases Nat.lt_trichotomy a b with hab | hab | hba
    · have hprop := proxyWidths_plain_node hproxy hpt hbpt
      have hptProper : run.proper.nodes[v]? = some pt := by
        rw [← hdrop]
        exact hprop
      exact XLEM_plainRightGap_of_nonproxy exactIds inp o res execution comp candidate
        run (candidateOrder candidate) cg i edge v hcomp rfl hrun hedge hbOwn pt hptProper
        (by rw [hbpt]; decide) hmem ha hb hab
    · subst b
      have hvEq : v = edge.tail := Option.some.inj (hb.symm.trans ha)
      rw [hvEq]
      unfold Disjoint Rect.meetsInterior
      change ¬ (max foot.x (RouteImpl.leftOf run.proper run.xs edge.tail) < min _
        (RouteImpl.leftOf run.proper run.xs edge.tail + RouteImpl.nodeW run.proper edge.tail) ∧ _)
      omega
    · obtain ⟨po, hpo, hbpo⟩ := plain_coord_node hrun howner hplain
      have hordered := XLrr_fixedSep0_holds exactIds execution.params inp cg run
        execution.measured (candidateOrder candidate) hrun ownLayer b a v edge.tail pt po
        hmem hba hb ha hpt hpo hbpt hbpo
      have hwidth := (hnonneg edge.tail ht).1
      unfold Disjoint Rect.meetsInterior
      change ¬ (max foot.x (RouteImpl.leftOf run.proper run.xs v) < min _
        (RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v) ∧ _)
      omega
  · obtain ⟨_, _, hlo, _⟩ :=
      XLEM_footBelow_holds exactIds (XLEM_plainReserve_holds exactIds)
        inp o res execution comp candidate run (candidateOrder candidate) cg i edge
        hcomp rfl hrun hedge hself (by omega)
    rw [← hrankEq] at hlo
    change run.top.getD ownRank 0 ≤ foot.y at hlo
    obtain ⟨used, hused, _, _, hhi⟩ := componentRunX_node_rank_band hrun hv
    have hgap := (X_ReserveBands_holds exactIds hrun).2 boxRank ownRank used ownLayer
      hgt hused hownLayer
    change (RouteImpl.boxRect run.proper run.xs run.ys v).y +
      (RouteImpl.boxRect run.proper run.xs run.ys v).h ≤
        run.top.getD boxRank 0 + CoordsImpl.layerHeight run.coordinateProper used at hhi
    unfold Disjoint Rect.meetsInterior
    omega

private theorem fixed_leaf_not_in_ancestors {inp : Input} {key : Nat} {source : ModelBox}
    (hsource : inp.boxes[key]? = some source) (hleaf : ExactFixedLeaf inp source.id) :
    ∀ (fuel : Nat) (child : ModelBox), child ∈ inp.boxes →
      key ∉ Compound.ancestors inp.boxes fuel child.parent := by
  intro fuel
  induction fuel with
  | zero => intro child _; simp [Compound.ancestors]
  | succ fuel ih =>
    intro child hchild
    by_cases hpar : child.parent = ""
    · simp [Compound.ancestors, hpar]
    cases hfind : inp.boxes.findIdx? (fun box => box.id == child.parent) with
    | none => simp [Compound.ancestors, hfind]
    | some j =>
      obtain ⟨hj, hid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      have hjb : inp.boxes[j]? = some inp.boxes[j] := List.getElem?_eq_getElem hj
      have hjne : key ≠ j := by
        intro hkj
        subst j
        have heq := Option.some.inj (hjb.symm.trans hsource)
        exact hleaf child hchild hpar ((beq_iff_eq.mp hid).symm.trans (congrArg ModelBox.id heq))
      have hn := ih inp.boxes[j] (List.mem_of_getElem? hjb)
      simp [Compound.ancestors, hfind, hjb, hn, hjne]

private theorem fixed_leaf_outside_group_path
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hleaf : ExactFixedLeaf inp source.id)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry)
    {comp : List Nat} {candidate t : Nat} {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : owner.border = -2) : key ∉ owner.clusterPath := by
  intro hmem
  have hpath : owner.clusterPath ≠ [] := by
    intro hnil
    simp [hnil] at hmem
  obtain ⟨j, _, hj⟩ := componentCandidate_nonempty_path_source howner hpath
  have hlen := exactGraph_length execution.graph_eq
  have hj0 : j < execution.graph0.nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hj).1
    omega
  have horigin : execution.graph0.nodes[j]? = some execution.graph0.nodes[j] :=
    List.getElem?_eq_getElem hj0
  obtain ⟨mapped, hm, hborder, hpathEq, _⟩ := exactGraph_node_key execution.graph_eq horigin
  have hsame : mapped = owner := Option.some.inj (hm.symm.trans hj)
  rw [hsame] at hborder hpathEq
  have hb0 : (execution.graph0.nodes[j]'hj0).border = -2 := hborder.symm.trans hgroup
  obtain ⟨hdecl, prepared, hprepared, _, hcluster⟩ :=
    measuredGraph_group_origin execution.graph0_eq horigin hb0
  rw [hdecl, List.getElem?_map] at hprepared
  obtain ⟨box, hbox, hpreparedEq⟩ := Option.map_eq_some_iff.mp hprepared
  obtain ⟨_, _, hmappedPath⟩ := fixedSizes_path_index inp hbox
  rw [← hpreparedEq, hmappedPath, hdecl] at hcluster
  rw [hpathEq, hcluster] at hmem
  rcases List.mem_append.mp hmem with ha | ha
  · exact fixed_leaf_not_in_ancestors hsource hleaf inp.boxes.length
      box (List.mem_of_getElem? hbox) ha
  · have heq : key = j := List.mem_singleton.mp ha
    subst j
    obtain ⟨fixedNode, hnode, hzero⟩ := fixed_graph_border execution hsource hfixed
    have heq := congrArg Node.border (Option.some.inj (hnode.symm.trans hj))
    omega

/-- Actual group-loop geometry still needed: in the loop's own component,
    an original plain outsider in a different rank vertically overlaps the
    reservation. The remaining claim is a horizontal gap in these coordinates. -/
def ExactGroupLoopFixedLeafGap (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components execution.graph →
    ∀ {candidate : Nat} {run : Run},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
    ∀ {i : Nat} {edge : Edge},
      (componentCandidate execution.graph comp candidate).edges[i]? = some edge →
      edge.tail = edge.head →
    ∀ {owner : Node} {v key : Nat} {target : Node} {source : ModelBox} {entry : String × Size},
      (componentCandidate execution.graph comp candidate).nodes[edge.tail]? = some owner →
      owner.border = -2 →
      comp[v]? = some key →
      inp.boxes[key]? = some source →
      inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry →
      ExactFixedLeaf inp source.id →
      (componentCandidate execution.graph comp candidate).nodes[v]? = some target →
      target.border = 0 →
      target.clusterPath.contains owner.decl = false →
      (rk run.proper.rank v).toNat ≠ (rk run.proper.rank edge.tail).toNat →
      let cg := componentCandidate execution.graph comp candidate
      let foot := loopFootprintExt cg run execution.measured edge.tail
      let frame := frameRect execution.params cg run v
      0 < frame.w →
      max foot.y frame.y < min (foot.y + foot.h) (frame.y + frame.h) →
      foot.x + foot.w ≤ frame.x ∨ frame.x + frame.w ≤ foot.x

private theorem groupLoop_footprint_miss
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hgap : ExactGroupLoopFixedLeafGap exactIds)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head)
    {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[edge.tail]? = some owner)
    (hgroup : owner.border = -2)
    {v key : Nat} {target : Node} {source : ModelBox} {entry : String × Size}
    (hkey : comp[v]? = some key) (hsource : inp.boxes[key]? = some source)
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry)
    (hleaf : ExactFixedLeaf inp source.id)
    (htarget : (componentCandidate execution.graph comp candidate).nodes[v]? = some target)
    (hzero : target.border = 0) :
    Disjoint (loopFootprintExt (componentCandidate execution.graph comp candidate)
        run execution.measured edge.tail)
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run v) := by
  let cg := componentCandidate execution.graph comp candidate
  let foot := loopFootprintExt cg run execution.measured edge.tail
  let frame := frameRect execution.params cg run v
  change Disjoint foot frame
  by_cases hmember : target.clusterPath.contains owner.decl = true
  · have hcontained := (exactRunFrameNesting execution hwf hfp).1 comp candidate
      run (candidateOrder candidate) hcomp hrun edge.tail v owner target howner hgroup
      htarget hzero hmember
    have hside : frame.x + frame.w ≤ foot.x := hcontained.2.1
    unfold Disjoint Rect.meetsInterior
    omega
  have hv := componentRunX_original_nodes_covered hrun v (List.getElem?_eq_some_iff.mp htarget).1
  have ht := componentRunX_original_nodes_covered hrun edge.tail
    (List.getElem?_eq_some_iff.mp howner).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, _, _⟩ := componentRunX_spec hrun
  have hcovered := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hlanes).1).2.2.2.1
  by_cases hrank : (rk run.proper.rank v).toNat = (rk run.proper.rank edge.tail).toNat
  · obtain ⟨layer, hlayer, htMem, _⟩ := hcovered edge.tail ht
    obtain ⟨layer', hlayer', hvMem, _⟩ := hcovered v hv
    rw [hrank, hlayer] at hlayer'
    have heq : layer = layer' := Option.some.inj hlayer'
    subst layer'
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp htMem
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvMem
    have hnodeDecl : RouteImpl.nodeDecl run.proper v = key :=
      x_exclusiveRunNodeDecl_holds exactIds inp o res execution
        comp candidate run hcomp hrun v key source hkey hsource
    have hscope : RouteImpl.nodeDecl run.proper v ∉
        ((cg.nodes[edge.tail]?).map (·.clusterPath)).getD [] := by
      simpa only [cg, hnodeDecl, howner, Option.map_some, Option.getD_some] using
        fixed_leaf_outside_group_path execution hsource hleaf hfixed howner hgroup
    have hg : (cg.nodes.getD edge.tail default).border ≠ 0 := by
      simpa only [cg, List.getD_eq_getElem?_getD, howner, Option.getD_some, hgroup] using
        (by decide : (-2 : Int) ≠ 0)
    have hmarker := XLEG_groupMarkerOrderX_of_leaves exactIds
      (xleg_loopMarkerCoreX_holds exactIds) (xleg_loopMarkerLayerOrderX_holds exactIds)
      (xleg_loopMarkerSpanX_holds exactIds)
    have hmiss := XLEM_groupOwnerMiss_holds exactIds hmarker inp o res execution hwf hfp
      comp candidate run (candidateOrder candidate) cg i edge v hcomp rfl hrun
      hedge hself hv (X_componentRun_source_isReal hrun htarget) hscope
      (by rw [← hself]; exact hscope) hg (List.mem_of_getElem? hlayer) hpu hpv
    have htargetBorder : (cg.nodes.getD v default).border ≠ -2 := by
      simpa only [cg, List.getD_eq_getElem?_getD, htarget, Option.getD_some, hzero] using
        (by decide : (0 : Int) ≠ -2)
    change Disjoint foot (frameRect execution.params cg run v)
    rw [plain_frame_eq_boxRect _ _ _ _ hv htargetBorder]
    exact hmiss
  · unfold Disjoint Rect.meetsInterior
    intro hmeet
    obtain ⟨hx, hy⟩ := hmeet
    have hwidth : 0 < frame.w := by omega
    have hsep : foot.x + foot.w ≤ frame.x ∨ frame.x + frame.w ≤ foot.x :=
      hgap execution hwf hfp hcomp hrun hedge hself howner hgroup
        hkey hsource hfixed hleaf htarget hzero (Bool.eq_false_iff.mpr hmember) hrank hwidth hy
    omega

/-- Exact execution keeps the route array length. File-local copy of the
private fact in the repaired `ExactFlatC5ChosenPart` and
`ExactFlatC5SelfRoutes` files. -/
private theorem SceneExecutionX.components_routes_sizeX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.componentsAcc.routes.size = inp.routes.length := by
  have h := ExactStraighten.components_fold_routes_size execution.params exactIds inp o execution.graph
    execution.measured (components execution.graph) _ _ execution.components_eq
  simpa only [Array.size_replicate] using h

set_option maxHeartbeats 700000 in
/-- An emitted route cannot hit a box read from a different packed part.
    Both are looked up in the executed scene; this also covers degenerate shelves. -/
theorem SceneExecutionX.chosenRoute_misses_other_part
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i decl : Nat} {points : List Point} {minX minY : Int}
    (hlocal : q.1.2.routes[i]? = some (decl, points.map (shiftPoint (0 - minX) (-minY))))
    (hnd : (q.1.2.routes.map (·.1)).Nodup)
    {model : ModelRoute} (hmodel : inp.routes[decl]? = some model)
    {route : Route} (hroute : res.scene.routes[decl]? = some route)
    {c' : Nat} (hne : c ≠ c') {part : List Nat × Part}
    (hpart : execution.componentsAcc.parts[c']? = some part)
    {pos key : Nat} (hpos : part.1[pos]? = some key)
    {frame : Box} (hframe : res.scene.boxes[key]? = some frame) :
    ¬ Polyline.hitsRect route.points frame.rect := by
  obtain ⟨source, hsource, _, _, _, hframeEq⟩ := sceneBox_source_rectX execution hframe
  have hkeyLen := (List.getElem?_eq_some_iff.mp hsource).1
  have hdeclLt : decl < inp.routes.length := (List.getElem?_eq_some_iff.mp hmodel).1
  have hshelf := (List.getElem?_zip_eq_some.mp hselected).2
  have hc' := part_packed_box_lenX execution packed hpacked hpart
  have hshelf' : packed.boxes[c']? = some packed.boxes[c'] := List.getElem?_eq_getElem hc'
  let shelf := packed.boxes[c']
  let other : (List Nat × Part) × Rect := (part, shelf)
  have hother : (execution.componentsAcc.parts.zip packed.boxes)[c']? = some other :=
    List.getElem?_zip_eq_some.mpr ⟨hpart, hshelf'⟩
  obtain ⟨candidate, run, loops, area, _, _, hotherPart, _⟩ :=
    part_frame_lookupX execution packed hpacked hpart hshelf'
  have hpart' : other.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph other.1.1 candidate) run 0
      execution.measured loops with area := area } := hotherPart
  obtain ⟨hrect, hcontain⟩ :=
    chosen_frame_packed execution hpacked hother hpart' hpos hkeyLen
  have hsep : RectAxisSeparated q.2 shelf := pack_shelves_axisSeparatedX hpacked hne hshelf hshelf'
  have hframeSep : RectAxisSeparated q.2 (execution.packedAcc.rects.getD key default) := by
    have hsub : shelf.Contained (execution.packedAcc.rects.getD key default) := by
      rw [hrect]
      exact hcontain
    simp only [RectAxisSeparated] at hsep ⊢
    simp only [Rect.Contained] at hsub
    omega
  have hsuff : res.scene.routes[decl]? =
      some (Route.mk model.id model.fromId model.toId model.orthogonal
        (points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y minX minY))) →
      ¬ Polyline.hitsRect route.points frame.rect := by
    intro hscene0
    have hrouteEq : route.points =
        points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y minX minY) :=
      congrArg Route.points (Option.some.inj (hroute.symm.trans hscene0))
    have hp := chosen_route_packed_points execution hpacked hselected
      (List.mem_of_getElem? hlocal)
    have hmiss := Polyline.not_hits_of_allMiss (allSegsMiss_of_pointIn_of_separated hframeSep
      _ hp)
    rw [hrouteEq, hframeEq]
    have htransport := not_hitsRect_shift_orient o.direction execution.packedAcc.canvasH
      execution.params.canvasMargin execution.params.canvasMargin _ _ hmiss
    change ¬ Polyline.hitsRect (points.map (fun p =>
      shiftPoint execution.params.canvasMargin execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH
          (shiftPoint (q.2.x - minX) (q.2.y - minY) p)))) _
    simpa only [List.map_map, Function.comp_def] using htransport
  have hscene := X_chosen_part_route_from_points execution packed hpacked hselected
    hlocal hnd hmodel
  rcases hscene with hscene | ⟨ptsCorr, hcor, hrouteC⟩
  · exact hsuff hscene
  · obtain ⟨_, _, _, _, hptsCorrEq⟩ := hcor
    have hgetD : execution.straightAcc.routes.getD decl [] = ptsCorr :=
      ExactStraighten.straight_points_of_scene execution hrouteC
    have hptsNe : ptsCorr ≠ [] := by
      rw [hptsCorrEq]
      intro hcon
      simp at hcon
    have hpts : execution.straightAcc.routes[decl]? = some ptsCorr := by
      have hgd : (execution.straightAcc.routes[decl]?.getD []) = ptsCorr := by
        have h := hgetD
        rw [Array.getD_eq_getD_getElem?] at h
        exact h
      cases ho : execution.straightAcc.routes[decl]? with
      | none =>
        simp only [ho, Option.getD_none] at hgd
        exact absurd hgd.symm hptsNe
      | some v =>
        simp only [ho, Option.getD_some] at hgd
        exact congrArg Option.some hgd
    rcases ExactStraighten.route_cases execution X_componentRun_normalized_source hpts with hpackedPts | hinst
    · have hsize : decl < execution.componentsAcc.routes.size := by
        rw [execution.components_routes_sizeX]
        exact hdeclLt
      have hpackedRoute := ExactStraighten.actual_components_packAcc_routes_getD (by rfl)
        execution.components_eq
        (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
        packed execution.packed_eq hpacked c q hselected i _ _ [] hlocal hnd hsize
      have hgd : execution.packedAcc.routes.getD decl [] = ptsCorr := by
        rw [Array.getD_eq_getD_getElem?, hpackedPts, Option.getD_some]
      have hPlaced : (points.map (shiftPoint (0 - minX) (-minY))).map
          (shiftPoint q.2.x q.2.y) = ptsCorr :=
        hpackedRoute.symm.trans hgd
      have hneg : -minY = 0 - minY := by omega
      have hEq : (ptsCorr.map fun p => shiftPoint execution.params.canvasMargin
          execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)) =
          (points.map (routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y minX minY)) := by
        rw [← hPlaced, hneg, routePointTransport_eq]
      have hScenePacked : res.scene.routes[decl]? =
          some (Route.mk model.id model.fromId model.toId model.orthogonal
            (points.map (routePointTransport execution.params.canvasMargin o.direction
              execution.packedAcc.canvasH q.2.x q.2.y minX minY))) := by
        rw [hEq] at hrouteC
        exact hrouteC
      exact hsuff hScenePacked
    · have hpartC := (List.getElem?_zip_eq_some.mp hselected).1
      have hshelfC := (List.getElem?_zip_eq_some.mp hselected).2
      obtain ⟨candidateI, runI, loopsI, areaI, hrunI, _, hpartEqI, _⟩ :=
        part_frame_lookupX execution packed hpacked hpartC hshelfC
      have hmemRoute : (decl, points.map (shiftPoint (0 - minX) (-minY))) ∈ q.1.2.routes :=
        List.mem_of_getElem? hlocal
      have hmemDecl : decl ∈
          (componentCandidate execution.graph q.1.1 candidateI).edges.map (·.decl) := by
        have h2 : decl ∈ q.1.2.routes.map (·.1) := List.mem_map_of_mem hmemRoute
        rw [hpartEqI] at h2
        have h2bare : decl ∈ (placeComponentExact execution.params
            (componentCandidate execution.graph q.1.1 candidateI) runI 0
            execution.measured loopsI).routes.map (·.1) :=
          h2
        rw [ExactStraighten.placeComponentExact_routes_decls] at h2bare
        exact h2bare
      obtain ⟨j, edgeOur, hedgeOur, hdeclOur⟩ :
          ∃ (j : Nat) (edge : Edge), (componentCandidate execution.graph q.1.1 candidateI).edges[j]? =
            some edge ∧ edge.decl = decl := by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmemDecl
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
        exact ⟨k, _, hk, rfl⟩
      obtain ⟨tailKey, headKey, tailRect, headRect, spanT, hTailLt, hHeadLt, hKeyTB, hKeyHB,
        htkA, hhkA, hlookT, hlookH, hthT, hhhT, htxTEq, htwTEq, hhxTEq, hhwTEq,
        htxT, htwT, hhxT, hhwT, htopT, hbotT,
        hptsT⟩ :=
        execution.installed_part_edge_rects hinst hselected hedgeOur hdeclOur hrunI hpartEqI
      have hptsEq2 : ptsCorr = [⟨spanT.column, spanT.top⟩, ⟨spanT.column, spanT.bottom⟩] := by
        rw [hptsT]
        rfl
      obtain ⟨htailEq, htailSub⟩ := chosen_frame_packed execution hpacked hselected
        hpartEqI htkA hKeyTB
      obtain ⟨hheadEq, hheadSub⟩ := chosen_frame_packed execution hpacked hselected
        hpartEqI hhkA hKeyHB
      have htailGet : execution.packedAcc.rects.getD tailKey default = tailRect := by
        simp only [Array.getD_eq_getD_getElem?, hlookT, Option.getD_some]
      have hheadGet : execution.packedAcc.rects.getD headKey default = headRect := by
        simp only [Array.getD_eq_getD_getElem?, hlookH, Option.getD_some]
      have htailIn : q.2.Contained tailRect := by
        rw [← htailGet, htailEq]
        exact htailSub
      have hheadIn : q.2.Contained headRect := by
        rw [← hheadGet, hheadEq]
        exact hheadSub
      have hpCorr : ∀ p ∈ ptsCorr, PointIn q.2 p := by
        intro p hp
        rw [hptsEq2] at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · simp only [PointIn] at htailIn ⊢
          simp only [Rect.Contained] at htailIn
          omega
        · simp only [PointIn] at hheadIn ⊢
          simp only [Rect.Contained] at hheadIn
          omega
      have hrouteEqC : route.points =
          ptsCorr.map fun p => shiftPoint execution.params.canvasMargin
            execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH p) :=
        congrArg Route.points (Option.some.inj (hroute.symm.trans hrouteC))
      have hmissC := Polyline.not_hits_of_allMiss
        (allSegsMiss_of_pointIn_of_separated hframeSep _ hpCorr)
      rw [hrouteEqC, hframeEq]
      exact not_hitsRect_shift_orient o.direction execution.packedAcc.canvasH
        execution.params.canvasMargin execution.params.canvasMargin _ _ hmissC

set_option maxHeartbeats 1200000 in
/-- The self-loop branch of `ExactFlatFixedLeafMiss`. Distinct packed shelves,
    plain loop owners, same-rank group loop owners, and descendants of the
    looping group need no additional geometric premise. -/
theorem layoutX_selfLoop_fixedLeaf_frame_miss_of_group_gap
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutX exactIds inp o = .ok res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hgap : ExactGroupLoopFixedLeafGap exactIds)
    {boxId : String} {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == boxId) = some entry)
    (hleaf : ExactFixedLeaf inp boxId)
    {frame : Box} (hframe : res.scene.boxes.find? (fun box => box.id == boxId) = some frame)
    {route : Route} (hroute : route ∈ res.scene.routes) (hself : route.fromId = route.toId) :
    ¬ Polyline.hitsRect route.points frame.rect := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hroute
  have hkLen : k < inp.routes.length := by
    rw [← sceneOf_routes_length execution.params inp o execution.lines
      execution.straightAcc execution.measured, ← execution.scene_eq]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ := execution.route_component_sourceX hkLen
  have hrouteAt : res.scene.routes[edge.decl]? = some route := by rwa [hdecl]
  obtain ⟨⟨model, hmodel⟩, hselfEdge⟩ := scene_selfLoop_candidate execution hedge hrouteAt hself
  let cg := componentCandidate execution.graph q.1.1 candidate
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  obtain ⟨hparts, _⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
  have hcomp : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  have hv := (candidate_edge_endpoints_bounded_general execution.graph q.1.1 candidate
    hcomp (sceneExecutionX_edges_bounded execution) (List.mem_of_getElem? hedge)).1
  obtain ⟨native, hnative, hemit, hnativeDecl⟩ := selected_loop_points hloops hedge hv hselfEdge
  have hrouteLocal : q.1.2.routes[i]? = some (edge.decl,
      native.2.points.map (shiftPoint (0 - bounds.minX) (-bounds.minY))) := by
    rw [hpart]
    exact hemit
  have hnd : (q.1.2.routes.map (·.1)).Nodup :=
    chosen_route_decls execution hpart
  have hrouteDecl : edge.decl < inp.routes.length := (List.getElem?_eq_some_iff.mp hmodel).1
  obtain ⟨key, hframeAt⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hframe)
  obtain ⟨source, hsource, hsourceId, _, _, hframeEq⟩ :=
    sceneBox_source_rectX execution hframeAt
  have hid : source.id = boxId := hsourceId.symm.trans (by simpa using List.find?_some hframe)
  have hsourceFixed : inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry :=
    by simpa only [hid] using hfixed
  have hsourceLeaf : ExactFixedLeaf inp source.id := by simpa only [hid] using hleaf
  have hkeyLen := (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨part, pos, c', _, hentry, hpos⟩ := key_part_positionX execution hkeyLen
  have hsuff : res.scene.routes[edge.decl]? =
      some (Route.mk model.id model.fromId model.toId model.orthogonal
        (native.2.points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY))) →
      ¬ Polyline.hitsRect route.points frame.rect := by
    intro hscene0
    have hrouteEq : route.points =
        native.2.points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY) :=
      congrArg Route.points (Option.some.inj (hrouteAt.symm.trans hscene0))
    by_cases hsame : c' = c
    · subst c'
      have heq : part = q.1 := Option.some.inj (hentry.symm.trans (zip_getElem?_left hselected))
      subst part
      obtain ⟨hrect, _⟩ := chosen_frame_packed execution hpacked hselected hpart hpos hkeyLen
      obtain ⟨target, htargetGlobal, htargetZero⟩ :=
        fixed_graph_border execution hsource hsourceFixed
      have htarget : cg.nodes[pos]? = some target := component_node_lookupX hpos htargetGlobal
      have hslot := chosen_candidate_slot_pos execution q.1.1 candidate
      obtain ⟨v, _, origin, horigin, horiginDecl, horiginTail, _, hwidth, hheight, hpoints⟩ :=
        componentLoops_entry_in_footprintExt hloops hslot hnative
      have hndCg := componentCandidate_decls_nodup execution.graph q.1.1 candidate
        (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
      have horiginEq : origin = edge :=
        nodup_map_eq_of_mem hndCg (List.mem_filter.mp horigin).1 (List.mem_of_getElem? hedge)
          (horiginDecl.symm.trans hnativeDecl)
      have hvEq : v = edge.tail := horiginTail.symm.trans (congrArg Edge.tail horiginEq)
      rw [hvEq] at hwidth hheight hpoints
      obtain ⟨owner, howner⟩ : ∃ owner, cg.nodes[edge.tail]? = some owner :=
        ⟨_, List.getElem?_eq_getElem hv⟩
      have hdisj : Disjoint (loopFootprintExt cg run execution.measured edge.tail)
          (frameRect execution.params cg run pos) := by
        rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq
          howner).1 with hzero | hgroup | hbottom
        · exact componentRunX_plainLoop_footprint_misses_plain_frame execution
            hcomp hrun hedge hselfEdge howner hzero htarget htargetZero
        · exact groupLoop_footprint_miss execution hwf hfp hgap hcomp hrun hedge hselfEdge
            howner hgroup hpos hsource hsourceFixed hsourceLeaf htarget htargetZero
        · exact False.elim (exactBottomNoLoopX execution q.1.1 candidate run
            (candidateOrder candidate) hcomp cg rfl hrun edge.tail owner howner hbottom
            ⟨edge, List.mem_of_getElem? hedge, rfl, hselfEdge.symm⟩)
      have hmiss := polyline_in_box_misses_disjoint hwidth hheight hpoints hdisj
      rw [hrouteEq, hframeEq, hrect]
      have hshift : shiftRect q.2.x q.2.y
          (shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect execution.params cg run pos)) =
          shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY)
            (frameRect execution.params cg run pos) := by
        rw [shiftRect_shiftRect]
        congr 1 <;> omega
      rw [hshift]
      exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
    · exact execution.chosenRoute_misses_other_part hpacked hselected hrouteLocal hnd
        hmodel hrouteAt (Ne.symm hsame) hentry hpos hframeAt
  have hscene := X_chosen_part_route_from_points execution packed hpacked hselected
    hrouteLocal hnd hmodel
  rcases hscene with hscene | ⟨ptsCorr, hcor, hrouteC⟩
  · exact hsuff hscene
  · obtain ⟨_, _, _, _, hptsCorrEq⟩ := hcor
    have hgetD : execution.straightAcc.routes.getD edge.decl [] = ptsCorr :=
      ExactStraighten.straight_points_of_scene execution hrouteC
    have hptsNe : ptsCorr ≠ [] := by
      rw [hptsCorrEq]
      intro hcon
      simp at hcon
    have hpts : execution.straightAcc.routes[edge.decl]? = some ptsCorr := by
      have hgd : (execution.straightAcc.routes[edge.decl]?.getD []) = ptsCorr := by
        have h := hgetD
        rw [Array.getD_eq_getD_getElem?] at h
        exact h
      cases ho : execution.straightAcc.routes[edge.decl]? with
      | none =>
        simp only [ho, Option.getD_none] at hgd
        exact absurd hgd.symm hptsNe
      | some v =>
        simp only [ho, Option.getD_some] at hgd
        exact congrArg Option.some hgd
    rcases ExactStraighten.route_cases execution X_componentRun_normalized_source hpts with hpackedPts | hinst
    · have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
        rw [execution.components_routes_sizeX]
        exact hrouteDecl
      have hpackedRoute := ExactStraighten.actual_components_packAcc_routes_getD (by rfl)
        execution.components_eq
        (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
        packed execution.packed_eq hpacked c q hselected i _ _ [] hrouteLocal hnd hrouteSize
      have hpsize : edge.decl < execution.packedAcc.routes.size := by
        rw [packAcc_routes_size execution.packed_eq, execution.components_routes_sizeX]
        exact hrouteDecl
      have hgetP : execution.packedAcc.routes[edge.decl]? =
          some (execution.packedAcc.routes.getD edge.decl []) := by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpsize,
          Option.getD_some]
      have hBridgePts : ptsCorr = execution.packedAcc.routes.getD edge.decl [] :=
        Option.some.inj (hpackedPts.symm.trans hgetP)
      have hneg : -bounds.minY = 0 - bounds.minY := by omega
      have hptsMap : (ptsCorr.map fun p => shiftPoint execution.params.canvasMargin
          execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)) =
          (native.2.points.map (routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY)) := by
        rw [hBridgePts, hpackedRoute, hneg, routePointTransport_eq]
      have hscenePacked : res.scene.routes[edge.decl]? =
          some (Route.mk model.id model.fromId model.toId model.orthogonal
            (native.2.points.map (routePointTransport execution.params.canvasMargin o.direction
              execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY))) := by
        rw [hptsMap] at hrouteC
        exact hrouteC
      exact hsuff hscenePacked
    · exact absurd hinst
        (execution.straight_corridor_not_selfloop hselected hedge hselfEdge)

end Elegant.Layered.PipelineImpl
