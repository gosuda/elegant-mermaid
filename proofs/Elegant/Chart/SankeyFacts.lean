import Elegant.Chart.Sankey

set_option autoImplicit false

namespace Elegant.Chart.Sankey

theorem roundHalfUp_full_strength (n : Int) : roundHalfUp (n * 65536) 65536 = n := by
  unfold roundHalfUp
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem final_beta :
    max (65536 - Int.fdiv (65536 * (99 : Int)^5) ((100 : Int)^5))
      (Int.fdiv ((Int.ofNat 5 + 1) * 65536) 6) = 65536 := by decide

def scaledSum (values : List Int) (ky : Int) : Int :=
  (values.map (fun v => Int.fdiv (v * ky) 65536)).sum

theorem scaledSum_le (values : List Int) (ky : Int) :
    scaledSum values ky ≤ Int.fdiv (values.sum * ky) 65536 := by
  induction values with
  | nil => simp [scaledSum]
  | cons v vs ih =>
    simp only [scaledSum, List.map_cons, List.sum_cons] at *
    rw [Int.add_mul]
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 65536 by decide)] at *
    have h := Int.ediv_add_ediv_le_add_ediv (x := v * ky) (y := vs.sum * ky)
      (show (0 : Int) < 65536 by decide)
    omega

theorem relax_zero (f : Flow) : relax 0 f = f := by rfl

theorem relax_succ (count : Nat) (f : Flow) :
    relax (count + 1) f = iteration (count + 1) count
      ((List.range count).foldl (fun f i => iteration (count + 1) i f) f) := by
  simp [relax, List.range_succ, List.foldl_append]

theorem relaxation_schedule_length (count : Nat) : (List.range count).length = count := by
  simp

theorem linkWidths_le_nodeHeight (values : List Int) (value ky : Int)
    (hvalue : values.sum ≤ value) (hky : 0 ≤ ky) :
    scaledSum values ky ≤ Int.fdiv (value * ky) 65536 := by
  have hmul := Int.mul_le_mul_of_nonneg_right hvalue hky
  have hdiv := Int.ediv_le_ediv (show (0 : Int) < 65536 by decide) hmul
  have hsum := scaledSum_le values ky
  simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 65536 by decide)] at *
  omega

theorem columnHeights_le_room (values : List Int) (ky room : Int)
    (hproduct : values.sum * ky ≤ room * 65536) :
    scaledSum values ky ≤ room := by
  have hsum := scaledSum_le values ky
  simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 65536 by decide)] at hsum
  omega

theorem pushDownNode_full_strength (n : Node) (y : Int) :
    y ≤ (pushDownNode n y 65536).y0 := by
  simp only [pushDownNode, roundHalfUp_full_strength]
  omega

theorem pushDownNode_preserves_height (n : Node) (y beta : Int) :
    (pushDownNode n y beta).y1 - (pushDownNode n y beta).y0 = n.y1 - n.y0 := by
  simp only [pushDownNode]
  omega

theorem counted_fold (count : Nat) (indices : List Nat) (f : Flow) (n : Nat) :
    indices.foldl (fun acc i => (iteration count i acc.1, acc.2 + 1)) (f, n) =
      (indices.foldl (fun f i => iteration count i f) f, n + indices.length) := by
  induction indices generalizing f n with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [List.length_cons]
    congr 1
    omega

theorem sankey_passes_exact (count : Nat) (f : Flow) :
    countedRelax count f = (relax count f, count) := by
  simp only [countedRelax, counted_fold, List.length_range, Nat.zero_add, relax]

theorem foldMin_le_seed (rs : List Rect) (seed : Int) (axis : Rect → Int) :
    rs.foldl (fun x r => min x (axis r)) seed ≤ seed := by
  induction rs generalizing seed with
  | nil => simp
  | cons r rest ih =>
    simp only [List.foldl_cons]
    have h := ih (min seed (axis r))
    have hm := Int.min_le_left seed (axis r)
    omega

theorem foldMax_ge_seed (rs : List Rect) (seed : Int) (axis : Rect → Int) :
    seed ≤ rs.foldl (fun x r => max x (axis r)) seed := by
  induction rs generalizing seed with
  | nil => simp
  | cons r rest ih =>
    simp only [List.foldl_cons]
    have h := ih (max seed (axis r))
    have hm := Int.le_max_left seed (axis r)
    omega

theorem foldMin_le_member (rs : List Rect) (seed : Int) (axis : Rect → Int)
    (r : Rect) (hr : r ∈ rs) :
    rs.foldl (fun x r => min x (axis r)) seed ≤ axis r := by
  induction rs generalizing seed with
  | nil => simp at hr
  | cons a rest ih =>
    simp only [List.mem_cons] at hr
    simp only [List.foldl_cons]
    rcases hr with h | h
    · subst a
      have h := foldMin_le_seed rest (min seed (axis r)) axis
      have hm := Int.min_le_right seed (axis r)
      omega
    · exact ih (min seed (axis a)) h

theorem foldMax_ge_member (rs : List Rect) (seed : Int) (axis : Rect → Int)
    (r : Rect) (hr : r ∈ rs) :
    axis r ≤ rs.foldl (fun x r => max x (axis r)) seed := by
  induction rs generalizing seed with
  | nil => simp at hr
  | cons a rest ih =>
    simp only [List.mem_cons] at hr
    simp only [List.foldl_cons]
    rcases hr with h | h
    · subst a
      have h := foldMax_ge_seed rest (max seed (axis r)) axis
      have hm := Int.le_max_right seed (axis r)
      omega
    · exact ih (max seed (axis a)) h

theorem translated_rect_contained (r : Rect) (loX loY hiX hiY : Int)
    (hx : loX ≤ r.x) (hy : loY ≤ r.y)
    (hr : r.x + r.w ≤ hiX) (hb : r.y + r.h ≤ hiY) :
    Rect.Contained ⟨0, 0, hiX - loX, hiY - loY⟩
      ⟨r.x - loX, r.y - loY, r.w, r.h⟩ := by
  simp only [Rect.Contained]
  omega

def settleNodeList (py : Int) : List Node → Int → List Node
  | [], _ => []
  | n :: ns, y =>
    let n := pushDownNode n y 65536
    n :: settleNodeList py ns (n.y1 + py)

theorem settleNodeList_lower (py : Int) (nodes : List Node) (y : Int)
    (hpy : 0 ≤ py) (heights : ∀ n ∈ nodes, n.y0 ≤ n.y1) :
    ∀ n ∈ settleNodeList py nodes y, y ≤ n.y0 := by
  induction nodes generalizing y with
  | nil => simp [settleNodeList]
  | cons n ns ih =>
    intro v hv
    simp only [settleNodeList, List.mem_cons] at hv
    rcases hv with hv | hv
    · subst v
      exact pushDownNode_full_strength n y
    · have hrest : ∀ a ∈ ns, a.y0 ≤ a.y1 := by
        intro a ha
        exact heights a (List.mem_cons_of_mem n ha)
      have h := ih ((pushDownNode n y 65536).y1 + py) hrest v hv
      have hn := pushDownNode_full_strength n y
      have hh := heights n (by simp)
      have hp := pushDownNode_preserves_height n y 65536
      omega

theorem settleNodeList_heights (py : Int) (nodes : List Node) (y : Int)
    (heights : ∀ n ∈ nodes, n.y0 ≤ n.y1) :
    ∀ n ∈ settleNodeList py nodes y, n.y0 ≤ n.y1 := by
  induction nodes generalizing y with
  | nil => simp [settleNodeList]
  | cons n ns ih =>
    intro v hv
    simp only [settleNodeList, List.mem_cons] at hv
    rcases hv with hv | hv
    · subst v
      have hh := heights n (by simp)
      have hp := pushDownNode_preserves_height n y 65536
      omega
    · exact ih _ (fun a ha => heights a (List.mem_cons_of_mem n ha)) v hv

theorem settleNodeList_gaps (py : Int) (nodes : List Node) (y : Int)
    (hpy : 0 ≤ py) (heights : ∀ n ∈ nodes, n.y0 ≤ n.y1) :
    (settleNodeList py nodes y).Pairwise (fun a b => a.y1 + py ≤ b.y0) := by
  induction nodes generalizing y with
  | nil => simp [settleNodeList]
  | cons n ns ih =>
    have hrest : ∀ a ∈ ns, a.y0 ≤ a.y1 := fun a ha =>
      heights a (List.mem_cons_of_mem n ha)
    rw [settleNodeList, List.pairwise_cons]
    constructor
    · exact settleNodeList_lower py ns _ hpy hrest
    · exact ih _ hrest

theorem settleNodeList_disjoint (py : Int) (nodes : List Node) (y : Int)
    (hpy : 0 ≤ py) (heights : ∀ n ∈ nodes, n.y0 ≤ n.y1) :
    (settleNodeList py nodes y).Pairwise (fun a b => a.y1 ≤ b.y0) := by
  have h := settleNodeList_gaps py nodes y hpy heights
  exact h.imp (by intro a b hab; omega)

theorem rounding_nonnegative (v ky : Int) (hv : 0 ≤ v) (hky : 0 ≤ ky) :
    0 ≤ Int.fdiv (v * ky) 65536 := by
  have hm := Int.mul_nonneg hv hky
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem linkMin_le_seed (links : Array Link) (seed : Int) :
    links.foldl (fun y l => min (min y l.y0) l.y1) seed ≤ seed := by
  apply Array.foldl_induction (motive := fun _ y => y ≤ seed)
  · exact Int.le_refl _
  · intro i y hy
    have h0 := Int.min_le_left y links[i].y0
    have h1 := Int.min_le_left (min y links[i].y0) links[i].y1
    omega

theorem linkMax_ge_seed (links : Array Link) (seed : Int) :
    seed ≤ links.foldl (fun y l => max (max y l.y0) l.y1) seed := by
  apply Array.foldl_induction (motive := fun _ y => seed ≤ y)
  · exact Int.le_refl _
  · intro i y hy
    have h0 := Int.le_max_left y links[i].y0
    have h1 := Int.le_max_left (max y links[i].y0) links[i].y1
    omega

theorem normalization_rect_in_canvas (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) (r : Rect)
    (hr : r ∈ rects.toList ++ labels.map (·.rect)) :
    let all := rects.toList ++ labels.map (·.rect)
    let loX := all.foldl (fun x r => min x r.x) 0
    let loY := f.links.foldl (fun y l => min (min y l.y0) l.y1)
      (all.foldl (fun y r => min y r.y) 0)
    let hiX := all.foldl (fun x r => max x (r.x + r.w))
      (labels.foldl (fun x p => max x (p.rect.x + p.rect.w)) width)
    let hiY := f.links.foldl (fun y l => max (max y l.y0) l.y1)
      (all.foldl (fun y r => max y (r.y + r.h))
        (labels.foldl (fun y p => max y (p.rect.y + p.rect.h)) height))
    Rect.Contained ⟨0, 0, hiX - loX, hiY - loY⟩
      ⟨r.x - loX, r.y - loY, r.w, r.h⟩ := by
  dsimp only
  apply translated_rect_contained
  · exact foldMin_le_member _ 0 (·.x) r hr
  · have h0 := foldMin_le_member _ 0 (·.y) r hr
    have h1 := linkMin_le_seed f.links
      ((rects.toList ++ labels.map (·.rect)).foldl (fun y r => min y r.y) 0)
    omega
  · exact foldMax_ge_member _ _ (fun r => r.x + r.w) r hr
  · have h0 := foldMax_ge_member (rects.toList ++ labels.map (·.rect))
      (labels.foldl (fun y p => max y (p.rect.y + p.rect.h)) height)
      (fun r => r.y + r.h) r hr
    have h1 := linkMax_ge_seed f.links
      ((rects.toList ++ labels.map (·.rect)).foldl (fun y r => max y (r.y + r.h))
        (labels.foldl (fun y p => max y (p.rect.y + p.rect.h)) height))
    omega

theorem nodeValue_bounds_incoming (incoming outgoing : List Int) :
    incoming.sum ≤ max incoming.sum outgoing.sum := Int.le_max_left _ _

theorem nodeValue_bounds_outgoing (incoming outgoing : List Int) :
    outgoing.sum ≤ max incoming.sum outgoing.sum := Int.le_max_right _ _

theorem link_sum_le_height_core (incoming outgoing : List Int) (ky : Int) (hky : 0 ≤ ky) :
    scaledSum incoming ky ≤ Int.fdiv (max incoming.sum outgoing.sum * ky) 65536 ∧
    scaledSum outgoing ky ≤ Int.fdiv (max incoming.sum outgoing.sum * ky) 65536 := by
  exact ⟨linkWidths_le_nodeHeight incoming _ ky (nodeValue_bounds_incoming incoming outgoing) hky,
    linkWidths_le_nodeHeight outgoing _ ky (nodeValue_bounds_outgoing incoming outgoing) hky⟩

theorem boundary_port_right (r : Rect) (offset : Int) (hw : 0 ≤ r.w)
    (hoff : 0 ≤ offset ∧ offset ≤ r.h) :
    Validator.onBoundary ⟨r.x + r.w, r.y + offset⟩ r := by
  refine ⟨?_, ?_, ?_, ?_, Or.inr (Or.inl rfl)⟩ <;> dsimp <;> omega

theorem boundary_port_left (r : Rect) (offset : Int) (hw : 0 ≤ r.w)
    (hoff : 0 ≤ offset ∧ offset ≤ r.h) :
    Validator.onBoundary ⟨r.x, r.y + offset⟩ r := by
  refine ⟨?_, ?_, ?_, ?_, Or.inl rfl⟩ <;> dsimp <;> omega

theorem prefix_width_le_sum (values : List Int) (k : Nat)
    (hvalues : ∀ v ∈ values, 0 ≤ v) :
    (values.take k).sum ≤ values.sum := by
  have nonneg : ∀ xs : List Int, (∀ v ∈ xs, 0 ≤ v) → 0 ≤ xs.sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons v vs ih =>
      intro h
      have hv := h v (by simp)
      have hs := ih (fun a ha => h a (List.mem_cons_of_mem v ha))
      simp only [List.sum_cons]
      omega
  have hdrop : 0 ≤ (values.drop k).sum :=
    nonneg _ (fun v hv => hvalues v (List.mem_of_mem_drop hv))
  have heq := List.take_append_drop k values
  have hsum := congrArg (fun xs : List Int => xs.sum) heq
  simp only [List.sum_append] at hsum
  omega

theorem half_width_inside (width : Int) (hw : 0 ≤ width) :
    0 ≤ Int.fdiv width 2 ∧ Int.fdiv width 2 ≤ width := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem anchor_offset_inside (before width after height : Int)
    (hb : 0 ≤ before) (hw : 0 ≤ width) (ha : 0 ≤ after)
    (hsum : before + width + after ≤ height) :
    0 ≤ before + Int.fdiv width 2 ∧ before + Int.fdiv width 2 ≤ height := by
  have hhalf := half_width_inside width hw
  omega

theorem link_anchor_ports (source target : Rect) (beforeSource beforeTarget width : Int)
    (hws : 0 ≤ source.w) (hwt : 0 ≤ target.w) (hw : 0 ≤ width)
    (hbs : 0 ≤ beforeSource) (hbt : 0 ≤ beforeTarget)
    (hsource : beforeSource + width ≤ source.h)
    (htarget : beforeTarget + width ≤ target.h) :
    Validator.onBoundary ⟨source.x + source.w, source.y + beforeSource + Int.fdiv width 2⟩ source ∧
    Validator.onBoundary ⟨target.x, target.y + beforeTarget + Int.fdiv width 2⟩ target := by
  have hs := anchor_offset_inside beforeSource width 0 source.h hbs hw (by omega) (by omega)
  have ht := anchor_offset_inside beforeTarget width 0 target.h hbt hw (by omega) (by omega)
  constructor
  · simpa only [Int.add_assoc] using boundary_port_right source
      (beforeSource + Int.fdiv width 2) hws hs
  · simpa only [Int.add_assoc] using boundary_port_left target
      (beforeTarget + Int.fdiv width 2) hwt ht

theorem nonexclusive_clauses (d : LayoutDump)
    (h : ∀ b ∈ d.boxes, b.exclusive = false) :
    Validator.C2 d ∧ Validator.C6 d ∧ Validator.C7 d := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb c hc hne he
    have hf := h b hb
    simp [hf] at he
  · intro r hr b hb he
    have hf := h b hb
    simp [hf] at he
  · intro l hl b hb he
    have hf := h b hb
    simp [hf] at he

theorem unparented_clause (d : LayoutDump)
    (h : ∀ b ∈ d.boxes, b.parent = "") : Validator.C3 d := by
  intro b hb hne
  exact False.elim (hne (h b hb))

theorem nonorthogonal_clause (d : LayoutDump)
    (h : ∀ r ∈ d.routes, r.orthogonal = false) : Validator.C4 d := by
  intro r hr he
  have hf := h r hr
  simp [hf] at he

theorem nongroup_clause (d : LayoutDump)
    (h : ∀ b ∈ d.boxes, b.role ≠ "group") : Validator.C8 d := by
  constructor
  · intro g hg he
    exact False.elim (h g hg he)
  · intro g hg he
    exact False.elim (h g hg he)

theorem scene_boxes_metadata (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (h : ∀ b ∈ m.boxes, b.parent = "" ∧ b.exclusive = false ∧ b.role = .node) :
    ∀ b ∈ (sceneOf m f rects labels width height).boxes,
      b.parent = "" ∧ b.exclusive = false ∧ b.role = "node" := by
  intro b hb
  simp only [sceneOf, List.mem_map] at hb
  obtain ⟨⟨source, i⟩, hi, rfl⟩ := hb
  have hs : source ∈ m.boxes :=
    List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hi)
  obtain ⟨hp, he, hr⟩ := h source hs
  simp [hp, he, hr, BoxRole.id]

theorem scene_routes_metadata (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (h : ∀ r ∈ m.routes, r.orthogonal = false) :
    ∀ r ∈ (sceneOf m f rects labels width height).routes, r.orthogonal = false := by
  intro r hr
  simp only [sceneOf, List.mem_map] at hr
  obtain ⟨⟨source, i⟩, hi, rfl⟩ := hr
  exact h source (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hi))

theorem scene_metadata_clauses (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (hb : ∀ b ∈ m.boxes, b.parent = "" ∧ b.exclusive = false ∧ b.role = .node)
    (hr : ∀ r ∈ m.routes, r.orthogonal = false) :
    let d := (sceneOf m f rects labels width height).layoutDump
    Validator.C2 d ∧ Validator.C3 d ∧ Validator.C4 d ∧
      Validator.C6 d ∧ Validator.C7 d ∧ Validator.C8 d := by
  let d := (sceneOf m f rects labels width height).layoutDump
  have hboxes := scene_boxes_metadata m f rects labels width height hb
  have hroutes := scene_routes_metadata m f rects labels width height hr
  have he : ∀ b ∈ d.boxes, b.exclusive = false := fun b h => (hboxes b h).2.1
  have hp : ∀ b ∈ d.boxes, b.parent = "" := fun b h => (hboxes b h).1
  have hg : ∀ b ∈ d.boxes, b.role ≠ "group" := by
    intro b h
    rw [(hboxes b h).2.2]
    decide
  have hn := nonexclusive_clauses d he
  exact ⟨hn.1, unparented_clause d hp, nonorthogonal_clause d hroutes,
    hn.2.1, hn.2.2, nongroup_clause d hg⟩

theorem layout_admissible (m : Model) (s : Scene) (h : layout m = .ok s) :
    admissible m = true := by
  unfold layout at h
  split at h
  · assumption
  · contradiction

theorem admissible_metadata (m : Model) (h : admissible m = true) :
    (∀ b ∈ m.boxes, b.parent = "" ∧ b.exclusive = false ∧ b.role = .node) ∧
    (∀ r ∈ m.routes, r.orthogonal = false) := by
  have hfalse : (m.routes.any (·.orthogonal) ||
      m.boxes.any (fun b => b.parent != "" || b.exclusive || b.role != .node)) = false := by
    have h' := h
    unfold admissible at h'
    cases he : (m.routes.any (·.orthogonal) ||
      m.boxes.any (fun b => b.parent != "" || b.exclusive || b.role != .node)) <;>
      simp_all
  have hs := Bool.or_eq_false_iff.mp hfalse
  constructor
  · intro b hb
    have hp := (List.any_eq_false.mp hs.2) b hb
    simpa [and_assoc] using hp
  · intro r hr
    have hp := (List.any_eq_false.mp hs.1) r hr
    cases he : r.orthogonal <;> simp_all

theorem layout_core_success (m : Model) (s : Scene) (h : layout m = .ok s) :
    layoutCore m = .ok s := by
  unfold layout at h
  split at h
  · exact h
  · contradiction

theorem admission_preserves_model (m : Model) (h : admissible m = true) :
    layout m = layoutCore m := by
  simp only [layout, h, ite_true]

theorem normalization_rects_contained (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) :
    let result := normalize f rects labels width height
    ∀ r ∈ result.2.1.toList,
      Rect.Contained ⟨0, 0, result.2.2.2.1, result.2.2.2.2⟩ r := by
  dsimp only [normalize]
  intro r hr
  simp only [Array.toList_map, List.mem_map] at hr
  obtain ⟨original, ho, rfl⟩ := hr
  exact normalization_rect_in_canvas f rects labels width height original
    (List.mem_append_left _ ho)

theorem scene_canvas_clause (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (hsize : m.boxes.length ≤ rects.size)
    (hrect : ∀ r ∈ rects.toList, Rect.Contained ⟨0, 0, width, height⟩ r) :
    Validator.C1 (sceneOf m f rects labels width height).layoutDump := by
  intro b hb
  simp only [sceneOf, Scene.layoutDump, List.mem_map] at hb
  obtain ⟨⟨source, i⟩, hi, rfl⟩ := hb
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hi
  have hil : i < m.boxes.length := by
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hir : i < rects.size := by omega
  have hmem : rects[i]! ∈ rects.toList := by
    rw [getElem!_pos rects i hir]
    exact Array.getElem_mem_toList hir
  have h := hrect (rects[i]!) hmem
  have grows : ∀ (ps : List LabelPlacement) (seed : Int) (axis : LabelPlacement → Int),
      seed ≤ ps.foldl (fun x p => max x (axis p)) seed := by
    intro ps
    induction ps with
    | nil => intro seed axis; simp
    | cons p ps ih =>
      intro seed axis
      have h := ih (max seed (axis p)) axis
      have hm := Int.le_max_left seed (axis p)
      simp only [List.foldl_cons]
      omega
  have hw := grows labels width (fun p => p.rect.x + p.rect.w)
  have hh := grows labels height (fun p => p.rect.y + p.rect.h)
  simp only [Validator.canvasRect, Scene.layoutDump, sceneOf, Rect.Contained] at *
  omega

theorem pushDownNode_nonnegative_height (n : Node) (y beta : Int) (h : n.y0 ≤ n.y1) :
    (pushDownNode n y beta).y0 ≤ (pushDownNode n y beta).y1 := by
  have hp := pushDownNode_preserves_height n y beta
  omega

theorem normalize_preserves_node_count (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) :
    (normalize f rects labels width height).2.1.size = rects.size := by
  simp only [normalize, Array.size_map]

theorem normalize_preserves_link_count (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) :
    (normalize f rects labels width height).1.links.size = f.links.size := by
  simp only [normalize, Array.size_map]

theorem normalize_preserves_label_count (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) :
    (normalize f rects labels width height).2.2.1.length = labels.length := by
  simp only [normalize, List.length_map]

theorem modify_preserves_heights (nodes : Array Node) (i : Nat) (update : Node → Node)
    (hu : ∀ n, (update n).y1 - (update n).y0 = n.y1 - n.y0) :
    ∀ j (hj : j < nodes.size),
      ((nodes.modify i update)[j]'(by simpa using hj)).y1 -
        ((nodes.modify i update)[j]'(by simpa using hj)).y0 =
      nodes[j].y1 - nodes[j].y0 := by
  intro j hj
  rw [Array.getElem_modify]
  split
  · exact hu _
  · rfl

theorem translated_node_height (n : Node) (dy : Int) :
    ({ n with y0 := n.y0 + dy, y1 := n.y1 + dy } : Node).y1 -
      ({ n with y0 := n.y0 + dy, y1 := n.y1 + dy } : Node).y0 = n.y1 - n.y0 := by
  dsimp only
  omega

theorem nodeIndex_lt (m : Model) (id : String) (h : ∃ b ∈ m.boxes, b.id = id) :
    nodeIndex m id < m.boxes.length := by
  obtain ⟨b, hb, hid⟩ := h
  have hex : ∃ b ∈ m.boxes, (b.id == id) = true := by
    exact ⟨b, hb, by simp [hid]⟩
  have he := List.findIdx?_eq_some_of_exists hex
  have hl := (List.findIdx?_eq_some_iff_findIdx_eq.mp he).1
  simpa only [nodeIndex, he, Option.getD_some] using hl

theorem nodeIndex_id (m : Model) (id : String) (h : ∃ b ∈ m.boxes, b.id = id) :
    (m.boxes[nodeIndex m id]'(nodeIndex_lt m id h)).id = id := by
  obtain ⟨b, hb, hid⟩ := h
  have hex : ∃ b ∈ m.boxes, (b.id == id) = true := ⟨b, hb, by simp [hid]⟩
  have he := List.findIdx?_eq_some_of_exists hex
  have hp := (List.findIdx?_eq_some_iff_getElem.mp he).2.1
  simpa only [nodeIndex, he, Option.getD_some, beq_iff_eq] using hp

theorem wellFormed_route_endpoints (m : Model) (h : Elegant.WellFormed m)
    (r : ModelRoute) (hr : r ∈ m.routes) :
    (∃ b ∈ m.boxes, b.id = r.fromId) ∧ (∃ b ∈ m.boxes, b.id = r.toId) := by
  have hall : m.routes.all (fun r =>
      (m.boxes.map (·.id)).contains r.fromId && (m.boxes.map (·.id)).contains r.toId) = true := by
    unfold Elegant.WellFormed modelWellFormed at h
    repeat rw [Bool.and_eq_true] at h
    exact h.1.1.2
  have hone := List.all_eq_true.mp hall r hr
  rcases Bool.and_eq_true_iff.mp hone with ⟨hs, ht⟩
  constructor
  · have hm := List.mem_of_elem_eq_true hs
    obtain ⟨b, hb, hid⟩ := List.mem_map.mp hm
    exact ⟨b, hb, hid⟩
  · have hm := List.mem_of_elem_eq_true ht
    obtain ⟨b, hb, hid⟩ := List.mem_map.mp hm
    exact ⟨b, hb, hid⟩

theorem set_preserves_heights (nodes : Array Node) (i : Nat) (n : Node)
    (hn : n.y1 - n.y0 = (nodes[i]!).y1 - (nodes[i]!).y0) :
    ∀ j : Nat, ((nodes.set! i n)[j]!).y1 - ((nodes.set! i n)[j]!).y0 =
      (nodes[j]!).y1 - (nodes[j]!).y0 := by
  intro j
  by_cases hij : i = j
  · subst j
    by_cases hi : i < nodes.size
    · rw [Array.getElem!_set!_self nodes i n hi]
      exact hn
    · have he : nodes.set! i n = nodes := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne nodes i j n hij]

theorem empty_scene_valid (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (hb : m.boxes = []) (hr : m.routes = []) :
    HardConstraints (sceneOf m f rects labels width height).layoutDump := by
  simp [HardConstraints, Validator.C1, Validator.C2, Validator.C3, Validator.C4,
    Validator.C5, Validator.C6, Validator.C7, Validator.C8, Validator.C8a, Validator.C8b,
    Scene.layoutDump, sceneOf, hb, hr]

theorem fold_nodes_size (step : Flow → Nat → Flow)
    (hs : ∀ f i, (step f i).nodes.size = f.nodes.size) (indices : List Nat) (f : Flow) :
    (indices.foldl step f).nodes.size = f.nodes.size := by
  induction indices generalizing f with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem reorderLinks_nodes_size (f : Flow) (column : List Nat) :
    (reorderLinks f column).nodes.size = f.nodes.size := by
  apply fold_nodes_size
  intro f i
  simp only [Array.size_set!]

theorem reorderNodeLinks_nodes_size (f : Flow) (i : Nat) :
    (reorderNodeLinks f i).nodes.size = f.nodes.size := by
  unfold reorderNodeLinks
  rw [fold_nodes_size]
  · apply fold_nodes_size
    intro f j
    simp only [Array.size_modify]
  · intro f j
    simp only [Array.size_modify]

theorem fold_pair_nodes_size (step : Flow × Int → Nat → Flow × Int)
    (hs : ∀ f i, (step f i).1.nodes.size = f.1.nodes.size)
    (indices : List Nat) (f : Flow × Int) :
    (indices.foldl step f).1.nodes.size = f.1.nodes.size := by
  induction indices generalizing f with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem pushDown_nodes_size (f : Flow) (column : List Nat) (y beta : Int) :
    (pushDown f column y beta).nodes.size = f.nodes.size := by
  apply fold_pair_nodes_size
  intro f i
  simp only [Array.size_set!]

theorem pushUp_nodes_size (f : Flow) (column : List Nat) (y beta : Int) :
    (pushUp f column y beta).nodes.size = f.nodes.size := by
  apply fold_pair_nodes_size
  intro f i
  simp only [Array.size_set!]

theorem collision_nodes_size (f : Flow) (column : List Nat) (beta : Int) :
    (resolveCollisions f column beta).nodes.size = f.nodes.size := by
  unfold resolveCollisions
  split
  · rfl
  · simp only [pushDown_nodes_size, pushUp_nodes_size]

theorem shiftNode_nodes_size (f : Flow) (i : Nat) (y w alpha : Int) :
    (shiftNode f i y w alpha).nodes.size = f.nodes.size := by
  unfold shiftNode
  split
  · rfl
  · simp only [reorderNodeLinks_nodes_size, Array.size_modify]

theorem pull_nodes_size (f : Flow) (i : Nat) (alpha : Int) (reverse : Bool) :
    (pull f i alpha reverse).nodes.size = f.nodes.size := by
  simp only [pull, shiftNode_nodes_size]

theorem settle_nodes_size (f : Flow) (column : Nat) (beta : Int) :
    (settle f column beta).nodes.size = f.nodes.size := by
  simp only [settle, collision_nodes_size]

theorem pass_nodes_size (f : Flow) (alpha beta : Int) (reverse : Bool) :
    (pass f alpha beta reverse).nodes.size = f.nodes.size := by
  apply fold_nodes_size
  intro f c
  rw [settle_nodes_size]
  apply fold_nodes_size
  intro f i
  exact pull_nodes_size f i alpha reverse

theorem iteration_nodes_size (count i : Nat) (f : Flow) :
    (iteration count i f).nodes.size = f.nodes.size := by
  simp only [iteration, pass_nodes_size]

theorem relax_nodes_size (count : Nat) (f : Flow) :
    (relax count f).nodes.size = f.nodes.size := by
  apply fold_nodes_size
  intro f i
  exact iteration_nodes_size count i f

theorem countedRelax_nodes_size (count : Nat) (f : Flow) :
    (countedRelax count f).1.nodes.size = f.nodes.size := by
  rw [sankey_passes_exact]
  exact relax_nodes_size count f

theorem anchorLinks_nodes_size (f : Flow) :
    (anchorLinks f).nodes.size = f.nodes.size := by
  apply fold_nodes_size
  intro f i
  rw [fold_pair_nodes_size]
  · apply fold_pair_nodes_size
    intro f j
    rfl
  · intro f j
    rfl

theorem nodeRects_size (f : Flow) (width nodeWidth : Int) :
    (nodeRects f width nodeWidth).size = f.nodes.size := by
  simp only [nodeRects, Array.size_map]

theorem place_nodes_size (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) : out.nodes.size = f.nodes.size := by
  unfold place at h
  cases hd : levels f false with
  | error e => simp [hd, Bind.bind, Except.bind] at h
  | ok depths =>
    cases hh : levels f true with
    | error e => simp [hd, hh, Bind.bind, Except.bind] at h
    | ok heights =>
      simp [hd, hh] at h
      cases h
      simp only [Array.size_mapIdx]

theorem boundary_translate (p : Point) (r : Rect) (dx dy : Int)
    (h : Validator.onBoundary p r) :
    Validator.onBoundary ⟨p.x + dx, p.y + dy⟩
      ⟨r.x + dx, r.y + dy, r.w, r.h⟩ := by
  obtain ⟨hx, hxr, hy, hyb, hedge⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp; omega
  · dsimp; omega
  · dsimp; omega
  · dsimp; omega
  · rcases hedge with h | h | h | h
    · exact Or.inl (by dsimp; omega)
    · exact Or.inr (Or.inl (by dsimp; omega))
    · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

theorem id_forIn_invariant (α β : Type) (xs : List α) (init : β)
    (step : α → β → Id (ForInStep β)) (P : β → Prop)
    (hinit : P init)
    (hstep : ∀ a state, P state → P (ForInStep.value (step a state))) :
    P (ForIn.forIn (m := Id) xs init step) := by
  induction xs generalizing init with
  | nil => exact hinit
  | cons a xs ih =>
    rw [List.forIn_cons]
    change P (match step a init with
      | .done state => state
      | .yield state => ForIn.forIn (m := Id) xs state step)
    have hp := hstep a init hinit
    cases hs : step a init with
    | done state => simpa only [hs, ForInStep.value] using hp
    | yield state =>
      apply ih state
      simpa only [hs, ForInStep.value] using hp

theorem stack_nodes_size (f : Flow) (column : List Nat) (ky : Int) :
    (stack f column ky).nodes.size = f.nodes.size := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant (P := fun out : Flow => out.nodes.size = f.nodes.size)
  · apply id_forIn_invariant (P := fun out : Flow × Int => out.1.nodes.size = f.nodes.size)
    · rfl
    · intro i state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant (P := fun out : Flow => out.nodes.size = f.nodes.size)
      · simpa only [Array.size_set!] using hstate
      · intro j out hout
        exact hout
  · intro pair out hout
    dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
    simpa only [Array.size_set!] using hout

theorem except_forIn_invariant (α β : Type) (xs : List α) (init out : β)
    (step : α → β → Except LayoutError (ForInStep β)) (P : β → Prop)
    (hinit : P init)
    (hstep : ∀ a state next, P state → step a state = .ok next → P next.value)
    (hsuccess : ForIn.forIn xs init step = .ok out) : P out := by
  induction xs generalizing init with
  | nil =>
    change Except.ok init = Except.ok out at hsuccess
    cases hsuccess
    exact hinit
  | cons a xs ih =>
    rw [List.forIn_cons] at hsuccess
    cases he : step a init with
    | error e => simp [he, Bind.bind, Except.bind] at hsuccess
    | ok next =>
      have hp := hstep a init next hinit he
      cases next with
      | done state =>
        simp only [he, Bind.bind, Except.bind] at hsuccess
        cases hsuccess
        exact hp
      | yield state =>
        simp only [he, Bind.bind, Except.bind] at hsuccess
        exact ih state hp hsuccess

theorem fold_preserves_heights (step : Flow → Nat → Flow)
    (hs : ∀ (f : Flow) (i j : Nat), ((step f i).nodes[j]!).y1 - ((step f i).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0)
    (indices : List Nat) (f : Flow) (j : Nat) :
    ((indices.foldl step f).nodes[j]!).y1 - ((indices.foldl step f).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  induction indices generalizing f with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem modify_preserves_all_heights (nodes : Array Node) (i : Nat)
    (update : Node → Node)
    (hu : ∀ n, (update n).y1 - (update n).y0 = n.y1 - n.y0) (j : Nat) :
    ((nodes.modify i update)[j]!).y1 - ((nodes.modify i update)[j]!).y0 =
      (nodes[j]!).y1 - (nodes[j]!).y0 := by
  by_cases hj : j < nodes.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj]
    exact modify_preserves_heights nodes i update hu j hj
  · have hj' : ¬j < (nodes.modify i update).size := by simpa using hj
    rw [getElem!_neg (nodes.modify i update) j hj', getElem!_neg nodes j hj]

theorem reorderLinks_heights (f : Flow) (column : List Nat) (j : Nat) :
    ((reorderLinks f column).nodes[j]!).y1 - ((reorderLinks f column).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold reorderLinks
  apply fold_preserves_heights
  intro state i k
  apply set_preserves_heights
  rfl

theorem reorderNodeLinks_heights (f : Flow) (i j : Nat) :
    ((reorderNodeLinks f i).nodes[j]!).y1 - ((reorderNodeLinks f i).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold reorderNodeLinks
  rw [fold_preserves_heights]
  · apply fold_preserves_heights
    intro state k q
    apply modify_preserves_all_heights
    intro n
    rfl
  · intro state k q
    apply modify_preserves_all_heights
    intro n
    rfl

theorem fold_pair_preserves_heights (step : Flow × Int → Nat → Flow × Int)
    (hs : ∀ (state : Flow × Int) (i j : Nat),
      (((step state i).1.nodes)[j]!).y1 - (((step state i).1.nodes)[j]!).y0 =
        (state.1.nodes[j]!).y1 - (state.1.nodes[j]!).y0)
    (indices : List Nat) (state : Flow × Int) (j : Nat) :
    (((indices.foldl step state).1.nodes)[j]!).y1 -
        (((indices.foldl step state).1.nodes)[j]!).y0 =
      (state.1.nodes[j]!).y1 - (state.1.nodes[j]!).y0 := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem pushDown_heights (f : Flow) (column : List Nat) (y beta : Int) (j : Nat) :
    ((pushDown f column y beta).nodes[j]!).y1 -
        ((pushDown f column y beta).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold pushDown
  apply fold_pair_preserves_heights
  intro state i k
  apply set_preserves_heights
  exact pushDownNode_preserves_height _ _ _

theorem pushUp_heights (f : Flow) (column : List Nat) (y beta : Int) (j : Nat) :
    ((pushUp f column y beta).nodes[j]!).y1 -
        ((pushUp f column y beta).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold pushUp
  apply fold_pair_preserves_heights
  intro state i k
  apply set_preserves_heights
  dsimp only
  omega

theorem collision_heights (f : Flow) (column : List Nat) (beta : Int) (j : Nat) :
    ((resolveCollisions f column beta).nodes[j]!).y1 -
        ((resolveCollisions f column beta).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold resolveCollisions
  split
  · rfl
  · simp only [pushDown_heights, pushUp_heights]

theorem shiftNode_heights (f : Flow) (i : Nat) (y w alpha : Int) (j : Nat) :
    ((shiftNode f i y w alpha).nodes[j]!).y1 -
        ((shiftNode f i y w alpha).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold shiftNode
  split
  · rfl
  · rw [reorderNodeLinks_heights]
    apply modify_preserves_all_heights
    intro n
    exact translated_node_height n _

theorem pull_heights (f : Flow) (i : Nat) (alpha : Int) (reverse : Bool) (j : Nat) :
    ((pull f i alpha reverse).nodes[j]!).y1 -
        ((pull f i alpha reverse).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  simp only [pull, shiftNode_heights]

theorem settle_heights (f : Flow) (column : Nat) (beta : Int) (j : Nat) :
    ((settle f column beta).nodes[j]!).y1 - ((settle f column beta).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  simp only [settle, collision_heights]

theorem pass_heights (f : Flow) (alpha beta : Int) (reverse : Bool) (j : Nat) :
    ((pass f alpha beta reverse).nodes[j]!).y1 - ((pass f alpha beta reverse).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold pass
  apply fold_preserves_heights
  intro state c k
  rw [settle_heights]
  apply fold_preserves_heights
  intro state i q
  exact pull_heights state i alpha reverse q

theorem iteration_heights (count i : Nat) (f : Flow) (j : Nat) :
    ((iteration count i f).nodes[j]!).y1 - ((iteration count i f).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  simp only [iteration, pass_heights]

theorem relax_heights (count : Nat) (f : Flow) (j : Nat) :
    ((relax count f).nodes[j]!).y1 - ((relax count f).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold relax
  apply fold_preserves_heights
  intro state i k
  exact iteration_heights count i state k

theorem anchorLinks_heights (f : Flow) (j : Nat) :
    ((anchorLinks f).nodes[j]!).y1 - ((anchorLinks f).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  unfold anchorLinks
  apply fold_preserves_heights
  intro state i k
  rw [fold_pair_preserves_heights]
  · apply fold_pair_preserves_heights
    intro state i k
    rfl
  · intro state i k
    rfl

theorem final_heights (f : Flow) (count j : Nat) :
    ((anchorLinks (countedRelax count f).1).nodes[j]!).y1 -
        ((anchorLinks (countedRelax count f).1).nodes[j]!).y0 =
      (f.nodes[j]!).y1 - (f.nodes[j]!).y0 := by
  rw [anchorLinks_heights, sankey_passes_exact]
  exact relax_heights count f j

theorem pushDown_py (f : Flow) (column : List Nat) (y beta : Int) :
    (pushDown f column y beta).py = f.py := by
  unfold pushDown
  have invariant : ∀ (indices : List Nat) (state : Flow × Int),
      ((indices.foldl (fun (acc : Flow × Int) i =>
        let n := pushDownNode (acc.1.nodes[i]!) acc.2 beta
        let old := acc.1.nodes[i]!
        let product := (acc.2 - old.y0) * beta
        let safe := [product, 2 * product, 2 * product + 65536,
          n.y0, n.y1, n.y1 + acc.1.py].all fitsI64
        ({ acc.1 with nodes := acc.1.nodes.set! i n, arithmeticFailed := acc.1.arithmeticFailed || !safe },
          n.y1 + acc.1.py)) state).1).py = state.1.py := by
    intro indices
    induction indices with
    | nil => intro state; rfl
    | cons i rest ih =>
      intro state
      simp only [List.foldl_cons]
      exact ih _
  exact invariant column (f, y)

theorem pushDown_untouched (f : Flow) (column : List Nat) (y beta : Int) (j : Nat)
    (hj : j ∉ column) : (pushDown f column y beta).nodes[j]! = f.nodes[j]! := by
  induction column generalizing f y with
  | nil => rfl
  | cons i rest ih =>
    have hji : i ≠ j := by
      intro h
      subst i
      exact hj (by simp)
    have hjr : j ∉ rest := fun h => hj (List.mem_cons_of_mem i h)
    let n := pushDownNode (f.nodes[i]!) y beta
    let product := (y - (f.nodes[i]!).y0) * beta
    let safe := [product, 2 * product, 2 * product + 65536,
      n.y0, n.y1, n.y1 + f.py].all fitsI64
    let next : Flow := { f with nodes := f.nodes.set! i n, arithmeticFailed := f.arithmeticFailed || !safe }
    have he : pushDown f (i :: rest) y beta =
        pushDown next rest (n.y1 + f.py) beta := by
      rfl
    rw [he, ih next _ hjr]
    exact Array.getElem!_set!_ne f.nodes i j n hji

theorem pushDown_as_settleNodeList (f : Flow) (column : List Nat) (y : Int)
    (hnodup : column.Nodup) (hindices : ∀ i ∈ column, i < f.nodes.size) :
    column.map (fun i => (pushDown f column y 65536).nodes[i]!) =
      settleNodeList f.py (column.map (fun i => f.nodes[i]!)) y := by
  induction column generalizing f y with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hnodup
    have hi : i < f.nodes.size := hindices i (by simp)
    let n := pushDownNode (f.nodes[i]!) y 65536
    let product := (y - (f.nodes[i]!).y0) * 65536
    let safe := [product, 2 * product, 2 * product + 65536,
      n.y0, n.y1, n.y1 + f.py].all fitsI64
    let next : Flow := { f with nodes := f.nodes.set! i n, arithmeticFailed := f.arithmeticFailed || !safe }
    have he : pushDown f (i :: rest) y 65536 =
        pushDown next rest (n.y1 + f.py) 65536 := by
      rfl
    have htail : ∀ k ∈ rest, k < next.nodes.size := by
      intro k hk
      simpa only [next, Array.size_set!] using hindices k (List.mem_cons_of_mem i hk)
    have hhead : (pushDown next rest (n.y1 + f.py) 65536).nodes[i]! = n := by
      rw [pushDown_untouched next rest _ _ i hnot]
      exact Array.getElem!_set!_self f.nodes i n hi
    have hmap : rest.map (fun k => next.nodes[k]!) =
        rest.map (fun k => f.nodes[k]!) := by
      apply List.map_congr_left
      intro k hk
      have hne : i ≠ k := by
        intro heq
        subst k
        exact hnot hk
      exact Array.getElem!_set!_ne f.nodes i k n hne
    rw [he, List.map_cons, hhead, ih next _ hrest htail, hmap]
    rfl

theorem pushDown_gaps (f : Flow) (column : List Nat) (y : Int)
    (hnodup : column.Nodup) (hindices : ∀ i ∈ column, i < f.nodes.size)
    (hpy : 0 ≤ f.py) (heights : ∀ i ∈ column, (f.nodes[i]!).y0 ≤ (f.nodes[i]!).y1) :
    (column.map (fun i => (pushDown f column y 65536).nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0) := by
  rw [pushDown_as_settleNodeList f column y hnodup hindices]
  apply settleNodeList_gaps f.py _ y hpy
  intro n hn
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
  exact heights i hi

theorem fold_pair_preserves_py (step : Flow × Int → Nat → Flow × Int)
    (hs : ∀ state i, (step state i).1.py = state.1.py)
    (indices : List Nat) (state : Flow × Int) :
    (indices.foldl step state).1.py = state.1.py := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem pushUp_py (f : Flow) (column : List Nat) (y beta : Int) :
    (pushUp f column y beta).py = f.py := by
  unfold pushUp
  apply fold_pair_preserves_py
  intro state i
  rfl

theorem collision_gaps_full_strength (f : Flow) (column : List Nat)
    (hnodup : column.Nodup) (hindices : ∀ i ∈ column, i < f.nodes.size)
    (hpy : 0 ≤ f.py) (heights : ∀ i ∈ column, (f.nodes[i]!).y0 ≤ (f.nodes[i]!).y1) :
    (column.map (fun i => (resolveCollisions f column 65536).nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0) := by
  unfold resolveCollisions
  split
  · cases column <;> simp_all
  · let k := column.length / 2
    let subject := f.nodes[column.getD k 0]!
    let first := pushUp f (column.take k) (subject.y0 - f.py) 65536
    let second := pushDown first (column.drop (k + 1)) (subject.y1 + first.py) 65536
    let third := pushUp second column second.extent 65536
    change (column.map (fun i => (pushDown third column 0 65536).nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0)
    have hsize : third.nodes.size = f.nodes.size := by
      simp only [third, second, first, pushUp_nodes_size, pushDown_nodes_size]
    have hpad : third.py = f.py := by
      simp only [third, second, first, pushUp_py, pushDown_py]
    have hheight : ∀ i : Nat, (third.nodes[i]!).y1 - (third.nodes[i]!).y0 =
        (f.nodes[i]!).y1 - (f.nodes[i]!).y0 := by
      intro i
      simp only [third, second, first, pushUp_heights, pushDown_heights]
    have hi : ∀ i ∈ column, i < third.nodes.size := by
      intro i him
      rw [hsize]
      exact hindices i him
    have hh : ∀ i ∈ column, (third.nodes[i]!).y0 ≤ (third.nodes[i]!).y1 := by
      intro i him
      have hd := hheight i
      have hp := heights i him
      omega
    have hp : 0 ≤ third.py := by rw [hpad]; exact hpy
    have h := pushDown_gaps third column 0 hnodup hi hp hh
    simpa only [hpad] using h

theorem scaledSum_nonnegative (values : List Int) (ky : Int)
    (hvalues : ∀ v ∈ values, 0 ≤ v) (hky : 0 ≤ ky) :
    0 ≤ scaledSum values ky := by
  induction values with
  | nil => simp [scaledSum]
  | cons v vs ih =>
    have hv := rounding_nonnegative v ky (hvalues v (by simp)) hky
    have hs := ih (fun a ha => hvalues a (List.mem_cons_of_mem v ha))
    simp only [scaledSum, List.map_cons, List.sum_cons] at *
    omega

theorem scaledSum_perm (values other : List Int) (ky : Int)
    (h : values.Perm other) : scaledSum values ky = scaledSum other ky := by
  induction h with
  | nil => rfl
  | cons v _ ih =>
    simpa only [scaledSum, List.map_cons, List.sum_cons] using
      congrArg (fun total => Int.fdiv (v * ky) 65536 + total) ih
  | swap v w rest =>
    simp only [scaledSum, List.map_cons, List.sum_cons]
    omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem scale_candidate_product_bound (total room ky : Int) (htotal : 0 < total)
    (hky : ky ≤ Int.fdiv (room * 65536) total) :
    total * ky ≤ room * 65536 := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt htotal)] at hky
  have hm := Int.mul_le_mul_of_nonneg_right hky (Int.le_of_lt htotal)
  have hd := Int.ediv_mul_le (room * 65536) (Int.ne_of_gt htotal)
  rw [Int.mul_comm total ky]
  omega

theorem columnHeights_le_room_of_candidate (values : List Int) (ky room : Int)
    (htotal : 0 < values.sum)
    (hky : ky ≤ Int.fdiv (room * 65536) values.sum) :
    scaledSum values ky ≤ room := by
  exact columnHeights_le_room values ky room
    (scale_candidate_product_bound values.sum room ky htotal hky)

theorem scaled_prefix_anchor_inside (values : List Int) (ky height : Int) (k : Nat)
    (hvalues : ∀ v ∈ values, 0 ≤ v) (hky : 0 ≤ ky)
    (hsum : scaledSum values ky ≤ height) :
    0 ≤ scaledSum (values.take k) ky ∧ scaledSum (values.take k) ky ≤ height := by
  have hnonneg : ∀ w ∈ values.map (fun v => Int.fdiv (v * ky) 65536), 0 ≤ w := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact rounding_nonnegative v ky (hvalues v hv) hky
  have hprefix := prefix_width_le_sum
    (values.map (fun v => Int.fdiv (v * ky) 65536)) k hnonneg
  have hzero := scaledSum_nonnegative (values.take k) ky
    (fun v hv => hvalues v (List.mem_of_mem_take hv)) hky
  simp only [scaledSum, List.map_take] at *
  exact ⟨hzero, Int.le_trans hprefix hsum⟩

theorem initialise_nodes_size (f out : Flow) (h : initialise f = .ok out) :
    out.nodes.size = f.nodes.size := by
  unfold initialise at h
  cases hs : scale f with
  | error e => simp [hs, Bind.bind, Except.bind] at h
  | ok ky =>
    simp [hs] at h
    cases h
    change (f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).nodes.size =
      f.nodes.size
    apply Array.foldl_induction
      (motive := fun _ (state : Flow) => state.nodes.size = f.nodes.size)
    · rfl
    · intro i state hstate
      simpa only [reorderLinks_nodes_size, stack_nodes_size] using hstate

theorem run_nodes_size (f out : Flow) (alignment : String) (count : Nat)
    (h : run f alignment count = .ok out) : out.nodes.size = f.nodes.size := by
  unfold run at h
  cases hp : place f alignment with
  | error e => simp [hp, Bind.bind, Except.bind] at h
  | ok placed =>
    cases hi : initialise (withPadding placed) with
    | error e => simp [hp, hi, Bind.bind, Except.bind] at h
    | ok initialised =>
      simp only [hp, hi, Bind.bind, Except.bind] at h
      split at h
      · contradiction
      · cases h
        rw [anchorLinks_nodes_size, countedRelax_nodes_size,
          initialise_nodes_size (withPadding placed) initialised hi]
        exact place_nodes_size f placed alignment hp

theorem fold_preserves_links (step : Flow → Nat → Flow)
    (hs : ∀ f i, (step f i).links = f.links) (indices : List Nat) (f : Flow) :
    (indices.foldl step f).links = f.links := by
  induction indices generalizing f with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem fold_pair_preserves_links (step : Flow × Int → Nat → Flow × Int)
    (hs : ∀ state i, (step state i).1.links = state.1.links)
    (indices : List Nat) (state : Flow × Int) :
    (indices.foldl step state).1.links = state.1.links := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem reorderLinks_links (f : Flow) (column : List Nat) :
    (reorderLinks f column).links = f.links := by
  unfold reorderLinks
  apply fold_preserves_links
  intro state i
  rfl

theorem reorderNodeLinks_links (f : Flow) (i : Nat) :
    (reorderNodeLinks f i).links = f.links := by
  unfold reorderNodeLinks
  rw [fold_preserves_links]
  · apply fold_preserves_links
    intro state j
    rfl
  · intro state j
    rfl

theorem pushDown_links (f : Flow) (column : List Nat) (y beta : Int) :
    (pushDown f column y beta).links = f.links := by
  unfold pushDown
  apply fold_pair_preserves_links
  intro state i
  rfl

theorem pushUp_links (f : Flow) (column : List Nat) (y beta : Int) :
    (pushUp f column y beta).links = f.links := by
  unfold pushUp
  apply fold_pair_preserves_links
  intro state i
  rfl

theorem collision_links (f : Flow) (column : List Nat) (beta : Int) :
    (resolveCollisions f column beta).links = f.links := by
  unfold resolveCollisions
  split
  · rfl
  · simp only [pushDown_links, pushUp_links]

theorem shiftNode_links (f : Flow) (i : Nat) (y w alpha : Int) :
    (shiftNode f i y w alpha).links = f.links := by
  unfold shiftNode
  split
  · rfl
  · exact reorderNodeLinks_links _ i

theorem pull_links (f : Flow) (i : Nat) (alpha : Int) (reverse : Bool) :
    (pull f i alpha reverse).links = f.links := by
  simp only [pull, shiftNode_links]

theorem settle_links (f : Flow) (column : Nat) (beta : Int) :
    (settle f column beta).links = f.links := by
  simp only [settle, collision_links]

theorem pass_links (f : Flow) (alpha beta : Int) (reverse : Bool) :
    (pass f alpha beta reverse).links = f.links := by
  unfold pass
  apply fold_preserves_links
  intro state c
  rw [settle_links]
  apply fold_preserves_links
  intro state i
  exact pull_links state i alpha reverse

theorem iteration_links (count i : Nat) (f : Flow) :
    (iteration count i f).links = f.links := by
  simp only [iteration, pass_links]

theorem relax_links (count : Nat) (f : Flow) : (relax count f).links = f.links := by
  unfold relax
  apply fold_preserves_links
  intro state i
  exact iteration_links count i state

def linkData (l : Link) : Nat × Nat × Int × Int :=
  (l.source, l.target, l.value, l.width)

theorem set_preserves_linkData (links : Array Link) (i : Nat) (l : Link)
    (hl : linkData l = linkData (links[i]!)) (j : Nat) :
    linkData ((links.set! i l)[j]!) = linkData (links[j]!) := by
  by_cases hij : i = j
  · subst j
    by_cases hi : i < links.size
    · rw [Array.getElem!_set!_self links i l hi]
      exact hl
    · have he : links.set! i l = links := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne links i j l hij]

theorem fold_preserves_linkData (step : Flow → Nat → Flow)
    (hs : ∀ (f : Flow) (i j : Nat), linkData ((step f i).links[j]!) = linkData (f.links[j]!))
    (indices : List Nat) (f : Flow) (j : Nat) :
    linkData ((indices.foldl step f).links[j]!) = linkData (f.links[j]!) := by
  induction indices generalizing f with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem fold_pair_preserves_linkData (step : Flow × Int → Nat → Flow × Int)
    (hs : ∀ (state : Flow × Int) (i j : Nat),
      linkData ((step state i).1.links[j]!) = linkData (state.1.links[j]!))
    (indices : List Nat) (state : Flow × Int) (j : Nat) :
    linkData ((indices.foldl step state).1.links[j]!) = linkData (state.1.links[j]!) := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem anchorLinks_linkData (f : Flow) (j : Nat) :
    linkData ((anchorLinks f).links[j]!) = linkData (f.links[j]!) := by
  unfold anchorLinks
  apply fold_preserves_linkData
  intro state i k
  rw [fold_pair_preserves_linkData]
  · apply fold_pair_preserves_linkData
    intro state i k
    apply set_preserves_linkData
    rfl
  · intro state i k
    apply set_preserves_linkData
    rfl

theorem final_linkData (f : Flow) (count j : Nat) :
    linkData ((anchorLinks (countedRelax count f).1).links[j]!) =
      linkData (f.links[j]!) := by
  rw [anchorLinks_linkData, sankey_passes_exact]
  rw [relax_links]

theorem final_common_scale (f : Flow) (count : Nat) (ky : Int)
    (hwidth : ∀ j : Nat, (f.links[j]!).width = Int.fdiv ((f.links[j]!).value * ky) 65536)
    (hheight : ∀ i : Nat, (f.nodes[i]!).y1 - (f.nodes[i]!).y0 =
      Int.fdiv ((f.nodes[i]!).value * ky) 65536) :
    (∀ j : Nat, ((anchorLinks (countedRelax count f).1).links[j]!).width =
      Int.fdiv ((f.links[j]!).value * ky) 65536) ∧
    (∀ i : Nat, ((anchorLinks (countedRelax count f).1).nodes[i]!).y1 -
      ((anchorLinks (countedRelax count f).1).nodes[i]!).y0 =
        Int.fdiv ((f.nodes[i]!).value * ky) 65536) := by
  constructor
  · intro j
    have hd := congrArg (fun data : Nat × Nat × Int × Int => data.2.2.2)
      (final_linkData f count j)
    exact hd.trans (hwidth j)
  · intro i
    exact (final_heights f count i).trans (hheight i)

theorem scaled_anchor_inside (before after : List Int) (value ky height : Int)
    (hb : ∀ v ∈ before, 0 ≤ v) (ha : ∀ v ∈ after, 0 ≤ v)
    (hv : 0 ≤ value) (hky : 0 ≤ ky)
    (hsum : scaledSum (before ++ value :: after) ky ≤ height) :
    0 ≤ scaledSum before ky + Int.fdiv (Int.fdiv (value * ky) 65536) 2 ∧
      scaledSum before ky + Int.fdiv (Int.fdiv (value * ky) 65536) 2 ≤ height := by
  have hb' := scaledSum_nonnegative before ky hb hky
  have ha' := scaledSum_nonnegative after ky ha hky
  have hv' := rounding_nonnegative value ky hv hky
  have hsum' : scaledSum before ky + Int.fdiv (value * ky) 65536 +
      scaledSum after ky ≤ height := by
    simpa only [scaledSum, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, Int.add_assoc] using hsum
  exact anchor_offset_inside (scaledSum before ky) (Int.fdiv (value * ky) 65536)
    (scaledSum after ky) height hb' hv' ha' hsum'

theorem withPadding_nonnegative (f : Flow) (hextent : 0 ≤ f.extent)
    (hpadding : 0 ≤ f.padding) : 0 ≤ (withPadding f).py := by
  unfold withPadding
  dsimp only
  split
  · apply Int.le_min.mpr
    constructor
    · exact hpadding
    · exact Int.fdiv_nonneg hextent (by omega)
  · exact hpadding

theorem stack_shift_monotone (free : Int) (size k l : Nat)
    (hfree : 0 ≤ free) (hkl : k ≤ l) :
    Int.fdiv ((Int.ofNat k + 1) * free) (Int.ofNat size + 1) ≤
      Int.fdiv ((Int.ofNat l + 1) * free) (Int.ofNat size + 1) := by
  have horder : Int.ofNat k + 1 ≤ Int.ofNat l + 1 := by
    change (k : Int) + 1 ≤ (l : Int) + 1
    omega
  have hden : (0 : Int) < Int.ofNat size + 1 := by
    change (0 : Int) < (size : Int) + 1
    omega
  have hm := Int.mul_le_mul_of_nonneg_right horder hfree
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hden),
    Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hden)]
  exact Int.ediv_le_ediv hden hm

theorem stack_shift_preserves_gap (first second : Node) (py free : Int)
    (size k l : Nat) (hgap : first.y1 + py ≤ second.y0)
    (hfree : 0 ≤ free) (hkl : k ≤ l) :
    first.y1 + Int.fdiv ((Int.ofNat k + 1) * free) (Int.ofNat size + 1) + py ≤
      second.y0 + Int.fdiv ((Int.ofNat l + 1) * free) (Int.ofNat size + 1) := by
  have hshift := stack_shift_monotone free size k l hfree hkl
  omega

theorem collision_disjoint_full_strength (f : Flow) (column : List Nat)
    (hnodup : column.Nodup) (hindices : ∀ i ∈ column, i < f.nodes.size)
    (hpy : 0 ≤ f.py) (heights : ∀ i ∈ column, (f.nodes[i]!).y0 ≤ (f.nodes[i]!).y1) :
    (column.map (fun i => (resolveCollisions f column 65536).nodes[i]!)).Pairwise
      (fun a b => a.y1 ≤ b.y0) := by
  have h := collision_gaps_full_strength f column hnodup hindices hpy heights
  exact h.imp (by intro a b hab; omega)

theorem decode_nodes_size (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) : f.nodes.size = m.boxes.length := by
  unfold decode at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i state hloop
    have hsize : state.2.size = m.boxes.length := by
      refine except_forIn_invariant _ _ m.routes.zipIdx _ state _
        (fun state => state.2.size = m.boxes.length) ?_ ?_ hloop
      · simp
      · intro item previous next hprevious hnext
        split at hnext
        · contradiction
        · split at hnext
          · contradiction
          · split at hnext
            · contradiction
            · cases hnext
              simpa only [ForInStep.value, Array.size_modify] using hprevious
    cases h
    simpa only [Array.size_map] using hsize

theorem decode_link_bounds (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) :
    ∀ l ∈ f.links.toList,
      0 ≤ l.value ∧ l.source < m.boxes.length ∧ l.target < m.boxes.length := by
  unfold decode at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i state hloop
    have hinvariant :
        state.2.size = m.boxes.length ∧
          ∀ l ∈ state.1.toList,
            0 ≤ l.value ∧ l.source < m.boxes.length ∧ l.target < m.boxes.length := by
      refine except_forIn_invariant _ _ m.routes.zipIdx _ state _
        (fun state : Array Link × Array Node =>
          state.2.size = m.boxes.length ∧
            ∀ l ∈ state.1.toList,
              0 ≤ l.value ∧ l.source < m.boxes.length ∧ l.target < m.boxes.length)
        ?_ ?_ hloop
      · simp
      · intro item previous next hprevious hnext
        split at hnext
        · contradiction
        · split at hnext
          · contradiction
          · split at hnext
            · contradiction
            · cases hnext
              constructor
              · simpa only [ForInStep.value, Array.size_modify] using hprevious.1
              · intro l hl
                simp only [ForInStep.value, Array.toList_push, List.mem_append,
                  List.mem_singleton] at hl
                rcases hl with hl | hl
                · exact hprevious.2 l hl
                · subst l
                  dsimp only
                  constructor
                  · omega
                  · constructor <;> omega
    cases h
    exact hinvariant.2

theorem except_forIn_yield_map (α β γ : Type) (xs : List α) (init out : β)
    (step : α → β → Except LayoutError (ForInStep β))
    (observe : β → List γ) (encode : α → γ)
    (hstep : ∀ a state next, step a state = .ok next →
      ∃ state', next = .yield state' ∧
        observe state' = observe state ++ [encode a])
    (hsuccess : ForIn.forIn xs init step = .ok out) :
    observe out = observe init ++ xs.map encode := by
  induction xs generalizing init with
  | nil =>
    change Except.ok init = Except.ok out at hsuccess
    cases hsuccess
    simp
  | cons a xs ih =>
    rw [List.forIn_cons] at hsuccess
    cases he : step a init with
    | error e => simp [he, Bind.bind, Except.bind] at hsuccess
    | ok next =>
      obtain ⟨state', rfl, hobserve⟩ := hstep a init next he
      simp only [he, Bind.bind, Except.bind] at hsuccess
      rw [ih state' hsuccess, hobserve]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]

theorem decode_links (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) :
    f.links.toList = m.routes.zipIdx.map (fun (r, i) =>
      ({ source := nodeIndex m r.fromId
         target := nodeIndex m r.toId
         value := unzigzag
           ((((m.regionSets.head?).map (·.regions)).getD []).getD (2 * i + 1) 0) } : Link)) := by
  unfold decode at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i state hloop
    have hlinks := except_forIn_yield_map _ _ _ m.routes.zipIdx _ state _
      (fun state : Array Link × Array Node => state.1.toList)
      (fun (r, i) =>
        ({ source := nodeIndex m r.fromId
           target := nodeIndex m r.toId
           value := unzigzag
             ((((m.regionSets.head?).map (·.regions)).getD []).getD (2 * i + 1) 0) } : Link))
      (by
        intro item previous next hnext
        repeat' (split at hnext <;> try contradiction)
        cases hnext
        refine ⟨_, rfl, ?_⟩
        simp only [Array.toList_push])
      hloop
    cases h
    simpa using hlinks

theorem decode_links_size (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) : f.links.size = m.routes.length := by
  have hlength := congrArg List.length (decode_links m extent padding f h)
  simpa using hlength

theorem decode_link_endpoints (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) (i : Nat) (hi : i < m.routes.length) :
    (f.links[i]!).source = nodeIndex m (m.routes[i]).fromId ∧
      (f.links[i]!).target = nodeIndex m (m.routes[i]).toId := by
  have heq := congrArg (fun links : List Link => links[i]!)
    (decode_links m extent padding f h)
  rw [Array.getElem!_toList] at heq
  have hmap : i < (m.routes.zipIdx.map (fun (r, j) =>
      ({ source := nodeIndex m r.fromId
         target := nodeIndex m r.toId
         value := unzigzag
           ((((m.regionSets.head?).map (fun region : ModelRegionSet => region.regions)).getD []).getD (2 * j + 1) 0) } : Link))).length := by
    simpa using hi
  have hlinks : i < f.links.size := by
    rw [decode_links_size m extent padding f h]
    exact hi
  rw [getElem!_pos f.links i hlinks] at heq
  rw [getElem!_pos _ i hmap] at heq
  constructor
  · simpa only [getElem!_pos f.links i hlinks, List.getElem_map,
      List.getElem_zipIdx, Nat.zero_add] using
      congrArg Link.source heq
  · simpa only [getElem!_pos f.links i hlinks, List.getElem_map,
      List.getElem_zipIdx, Nat.zero_add] using
      congrArg Link.target heq

theorem except_forIn_index_invariant (α β : Type) (xs : List α) (start : Nat)
    (init out : β) (step : α × Nat → β → Except LayoutError (ForInStep β))
    (P : Nat → β → Prop) (hinit : P start init)
    (hstep : ∀ a i state next, P i state → step (a, i) state = .ok next →
      ∃ state', next = .yield state' ∧ P (i + 1) state')
    (hsuccess : ForIn.forIn (xs.zipIdx start) init step = .ok out) :
    P (start + xs.length) out := by
  induction xs generalizing start init with
  | nil =>
    change Except.ok init = Except.ok out at hsuccess
    cases hsuccess
    exact hinit
  | cons a xs ih =>
    rw [List.zipIdx_cons, List.forIn_cons] at hsuccess
    cases he : step (a, start) init with
    | error e => simp [he, Bind.bind, Except.bind] at hsuccess
    | ok next =>
      obtain ⟨state', rfl, hp⟩ := hstep a start init next hinit he
      simp only [he, Bind.bind, Except.bind] at hsuccess
      have hindex : start + 1 + xs.length = start + (a :: xs).length := by
        simp only [List.length_cons]
        omega
      rw [← hindex]
      exact ih (start + 1) state' hp hsuccess

theorem modify_preserves_node_predicate (nodes : Array Node) (i : Nat)
    (update : Node → Node) (P : Node → Prop)
    (hnodes : ∀ n ∈ nodes.toList, P n)
    (hupdate : ∀ n, P n → P (update n)) :
    ∀ n ∈ (nodes.modify i update).toList, P n := by
  intro n hn
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hn
  rw [← heq, Array.getElem_toList, Array.getElem_modify]
  have hmem : nodes[j]'(by simpa using hj) ∈ nodes.toList :=
    Array.getElem_mem_toList (by simpa using hj)
  split
  · exact hupdate _ (hnodes _ hmem)
  · exact hnodes _ hmem

theorem decode_adjacency_indices (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) :
    ∀ n ∈ f.nodes.toList,
      (∀ j ∈ n.incoming, j < f.links.size) ∧
        (∀ j ∈ n.outgoing, j < f.links.size) := by
  unfold decode at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i state hloop
    have hinvariant :
        state.1.size = m.routes.length ∧
          ∀ n ∈ state.2.toList,
            (∀ j ∈ n.incoming, j < m.routes.length) ∧
              (∀ j ∈ n.outgoing, j < m.routes.length) := by
      refine (Nat.zero_add m.routes.length) ▸
        except_forIn_index_invariant _ _ m.routes 0 _ state _
        (fun i (state : Array Link × Array Node) =>
          state.1.size = i ∧
            ∀ n ∈ state.2.toList,
              (∀ j ∈ n.incoming, j < i) ∧ (∀ j ∈ n.outgoing, j < i))
        ?_ ?_ hloop
      · constructor
        · rfl
        · intro n hn
          simp only [List.mem_map] at hn
          obtain ⟨b, _, rfl⟩ := hn
          simp
      · intro r i previous next hprevious hnext
        repeat' (split at hnext <;> try contradiction)
        cases hnext
        refine ⟨_, rfl, ?_⟩
        constructor
        · simpa only [Array.size_push] using congrArg Nat.succ hprevious.1
        · apply modify_preserves_node_predicate
          · apply modify_preserves_node_predicate
            · intro n hn
              obtain ⟨hin, hout⟩ := hprevious.2 n hn
              constructor
              · intro j hj
                have hj' := hin j hj
                omega
              · intro j hj
                have hj' := hout j hj
                omega
            · intro n hn
              constructor
              · exact hn.1
              · intro j hj
                simp only [List.mem_append, List.mem_singleton] at hj
                rcases hj with hj | rfl
                · exact hn.2 j hj
                · omega
          · intro n hn
            constructor
            · intro j hj
              simp only [List.mem_append, List.mem_singleton] at hj
              rcases hj with hj | rfl
              · exact hn.1 j hj
              · omega
            · exact hn.2
    cases h
    intro n hn
    simp only [Array.toList_map, List.mem_map] at hn
    obtain ⟨original, horiginal, rfl⟩ := hn
    simpa only [hinvariant.1] using hinvariant.2 original horiginal

theorem append_fresh_index (indices : List Nat) (i : Nat)
    (h : indices.Nodup ∧ ∀ j ∈ indices, j < i) :
    (indices ++ [i]).Nodup ∧ ∀ j ∈ indices ++ [i], j < i + 1 := by
  constructor
  · apply List.nodup_append.mpr
    refine ⟨h.1, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    have ha' := h.2 a ha
    omega
  · intro j hj
    simp only [List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · have hj' := h.2 j hj
      omega
    · omega

theorem modify_transfers_node_predicate (nodes : Array Node) (i : Nat)
    (update : Node → Node) (P Q : Node → Prop)
    (hnodes : ∀ n ∈ nodes.toList, P n)
    (hkeep : ∀ n, P n → Q n) (hupdate : ∀ n, P n → Q (update n)) :
    ∀ n ∈ (nodes.modify i update).toList, Q n := by
  intro n hn
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hn
  rw [← heq, Array.getElem_toList, Array.getElem_modify]
  have hmem : nodes[j]'(by simpa using hj) ∈ nodes.toList :=
    Array.getElem_mem_toList (by simpa using hj)
  split
  · exact hupdate _ (hnodes _ hmem)
  · exact hkeep _ (hnodes _ hmem)

theorem decode_adjacency_nodup (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) :
    ∀ n ∈ f.nodes.toList, n.incoming.Nodup ∧ n.outgoing.Nodup := by
  unfold decode at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i state hloop
    have hinvariant :
        ∀ n ∈ state.2.toList,
          (n.incoming.Nodup ∧ ∀ j ∈ n.incoming, j < m.routes.length) ∧
            (n.outgoing.Nodup ∧ ∀ j ∈ n.outgoing, j < m.routes.length) := by
      refine (Nat.zero_add m.routes.length) ▸
        except_forIn_index_invariant _ _ m.routes 0 _ state _
        (fun i (state : Array Link × Array Node) =>
          ∀ n ∈ state.2.toList,
            (n.incoming.Nodup ∧ ∀ j ∈ n.incoming, j < i) ∧
              (n.outgoing.Nodup ∧ ∀ j ∈ n.outgoing, j < i))
        ?_ ?_ hloop
      · intro n hn
        simp only [List.mem_map] at hn
        obtain ⟨b, _, rfl⟩ := hn
        simp
      · intro r i previous next hprevious hnext
        repeat' (split at hnext <;> try contradiction)
        cases hnext
        refine ⟨_, rfl, ?_⟩
        have widen : ∀ indices : List Nat,
            (indices.Nodup ∧ ∀ j ∈ indices, j < i) →
              (indices.Nodup ∧ ∀ j ∈ indices, j < i + 1) := by
          intro indices hs
          refine ⟨hs.1, ?_⟩
          intro j hj
          have hj' := hs.2 j hj
          omega
        apply modify_transfers_node_predicate
          (P := fun n =>
            (n.incoming.Nodup ∧ ∀ j ∈ n.incoming, j < i) ∧
              (n.outgoing.Nodup ∧ ∀ j ∈ n.outgoing, j < i + 1))
        · apply modify_transfers_node_predicate
            (P := fun n =>
              (n.incoming.Nodup ∧ ∀ j ∈ n.incoming, j < i) ∧
                (n.outgoing.Nodup ∧ ∀ j ∈ n.outgoing, j < i))
          · exact hprevious
          · intro n hn
            exact ⟨hn.1, widen n.outgoing hn.2⟩
          · intro n hn
            exact ⟨hn.1, append_fresh_index n.outgoing i hn.2⟩
        · intro n hn
          exact ⟨widen n.incoming hn.1, hn.2⟩
        · intro n hn
          exact ⟨append_fresh_index n.incoming i hn.1, hn.2⟩
    cases h
    intro n hn
    simp only [Array.toList_map, List.mem_map] at hn
    obtain ⟨original, horiginal, rfl⟩ := hn
    exact ⟨(hinvariant original horiginal).1.1, (hinvariant original horiginal).2.1⟩

theorem pushed_link_incidence (links : Array Link) (l : Link)
    (endpoint : Link → Nat) (j k : Nat) :
    (j < (links.push l).size ∧ endpoint ((links.push l)[j]!) = k) ↔
      (j < links.size ∧ endpoint (links[j]!) = k) ∨
        (j = links.size ∧ endpoint l = k) := by
  by_cases hj : j < links.size
  · have hp : j < (links.push l).size := by
      rw [Array.size_push]
      omega
    have heq : (links.push l)[j]! = links[j]! := by
      rw [getElem!_pos (links.push l) j hp, Array.getElem_push_lt hj,
        getElem!_pos links j hj]
    rw [heq]
    omega
  · by_cases he : j = links.size
    · subst j
      have hp : links.size < (links.push l).size := by
        rw [Array.size_push]
        omega
      have heq : (links.push l)[links.size]! = l := by
        rw [getElem!_pos (links.push l) links.size hp, Array.getElem_push_eq]
      rw [heq]
      omega
    · have hp : ¬ j < (links.push l).size := by
        rw [Array.size_push]
        omega
      omega

theorem append_link_adjacency (links : Array Link) (nodes : Array Node) (l : Link)
    (hadj : ∀ k, k < nodes.size →
      (∀ j, j ∈ (nodes[k]!).incoming ↔ j < links.size ∧ (links[j]!).target = k) ∧
        (∀ j, j ∈ (nodes[k]!).outgoing ↔ j < links.size ∧ (links[j]!).source = k)) :
    let updated := (nodes.modify l.source (fun n =>
      { n with outgoing := n.outgoing ++ [links.size] })).modify l.target (fun n =>
        { n with incoming := n.incoming ++ [links.size] })
    ∀ k, k < updated.size →
      (∀ j, j ∈ (updated[k]!).incoming ↔
        j < (links.push l).size ∧ ((links.push l)[j]!).target = k) ∧
      (∀ j, j ∈ (updated[k]!).outgoing ↔
        j < (links.push l).size ∧ ((links.push l)[j]!).source = k) := by
  dsimp only
  intro k hk
  have hkold : k < nodes.size := by simpa only [Array.size_modify] using hk
  have hmid : k < (nodes.modify l.source (fun n =>
      { n with outgoing := n.outgoing ++ [links.size] })).size := by
    simpa only [Array.size_modify] using hkold
  have hin :
      (((nodes.modify l.source (fun n =>
        { n with outgoing := n.outgoing ++ [links.size] })).modify l.target (fun n =>
          { n with incoming := n.incoming ++ [links.size] }))[k]!).incoming =
        if l.target = k then (nodes[k]!).incoming ++ [links.size]
        else (nodes[k]!).incoming := by
    rw [getElem!_pos _ k hk, Array.getElem_modify hk, Array.getElem_modify hmid,
      getElem!_pos nodes k hkold]
    by_cases hs : l.source = k <;> by_cases ht : l.target = k <;>
      simp only [hs, ht, ite_true, ite_false]
  have hout :
      (((nodes.modify l.source (fun n =>
        { n with outgoing := n.outgoing ++ [links.size] })).modify l.target (fun n =>
          { n with incoming := n.incoming ++ [links.size] }))[k]!).outgoing =
        if l.source = k then (nodes[k]!).outgoing ++ [links.size]
        else (nodes[k]!).outgoing := by
    rw [getElem!_pos _ k hk, Array.getElem_modify hk, Array.getElem_modify hmid,
      getElem!_pos nodes k hkold]
    by_cases hs : l.source = k <;> by_cases ht : l.target = k <;>
      simp only [hs, ht, ite_true, ite_false]
  obtain ⟨hinc, houtgoing⟩ := hadj k hkold
  constructor
  · intro j
    rw [hin, pushed_link_incidence links l (·.target)]
    by_cases ht : l.target = k
    · simp only [ht, ite_true, List.mem_append, List.mem_singleton, hinc j,
        and_true]
    · simp only [ht, ite_false, hinc j, and_false, or_false]
  · intro j
    rw [hout, pushed_link_incidence links l (·.source)]
    by_cases hs : l.source = k
    · simp only [hs, ite_true, List.mem_append, List.mem_singleton, houtgoing j,
        and_true]
    · simp only [hs, ite_false, houtgoing j, and_false, or_false]

theorem decode_adjacency_incidence (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) :
    ∀ k, k < f.nodes.size →
      (∀ j, j ∈ (f.nodes[k]!).incoming ↔
        j < f.links.size ∧ (f.links[j]!).target = k) ∧
      (∀ j, j ∈ (f.nodes[k]!).outgoing ↔
        j < f.links.size ∧ (f.links[j]!).source = k) := by
  unfold decode at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i state hloop
    have hinvariant :
        state.1.size = m.routes.length ∧
          ∀ k, k < state.2.size →
            (∀ j, j ∈ (state.2[k]!).incoming ↔
              j < state.1.size ∧ (state.1[j]!).target = k) ∧
            (∀ j, j ∈ (state.2[k]!).outgoing ↔
              j < state.1.size ∧ (state.1[j]!).source = k) := by
      refine (Nat.zero_add m.routes.length) ▸
        except_forIn_index_invariant _ _ m.routes 0 _ state _
        (fun i (state : Array Link × Array Node) =>
          state.1.size = i ∧
            ∀ k, k < state.2.size →
              (∀ j, j ∈ (state.2[k]!).incoming ↔
                j < state.1.size ∧ (state.1[j]!).target = k) ∧
              (∀ j, j ∈ (state.2[k]!).outgoing ↔
                j < state.1.size ∧ (state.1[j]!).source = k))
        ?_ ?_ hloop
      · constructor
        · rfl
        · intro k hk
          rw [getElem!_pos _ k hk]
          simp
      · intro r i previous next hprevious hnext
        repeat' (split at hnext <;> try contradiction)
        cases hnext
        refine ⟨_, rfl, ?_⟩
        constructor
        · simpa only [Array.size_push] using congrArg Nat.succ hprevious.1
        · simpa only [hprevious.1] using
            append_link_adjacency previous.1 previous.2
              { source := nodeIndex m r.fromId
                target := nodeIndex m r.toId
                value := unzigzag
                  ((((m.regionSets.head?).map (fun region : ModelRegionSet => region.regions)).getD []).getD (2 * i + 1) 0) }
              hprevious.2
    cases h
    intro k hk
    have hkold : k < state.2.size := by simpa only [Array.size_map] using hk
    obtain ⟨hinc, hout⟩ := hinvariant.2 k hkold
    rw [getElem!_pos state.2 k hkold] at hinc hout
    rw [getElem!_pos _ k hk, Array.getElem_map]
    exact ⟨hinc, hout⟩

theorem except_forIn_visit_invariant (α β : Type) (xs : List α) (visited : α)
    (init out : β) (step : α → β → Except LayoutError (ForInStep β))
    (P : β → Prop) (hmember : visited ∈ xs)
    (hyield : ∀ a state next, step a state = .ok next →
      ∃ state', next = .yield state')
    (hpreserve : ∀ a state next, P state → step a state = .ok next → P next.value)
    (hvisit : ∀ state next, step visited state = .ok next → P next.value)
    (hsuccess : ForIn.forIn xs init step = .ok out) : P out := by
  induction xs generalizing init with
  | nil => simp at hmember
  | cons a xs ih =>
    rw [List.forIn_cons] at hsuccess
    cases he : step a init with
    | error e => simp [he, Bind.bind, Except.bind] at hsuccess
    | ok next =>
      obtain ⟨state', rfl⟩ := hyield a init next he
      simp only [he, Bind.bind, Except.bind] at hsuccess
      rcases List.mem_cons.mp hmember with ha | htail
      · subst a
        exact except_forIn_invariant _ _ xs state' out step P
          (hvisit init (.yield state') he) hpreserve hsuccess
      · exact ih state' htail hsuccess

theorem scale_le_column (f : Flow) (ky : Int) (h : scale f = .ok ky)
    (column : List Nat) (hcolumn : column ∈ f.columns.toList)
    (htotal : 0 < column.foldl (fun total i => total + (f.nodes[i]!).value) 0) :
    ky ≤ Int.fdiv
      ((f.extent - (Int.ofNat column.length - 1) * f.py) * 65536)
      (column.foldl (fun total i => total + (f.nodes[i]!).value) 0) := by
  let bound := Int.fdiv
    ((f.extent - (Int.ofNat column.length - 1) * f.py) * 65536)
    (column.foldl (fun total i => total + (f.nodes[i]!).value) 0)
  have hnonempty : column.isEmpty = false := by
    cases column with
    | nil => simp at htotal
    | cons i rest => rfl
  unfold scale at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i best hloop
    rw [← Array.forIn_toList] at hloop
    have hbest : ∃ value, best = some value ∧ value ≤ bound := by
      refine except_forIn_visit_invariant _ _ f.columns.toList column _ best _
        (fun best : Option Int => ∃ value, best = some value ∧ value ≤ bound)
        hcolumn ?_ ?_ ?_ hloop
      · intro c previous next hnext
        repeat' (split at hnext <;> try contradiction)
        all_goals
          cases hnext
          exact ⟨_, rfl⟩
      · intro c previous next hprevious hnext
        obtain ⟨value, rfl, hvalue⟩ := hprevious
        repeat' (split at hnext <;> try contradiction)
        all_goals
          cases hnext
          try simp_all only [Option.some.injEq]
          first
          | exact ⟨value, rfl, hvalue⟩
          | exact ⟨_, rfl, Int.le_trans (Int.min_le_left _ _) hvalue⟩
      · intro previous next hnext
        simp only [hnonempty, Bool.not_false, htotal, ite_true] at hnext
        repeat' (split at hnext <;> try contradiction)
        all_goals
          cases hnext
          first
          | exact ⟨_, rfl, Int.le_refl bound⟩
          | exact ⟨_, rfl, Int.min_le_right _ bound⟩
    cases h
    obtain ⟨value, rfl, hvalue⟩ := hbest
    exact hvalue

theorem scale_column_room_nonnegative (f : Flow) (ky : Int) (h : scale f = .ok ky)
    (column : List Nat) (hcolumn : column ∈ f.columns.toList)
    (hnonempty : column.isEmpty = false) :
    0 ≤ f.extent - (Int.ofNat column.length - 1) * f.py := by
  unfold scale at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i best hloop
    rw [← Array.forIn_toList] at hloop
    refine except_forIn_visit_invariant _ _ f.columns.toList column _ best _
      (fun _ : Option Int => 0 ≤ f.extent - (Int.ofNat column.length - 1) * f.py)
      hcolumn ?_ ?_ ?_ hloop
    · intro c previous next hnext
      repeat' (split at hnext <;> try contradiction)
      all_goals
        cases hnext
        exact ⟨_, rfl⟩
    · intro c previous next hprevious hnext
      exact hprevious
    · intro previous next hnext
      simp only [hnonempty, Bool.not_false, ite_true] at hnext
      split at hnext
      · contradiction
      · omega

theorem node_value_fold_sum (nodes : Array Node) (indices : List Nat) (seed : Int) :
    indices.foldl (fun total i => total + (nodes[i]!).value) seed =
      seed + (indices.map (fun i => (nodes[i]!).value)).sum := by
  induction indices generalizing seed with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    omega

theorem scale_column_capacity_positive (f : Flow) (ky : Int) (h : scale f = .ok ky)
    (column : List Nat) (hcolumn : column ∈ f.columns.toList)
    (htotal : 0 < column.foldl (fun total i => total + (f.nodes[i]!).value) 0) :
    scaledSum (column.map (fun i => (f.nodes[i]!).value)) ky ≤
      f.extent - (Int.ofNat column.length - 1) * f.py := by
  let total := column.foldl (fun total i => total + (f.nodes[i]!).value) 0
  let room := f.extent - (Int.ofNat column.length - 1) * f.py
  have hbound := scale_le_column f ky h column hcolumn htotal
  change ky ≤ Int.fdiv (room * 65536) total at hbound
  have ht : 0 < total := htotal
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt ht)] at hbound
  have hproduct : total * ky ≤ room * 65536 := by
    calc
      total * ky = ky * total := Int.mul_comm _ _
      _ ≤ (room * 65536 / total) * total :=
        Int.mul_le_mul_of_nonneg_right hbound (Int.le_of_lt ht)
      _ ≤ room * 65536 := Int.ediv_mul_le _ (Int.ne_of_gt ht)
  apply columnHeights_le_room
  have hsum : (column.map (fun i => (f.nodes[i]!).value)).sum = total := by
    simpa only [Int.zero_add] using (node_value_fold_sum f.nodes column 0).symm
  rw [hsum]
  exact hproduct

theorem nonnegative_value_sum (values : List Int)
    (hvalues : ∀ value ∈ values, 0 ≤ value) : 0 ≤ values.sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    have hv := hvalues value (by simp)
    have hr := ih (fun v hv => hvalues v (List.mem_cons_of_mem value hv))
    simp only [List.sum_cons]
    omega

theorem scaledSum_zero_of_sum_zero (values : List Int) (ky : Int)
    (hvalues : ∀ value ∈ values, 0 ≤ value) (hsum : values.sum = 0) :
    scaledSum values ky = 0 := by
  induction values with
  | nil => simp [scaledSum]
  | cons value rest ih =>
    have hv := hvalues value (by simp)
    have hrest : ∀ v ∈ rest, 0 ≤ v :=
      fun v hv => hvalues v (List.mem_cons_of_mem value hv)
    have hr := nonnegative_value_sum rest hrest
    have hsum' : value + rest.sum = 0 := hsum
    have hvzero : value = 0 := by omega
    have hrzero : rest.sum = 0 := by omega
    subst value
    simpa [scaledSum] using ih hrest hrzero

theorem scale_column_capacity (f : Flow) (ky : Int) (h : scale f = .ok ky)
    (column : List Nat) (hcolumn : column ∈ f.columns.toList)
    (hnonempty : column.isEmpty = false)
    (hvalues : ∀ i ∈ column, 0 ≤ (f.nodes[i]!).value) :
    scaledSum (column.map (fun i => (f.nodes[i]!).value)) ky ≤
      f.extent - (Int.ofNat column.length - 1) * f.py := by
  have hmap : ∀ value ∈ column.map (fun i => (f.nodes[i]!).value), 0 ≤ value := by
    intro value hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hvalues i hi
  have hsum := nonnegative_value_sum _ hmap
  have htotal := node_value_fold_sum f.nodes column 0
  simp only [Int.zero_add] at htotal
  by_cases hp : 0 < column.foldl (fun total i => total + (f.nodes[i]!).value) 0
  · exact scale_column_capacity_positive f ky h column hcolumn hp
  · have hz : (column.map (fun i => (f.nodes[i]!).value)).sum = 0 := by omega
    rw [scaledSum_zero_of_sum_zero _ ky hmap hz]
    exact scale_column_room_nonnegative f ky h column hcolumn hnonempty

theorem column_fold_size (nodes : Array Node) (indices : List Nat)
    (columns : Array (List Nat)) :
    (indices.foldl (fun columns i =>
      columns.modify (nodes[i]!).layer (fun column => column ++ [i])) columns).size =
        columns.size := by
  induction indices generalizing columns with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, Array.size_modify]

theorem column_fold_partition (nodes : Array Node) (count n : Nat) :
    let columns := (List.range n).foldl (fun columns i =>
      columns.modify (nodes[i]!).layer (fun column => column ++ [i]))
        (Array.replicate count [])
    ∀ c, c < count →
      (columns[c]!).Nodup ∧
        ∀ i, i ∈ columns[c]! ↔ i < n ∧ (nodes[i]!).layer = c := by
  dsimp only
  induction n with
  | zero =>
    intro c hc
    have hb : c < (Array.replicate count ([] : List Nat)).size := by simpa using hc
    rw [getElem!_pos _ c hb]
    simp
  | succ n ih =>
    let previous := (List.range n).foldl (fun columns i =>
      columns.modify (nodes[i]!).layer (fun column => column ++ [i]))
        (Array.replicate count [])
    have hsize : previous.size = count := by
      simp only [previous, column_fold_size, Array.size_replicate]
    intro c hc
    have hcold : c < previous.size := by omega
    have hcnew : c < (previous.modify (nodes[n]!).layer
        (fun column => column ++ [n])).size := by
      simpa only [Array.size_modify] using hcold
    have hprevious := ih c hc
    change (previous[c]!).Nodup ∧
      (∀ i, i ∈ previous[c]! ↔ i < n ∧ (nodes[i]!).layer = c) at hprevious
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ((previous.modify (nodes[n]!).layer (fun column => column ++ [n]))[c]!).Nodup ∧
      (∀ i, i ∈ (previous.modify (nodes[n]!).layer
        (fun column => column ++ [n]))[c]! ↔ i < n + 1 ∧ (nodes[i]!).layer = c)
    rw [getElem!_pos _ c hcnew, Array.getElem_modify hcnew]
    rw [getElem!_pos previous c hcold] at hprevious
    by_cases hlayer : (nodes[n]!).layer = c
    · simp only [hlayer, ite_true]
      constructor
      · exact (append_fresh_index _ n
          ⟨hprevious.1, fun i hi => ((hprevious.2 i).mp hi).1⟩).1
      · intro i
        rw [List.mem_append, List.mem_singleton, hprevious.2 i]
        constructor
        · intro hi
          rcases hi with hi | rfl
          · exact ⟨by omega, hi.2⟩
          · exact ⟨by omega, hlayer⟩
        · intro hi
          by_cases hlt : i < n
          · exact Or.inl ⟨hlt, hi.2⟩
          · have heq : i = n := by omega
            exact Or.inr heq
    · simp only [hlayer, ite_false]
      refine ⟨hprevious.1, ?_⟩
      intro i
      rw [hprevious.2 i]
      constructor
      · intro hi
        exact ⟨by omega, hi.2⟩
      · intro hi
        refine ⟨?_, hi.2⟩
        by_cases hlt : i < n
        · exact hlt
        · have heq : i = n := by omega
          subst i
          exact False.elim (hlayer hi.2)

theorem place_column_partition (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) :
    ∀ c, c < out.columns.size →
      (out.columns[c]!).Nodup ∧
        ∀ i, i ∈ out.columns[c]! ↔
          i < out.nodes.size ∧ (out.nodes[i]!).layer = c := by
  unfold place at h
  cases hd : levels f false with
  | error e => simp [hd, Bind.bind, Except.bind] at h
  | ok depths =>
    cases hh : levels f true with
    | error e => simp [hd, hh, Bind.bind, Except.bind] at h
    | ok heights =>
      simp [hd, hh] at h
      cases h
      simp only [column_fold_size, Array.size_replicate, Array.size_mapIdx]
      exact column_fold_partition _ _ _

theorem place_layers_bounded (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) :
    ∀ i, i < out.nodes.size → (out.nodes[i]!).layer < out.columns.size := by
  unfold place at h
  cases hd : levels f false with
  | error e => simp [hd, Bind.bind, Except.bind] at h
  | ok depths =>
    cases hh : levels f true with
    | error e => simp [hd, hh, Bind.bind, Except.bind] at h
    | ok heights =>
      let count := depths.foldl (fun n d => max n (d + 1)) 1
      have hcount : 0 < count := by
        have hseed : 1 ≤ depths.foldl (fun n d => max n (d + 1)) 1 := by
          apply Array.foldl_induction (motive := fun _ n => 1 ≤ n)
          · decide
          · intro i n hn
            exact Nat.le_trans hn (Nat.le_max_left _ _)
        omega
      simp [hd, hh] at h
      cases h
      intro i hi
      rw [getElem!_pos _ i hi, Array.getElem_mapIdx]
      simp only [column_fold_size, Array.size_replicate]
      change min _ (count - 1) < count
      exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)

theorem place_column_coverage (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) :
    ∀ i, i < out.nodes.size →
      ∃ c, c < out.columns.size ∧ i ∈ out.columns[c]! := by
  intro i hi
  have hc := place_layers_bounded f out alignment h i hi
  refine ⟨(out.nodes[i]!).layer, hc, ?_⟩
  exact ((place_column_partition f out alignment h _ hc).2 i).mpr ⟨hi, rfl⟩

theorem id_forIn_visit_invariant (α β : Type) (xs : List α) (visited : α)
    (init : β) (step : α → β → Id (ForInStep β)) (P : β → Prop)
    (hmember : visited ∈ xs)
    (hyield : ∀ a state, ∃ state', step a state = .yield state')
    (hpreserve : ∀ a state, P state → P (step a state).value)
    (hvisit : ∀ state, P (step visited state).value) :
    P (ForIn.forIn (m := Id) xs init step) := by
  induction xs generalizing init with
  | nil => simp at hmember
  | cons a xs ih =>
    rw [List.forIn_cons]
    change P (match step a init with
      | .done state => state
      | .yield state => ForIn.forIn (m := Id) xs state step)
    obtain ⟨state', hnext⟩ := hyield a init
    rw [hnext]
    rcases List.mem_cons.mp hmember with ha | htail
    · subst a
      exact id_forIn_invariant _ _ xs state' step P
        (by simpa only [hnext, ForInStep.value] using hvisit init) hpreserve
    · exact ih state' htail

theorem set_preserves_node_values (nodes : Array Node) (i : Nat) (n : Node)
    (hn : n.value = (nodes[i]!).value) (j : Nat) :
    ((nodes.set! i n)[j]!).value = (nodes[j]!).value := by
  by_cases hij : i = j
  · subst j
    by_cases hi : i < nodes.size
    · rw [Array.getElem!_set!_self nodes i n hi]
      exact hn
    · have he : nodes.set! i n = nodes := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne nodes i j n hij]

theorem set_coordinates_preserves_value (nodes : Array Node) (j : Nat)
    (y0 y1 : Int) (i : Nat) :
    ((nodes.set! j { nodes[j]! with y0, y1 })[i]!).value = (nodes[i]!).value :=
  set_preserves_node_values nodes j { nodes[j]! with y0 := y0, y1 := y1 } rfl i

theorem refresh_scaled_height (nodes : Array Node) (j : Nat) (y ky : Int) (i : Nat)
    (hprevious : i ≠ j →
      (nodes[i]!).y1 - (nodes[i]!).y0 = Int.fdiv ((nodes[i]!).value * ky) 65536) :
    let refreshed : Node := { nodes[j]! with y0 := y, y1 := y + Int.fdiv ((nodes[j]!).value * ky) 65536 }
    let updated := nodes.set! j refreshed
    (updated[i]!).y1 - (updated[i]!).y0 =
      Int.fdiv ((updated[i]!).value * ky) 65536 := by
  dsimp only
  by_cases hji : j = i
  · subst i
    by_cases hj : j < nodes.size
    · rw [Array.getElem!_set!_self _ _ _ hj]
      dsimp only
      omega
    · have he : nodes.set! j
          ({ nodes[j]! with y0 := y, y1 := y + Int.fdiv ((nodes[j]!).value * ky) 65536 } : Node) = nodes := by
        simp [Array.set!, Array.setIfInBounds, hj]
      rw [he, getElem!_neg nodes j hj]
      change (0 : Int) - 0 = Int.fdiv (0 * ky) 65536
      simp only [Int.zero_mul, Int.sub_self]
      decide
  · rw [Array.getElem!_set!_ne _ _ _ _ hji]
    exact hprevious (Ne.symm hji)

theorem translate_scaled_height (nodes : Array Node) (j : Nat) (dy ky : Int) (i : Nat)
    (hprevious : (nodes[i]!).y1 - (nodes[i]!).y0 =
      Int.fdiv ((nodes[i]!).value * ky) 65536) :
    let updated := nodes.set! j { nodes[j]! with
      y0 := (nodes[j]!).y0 + dy, y1 := (nodes[j]!).y1 + dy }
    (updated[i]!).y1 - (updated[i]!).y0 =
      Int.fdiv ((updated[i]!).value * ky) 65536 := by
  dsimp only
  rw [set_preserves_heights nodes j
      { nodes[j]! with y0 := (nodes[j]!).y0 + dy, y1 := (nodes[j]!).y1 + dy }
      (by dsimp only; omega) i, set_coordinates_preserves_value]
  exact hprevious

theorem stack_node_values (f : Flow) (column : List Nat) (ky : Int) :
    ∀ (i : Nat), ((stack f column ky).nodes[i]!).value = (f.nodes[i]!).value := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant
    (P := fun out : Flow => ∀ (i : Nat), (out.nodes[i]!).value = (f.nodes[i]!).value)
  · apply id_forIn_invariant
      (P := fun out : Flow × Int => ∀ (i : Nat), (out.1.nodes[i]!).value = (f.nodes[i]!).value)
    · intro i
      rfl
    · intro j state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant
        (P := fun out : Flow => ∀ (i : Nat), (out.nodes[i]!).value = (f.nodes[i]!).value)
      · intro i
        rw [set_coordinates_preserves_value]
        exact hstate i
      · intro j out hout
        exact hout
  · intro pair out hout
    dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
    intro i
    rw [set_coordinates_preserves_value]
    exact hout i

theorem stack_node_height (f : Flow) (column : List Nat) (ky : Int)
    (i : Nat) (hmember : i ∈ column) :
    ((stack f column ky).nodes[i]!).y1 - ((stack f column ky).nodes[i]!).y0 =
      Int.fdiv ((f.nodes[i]!).value * ky) 65536 := by
  have hscaled :
      ((stack f column ky).nodes[i]!).y1 - ((stack f column ky).nodes[i]!).y0 =
        Int.fdiv (((stack f column ky).nodes[i]!).value * ky) 65536 := by
    unfold stack
    dsimp only [Id.run, Bind.bind, Id.instMonad]
    apply id_forIn_invariant
      (P := fun out : Flow => (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
        Int.fdiv ((out.nodes[i]!).value * ky) 65536)
    · apply id_forIn_visit_invariant (visited := i)
        (P := fun out : Flow × Int => (out.1.nodes[i]!).y1 - (out.1.nodes[i]!).y0 =
          Int.fdiv ((out.1.nodes[i]!).value * ky) 65536)
      · exact hmember
      · intro j state
        exact ⟨_, rfl⟩
      · intro j state hstate
        dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
        apply id_forIn_invariant
          (P := fun out : Flow => (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
            Int.fdiv ((out.nodes[i]!).value * ky) 65536)
        · apply refresh_scaled_height
          intro hne
          exact hstate
        · intro j out hout
          exact hout
      · intro state
        dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
        apply id_forIn_invariant
          (P := fun out : Flow => (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
            Int.fdiv ((out.nodes[i]!).value * ky) 65536)
        · apply refresh_scaled_height
          intro hne
          exact False.elim (hne rfl)
        · intro j out hout
          exact hout
    · intro pair out hout
      dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
      exact translate_scaled_height _ _ _ ky i hout
  rw [stack_node_values f column ky i] at hscaled
  exact hscaled

theorem id_forIn_visit_with_invariant (α β : Type) (xs : List α) (visited : α)
    (init : β) (step : α → β → Id (ForInStep β)) (I P : β → Prop)
    (hmember : visited ∈ xs) (hinit : I init)
    (hyield : ∀ a state, ∃ state', step a state = .yield state')
    (hbase : ∀ a state, I state → I (step a state).value)
    (hpreserve : ∀ a state, I state → P state → P (step a state).value)
    (hvisit : ∀ state, I state → P (step visited state).value) :
    P (ForIn.forIn (m := Id) xs init step) := by
  induction xs generalizing init with
  | nil => simp at hmember
  | cons a xs ih =>
    rw [List.forIn_cons]
    change P (match step a init with
      | .done state => state
      | .yield state => ForIn.forIn (m := Id) xs state step)
    obtain ⟨state', hnext⟩ := hyield a init
    rw [hnext]
    have hnew : I state' := by
      simpa only [hnext, ForInStep.value] using hbase a init hinit
    rcases List.mem_cons.mp hmember with ha | htail
    · subst a
      have hp : P state' := by
        simpa only [hnext, ForInStep.value] using hvisit init hinit
      have hfinal := id_forIn_invariant _ _ xs state' step
        (fun state => I state ∧ P state) ⟨hnew, hp⟩
        (by
          intro a state hs
          exact ⟨hbase a state hs.1, hpreserve a state hs.1 hs.2⟩)
      exact hfinal.2
    · exact ih state' htail hnew

theorem set_preserves_node_projection (α : Type) (nodes : Array Node)
    (i : Nat) (n : Node) (project : Node → α)
    (hn : project n = project (nodes[i]!)) (j : Nat) :
    project ((nodes.set! i n)[j]!) = project (nodes[j]!) := by
  by_cases hij : i = j
  · subst j
    by_cases hi : i < nodes.size
    · rw [Array.getElem!_set!_self nodes i n hi]
      exact hn
    · have he : nodes.set! i n = nodes := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne nodes i j n hij]

theorem set_coordinates_preserves_outgoing (nodes : Array Node) (j : Nat)
    (y0 y1 : Int) (i : Nat) :
    ((nodes.set! j { nodes[j]! with y0, y1 })[i]!).outgoing = (nodes[i]!).outgoing :=
  set_preserves_node_projection _ nodes j
    { nodes[j]! with y0 := y0, y1 := y1 } (·.outgoing) rfl i

theorem set_preserves_link_values (links : Array Link) (i : Nat) (l : Link)
    (hl : l.value = (links[i]!).value) (j : Nat) :
    ((links.set! i l)[j]!).value = (links[j]!).value := by
  by_cases hij : i = j
  · subst j
    by_cases hi : i < links.size
    · rw [Array.getElem!_set!_self links i l hi]
      exact hl
    · have he : links.set! i l = links := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne links i j l hij]

theorem set_width_preserves_value (links : Array Link) (j : Nat) (width : Int)
    (i : Nat) :
    ((links.set! j { links[j]! with width })[i]!).value = (links[i]!).value :=
  set_preserves_link_values links j { links[j]! with width := width } rfl i

theorem refresh_scaled_width (links : Array Link) (j : Nat) (ky : Int) (i : Nat)
    (hprevious : i ≠ j →
      (links[i]!).width = Int.fdiv ((links[i]!).value * ky) 65536) :
    let refreshed : Link := { links[j]! with width := Int.fdiv ((links[j]!).value * ky) 65536 }
    let updated := links.set! j refreshed
    (updated[i]!).width = Int.fdiv ((updated[i]!).value * ky) 65536 := by
  dsimp only
  by_cases hji : j = i
  · subst i
    by_cases hj : j < links.size
    · rw [Array.getElem!_set!_self _ _ _ hj]
    · have he : links.set! j
          ({ links[j]! with width := Int.fdiv ((links[j]!).value * ky) 65536 } : Link) = links := by
        simp [Array.set!, Array.setIfInBounds, hj]
      rw [he, getElem!_neg links j hj]
      change (0 : Int) = Int.fdiv (0 * ky) 65536
      simp only [Int.zero_mul]
      decide
  · rw [Array.getElem!_set!_ne _ _ _ _ hji]
    exact hprevious (Ne.symm hji)

theorem stack_link_values (f : Flow) (column : List Nat) (ky : Int) :
    ∀ (i : Nat), ((stack f column ky).links[i]!).value = (f.links[i]!).value := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant
    (P := fun out : Flow => ∀ (i : Nat), (out.links[i]!).value = (f.links[i]!).value)
  · apply id_forIn_invariant
      (P := fun out : Flow × Int => ∀ (i : Nat), (out.1.links[i]!).value = (f.links[i]!).value)
    · intro i
      rfl
    · intro j state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant
        (P := fun out : Flow => ∀ (i : Nat), (out.links[i]!).value = (f.links[i]!).value)
      · exact hstate
      · intro j out hout
        dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
        intro i
        rw [set_width_preserves_value]
        exact hout i
  · intro pair out hout
    exact hout

theorem stack_link_width (f : Flow) (column : List Nat) (ky : Int)
    (source link : Nat) (hsource : source ∈ column)
    (hlink : link ∈ (f.nodes[source]!).outgoing) :
    ((stack f column ky).links[link]!).width =
      Int.fdiv ((f.links[link]!).value * ky) 65536 := by
  have hscaled : ((stack f column ky).links[link]!).width =
      Int.fdiv (((stack f column ky).links[link]!).value * ky) 65536 := by
    unfold stack
    dsimp only [Id.run, Bind.bind, Id.instMonad]
    apply id_forIn_invariant
      (P := fun out : Flow => (out.links[link]!).width =
        Int.fdiv ((out.links[link]!).value * ky) 65536)
    · apply id_forIn_visit_with_invariant (visited := source)
        (I := fun state : Flow × Int =>
          (state.1.nodes[source]!).outgoing = (f.nodes[source]!).outgoing)
        (P := fun state : Flow × Int => (state.1.links[link]!).width =
          Int.fdiv ((state.1.links[link]!).value * ky) 65536)
      · exact hsource
      · rfl
      · intro j state
        exact ⟨_, rfl⟩
      · intro j state hstate
        dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
        apply id_forIn_invariant
          (P := fun out : Flow => (out.nodes[source]!).outgoing =
            (f.nodes[source]!).outgoing)
        · rw [set_coordinates_preserves_outgoing]
          exact hstate
        · intro j out hout
          exact hout
      · intro j state hbase hstate
        dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
        apply id_forIn_invariant
          (P := fun out : Flow => (out.links[link]!).width =
            Int.fdiv ((out.links[link]!).value * ky) 65536)
        · exact hstate
        · intro j out hout
          dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
          exact refresh_scaled_width _ _ ky link (fun _ => hout)
      · intro state hstate
        dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
        apply id_forIn_visit_invariant (visited := link)
          (P := fun out : Flow => (out.links[link]!).width =
            Int.fdiv ((out.links[link]!).value * ky) 65536)
        · rw [hstate]
          exact hlink
        · intro j out
          exact ⟨_, rfl⟩
        · intro j out hout
          dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
          exact refresh_scaled_width _ _ ky link (fun _ => hout)
        · intro out
          dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
          apply refresh_scaled_width
          intro hne
          exact False.elim (hne rfl)
    · intro pair out hout
      exact hout
  rw [stack_link_values f column ky link] at hscaled
  exact hscaled

theorem stack_preserves_scaled_width (f : Flow) (column : List Nat) (ky : Int)
    (link : Nat)
    (hwidth : (f.links[link]!).width = Int.fdiv ((f.links[link]!).value * ky) 65536) :
    ((stack f column ky).links[link]!).width =
      Int.fdiv (((stack f column ky).links[link]!).value * ky) 65536 := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant
    (P := fun out : Flow => (out.links[link]!).width =
      Int.fdiv ((out.links[link]!).value * ky) 65536)
  · apply id_forIn_invariant
      (P := fun state : Flow × Int => (state.1.links[link]!).width =
        Int.fdiv ((state.1.links[link]!).value * ky) 65536)
    · exact hwidth
    · intro j state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant
        (P := fun out : Flow => (out.links[link]!).width =
          Int.fdiv ((out.links[link]!).value * ky) 65536)
      · exact hstate
      · intro j out hout
        dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
        exact refresh_scaled_width _ _ ky link (fun _ => hout)
  · intro pair out hout
    exact hout

theorem scale_nonnegative (f : Flow) (ky : Int) (h : scale f = .ok ky) :
    0 ≤ ky := by
  unfold scale at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i best hloop
    rw [← Array.forIn_toList] at hloop
    have hbest : 0 ≤ best.getD 0 := by
      refine except_forIn_invariant _ _ f.columns.toList _ best _
        (fun best : Option Int => 0 ≤ best.getD 0) ?_ ?_ hloop
      · decide
      · intro column previous next hprevious hnext
        repeat' (split at hnext <;> try contradiction)
        all_goals
          cases hnext
          simp_all only [ForInStep.value, Option.getD_none, Option.getD_some]
        all_goals
          first
          | exact hprevious
          | apply Int.fdiv_nonneg <;> omega
          | apply Int.le_min.mpr
            constructor
            · exact hprevious
            · apply Int.fdiv_nonneg <;> omega
    cases h
    exact hbest

theorem link_value_fold_sum (links : Array Link) (indices : List Nat) (seed : Int) :
    indices.foldl (fun total i => total + (links[i]!).value) seed =
      seed + (indices.map (fun i => (links[i]!).value)).sum := by
  induction indices generalizing seed with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    omega

theorem decode_node_values (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) :
    ∀ n ∈ f.nodes.toList,
      n.value = max
        (n.incoming.map (fun i => (f.links[i]!).value)).sum
        (n.outgoing.map (fun i => (f.links[i]!).value)).sum := by
  unfold decode at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · cases h
    intro n hn
    simp only [Array.toList_map, List.mem_map] at hn
    obtain ⟨original, _, rfl⟩ := hn
    simp only [link_value_fold_sum, Int.zero_add]

theorem decode_indexed_link_nonnegative (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) (j : Nat) :
    0 ≤ (f.links[j]!).value := by
  by_cases hj : j < f.links.size
  · rw [getElem!_pos f.links j hj]
    exact (decode_link_bounds m extent padding f h _ (Array.getElem_mem_toList hj)).1
  · rw [getElem!_neg f.links j hj]
    decide

theorem decode_node_nonnegative (m : Model) (extent padding : Int) (f : Flow)
    (h : decode m extent padding = .ok f) :
    ∀ n ∈ f.nodes.toList, 0 ≤ n.value := by
  have hsum : ∀ indices : List Nat,
      0 ≤ (indices.map (fun i => (f.links[i]!).value)).sum := by
    intro indices
    induction indices with
    | nil => simp
    | cons i rest ih =>
      have hi := decode_indexed_link_nonnegative m extent padding f h i
      simp only [List.map_cons, List.sum_cons]
      omega
  intro n hn
  rw [decode_node_values m extent padding f h n hn]
  exact Int.le_trans (hsum n.incoming) (Int.le_max_left _ _)

theorem layoutCore_canvas (m : Model) (s : Scene) (h : layoutCore m = .ok s) :
    Validator.C1 s.layoutDump := by
  let width := configInt m "width"
    (Int.fdiv (LayoutConst.sankey_width.get .vector) 64) * 64
  let height := configInt m "height"
    (Int.fdiv (LayoutConst.sankey_height.get .vector) 64) * 64
  let padding := LayoutConst.sankey_node_padding.get .vector +
    (if showValues m then LayoutConst.sankey_show_values_pad.get .vector else 0)
  unfold layoutCore at h
  cases hd : decode m height padding with
  | error e => simp [height, padding, hd, Bind.bind, Except.bind] at h
  | ok decoded =>
    cases hr : run decoded (configString m "nodeAlignment" "justify")
        (LayoutConst.sankey_iterations.get .vector).toNat with
    | error e => simp [height, padding, hd, hr, Bind.bind, Except.bind] at h
    | ok flowed =>
      let rects := nodeRects flowed width (LayoutConst.sankey_node_width.get .vector)
      cases hl : measureLabels m rects width height
          (LayoutConst.sankey_label_gap.get .vector) with
      | error e =>
        simp [width, height, padding, rects, hd, hr, hl, Bind.bind, Except.bind] at h
      | ok labels =>
        have hcount : m.boxes.length ≤ rects.size := by
          have hdsize := decode_nodes_size m height padding decoded hd
          have hrsize := run_nodes_size decoded flowed _ _ hr
          simp only [rects, nodeRects_size]
          omega
        have hnormal := normalization_rects_contained flowed rects labels width height
        have hnsize := normalize_preserves_node_count flowed rects labels width height
        simp only [width, height, padding, rects] at hd hr hl hcount hnormal hnsize
        simp only [hd, hr, hl, Bind.bind, Except.bind] at h
        repeat' (split at h <;> try contradiction)
        cases h
        apply scene_canvas_clause
        · exact Nat.le_trans hcount (Nat.le_of_eq hnsize.symm)
        · exact hnormal

theorem layout_canvas (m : Model) (s : Scene) (h : layout m = .ok s) :
    Validator.C1 s.layoutDump :=
  layoutCore_canvas m s (layout_core_success m s h)

theorem layoutCore_sceneOf (m : Model) (s : Scene) (h : layoutCore m = .ok s) :
    ∃ (f : Flow) (rects : Array Rect) (labels : List LabelPlacement)
      (width height : Int), s = sceneOf m f rects labels width height := by
  let width := configInt m "width"
    (Int.fdiv (LayoutConst.sankey_width.get .vector) 64) * 64
  let height := configInt m "height"
    (Int.fdiv (LayoutConst.sankey_height.get .vector) 64) * 64
  let padding := LayoutConst.sankey_node_padding.get .vector +
    (if showValues m then LayoutConst.sankey_show_values_pad.get .vector else 0)
  unfold layoutCore at h
  cases hd : decode m height padding with
  | error e => simp [height, padding, hd, Bind.bind, Except.bind] at h
  | ok decoded =>
    cases hr : run decoded (configString m "nodeAlignment" "justify")
        (LayoutConst.sankey_iterations.get .vector).toNat with
    | error e => simp [height, padding, hd, hr, Bind.bind, Except.bind] at h
    | ok flowed =>
      let rects := nodeRects flowed width (LayoutConst.sankey_node_width.get .vector)
      cases hl : measureLabels m rects width height
          (LayoutConst.sankey_label_gap.get .vector) with
      | error e =>
        simp [width, height, padding, rects, hd, hr, hl, Bind.bind, Except.bind] at h
      | ok labels =>
        simp only [width, height, padding, rects] at hd hr hl
        simp only [hd, hr, hl, Bind.bind, Except.bind] at h
        repeat' (split at h <;> try contradiction)
        cases h
        exact ⟨_, _, _, _, _, rfl⟩

theorem layout_metadata_clauses (m : Model) (s : Scene) (h : layout m = .ok s) :
    Validator.C2 s.layoutDump ∧ Validator.C3 s.layoutDump ∧
      Validator.C4 s.layoutDump ∧ Validator.C6 s.layoutDump ∧
      Validator.C7 s.layoutDump ∧ Validator.C8 s.layoutDump := by
  obtain ⟨hb, hr⟩ := admissible_metadata m (layout_admissible m s h)
  obtain ⟨f, rects, labels, width, height, rfl⟩ :=
    layoutCore_sceneOf m s (layout_core_success m s h)
  exact scene_metadata_clauses m f rects labels width height hb hr

theorem stack_node_outgoing (f : Flow) (column : List Nat) (ky : Int) :
    ∀ (i : Nat), ((stack f column ky).nodes[i]!).outgoing = (f.nodes[i]!).outgoing := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant
    (P := fun out : Flow => ∀ (i : Nat), (out.nodes[i]!).outgoing = (f.nodes[i]!).outgoing)
  · apply id_forIn_invariant
      (P := fun state : Flow × Int =>
        ∀ (i : Nat), (state.1.nodes[i]!).outgoing = (f.nodes[i]!).outgoing)
    · intro i
      rfl
    · intro j state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant
        (P := fun out : Flow =>
          ∀ (i : Nat), (out.nodes[i]!).outgoing = (f.nodes[i]!).outgoing)
      · intro i
        rw [set_coordinates_preserves_outgoing]
        exact hstate i
      · intro j out hout
        exact hout
  · intro pair out hout
    dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
    intro i
    rw [set_coordinates_preserves_outgoing]
    exact hout i

theorem decode_stack_outgoing_sum_le_height (m : Model) (extent padding : Int)
    (f : Flow) (hdecode : decode m extent padding = .ok f)
    (column : List Nat) (ky : Int) (hky : 0 ≤ ky) (source : Nat)
    (hsource : source ∈ column) (hindex : source < f.nodes.size) :
    (((stack f column ky).nodes[source]!).outgoing.map
      (fun j => ((stack f column ky).links[j]!).width)).sum ≤
        ((stack f column ky).nodes[source]!).y1 -
          ((stack f column ky).nodes[source]!).y0 := by
  have hmem : f.nodes[source]! ∈ f.nodes.toList := by
    rw [getElem!_pos f.nodes source hindex]
    exact Array.getElem_mem_toList hindex
  have hvalue := decode_node_values m extent padding f hdecode _ hmem
  have houtgoing :
      ((f.nodes[source]!).outgoing.map (fun j => (f.links[j]!).value)).sum ≤
        (f.nodes[source]!).value := by
    rw [hvalue]
    exact Int.le_max_right _ _
  have hscaled := linkWidths_le_nodeHeight
    ((f.nodes[source]!).outgoing.map (fun j => (f.links[j]!).value))
    (f.nodes[source]!).value ky houtgoing hky
  have hsum :
      (((stack f column ky).nodes[source]!).outgoing.map
        (fun j => ((stack f column ky).links[j]!).width)).sum =
      scaledSum ((f.nodes[source]!).outgoing.map (fun j => (f.links[j]!).value)) ky := by
    rw [stack_node_outgoing f column ky source]
    simp only [scaledSum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    exact stack_link_width f column ky source j hsource hj
  rw [hsum, stack_node_height f column ky source hsource]
  exact hscaled

theorem set_coordinates_preserves_incoming (nodes : Array Node) (j : Nat)
    (y0 y1 : Int) (i : Nat) :
    ((nodes.set! j { nodes[j]! with y0, y1 })[i]!).incoming = (nodes[i]!).incoming :=
  set_preserves_node_projection _ nodes j
    { nodes[j]! with y0 := y0, y1 := y1 } (·.incoming) rfl i

theorem stack_node_incoming (f : Flow) (column : List Nat) (ky : Int) :
    ∀ (i : Nat), ((stack f column ky).nodes[i]!).incoming = (f.nodes[i]!).incoming := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant
    (P := fun out : Flow => ∀ (i : Nat), (out.nodes[i]!).incoming = (f.nodes[i]!).incoming)
  · apply id_forIn_invariant
      (P := fun state : Flow × Int =>
        ∀ (i : Nat), (state.1.nodes[i]!).incoming = (f.nodes[i]!).incoming)
    · intro i
      rfl
    · intro j state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant
        (P := fun out : Flow =>
          ∀ (i : Nat), (out.nodes[i]!).incoming = (f.nodes[i]!).incoming)
      · intro i
        rw [set_coordinates_preserves_incoming]
        exact hstate i
      · intro j out hout
        exact hout
  · intro pair out hout
    dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
    intro i
    rw [set_coordinates_preserves_incoming]
    exact hout i

theorem stack_incoming_link_width (f : Flow) (column : List Nat) (ky : Int)
    (target link : Nat) (hlink : link ∈ (f.nodes[target]!).incoming)
    (hscaled : ∀ j ∈ (f.nodes[target]!).incoming,
      (f.links[j]!).width = Int.fdiv ((f.links[j]!).value * ky) 65536) :
    ((stack f column ky).links[link]!).width =
      Int.fdiv ((f.links[link]!).value * ky) 65536 := by
  have h := stack_preserves_scaled_width f column ky link (hscaled link hlink)
  rw [stack_link_values f column ky link] at h
  exact h

theorem decode_stack_incoming_sum_le_height (m : Model) (extent padding : Int)
    (f : Flow) (hdecode : decode m extent padding = .ok f)
    (column : List Nat) (ky : Int) (hky : 0 ≤ ky) (target : Nat)
    (htarget : target ∈ column) (hindex : target < f.nodes.size)
    (hscaled : ∀ j ∈ (f.nodes[target]!).incoming,
      (f.links[j]!).width = Int.fdiv ((f.links[j]!).value * ky) 65536) :
    (((stack f column ky).nodes[target]!).incoming.map
      (fun j => ((stack f column ky).links[j]!).width)).sum ≤
        ((stack f column ky).nodes[target]!).y1 -
          ((stack f column ky).nodes[target]!).y0 := by
  have hmem : f.nodes[target]! ∈ f.nodes.toList := by
    rw [getElem!_pos f.nodes target hindex]
    exact Array.getElem_mem_toList hindex
  have hvalue := decode_node_values m extent padding f hdecode _ hmem
  have hincoming :
      ((f.nodes[target]!).incoming.map (fun j => (f.links[j]!).value)).sum ≤
        (f.nodes[target]!).value := by
    rw [hvalue]
    exact Int.le_max_left _ _
  have hbound := linkWidths_le_nodeHeight
    ((f.nodes[target]!).incoming.map (fun j => (f.links[j]!).value))
    (f.nodes[target]!).value ky hincoming hky
  have hsum :
      (((stack f column ky).nodes[target]!).incoming.map
        (fun j => ((stack f column ky).links[j]!).width)).sum =
      scaledSum ((f.nodes[target]!).incoming.map (fun j => (f.links[j]!).value)) ky := by
    rw [stack_node_incoming f column ky target]
    simp only [scaledSum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    exact stack_incoming_link_width f column ky target j hj hscaled
  rw [hsum, stack_node_height f column ky target htarget]
  exact hbound

theorem stack_column_capacity (f : Flow) (ky : Int) (hscale : scale f = .ok ky)
    (column : List Nat) (hcolumn : column ∈ f.columns.toList)
    (hnonempty : column.isEmpty = false)
    (hvalues : ∀ i ∈ column, 0 ≤ (f.nodes[i]!).value) :
    (column.map (fun i => ((stack f column ky).nodes[i]!).y1 -
      ((stack f column ky).nodes[i]!).y0)).sum ≤
        f.extent - (Int.ofNat column.length - 1) * f.py := by
  have heq :
      (column.map (fun i => ((stack f column ky).nodes[i]!).y1 -
        ((stack f column ky).nodes[i]!).y0)).sum =
      scaledSum (column.map (fun i => (f.nodes[i]!).value)) ky := by
    simp only [scaledSum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    exact stack_node_height f column ky i hi
  rw [heq]
  exact scale_column_capacity f ky hscale column hcolumn hnonempty hvalues

theorem prefix_anchor_offset_inside (values : List Int) (k : Nat) (height : Int)
    (hvalues : ∀ value ∈ values, 0 ≤ value) (hsum : values.sum ≤ height)
    (hk : k < values.length) :
    0 ≤ (values.take k).sum + Int.fdiv values[k] 2 ∧
      (values.take k).sum + Int.fdiv values[k] 2 ≤ height := by
  have hbefore : 0 ≤ (values.take k).sum :=
    nonnegative_value_sum _ (fun value hv => hvalues value (List.mem_of_mem_take hv))
  have hwidth : 0 ≤ values[k] := hvalues _ (List.getElem_mem hk)
  have hafter : 0 ≤ (values.drop (k + 1)).sum :=
    nonnegative_value_sum _ (fun value hv => hvalues value (List.mem_of_mem_drop hv))
  have hsplit : values.take k ++ values[k] :: values.drop (k + 1) = values := by
    rw [← List.drop_eq_getElem_cons hk]
    exact List.take_append_drop k values
  have htotal := congrArg (fun xs : List Int => xs.sum) hsplit
  simp only [List.sum_append, List.sum_cons] at htotal
  exact anchor_offset_inside _ _ _ _ hbefore hwidth hafter (by omega)

theorem fold_pair_preserves_node
    (step : Flow × Int → Nat → Flow × Int) (indices : List Nat)
    (state : Flow × Int) (j : Nat)
    (hstep : ∀ previous i, i ∈ indices →
      (step previous i).1.nodes[j]! = previous.1.nodes[j]!) :
    (indices.foldl step state).1.nodes[j]! = state.1.nodes[j]! := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih (step state i) (fun previous k hk =>
      hstep previous k (List.mem_cons_of_mem i hk))]
    exact hstep state i (by simp)

theorem pushUp_untouched (f : Flow) (column : List Nat) (y beta : Int) (j : Nat)
    (hj : j ∉ column) : (pushUp f column y beta).nodes[j]! = f.nodes[j]! := by
  unfold pushUp
  apply fold_pair_preserves_node
  intro previous i hi
  have hne : i ≠ j := by
    intro heq
    subst i
    exact hj (List.mem_reverse.mp hi)
  dsimp only
  exact Array.getElem!_set!_ne _ _ _ _ hne

theorem collision_untouched (f : Flow) (column : List Nat) (beta : Int) (j : Nat)
    (hj : j ∉ column) :
    (resolveCollisions f column beta).nodes[j]! = f.nodes[j]! := by
  unfold resolveCollisions
  split
  · rfl
  · rw [pushDown_untouched _ column _ beta j hj,
      pushUp_untouched _ column _ beta j hj,
      pushDown_untouched _ (column.drop (column.length / 2 + 1)) _ beta j
        (fun h => hj (List.mem_of_mem_drop h)),
      pushUp_untouched _ (column.take (column.length / 2)) _ beta j
        (fun h => hj (List.mem_of_mem_take h))]

theorem collision_preserves_foreign_column_gaps (f : Flow)
    (column foreign : List Nat) (beta : Int)
    (hforeign : ∀ j ∈ foreign, j ∉ column)
    (hgaps : (foreign.map (fun i => f.nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0)) :
    (foreign.map (fun i => (resolveCollisions f column beta).nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0) := by
  have hmap : foreign.map (fun i => (resolveCollisions f column beta).nodes[i]!) =
      foreign.map (fun i => f.nodes[i]!) := by
    apply List.map_congr_left
    intro i hi
    exact collision_untouched f column beta i (hforeign i hi)
  rw [hmap]
  exact hgaps

theorem reorderLinks_adjacency_permutation (f : Flow) (column : List Nat) (j : Nat) :
    ((reorderLinks f column).nodes[j]!).incoming.Perm (f.nodes[j]!).incoming ∧
      ((reorderLinks f column).nodes[j]!).outgoing.Perm (f.nodes[j]!).outgoing := by
  unfold reorderLinks
  induction column generalizing f with
  | nil => exact ⟨List.Perm.refl _, List.Perm.refl _⟩
  | cons i rest ih =>
    simp only [List.foldl_cons]
    let next : Flow :=
      let n := f.nodes[i]!
      { f with nodes := f.nodes.set! i { n with
        outgoing := n.outgoing.mergeSort (byTarget f)
        incoming := n.incoming.mergeSort (bySource f) } }
    have hstep : (next.nodes[j]!).incoming.Perm (f.nodes[j]!).incoming ∧
        (next.nodes[j]!).outgoing.Perm (f.nodes[j]!).outgoing := by
      by_cases hij : i = j
      · subst j
        by_cases hi : i < f.nodes.size
        · dsimp only [next]
          rw [Array.getElem!_set!_self _ _ _ hi]
          exact ⟨List.mergeSort_perm _ _, List.mergeSort_perm _ _⟩
        · have he : next.nodes = f.nodes := by
            simp [next, Array.set!, Array.setIfInBounds, hi]
          rw [he]
          exact ⟨List.Perm.refl _, List.Perm.refl _⟩
      · dsimp only [next]
        rw [Array.getElem!_set!_ne _ _ _ _ hij]
        exact ⟨List.Perm.refl _, List.Perm.refl _⟩
    have hrest := ih next
    exact ⟨hrest.1.trans hstep.1, hrest.2.trans hstep.2⟩

private theorem perm_sum_eq {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp [Int.add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem reorderLinks_width_sums (f : Flow) (column : List Nat) (j : Nat) :
    (((reorderLinks f column).nodes[j]!).incoming.map
      (fun k => ((reorderLinks f column).links[k]!).width)).sum =
        ((f.nodes[j]!).incoming.map (fun k => (f.links[k]!).width)).sum ∧
    (((reorderLinks f column).nodes[j]!).outgoing.map
      (fun k => ((reorderLinks f column).links[k]!).width)).sum =
        ((f.nodes[j]!).outgoing.map (fun k => (f.links[k]!).width)).sum := by
  rw [reorderLinks_links]
  have hperm := reorderLinks_adjacency_permutation f column j
  exact ⟨perm_sum_eq (hperm.1.map (fun k => (f.links[k]!).width)),
    perm_sum_eq (hperm.2.map (fun k => (f.links[k]!).width))⟩

theorem decode_reorder_stack_link_sums_le_height (m : Model) (extent padding : Int)
    (f : Flow) (hdecode : decode m extent padding = .ok f)
    (column : List Nat) (ky : Int) (hky : 0 ≤ ky) (i : Nat)
    (hi : i ∈ column) (hindex : i < f.nodes.size)
    (hscaled : ∀ j ∈ (f.nodes[i]!).incoming,
      (f.links[j]!).width = Int.fdiv ((f.links[j]!).value * ky) 65536) :
    let out := reorderLinks (stack f column ky) column
    ((out.nodes[i]!).incoming.map (fun j => (out.links[j]!).width)).sum ≤
      (out.nodes[i]!).y1 - (out.nodes[i]!).y0 ∧
    ((out.nodes[i]!).outgoing.map (fun j => (out.links[j]!).width)).sum ≤
      (out.nodes[i]!).y1 - (out.nodes[i]!).y0 := by
  dsimp only
  simp only [(reorderLinks_width_sums (stack f column ky) column i).1,
    (reorderLinks_width_sums (stack f column ky) column i).2,
    reorderLinks_heights]
  exact ⟨decode_stack_incoming_sum_le_height m extent padding f hdecode
      column ky hky i hi hindex hscaled,
    decode_stack_outgoing_sum_le_height m extent padding f hdecode
      column ky hky i hi hindex⟩

theorem settle_untouched (f : Flow) (c : Nat) (beta : Int) (j : Nat)
    (hj : j ∉ f.columns[c]!) :
    (settle f c beta).nodes[j]! = f.nodes[j]! := by
  unfold settle
  apply collision_untouched
  intro hmem
  exact hj ((List.mergeSort_perm _ _).mem_iff.mp hmem)

theorem settle_preserves_foreign_column_gaps (f : Flow) (c : Nat)
    (foreign : List Nat) (beta : Int)
    (hforeign : ∀ j ∈ foreign, j ∉ f.columns[c]!)
    (hgaps : (foreign.map (fun i => f.nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0)) :
    (foreign.map (fun i => (settle f c beta).nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0) := by
  have hmap : foreign.map (fun i => (settle f c beta).nodes[i]!) =
      foreign.map (fun i => f.nodes[i]!) := by
    apply List.map_congr_left
    intro i hi
    exact settle_untouched f c beta i (hforeign i hi)
  rw [hmap]
  exact hgaps

theorem scene_box_ids (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) :
    ((sceneOf m f rects labels width height).layoutDump.boxes.map (·.id)) =
      m.boxes.map (·.id) := by
  simp only [sceneOf, Scene.layoutDump, List.map_map]
  have h := List.zipIdx_map_fst 0 m.boxes
  calc
    _ = (m.boxes.zipIdx.map Prod.fst).map (·.id) := by
      rw [List.map_map]; rfl
    _ = m.boxes.map (·.id) := by rw [h]

theorem scene_box_lookup (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (hids : (m.boxes.map (·.id)).Nodup) (b : Box)
    (hb : b ∈ (sceneOf m f rects labels width height).layoutDump.boxes) :
    (sceneOf m f rects labels width height).layoutDump.box? b.id = some b := by
  have findUnique : ∀ (boxes : List Box), (boxes.map (·.id)).Nodup →
      ∀ box ∈ boxes, boxes.find? (fun other => other.id == box.id) = some box := by
    intro boxes
    induction boxes with
    | nil => intro _ box hbox; simp at hbox
    | cons first rest ih =>
      intro hnodup box hbox
      have hparts := List.nodup_cons.mp
        (show (first.id :: rest.map (·.id)).Nodup from hnodup)
      rcases List.mem_cons.mp hbox with rfl | hrest
      · simp
      · have hne : first.id ≠ box.id := by
          intro heq
          exact hparts.1 (heq ▸ List.mem_map_of_mem hrest)
        have hfalse : (first.id == box.id) = false := by simpa using hne
        simp only [List.find?_cons, hfalse]
        exact ih hparts.2 box hrest
  apply findUnique _ _ b hb
  rw [scene_box_ids]
  exact hids

theorem settle_gaps_full_strength (f : Flow) (c : Nat)
    (hnodup : (f.columns[c]!).Nodup)
    (hindices : ∀ i ∈ f.columns[c]!, i < f.nodes.size)
    (hpy : 0 ≤ f.py)
    (heights : ∀ i ∈ f.columns[c]!, (f.nodes[i]!).y0 ≤ (f.nodes[i]!).y1) :
    let column := (f.columns[c]!).mergeSort (fun i j => (f.nodes[i]!).y0 ≤ (f.nodes[j]!).y0)
    (column.map (fun i => (settle f c 65536).nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0) ∧
    (column.map (fun i => (settle f c 65536).nodes[i]!)).Pairwise
      (fun a b => a.y1 ≤ b.y0) := by
  dsimp only
  let column := (f.columns[c]!).mergeSort (fun i j => (f.nodes[i]!).y0 ≤ (f.nodes[j]!).y0)
  have hperm : column.Perm (f.columns[c]!) := List.mergeSort_perm _ _
  have hnodup' : column.Nodup := hperm.nodup_iff.mpr hnodup
  have hindices' : ∀ i ∈ column, i < f.nodes.size :=
    fun i hi => hindices i (hperm.mem_iff.mp hi)
  have heights' : ∀ i ∈ column, (f.nodes[i]!).y0 ≤ (f.nodes[i]!).y1 :=
    fun i hi => heights i (hperm.mem_iff.mp hi)
  constructor
  · exact collision_gaps_full_strength { f with columns := f.columns.set! c column }
      column hnodup' hindices' hpy heights'
  · exact collision_disjoint_full_strength { f with columns := f.columns.set! c column }
      column hnodup' hindices' hpy heights'

theorem scene_box_lookup_at (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (hids : (m.boxes.map (·.id)).Nodup) (i : Nat) (source : ModelBox)
    (hsource : m.boxes[i]? = some source) :
    (sceneOf m f rects labels width height).layoutDump.box? source.id =
      some (Box.mk source.id source.role.id rects[i]! source.parent source.exclusive) := by
  apply scene_box_lookup m f rects labels width height hids
    (Box.mk source.id source.role.id rects[i]! source.parent source.exclusive)
  apply List.mem_map.mpr
  exact ⟨(source, i), List.mk_mem_zipIdx_iff_getElem?.mpr hsource, rfl⟩

theorem scene_endpoint_boundaries (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (hids : (m.boxes.map (·.id)).Nodup)
    (source target : ModelBox) (si ti : Nat)
    (hs : m.boxes[si]? = some source) (ht : m.boxes[ti]? = some target)
    (sourceOffset targetOffset : Int)
    (hsw : 0 ≤ (rects[si]!).w) (htw : 0 ≤ (rects[ti]!).w)
    (hso : 0 ≤ sourceOffset ∧ sourceOffset ≤ (rects[si]!).h)
    (hto : 0 ≤ targetOffset ∧ targetOffset ≤ (rects[ti]!).h) :
    ∃ sourceBox targetBox,
      (sceneOf m f rects labels width height).layoutDump.box? source.id = some sourceBox ∧
      (sceneOf m f rects labels width height).layoutDump.box? target.id = some targetBox ∧
      Validator.onBoundary
        ⟨(rects[si]!).x + (rects[si]!).w, (rects[si]!).y + sourceOffset⟩ sourceBox.rect ∧
      Validator.onBoundary
        ⟨(rects[ti]!).x, (rects[ti]!).y + targetOffset⟩ targetBox.rect := by
  refine ⟨_, _, scene_box_lookup_at m f rects labels width height hids si source hs,
    scene_box_lookup_at m f rects labels width height hids ti target ht, ?_, ?_⟩
  · exact boundary_port_right (rects[si]!) sourceOffset hsw hso
  · exact boundary_port_left (rects[ti]!) targetOffset htw hto

theorem reorder_stack_link_values (f : Flow) (column : List Nat) (ky : Int)
    (j : Nat) :
    ((reorderLinks (stack f column ky) column).links[j]!).value =
      (f.links[j]!).value := by
  rw [reorderLinks_links]
  exact stack_link_values f column ky j

theorem initialise_link_values (f out : Flow)
    (h : initialise f = .ok out) (j : Nat) :
    (out.links[j]!).value = (f.links[j]!).value := by
  unfold initialise at h
  cases hs : scale f with
  | error e => simp [hs, Bind.bind, Except.bind] at h
  | ok ky =>
    simp [hs] at h
    cases h
    change (f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).links[j]!.value =
      (f.links[j]!).value
    apply Array.foldl_induction
      (motive := fun _ (state : Flow) => (state.links[j]!).value = (f.links[j]!).value)
    · rfl
    · intro i state hstate
      rw [reorder_stack_link_values]
      exact hstate

theorem reorder_stack_preserves_scaled_width (f : Flow) (column : List Nat)
    (ky : Int) (j : Nat)
    (hwidth : (f.links[j]!).width = Int.fdiv ((f.links[j]!).value * ky) 65536) :
    ((reorderLinks (stack f column ky) column).links[j]!).width =
      Int.fdiv (((reorderLinks (stack f column ky) column).links[j]!).value * ky)
        65536 := by
  rw [reorderLinks_links]
  exact stack_preserves_scaled_width f column ky j hwidth

theorem initialise_preserves_scaled_width (f out : Flow) (ky : Int)
    (hscale : scale f = .ok ky) (h : initialise f = .ok out) (j : Nat)
    (hwidth : (f.links[j]!).width = Int.fdiv ((f.links[j]!).value * ky) 65536) :
    (out.links[j]!).width = Int.fdiv ((out.links[j]!).value * ky) 65536 := by
  unfold initialise at h
  simp [hscale] at h
  cases h
  change (f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).links[j]!.width =
    Int.fdiv ((f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).links[j]!.value * ky) 65536
  apply Array.foldl_induction
    (motive := fun _ (state : Flow) => (state.links[j]!).width =
      Int.fdiv ((state.links[j]!).value * ky) 65536)
  · exact hwidth
  · intro i state hstate
    exact reorder_stack_preserves_scaled_width state _ ky j hstate

theorem relax_preserves_scaled_width (count : Nat) (f : Flow) (ky : Int) (j : Nat)
    (hwidth : (f.links[j]!).width = Int.fdiv ((f.links[j]!).value * ky) 65536) :
    ((relax count f).links[j]!).width =
      Int.fdiv (((relax count f).links[j]!).value * ky) 65536 := by
  rw [relax_links]
  exact hwidth

namespace Scaling

theorem fold_preserves_scaled_width (columns : List (List Nat)) (f : Flow)
    (ky : Int) (j : Nat)
    (hwidth : (f.links[j]!).width = Int.fdiv ((f.links[j]!).value * ky) 65536) :
    let out := columns.foldl (fun state c => reorderLinks (stack state c ky) c) f
    (out.links[j]!).width = Int.fdiv ((out.links[j]!).value * ky) 65536 := by
  induction columns generalizing f with
  | nil => exact hwidth
  | cons column rest ih =>
    exact ih _ (reorder_stack_preserves_scaled_width f column ky j hwidth)

theorem fold_scales_link (columns : List (List Nat)) (f : Flow)
    (ky : Int) (source j : Nat)
    (hsource : ∃ column ∈ columns, source ∈ column)
    (hlink : j ∈ (f.nodes[source]!).outgoing) :
    let out := columns.foldl (fun state c => reorderLinks (stack state c ky) c) f
    (out.links[j]!).width = Int.fdiv ((out.links[j]!).value * ky) 65536 := by
  induction columns generalizing f with
  | nil => obtain ⟨column, hcolumn, _⟩ := hsource; simp at hcolumn
  | cons column rest ih =>
    let next := reorderLinks (stack f column ky) column
    change
      ((rest.foldl (fun state c => reorderLinks (stack state c ky) c) next).links[j]!).width =
        Int.fdiv
          (((rest.foldl (fun state c => reorderLinks (stack state c ky) c) next).links[j]!).value
            * ky) 65536
    by_cases hmember : source ∈ column
    · apply fold_preserves_scaled_width
      dsimp only [next]
      rw [reorderLinks_links, stack_link_values]
      exact stack_link_width f column ky source j hmember hlink
    · apply ih next
      · obtain ⟨visited, hvisited, hvisitedSource⟩ := hsource
        rcases List.mem_cons.mp hvisited with heq | hrest
        · subst visited
          exact False.elim (hmember hvisitedSource)
        · exact ⟨visited, hrest, hvisitedSource⟩
      · have hperm := (reorderLinks_adjacency_permutation
          (stack f column ky) column source).2
        apply hperm.mem_iff.mpr
        rw [stack_node_outgoing]
        exact hlink

theorem initialise_scales_link (f out : Flow) (ky : Int) (source j : Nat)
    (hscale : scale f = .ok ky) (h : initialise f = .ok out)
    (hsource : ∃ column ∈ f.columns.toList, source ∈ column)
    (hlink : j ∈ (f.nodes[source]!).outgoing) :
    (out.links[j]!).width = Int.fdiv ((out.links[j]!).value * ky) 65536 := by
  unfold initialise at h
  simp [hscale] at h
  cases h
  change (f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).links[j]!.width =
    Int.fdiv ((f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).links[j]!.value * ky) 65536
  simpa only [← Array.foldl_toList] using
    fold_scales_link f.columns.toList f ky source j hsource hlink

end Scaling

theorem place_source_column (f placed : Flow) (alignment : String)
    (hplace : place f alignment = .ok placed) (source : Nat)
    (hsource : source < placed.nodes.size) :
    ∃ column ∈ placed.columns.toList, source ∈ column := by
  let c := (placed.nodes[source]!).layer
  have hc : c < placed.columns.size :=
    place_layers_bounded f placed alignment hplace source hsource
  refine ⟨placed.columns[c]!, ?_, ?_⟩
  · rw [getElem!_pos placed.columns c hc]
    exact Array.getElem_mem_toList hc
  · exact ((place_column_partition f placed alignment hplace c hc).2 source).mpr
      ⟨hsource, rfl⟩

theorem placed_initialise_relax_scales_link (f placed initial : Flow)
    (alignment : String) (ky : Int) (count source j : Nat)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hsource : source < placed.nodes.size)
    (hlink : j ∈ (placed.nodes[source]!).outgoing) :
    ((relax count initial).links[j]!).width =
      Int.fdiv (((relax count initial).links[j]!).value * ky) 65536 := by
  apply relax_preserves_scaled_width
  exact Scaling.initialise_scales_link (withPadding placed) initial ky source j
    hscale hinitial (place_source_column f placed alignment hplace source hsource) hlink

theorem relax_six_final_pass (f : Flow) :
    let before := (List.range 5).foldl (fun state i => iteration 6 i state) f
    let alpha := Int.fdiv (65536 * (99 : Int)^5) ((100 : Int)^5)
    relax 6 f = pass (pass before alpha 65536 true) alpha 65536 false := by
  have h := relax_succ 5 f
  simp only [iteration, Nat.reduceAdd] at h
  exact h

theorem stack_preserves_scaled_height (f : Flow) (column : List Nat) (ky : Int)
    (i : Nat)
    (hheight : (f.nodes[i]!).y1 - (f.nodes[i]!).y0 =
      Int.fdiv ((f.nodes[i]!).value * ky) 65536) :
    ((stack f column ky).nodes[i]!).y1 - ((stack f column ky).nodes[i]!).y0 =
      Int.fdiv (((stack f column ky).nodes[i]!).value * ky) 65536 := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant
    (P := fun out : Flow => (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
      Int.fdiv ((out.nodes[i]!).value * ky) 65536)
  · apply id_forIn_invariant
      (P := fun out : Flow × Int => (out.1.nodes[i]!).y1 - (out.1.nodes[i]!).y0 =
        Int.fdiv ((out.1.nodes[i]!).value * ky) 65536)
    · exact hheight
    · intro j state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant
        (P := fun out : Flow => (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
          Int.fdiv ((out.nodes[i]!).value * ky) 65536)
      · exact refresh_scaled_height _ _ _ ky i (fun _ => hstate)
      · intro j out hout
        exact hout
  · intro pair out hout
    dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
    exact translate_scaled_height _ _ _ ky i hout

theorem reorderLinks_node_values (f : Flow) (column : List Nat) (i : Nat) :
    ((reorderLinks f column).nodes[i]!).value = (f.nodes[i]!).value := by
  unfold reorderLinks
  induction column generalizing f with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    apply set_preserves_node_values f.nodes j
      { f.nodes[j]! with
        incoming := (f.nodes[j]!).incoming.mergeSort (bySource f)
        outgoing := (f.nodes[j]!).outgoing.mergeSort (byTarget f) }
    rfl

namespace Scaling

theorem reorder_stack_preserves_scaled_height (f : Flow) (column : List Nat)
    (ky : Int) (i : Nat)
    (hheight : (f.nodes[i]!).y1 - (f.nodes[i]!).y0 =
      Int.fdiv ((f.nodes[i]!).value * ky) 65536) :
    let out := reorderLinks (stack f column ky) column
    (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
      Int.fdiv ((out.nodes[i]!).value * ky) 65536 := by
  dsimp only
  rw [reorderLinks_heights, reorderLinks_node_values]
  exact stack_preserves_scaled_height f column ky i hheight

theorem fold_preserves_scaled_height (columns : List (List Nat)) (f : Flow)
    (ky : Int) (i : Nat)
    (hheight : (f.nodes[i]!).y1 - (f.nodes[i]!).y0 =
      Int.fdiv ((f.nodes[i]!).value * ky) 65536) :
    let out := columns.foldl (fun state c => reorderLinks (stack state c ky) c) f
    (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
      Int.fdiv ((out.nodes[i]!).value * ky) 65536 := by
  induction columns generalizing f with
  | nil => exact hheight
  | cons column rest ih =>
    exact ih _ (reorder_stack_preserves_scaled_height f column ky i hheight)

theorem fold_scales_node (columns : List (List Nat)) (f : Flow)
    (ky : Int) (i : Nat)
    (hsource : ∃ column ∈ columns, i ∈ column) :
    let out := columns.foldl (fun state c => reorderLinks (stack state c ky) c) f
    (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
      Int.fdiv ((out.nodes[i]!).value * ky) 65536 := by
  induction columns generalizing f with
  | nil => obtain ⟨column, hcolumn, _⟩ := hsource; simp at hcolumn
  | cons column rest ih =>
    by_cases hi : i ∈ column
    · have hstep : ((reorderLinks (stack f column ky) column).nodes[i]!).y1 -
          ((reorderLinks (stack f column ky) column).nodes[i]!).y0 =
          Int.fdiv (((reorderLinks (stack f column ky) column).nodes[i]!).value * ky)
            65536 := by
        rw [reorderLinks_heights, reorderLinks_node_values, stack_node_values]
        exact stack_node_height f column ky i hi
      exact fold_preserves_scaled_height rest _ ky i hstep
    · apply ih
      obtain ⟨visited, hvisited, hmember⟩ := hsource
      rcases List.mem_cons.mp hvisited with heq | hrest
      · subst visited
        exact False.elim (hi hmember)
      · exact ⟨visited, hrest, hmember⟩

theorem initialise_scales_node (f out : Flow) (ky : Int) (i : Nat)
    (hscale : scale f = .ok ky) (h : initialise f = .ok out)
    (hsource : ∃ column ∈ f.columns.toList, i ∈ column) :
    (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
      Int.fdiv ((out.nodes[i]!).value * ky) 65536 := by
  unfold initialise at h
  simp [hscale] at h
  cases h
  change (f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).nodes[i]!.y1 -
      (f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).nodes[i]!.y0 =
    Int.fdiv ((f.columns.foldl (fun state c => reorderLinks (stack state c ky) c) f).nodes[i]!.value * ky) 65536
  simpa only [← Array.foldl_toList] using
    fold_scales_node f.columns.toList f ky i hsource

end Scaling

theorem placed_initialise_final_node_height (f placed initial : Flow)
    (alignment : String) (ky : Int) (count i : Nat)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hi : i < placed.nodes.size) :
    ((anchorLinks (countedRelax count initial).1).nodes[i]!).y1 -
      ((anchorLinks (countedRelax count initial).1).nodes[i]!).y0 =
        Int.fdiv ((initial.nodes[i]!).value * ky) 65536 := by
  rw [final_heights]
  exact Scaling.initialise_scales_node (withPadding placed) initial ky i hscale hinitial
    (place_source_column f placed alignment hplace i hi)

theorem placed_initialise_final_link_width (f placed initial : Flow)
    (alignment : String) (ky : Int) (count source j : Nat)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hsource : source < placed.nodes.size)
    (hlink : j ∈ (placed.nodes[source]!).outgoing) :
    ((anchorLinks (countedRelax count initial).1).links[j]!).width =
      Int.fdiv ((initial.links[j]!).value * ky) 65536 := by
  have hd := congrArg (fun data : Nat × Nat × Int × Int => data.2.2.2)
    (final_linkData initial count j)
  change ((anchorLinks (countedRelax count initial).1).links[j]!).width =
    (initial.links[j]!).width at hd
  rw [hd]
  exact Scaling.initialise_scales_link (withPadding placed) initial ky source j
    hscale hinitial (place_source_column f placed alignment hplace source hsource) hlink

theorem run_common_scale (f out : Flow) (alignment : String) (count : Nat)
    (h : run f alignment count = .ok out) :
    ∃ (placed initial : Flow) (ky : Int),
      place f alignment = .ok placed ∧
      scale (withPadding placed) = .ok ky ∧
      initialise (withPadding placed) = .ok initial ∧
      0 ≤ ky ∧
      out = anchorLinks (countedRelax count initial).1 ∧
      (∀ i : Nat, i < placed.nodes.size →
        (out.nodes[i]!).y1 - (out.nodes[i]!).y0 =
          Int.fdiv ((initial.nodes[i]!).value * ky) 65536) ∧
      (∀ source j : Nat, source < placed.nodes.size →
        j ∈ (placed.nodes[source]!).outgoing →
        (out.links[j]!).width = Int.fdiv ((initial.links[j]!).value * ky) 65536) := by
  unfold run at h
  cases hp : place f alignment with
  | error e => simp [hp, Bind.bind, Except.bind] at h
  | ok placed =>
    cases hi : initialise (withPadding placed) with
    | error e => simp [hp, hi, Bind.bind, Except.bind] at h
    | ok initial =>
      have hs : ∃ ky : Int, scale (withPadding placed) = .ok ky := by
        have hi' := hi
        unfold initialise at hi'
        cases hscale : scale (withPadding placed) with
        | error e => simp [hscale, Bind.bind, Except.bind] at hi'
        | ok ky => exact ⟨ky, rfl⟩
      obtain ⟨ky, hscale⟩ := hs
      simp only [hp, hi, Bind.bind, Except.bind] at h
      split at h
      · contradiction
      · cases h
        refine ⟨placed, initial, ky, rfl, hscale, hi,
          scale_nonnegative (withPadding placed) ky hscale, rfl, ?_, ?_⟩
        · intro i hi'
          exact placed_initialise_final_node_height f placed initial alignment ky
            count i hp hscale hi hi'
        · intro source j hsource hlink
          exact placed_initialise_final_link_width f placed initial alignment ky
            count source j hp hscale hi hsource hlink

theorem nodeRects_height (f : Flow) (width nodeWidth : Int) (i : Nat)
    (hi : i < f.nodes.size) :
    ((nodeRects f width nodeWidth)[i]!).h = (f.nodes[i]!).y1 - (f.nodes[i]!).y0 := by
  have hr : i < (nodeRects f width nodeWidth).size := by
    simpa only [nodeRects, Array.size_map] using hi
  rw [getElem!_pos _ i hr, getElem!_pos f.nodes i hi]
  simp only [nodeRects, Array.getElem_map]

theorem normalize_linkData (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) (j : Nat)
    (hj : j < f.links.size) :
    linkData (((normalize f rects labels width height).1.links)[j]!) =
      linkData (f.links[j]!) := by
  have hout : j < (normalize f rects labels width height).1.links.size := by
    simpa only [normalize_preserves_link_count] using hj
  rw [getElem!_pos _ j hout, getElem!_pos f.links j hj]
  simp only [normalize, Array.getElem_map, linkData]

theorem run_nodeRects_common_scale (f out : Flow) (alignment : String)
    (count : Nat) (width nodeWidth : Int)
    (h : run f alignment count = .ok out) :
    ∃ (initial : Flow) (ky : Int), 0 ≤ ky ∧
      ∀ i : Nat, i < out.nodes.size →
        ((nodeRects out width nodeWidth)[i]!).h =
          Int.fdiv ((initial.nodes[i]!).value * ky) 65536 := by
  obtain ⟨placed, initial, ky, _, _, hi, hky, hout, hnodes, _⟩ :=
    run_common_scale f out alignment count h
  have hsize : out.nodes.size = placed.nodes.size := by
    rw [hout, anchorLinks_nodes_size, countedRelax_nodes_size,
      initialise_nodes_size (withPadding placed) initial hi]
    rfl
  refine ⟨initial, ky, hky, ?_⟩
  intro i hi'
  rw [nodeRects_height out width nodeWidth i hi']
  exact hnodes i (by simpa only [hsize] using hi')

theorem initialise_node_values (f out : Flow)
    (h : initialise f = .ok out) (i : Nat) :
    (out.nodes[i]!).value = (f.nodes[i]!).value := by
  unfold initialise at h
  cases hs : scale f with
  | error e => simp [hs, Bind.bind, Except.bind] at h
  | ok ky =>
    simp [hs] at h
    cases h
    change (f.columns.foldl
      (fun state c => reorderLinks (stack state c ky) c) f).nodes[i]!.value =
        (f.nodes[i]!).value
    apply Array.foldl_induction
      (motive := fun _ (state : Flow) =>
        (state.nodes[i]!).value = (f.nodes[i]!).value)
    · rfl
    · intro j state hstate
      rw [reorderLinks_node_values, stack_node_values]
      exact hstate

theorem placed_initialise_final_outgoing_width_sum (f placed initial : Flow)
    (alignment : String) (ky : Int) (count source : Nat)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hsource : source < placed.nodes.size) :
    ((placed.nodes[source]!).outgoing.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum =
        scaledSum ((placed.nodes[source]!).outgoing.map
          (fun j => (initial.links[j]!).value)) ky := by
  simp only [scaledSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  exact placed_initialise_final_link_width f placed initial alignment ky count source j
    hplace hscale hinitial hsource hj

theorem placed_initialise_final_outgoing_capacity (f placed initial : Flow)
    (alignment : String) (ky : Int) (count source : Nat)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hsource : source < placed.nodes.size)
    (hvalue : ((placed.nodes[source]!).outgoing.map
      (fun j => (initial.links[j]!).value)).sum ≤ (initial.nodes[source]!).value) :
    ((placed.nodes[source]!).outgoing.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum ≤
        ((anchorLinks (countedRelax count initial).1).nodes[source]!).y1 -
          ((anchorLinks (countedRelax count initial).1).nodes[source]!).y0 := by
  rw [placed_initialise_final_outgoing_width_sum f placed initial alignment ky count
    source hplace hscale hinitial hsource,
    placed_initialise_final_node_height f placed initial alignment ky count source
      hplace hscale hinitial hsource]
  exact linkWidths_le_nodeHeight _ _ ky hvalue
    (scale_nonnegative (withPadding placed) ky hscale)

theorem place_node_payload (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) (i : Nat) (hi : i < f.nodes.size) :
    (out.nodes[i]!).value = (f.nodes[i]!).value ∧
      (out.nodes[i]!).outgoing = (f.nodes[i]!).outgoing ∧ out.links = f.links := by
  unfold place at h
  cases hd : levels f false with
  | error e => simp [hd, Bind.bind, Except.bind] at h
  | ok depths =>
    cases hh : levels f true with
    | error e => simp [hd, hh, Bind.bind, Except.bind] at h
    | ok heights =>
      simp [hd, hh] at h
      cases h
      constructor
      · rw [getElem!_pos _ i (by simpa only [Array.size_mapIdx] using hi),
          Array.getElem_mapIdx, getElem!_pos f.nodes i hi]
      · constructor
        · rw [getElem!_pos _ i (by simpa only [Array.size_mapIdx] using hi),
            Array.getElem_mapIdx, getElem!_pos f.nodes i hi]
        · rfl
theorem decode_placed_final_outgoing_capacity (m : Model) (extent padding : Int)
    (f placed initial : Flow) (alignment : String) (ky : Int) (count source : Nat)
    (hdecode : decode m extent padding = .ok f)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hsource : source < f.nodes.size) :
    ((placed.nodes[source]!).outgoing.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum ≤
        ((anchorLinks (countedRelax count initial).1).nodes[source]!).y1 -
          ((anchorLinks (countedRelax count initial).1).nodes[source]!).y0 := by
  apply placed_initialise_final_outgoing_capacity f placed initial alignment ky
    count source hplace hscale hinitial
    (by simpa only [place_nodes_size f placed alignment hplace] using hsource)
  have hp := place_node_payload f placed alignment hplace source hsource
  have hv := initialise_node_values (withPadding placed) initial hinitial source
  change (initial.nodes[source]!).value = (placed.nodes[source]!).value at hv
  rw [hv, hp.1, hp.2.1]
  have hsum :
      ((f.nodes[source]!).outgoing.map (fun j => (initial.links[j]!).value)).sum =
        ((f.nodes[source]!).outgoing.map (fun j => (f.links[j]!).value)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    have hj := initialise_link_values (withPadding placed) initial hinitial j
    change (initial.links[j]!).value = (placed.links[j]!).value at hj
    simpa only [hp.2.2] using hj
  rw [hsum]
  have hmem : f.nodes[source]! ∈ f.nodes.toList := by
    rw [getElem!_pos f.nodes source hsource]
    exact Array.getElem_mem_toList hsource
  rw [decode_node_values m extent padding f hdecode _ hmem]
  exact Int.le_max_right _ _

theorem fold_preserves_nodes (step : Flow → Nat → Flow)
    (hs : ∀ (f : Flow) (i : Nat), (step f i).nodes = f.nodes)
    (indices : List Nat) (f : Flow) :
    (indices.foldl step f).nodes = f.nodes := by
  induction indices generalizing f with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem fold_pair_preserves_nodes (step : Flow × Int → Nat → Flow × Int)
    (hs : ∀ (state : Flow × Int) (i : Nat), (step state i).1.nodes = state.1.nodes)
    (indices : List Nat) (state : Flow × Int) :
    (indices.foldl step state).1.nodes = state.1.nodes := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem anchorLinks_nodes (f : Flow) : (anchorLinks f).nodes = f.nodes := by
  unfold anchorLinks
  apply fold_preserves_nodes
  intro state i
  rw [fold_pair_preserves_nodes]
  · apply fold_pair_preserves_nodes
    intro state j
    rfl
  · intro state j
    rfl

theorem anchorLinks_column_gaps (f : Flow) (column : List Nat) :
    (column.map (fun i => (anchorLinks f).nodes[i]!)).Pairwise
        (fun a b => a.y1 + f.py ≤ b.y0) ↔
      (column.map (fun i => f.nodes[i]!)).Pairwise
        (fun a b => a.y1 + f.py ≤ b.y0) := by
  rw [anchorLinks_nodes]

theorem anchorLinks_width_sums (f : Flow) (i : Nat) :
    (((anchorLinks f).nodes[i]!).incoming.map
      (fun j => ((anchorLinks f).links[j]!).width)).sum =
        ((f.nodes[i]!).incoming.map (fun j => (f.links[j]!).width)).sum ∧
    (((anchorLinks f).nodes[i]!).outgoing.map
      (fun j => ((anchorLinks f).links[j]!).width)).sum =
        ((f.nodes[i]!).outgoing.map (fun j => (f.links[j]!).width)).sum := by
  have hw : ∀ j : Nat, ((anchorLinks f).links[j]!).width = (f.links[j]!).width := by
    intro j
    exact congrArg (fun data : Nat × Nat × Int × Int => data.2.2.2)
      (anchorLinks_linkData f j)
  rw [anchorLinks_nodes]
  constructor
  · apply congrArg List.sum
    exact List.map_congr_left (fun j _ => hw j)
  · apply congrArg List.sum
    exact List.map_congr_left (fun j _ => hw j)

theorem anchorLinks_preserves_capacity (f : Flow) (i : Nat)
    (hincoming : ((f.nodes[i]!).incoming.map
      (fun j => (f.links[j]!).width)).sum ≤ (f.nodes[i]!).y1 - (f.nodes[i]!).y0)
    (houtgoing : ((f.nodes[i]!).outgoing.map
      (fun j => (f.links[j]!).width)).sum ≤ (f.nodes[i]!).y1 - (f.nodes[i]!).y0) :
    (((anchorLinks f).nodes[i]!).incoming.map
      (fun j => ((anchorLinks f).links[j]!).width)).sum ≤
        ((anchorLinks f).nodes[i]!).y1 - ((anchorLinks f).nodes[i]!).y0 ∧
    (((anchorLinks f).nodes[i]!).outgoing.map
      (fun j => ((anchorLinks f).links[j]!).width)).sum ≤
        ((anchorLinks f).nodes[i]!).y1 - ((anchorLinks f).nodes[i]!).y0 := by
  rw [(anchorLinks_width_sums f i).1, (anchorLinks_width_sums f i).2,
    anchorLinks_heights]
  exact ⟨hincoming, houtgoing⟩

theorem anchored_settle_gaps_full_strength (f : Flow) (c : Nat)
    (hnodup : (f.columns[c]!).Nodup)
    (hindices : ∀ i ∈ f.columns[c]!, i < f.nodes.size)
    (hpy : 0 ≤ f.py)
    (heights : ∀ i ∈ f.columns[c]!, (f.nodes[i]!).y0 ≤ (f.nodes[i]!).y1) :
    let column := (f.columns[c]!).mergeSort (fun i j => (f.nodes[i]!).y0 ≤ (f.nodes[j]!).y0)
    (column.map (fun i => (anchorLinks (settle f c 65536)).nodes[i]!)).Pairwise
      (fun a b => a.y1 + f.py ≤ b.y0) ∧
    (column.map (fun i => (anchorLinks (settle f c 65536)).nodes[i]!)).Pairwise
      (fun a b => a.y1 ≤ b.y0) := by
  dsimp only
  rw [anchorLinks_nodes]
  exact settle_gaps_full_strength f c hnodup hindices hpy heights

theorem final_outgoing_capacity_of_permutation (m : Model) (extent padding : Int)
    (f placed initial : Flow) (alignment : String) (ky : Int) (count source : Nat)
    (hdecode : decode m extent padding = .ok f)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hsource : source < f.nodes.size)
    (hperm : ((anchorLinks (countedRelax count initial).1).nodes[source]!).outgoing.Perm
      (placed.nodes[source]!).outgoing) :
    (((anchorLinks (countedRelax count initial).1).nodes[source]!).outgoing.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum ≤
        ((anchorLinks (countedRelax count initial).1).nodes[source]!).y1 -
          ((anchorLinks (countedRelax count initial).1).nodes[source]!).y0 := by
  rw [perm_sum_eq (hperm.map
    (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width))]
  exact decode_placed_final_outgoing_capacity m extent padding f placed initial
    alignment ky count source hdecode hplace hscale hinitial hsource

theorem final_incoming_capacity_of_common_scale (f : Flow) (count target : Nat)
    (ky : Int) (hky : 0 ≤ ky)
    (hwidth : ∀ j ∈ ((anchorLinks (countedRelax count f).1).nodes[target]!).incoming,
      ((anchorLinks (countedRelax count f).1).links[j]!).width =
        Int.fdiv (((anchorLinks (countedRelax count f).1).links[j]!).value * ky) 65536)
    (hheight : ((anchorLinks (countedRelax count f).1).nodes[target]!).y1 -
      ((anchorLinks (countedRelax count f).1).nodes[target]!).y0 =
        Int.fdiv ((f.nodes[target]!).value * ky) 65536)
    (hvalue : (((anchorLinks (countedRelax count f).1).nodes[target]!).incoming.map
      (fun j => ((anchorLinks (countedRelax count f).1).links[j]!).value)).sum ≤
        (f.nodes[target]!).value) :
    (((anchorLinks (countedRelax count f).1).nodes[target]!).incoming.map
      (fun j => ((anchorLinks (countedRelax count f).1).links[j]!).width)).sum ≤
        ((anchorLinks (countedRelax count f).1).nodes[target]!).y1 -
          ((anchorLinks (countedRelax count f).1).nodes[target]!).y0 := by
  rw [hheight]
  have hs :
      (((anchorLinks (countedRelax count f).1).nodes[target]!).incoming.map
        (fun j => ((anchorLinks (countedRelax count f).1).links[j]!).width)).sum =
      scaledSum (((anchorLinks (countedRelax count f).1).nodes[target]!).incoming.map
        (fun j => ((anchorLinks (countedRelax count f).1).links[j]!).value)) ky := by
    simp only [scaledSum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    exact hwidth
  rw [hs]
  exact linkWidths_le_nodeHeight _ _ ky hvalue hky

theorem place_incoming (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) (i : Nat) (hi : i < f.nodes.size) :
    (out.nodes[i]!).incoming = (f.nodes[i]!).incoming := by
  unfold place at h
  cases hd : levels f false with
  | error e => simp [hd, Bind.bind, Except.bind] at h
  | ok depths =>
    cases hh : levels f true with
    | error e => simp [hd, hh, Bind.bind, Except.bind] at h
    | ok heights =>
      simp [hd, hh] at h
      cases h
      rw [getElem!_pos _ i (by simpa only [Array.size_mapIdx] using hi),
        Array.getElem_mapIdx, getElem!_pos f.nodes i hi]

theorem decode_incoming_value_bound (m : Model) (extent padding : Int)
    (f : Flow) (hdecode : decode m extent padding = .ok f)
    (i : Nat) (hi : i < f.nodes.size) :
    ((f.nodes[i]!).incoming.map (fun j => (f.links[j]!).value)).sum ≤
      (f.nodes[i]!).value := by
  have hmem : f.nodes[i]! ∈ f.nodes.toList := by
    rw [getElem!_pos f.nodes i hi]
    exact Array.getElem_mem_toList hi
  rw [decode_node_values m extent padding f hdecode _ hmem]
  exact Int.le_max_left _ _

end Elegant.Chart.Sankey
