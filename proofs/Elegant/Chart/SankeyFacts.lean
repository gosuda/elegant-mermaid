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

theorem sankey_nodeWidth_nonneg : 0 ≤ LayoutConst.sankey_node_width.get .vector := by decide

theorem place_preserves_incoming (f out : Flow) (alignment : String)
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

theorem place_outgoing_perm (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) (i : Nat) :
    ((out.nodes[i]!).outgoing).Perm ((f.nodes[i]!).outgoing) := by
  by_cases hi : i < f.nodes.size
  · have he := (place_node_payload f out alignment h i hi).2.1
    rw [he]
  · rw [getElem!_neg out.nodes i (by simpa only [place_nodes_size f out alignment h] using hi),
      getElem!_neg f.nodes i hi]

theorem place_incoming_perm (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) (i : Nat) :
    ((out.nodes[i]!).incoming).Perm ((f.nodes[i]!).incoming) := by
  by_cases hi : i < f.nodes.size
  · have he := place_preserves_incoming f out alignment h i hi
    rw [he]
  · rw [getElem!_neg out.nodes i (by simpa only [place_nodes_size f out alignment h] using hi),
      getElem!_neg f.nodes i hi]

theorem set_width_preserves_source (links : Array Link) (j : Nat) (width : Int)
    (i : Nat) :
    ((links.set! j { links[j]! with width })[i]!).source = (links[i]!).source := by
  by_cases hji : j = i
  · subst i
    by_cases hj : j < links.size
    · rw [Array.getElem!_set!_self _ _ _ hj]
    · have he : links.set! j ({ links[j]! with width } : Link) = links := by
        simp [Array.set!, Array.setIfInBounds, hj]
      rw [he]
  · rw [Array.getElem!_set!_ne _ _ _ _ hji]

theorem set_width_preserves_target (links : Array Link) (j : Nat) (width : Int)
    (i : Nat) :
    ((links.set! j { links[j]! with width })[i]!).target = (links[i]!).target := by
  by_cases hji : j = i
  · subst i
    by_cases hj : j < links.size
    · rw [Array.getElem!_set!_self _ _ _ hj]
    · have he : links.set! j ({ links[j]! with width } : Link) = links := by
        simp [Array.set!, Array.setIfInBounds, hj]
      rw [he]
  · rw [Array.getElem!_set!_ne _ _ _ _ hji]

theorem stack_links_source (f : Flow) (column : List Nat) (ky : Int) (j : Nat) :
    ((stack f column ky).links[j]!).source = (f.links[j]!).source := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant
    (P := fun out : Flow => (out.links[j]!).source = (f.links[j]!).source)
  · apply id_forIn_invariant
      (P := fun state : Flow × Int => (state.1.links[j]!).source = (f.links[j]!).source)
    · rfl
    · intro k state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant
        (P := fun out : Flow => (out.links[j]!).source = (f.links[j]!).source)
      · exact hstate
      · intro k out hout
        dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
        have hstep : ((out.links.set! k
            { out.links[k]! with width := Int.fdiv ((out.links[k]!).value * ky) 65536 })[j]!).source
          = (out.links[j]!).source :=
          set_width_preserves_source out.links k _ j
        rw [hstep]
        exact hout
  · intro pair out hout
    exact hout

theorem stack_links_target (f : Flow) (column : List Nat) (ky : Int) (j : Nat) :
    ((stack f column ky).links[j]!).target = (f.links[j]!).target := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant
    (P := fun out : Flow => (out.links[j]!).target = (f.links[j]!).target)
  · apply id_forIn_invariant
      (P := fun state : Flow × Int => (state.1.links[j]!).target = (f.links[j]!).target)
    · rfl
    · intro k state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant
        (P := fun out : Flow => (out.links[j]!).target = (f.links[j]!).target)
      · exact hstate
      · intro k out hout
        dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
        have hstep : ((out.links.set! k
            { out.links[k]! with width := Int.fdiv ((out.links[k]!).value * ky) 65536 })[j]!).target
          = (out.links[j]!).target :=
          set_width_preserves_target out.links k _ j
        rw [hstep]
        exact hout
  · intro pair out hout
    exact hout
theorem place_incidence (f placed : Flow) (alignment : String)
    (hplace : place f alignment = .ok placed)
    (hadj : ∀ k, k < f.nodes.size →
      (∀ j, j ∈ (f.nodes[k]!).incoming ↔ j < f.links.size ∧ (f.links[j]!).target = k) ∧
        (∀ j, j ∈ (f.nodes[k]!).outgoing ↔ j < f.links.size ∧ (f.links[j]!).source = k)) :
    ∀ k, k < placed.nodes.size →
      (∀ j, j ∈ (placed.nodes[k]!).incoming ↔
        j < placed.links.size ∧ (placed.links[j]!).target = k) ∧
        (∀ j, j ∈ (placed.nodes[k]!).outgoing ↔
          j < placed.links.size ∧ (placed.links[j]!).source = k) := by
  intro k hk
  have hsize : placed.nodes.size = f.nodes.size := place_nodes_size f placed alignment hplace
  have hlinks : placed.links = f.links := by
    have hp := hplace
    unfold place at hp
    cases hd : levels f false with
    | error e => simp [hd, Bind.bind, Except.bind] at hp
    | ok depths =>
      cases hh : levels f true with
      | error e => simp [hd, hh, Bind.bind, Except.bind] at hp
      | ok heights =>
        simp [hd, hh] at hp
        cases hp
        rfl
  have hkf : k < f.nodes.size := by omega
  obtain ⟨hinc, hout⟩ := hadj k hkf
  have hincEq : (placed.nodes[k]!).incoming = (f.nodes[k]!).incoming :=
    place_preserves_incoming f placed alignment hplace k hkf
  have houtEq : (placed.nodes[k]!).outgoing = (f.nodes[k]!).outgoing := by
    have hp := place_node_payload f placed alignment hplace k hkf
    exact hp.2.1
  constructor
  · intro j
    rw [hincEq, hlinks]
    exact hinc j
  · intro j
    rw [houtEq, hlinks]
    exact hout j

theorem stack_incidence (f : Flow) (column : List Nat) (ky : Int)
    (hadj : ∀ k, k < f.nodes.size →
      (∀ j, j ∈ (f.nodes[k]!).incoming ↔ j < f.links.size ∧ (f.links[j]!).target = k) ∧
        (∀ j, j ∈ (f.nodes[k]!).outgoing ↔ j < f.links.size ∧ (f.links[j]!).source = k)) :
    ∀ k, k < (stack f column ky).nodes.size →
      (∀ j, j ∈ ((stack f column ky).nodes[k]!).incoming ↔
        j < (stack f column ky).links.size ∧ (((stack f column ky).links[j]!).target = k)) ∧
      (∀ j, j ∈ ((stack f column ky).nodes[k]!).outgoing ↔
        j < (stack f column ky).links.size ∧ (((stack f column ky).links[j]!).source = k)) := by
  have hnodes : (stack f column ky).nodes.size = f.nodes.size := stack_nodes_size f column ky
  have hlinksSize : (stack f column ky).links.size = f.links.size := by
    unfold stack
    dsimp only [Id.run, Bind.bind, Id.instMonad]
    apply id_forIn_invariant (P := fun out : Flow => out.links.size = f.links.size)
    · apply id_forIn_invariant (P := fun state : Flow × Int => state.1.links.size = f.links.size)
      · rfl
      · intro k state hstate
        dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
        apply id_forIn_invariant (P := fun out : Flow => out.links.size = f.links.size)
        · exact hstate
        · intro k out hout
          dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
          simpa only [Array.size_set!] using hout
    · intro pair out hout
      exact hout
  intro k hk
  have hkf : k < f.nodes.size := by omega
  obtain ⟨hinc, hout⟩ := hadj k hkf
  have hincEq : ((stack f column ky).nodes[k]!).incoming = (f.nodes[k]!).incoming :=
    stack_node_incoming f column ky k
  have houtEq : ((stack f column ky).nodes[k]!).outgoing = (f.nodes[k]!).outgoing :=
    stack_node_outgoing f column ky k
  constructor
  · intro j
    rw [hincEq, hlinksSize, stack_links_target f column ky j]
    exact hinc j
  · intro j
    rw [houtEq, hlinksSize, stack_links_source f column ky j]
    exact hout j

/-- Total width of the links before the first occurrence of `j`. -/
def widthsBefore (f : Flow) : List Nat → Nat → Int
  | [], _ => 0
  | i :: rest, j => if i = j then 0 else (f.links[i]!).width + widthsBefore f rest j

theorem widthsBefore_nil (f : Flow) (j : Nat) : widthsBefore f [] j = 0 := rfl

theorem widthsBefore_cons (f : Flow) (i : Nat) (rest : List Nat) (j : Nat) :
    widthsBefore f (i :: rest) j =
      if i = j then 0 else (f.links[i]!).width + widthsBefore f rest j := rfl

theorem widthsBefore_nonneg (f : Flow) (l : List Nat) (j : Nat)
    (hw : ∀ i ∈ l, 0 ≤ (f.links[i]!).width) : 0 ≤ widthsBefore f l j := by
  induction l with
  | nil => exact Int.le_refl 0
  | cons i rest ih =>
    have hi := hw i (List.mem_cons_self)
    have hr := ih (fun k hk => hw k (List.mem_cons_of_mem i hk))
    rw [widthsBefore_cons]
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      exact Int.le_refl 0
    · rw [ite_eq_right hij]
      omega

theorem widthsBefore_add_le_sum (f : Flow) (l : List Nat) (j : Nat)
    (hj : j ∈ l) (hw : ∀ i ∈ l, 0 ≤ (f.links[i]!).width) :
    widthsBefore f l j + (f.links[j]!).width ≤
      (l.map (fun i => (f.links[i]!).width)).sum := by
  induction l with
  | nil => simp at hj
  | cons i rest ih =>
    have hwr : ∀ k ∈ rest, 0 ≤ (f.links[k]!).width :=
      fun k hk => hw k (List.mem_cons_of_mem i hk)
    rw [widthsBefore_cons, List.map_cons, List.sum_cons]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have hrest : 0 ≤ (rest.map (fun i => (f.links[i]!).width)).sum :=
        nonnegative_value_sum _ (fun v hv => by
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
          exact hwr k hk)
      have hi := hw i (List.mem_cons_self)
      omega
    · rw [ite_eq_right hij]
      have hjrest : j ∈ rest := by
        rcases List.mem_cons.mp hj with heq | hmem
        · exact absurd heq.symm hij
        · exact hmem
      have hih := ih hjrest hwr
      omega

theorem widthsBefore_congr (f g : Flow) (l : List Nat) (j : Nat)
    (h : ∀ k ∈ l, (g.links[k]!).width = (f.links[k]!).width) :
    widthsBefore g l j = widthsBefore f l j := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
    have hi := h i (List.mem_cons_self)
    have hr : ∀ k ∈ rest, (g.links[k]!).width = (f.links[k]!).width :=
      fun k hk => h k (List.mem_cons_of_mem i hk)
    rw [widthsBefore_cons, widthsBefore_cons, hi]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij]
    · rw [ite_eq_right hij, ite_eq_right hij, ih hr]


/-- The outgoing anchor step of `anchorLinks`, factored for fold reasoning. -/
def anchorStepOut (s : Flow × Int) (i : Nat) : Flow × Int :=
  let li := s.1.links[i]!
  ({ s.1 with links := s.1.links.set! i { li with y0 := s.2 + Int.fdiv li.width 2 } },
    s.2 + li.width)

/-- The incoming anchor step of `anchorLinks`, factored for fold reasoning. -/
def anchorStepIn (s : Flow × Int) (i : Nat) : Flow × Int :=
  let li := s.1.links[i]!
  ({ s.1 with links := s.1.links.set! i { li with y1 := s.2 + Int.fdiv li.width 2 } },
    s.2 + li.width)

theorem anchorStepOut_fst (s : Flow × Int) (i : Nat) :
    (anchorStepOut s i).1.links =
      s.1.links.set! i { s.1.links[i]! with
        y0 := s.2 + Int.fdiv (s.1.links[i]!).width 2 } := rfl

theorem anchorStepOut_snd (s : Flow × Int) (i : Nat) :
    (anchorStepOut s i).2 = s.2 + (s.1.links[i]!).width := rfl

theorem anchorStepIn_fst (s : Flow × Int) (i : Nat) :
    (anchorStepIn s i).1.links =
      s.1.links.set! i { s.1.links[i]! with
        y1 := s.2 + Int.fdiv (s.1.links[i]!).width 2 } := rfl

theorem anchorStepIn_snd (s : Flow × Int) (i : Nat) :
    (anchorStepIn s i).2 = s.2 + (s.1.links[i]!).width := rfl

theorem anchorStepOut_link_y0 (s : Flow × Int) (i : Nat)
    (hi : i < s.1.links.size) :
    ((anchorStepOut s i).1.links[i]!).y0 =
      s.2 + Int.fdiv (s.1.links[i]!).width 2 := by
  rw [anchorStepOut_fst, Array.getElem!_set!_self _ _ _ hi]

theorem anchorStepIn_link_y1 (s : Flow × Int) (i : Nat)
    (hi : i < s.1.links.size) :
    ((anchorStepIn s i).1.links[i]!).y1 =
      s.2 + Int.fdiv (s.1.links[i]!).width 2 := by
  rw [anchorStepIn_fst, Array.getElem!_set!_self _ _ _ hi]

theorem anchorStepOut_size (s : Flow × Int) (i : Nat) :
    (anchorStepOut s i).1.links.size = s.1.links.size := by
  rw [anchorStepOut_fst, Array.size_set!]

theorem anchorStepIn_size (s : Flow × Int) (i : Nat) :
    (anchorStepIn s i).1.links.size = s.1.links.size := by
  rw [anchorStepIn_fst, Array.size_set!]

theorem anchorStepOut_link_y0_ne (s : Flow × Int) (i j : Nat) (hij : i ≠ j) :
    ((anchorStepOut s i).1.links[j]!).y0 = (s.1.links[j]!).y0 := by
  rw [anchorStepOut_fst, Array.getElem!_set!_ne _ _ _ _ hij]

theorem anchorStepIn_link_y1_ne (s : Flow × Int) (i j : Nat) (hij : i ≠ j) :
    ((anchorStepIn s i).1.links[j]!).y1 = (s.1.links[j]!).y1 := by
  rw [anchorStepIn_fst, Array.getElem!_set!_ne _ _ _ _ hij]

theorem set_y0_width (links : Array Link) (j : Nat) (y0 : Int) (k : Nat) :
    ((links.set! j { links[j]! with y0 := y0 })[k]!).width = (links[k]!).width := by
  by_cases hjk : j = k
  · subst k
    by_cases hj : j < links.size
    · rw [Array.getElem!_set!_self _ _ _ hj]
    · have he : links.set! j ({ links[j]! with y0 := y0 } : Link) = links := by
        simp [Array.set!, Array.setIfInBounds, hj]
      rw [he]
  · rw [Array.getElem!_set!_ne _ _ _ _ hjk]

theorem set_y1_width (links : Array Link) (j : Nat) (y1 : Int) (k : Nat) :
    ((links.set! j { links[j]! with y1 := y1 })[k]!).width = (links[k]!).width := by
  by_cases hjk : j = k
  · subst k
    by_cases hj : j < links.size
    · rw [Array.getElem!_set!_self _ _ _ hj]
    · have he : links.set! j ({ links[j]! with y1 := y1 } : Link) = links := by
        simp [Array.set!, Array.setIfInBounds, hj]
      rw [he]
  · rw [Array.getElem!_set!_ne _ _ _ _ hjk]

theorem anchorStepOut_widths (l : List Nat) (f : Flow) (acc : Int) (k : Nat) :
    ((l.foldl anchorStepOut (f, acc)).1.links[k]!).width = (f.links[k]!).width := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    have hstep : ((anchorStepOut (f, acc) i).1.links[k]!).width = (f.links[k]!).width := by
      exact set_y0_width f.links i _ k
    rw [List.foldl_cons, ih (anchorStepOut (f, acc) i).1 (anchorStepOut (f, acc) i).2, hstep]

theorem anchorStepIn_widths (l : List Nat) (f : Flow) (acc : Int) (k : Nat) :
    ((l.foldl anchorStepIn (f, acc)).1.links[k]!).width = (f.links[k]!).width := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    have hstep : ((anchorStepIn (f, acc) i).1.links[k]!).width = (f.links[k]!).width := by
      exact set_y1_width f.links i _ k
    rw [List.foldl_cons, ih (anchorStepIn (f, acc) i).1 (anchorStepIn (f, acc) i).2, hstep]

theorem anchorStepOut_no_touch (l : List Nat) (f : Flow) (acc : Int) (j : Nat)
    (hj : j ∉ l) :
    ((l.foldl anchorStepOut (f, acc)).1.links[j]!).y0 = (f.links[j]!).y0 := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    have hji : i ≠ j := by intro heq; exact hj (heq ▸ List.mem_cons_self)
    have hjr : j ∉ rest := fun h => hj (List.mem_cons_of_mem i h)
    rw [List.foldl_cons, ih (anchorStepOut (f, acc) i).1 (anchorStepOut (f, acc) i).2 hjr]
    exact anchorStepOut_link_y0_ne (f, acc) i j hji

theorem anchorStepIn_no_touch (l : List Nat) (f : Flow) (acc : Int) (j : Nat)
    (hj : j ∉ l) :
    ((l.foldl anchorStepIn (f, acc)).1.links[j]!).y1 = (f.links[j]!).y1 := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    have hji : i ≠ j := by intro heq; exact hj (heq ▸ List.mem_cons_self)
    have hjr : j ∉ rest := fun h => hj (List.mem_cons_of_mem i h)
    rw [List.foldl_cons, ih (anchorStepIn (f, acc) i).1 (anchorStepIn (f, acc) i).2 hjr]
    exact anchorStepIn_link_y1_ne (f, acc) i j hji

theorem anchorStepOut_visit (l : List Nat) (f : Flow) (acc : Int) (j : Nat)
    (hnd : l.Nodup) (hj : j ∈ l) (hlen : ∀ i ∈ l, i < f.links.size) :
    ((l.foldl anchorStepOut (f, acc)).1.links[j]!).y0 =
      acc + widthsBefore f l j + Int.fdiv ((f.links[j]!).width) 2 := by
  induction l generalizing f acc with
  | nil => simp at hj
  | cons i rest ih =>
    rw [List.foldl_cons]
    obtain ⟨hnot, hndRest⟩ := List.nodup_cons.mp hnd
    by_cases hij : i = j
    · subst j
      have hstep : ((anchorStepOut (f, acc) i).1.links[i]!).y0 =
          acc + Int.fdiv (f.links[i]!).width 2 :=
        anchorStepOut_link_y0 (f, acc) i (hlen i (List.mem_cons_self))
      rw [anchorStepOut_no_touch rest (anchorStepOut (f, acc) i).1
        (anchorStepOut (f, acc) i).2 i hnot, hstep,
        widthsBefore_cons, ite_eq_left rfl]
      omega
    · have hjrest : j ∈ rest := by
        rcases List.mem_cons.mp hj with heq | hmem
        · exact absurd heq.symm hij
        · exact hmem
      have hlenRest : ∀ k ∈ rest, k < (anchorStepOut (f, acc) i).1.links.size := by
        intro k hk
        rw [anchorStepOut_size]
        exact hlen k (List.mem_cons_of_mem i hk)
      rw [ih (anchorStepOut (f, acc) i).1 (anchorStepOut (f, acc) i).2
        hndRest hjrest hlenRest]
      have hcongr : widthsBefore (anchorStepOut (f, acc) i).1 rest j =
          widthsBefore f rest j := by
        apply widthsBefore_congr
        intro k _
        exact set_y0_width f.links i _ k
      have hwidth : ((anchorStepOut (f, acc) i).1.links[j]!).width =
          (f.links[j]!).width := set_y0_width f.links i _ j
      rw [hcongr, hwidth]
      have hacc : (anchorStepOut (f, acc) i).2 = acc + (f.links[i]!).width :=
        anchorStepOut_snd (f, acc) i
      rw [hacc, widthsBefore_cons, ite_eq_right hij]
      omega

theorem anchorStepIn_visit (l : List Nat) (f : Flow) (acc : Int) (j : Nat)
    (hnd : l.Nodup) (hj : j ∈ l) (hlen : ∀ i ∈ l, i < f.links.size) :
    ((l.foldl anchorStepIn (f, acc)).1.links[j]!).y1 =
      acc + widthsBefore f l j + Int.fdiv ((f.links[j]!).width) 2 := by
  induction l generalizing f acc with
  | nil => simp at hj
  | cons i rest ih =>
    rw [List.foldl_cons]
    obtain ⟨hnot, hndRest⟩ := List.nodup_cons.mp hnd
    by_cases hij : i = j
    · subst j
      have hstep : ((anchorStepIn (f, acc) i).1.links[i]!).y1 =
          acc + Int.fdiv (f.links[i]!).width 2 :=
        anchorStepIn_link_y1 (f, acc) i (hlen i (List.mem_cons_self))
      rw [anchorStepIn_no_touch rest (anchorStepIn (f, acc) i).1
        (anchorStepIn (f, acc) i).2 i hnot, hstep,
        widthsBefore_cons, ite_eq_left rfl]
      omega
    · have hjrest : j ∈ rest := by
        rcases List.mem_cons.mp hj with heq | hmem
        · exact absurd heq.symm hij
        · exact hmem
      have hlenRest : ∀ k ∈ rest, k < (anchorStepIn (f, acc) i).1.links.size := by
        intro k hk
        rw [anchorStepIn_size]
        exact hlen k (List.mem_cons_of_mem i hk)
      rw [ih (anchorStepIn (f, acc) i).1 (anchorStepIn (f, acc) i).2
        hndRest hjrest hlenRest]
      have hcongr : widthsBefore (anchorStepIn (f, acc) i).1 rest j =
          widthsBefore f rest j := by
        apply widthsBefore_congr
        intro k _
        exact set_y1_width f.links i _ k
      have hwidth : ((anchorStepIn (f, acc) i).1.links[j]!).width =
          (f.links[j]!).width := set_y1_width f.links i _ j
      rw [hcongr, hwidth]
      have hacc : (anchorStepIn (f, acc) i).2 = acc + (f.links[i]!).width :=
        anchorStepIn_snd (f, acc) i
      rw [hacc, widthsBefore_cons, ite_eq_right hij]
      omega

theorem anchorStepOut_y1 (s : Flow × Int) (i j : Nat) :
    ((anchorStepOut s i).1.links[j]!).y1 = (s.1.links[j]!).y1 := by
  rw [anchorStepOut_fst]
  by_cases hij : i = j
  · subst j
    by_cases hi : i < s.1.links.size
    · rw [Array.getElem!_set!_self _ _ _ hi]
    · have he : s.1.links.set! i
          ({ s.1.links[i]! with y0 := s.2 + Int.fdiv (s.1.links[i]!).width 2 } : Link) =
          s.1.links := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne _ _ _ _ hij]

theorem anchorStepIn_y0 (s : Flow × Int) (i j : Nat) :
    ((anchorStepIn s i).1.links[j]!).y0 = (s.1.links[j]!).y0 := by
  rw [anchorStepIn_fst]
  by_cases hij : i = j
  · subst j
    by_cases hi : i < s.1.links.size
    · rw [Array.getElem!_set!_self _ _ _ hi]
    · have he : s.1.links.set! i
          ({ s.1.links[i]! with y1 := s.2 + Int.fdiv (s.1.links[i]!).width 2 } : Link) =
          s.1.links := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne _ _ _ _ hij]

theorem anchorStepOut_nodes_fold (l : List Nat) (s : Flow × Int) :
    ((l.foldl anchorStepOut s).1).nodes = s.1.nodes := by
  induction l generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih (anchorStepOut s i)]
    rfl

theorem anchorStepIn_nodes_fold (l : List Nat) (s : Flow × Int) :
    ((l.foldl anchorStepIn s).1).nodes = s.1.nodes := by
  induction l generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih (anchorStepIn s i)]
    rfl

theorem anchorStepOut_y1_fold (l : List Nat) (f : Flow) (acc : Int) (j : Nat) :
    ((l.foldl anchorStepOut (f, acc)).1.links[j]!).y1 = (f.links[j]!).y1 := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons]
    have hstep := anchorStepOut_y1 (f, acc) i j
    rw [ih (anchorStepOut (f, acc) i).1 (anchorStepOut (f, acc) i).2]
    exact hstep

theorem anchorStepIn_y0_fold (l : List Nat) (f : Flow) (acc : Int) (j : Nat) :
    ((l.foldl anchorStepIn (f, acc)).1.links[j]!).y0 = (f.links[j]!).y0 := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons]
    have hstep := anchorStepIn_y0 (f, acc) i j
    rw [ih (anchorStepIn (f, acc) i).1 (anchorStepIn (f, acc) i).2]
    exact hstep


theorem anchorStepOut_y0_bounds (l : List Nat) (f : Flow) (acc height : Int) (j : Nat)
    (hnd : l.Nodup) (hj : j ∈ l) (hlen : ∀ i ∈ l, i < f.links.size)
    (hw : ∀ i ∈ l, 0 ≤ (f.links[i]!).width)
    (hsum : (l.map (fun i => (f.links[i]!).width)).sum ≤ height) :
    0 ≤ ((l.foldl anchorStepOut (f, acc)).1.links[j]!).y0 - acc ∧
      ((l.foldl anchorStepOut (f, acc)).1.links[j]!).y0 - acc ≤ height := by
  have hvisit := anchorStepOut_visit l f acc j hnd hj hlen
  have hwj := hw j hj
  have hhalf := half_width_inside (f.links[j]!).width hwj
  have hb := widthsBefore_nonneg f l j hw
  have hsumj := widthsBefore_add_le_sum f l j hj hw
  rw [hvisit]
  constructor <;> omega

theorem anchorStepIn_y1_bounds (l : List Nat) (f : Flow) (acc height : Int) (j : Nat)
    (hnd : l.Nodup) (hj : j ∈ l) (hlen : ∀ i ∈ l, i < f.links.size)
    (hw : ∀ i ∈ l, 0 ≤ (f.links[i]!).width)
    (hsum : (l.map (fun i => (f.links[i]!).width)).sum ≤ height) :
    0 ≤ ((l.foldl anchorStepIn (f, acc)).1.links[j]!).y1 - acc ∧
      ((l.foldl anchorStepIn (f, acc)).1.links[j]!).y1 - acc ≤ height := by
  have hvisit := anchorStepIn_visit l f acc j hnd hj hlen
  have hwj := hw j hj
  have hhalf := half_width_inside (f.links[j]!).width hwj
  have hb := widthsBefore_nonneg f l j hw
  have hsumj := widthsBefore_add_le_sum f l j hj hw
  rw [hvisit]
  constructor <;> omega

/-- One `anchorLinks` node step, factored for fold reasoning. -/
def anchorStep (g : Flow) (i : Nat) : Flow :=
  let n := g.nodes[i]!
  (n.incoming.foldl anchorStepIn
    ((n.outgoing.foldl anchorStepOut (g, n.y0)).1, n.y0)).1

theorem anchorLinks_fold (f : Flow) :
    anchorLinks f = (List.range f.nodes.size).foldl anchorStep f := rfl

theorem anchorStepOut_links_size_fold (l : List Nat) (f : Flow) (acc : Int) :
    ((l.foldl anchorStepOut (f, acc)).1).links.size = f.links.size := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih (anchorStepOut (f, acc) i).1 (anchorStepOut (f, acc) i).2]
    exact anchorStepOut_size (f, acc) i

theorem anchorStepIn_links_size_fold (l : List Nat) (f : Flow) (acc : Int) :
    ((l.foldl anchorStepIn (f, acc)).1).links.size = f.links.size := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih (anchorStepIn (f, acc) i).1 (anchorStepIn (f, acc) i).2]
    exact anchorStepIn_size (f, acc) i

theorem anchorStepOut_linkData (s : Flow × Int) (i j : Nat) :
    linkData ((anchorStepOut s i).1.links[j]!) = linkData (s.1.links[j]!) := by
  rw [anchorStepOut_fst]
  by_cases hij : i = j
  · subst j
    by_cases hi : i < s.1.links.size
    · rw [Array.getElem!_set!_self _ _ _ hi]
      rfl
    · have he : s.1.links.set! i
          { s.1.links[i]! with y0 := s.2 + Int.fdiv (s.1.links[i]!).width 2 } =
          s.1.links := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne _ _ _ _ hij]

theorem anchorStepIn_linkData (s : Flow × Int) (i j : Nat) :
    linkData ((anchorStepIn s i).1.links[j]!) = linkData (s.1.links[j]!) := by
  rw [anchorStepIn_fst]
  by_cases hij : i = j
  · subst j
    by_cases hi : i < s.1.links.size
    · rw [Array.getElem!_set!_self _ _ _ hi]
      rfl
    · have he : s.1.links.set! i
          { s.1.links[i]! with y1 := s.2 + Int.fdiv (s.1.links[i]!).width 2 } =
          s.1.links := by
        simp [Array.set!, Array.setIfInBounds, hi]
      rw [he]
  · rw [Array.getElem!_set!_ne _ _ _ _ hij]

theorem anchorStepOut_linkData_fold (l : List Nat) (f : Flow) (acc : Int) (j : Nat) :
    linkData ((l.foldl anchorStepOut (f, acc)).1.links[j]!) =
      linkData (f.links[j]!) := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih (anchorStepOut (f, acc) i).1 (anchorStepOut (f, acc) i).2]
    exact anchorStepOut_linkData (f, acc) i j

theorem anchorStepIn_linkData_fold (l : List Nat) (f : Flow) (acc : Int) (j : Nat) :
    linkData ((l.foldl anchorStepIn (f, acc)).1.links[j]!) =
      linkData (f.links[j]!) := by
  induction l generalizing f acc with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih (anchorStepIn (f, acc) i).1 (anchorStepIn (f, acc) i).2]
    exact anchorStepIn_linkData (f, acc) i j

/-- The nodes array is untouched by one `anchorLinks` node step. -/
theorem anchorLinks_step_nodes (f : Flow) (i : Nat) :
    (anchorStep f i).nodes = f.nodes := by
  show ((f.nodes[i]!.incoming.foldl anchorStepIn
    ((f.nodes[i]!.outgoing.foldl anchorStepOut (f, f.nodes[i]!.y0)).1,
      f.nodes[i]!.y0)).1).nodes = f.nodes
  rw [anchorStepIn_nodes_fold]
  dsimp only
  rw [anchorStepOut_nodes_fold]

theorem anchorLinks_step_links_size (f : Flow) (i : Nat) :
    (anchorStep f i).links.size = f.links.size := by
  show ((f.nodes[i]!.incoming.foldl anchorStepIn
    ((f.nodes[i]!.outgoing.foldl anchorStepOut (f, f.nodes[i]!.y0)).1,
      f.nodes[i]!.y0)).1).links.size = f.links.size
  rw [anchorStepIn_links_size_fold]
  rw [anchorStepOut_links_size_fold]

theorem anchorLinks_step_linkData (f : Flow) (i j : Nat) :
    linkData ((anchorStep f i).links[j]!) = linkData (f.links[j]!) := by
  show linkData ((f.nodes[i]!.incoming.foldl anchorStepIn
    ((f.nodes[i]!.outgoing.foldl anchorStepOut (f, f.nodes[i]!.y0)).1,
      f.nodes[i]!.y0)).1.links[j]!) = _
  rw [anchorStepIn_linkData_fold]
  rw [anchorStepOut_linkData_fold]

/-- Incidence and sizes survive one `anchorLinks` node step. -/
theorem anchorStep_preserves (f : Flow) (i : Nat)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k)) :
    (anchorStep f i).nodes = f.nodes ∧
    (anchorStep f i).links.size = f.links.size ∧
    (∀ x : Nat, linkData ((anchorStep f i).links[x]!) = linkData (f.links[x]!)) ∧
    (∀ k, k < (anchorStep f i).nodes.size →
      (∀ x, x ∈ ((anchorStep f i).nodes[k]!).incoming ↔
        x < (anchorStep f i).links.size ∧ ((anchorStep f i).links[x]!).target = k) ∧
      (∀ x, x ∈ ((anchorStep f i).nodes[k]!).outgoing ↔
        x < (anchorStep f i).links.size ∧ ((anchorStep f i).links[x]!).source = k)) := by
  refine ⟨anchorLinks_step_nodes f i, anchorLinks_step_links_size f i,
    anchorLinks_step_linkData f i, ?_⟩
  have hnodes := anchorLinks_step_nodes f i
  have hsize := anchorLinks_step_links_size f i
  have hdata := anchorLinks_step_linkData f i
  intro k hk
  rw [hnodes] at hk
  obtain ⟨h1, h2⟩ := hinc k hk
  have et : ∀ x : Nat, ((anchorStep f i).links[x]!).target = (f.links[x]!).target :=
    fun x => congrArg (fun d : Nat × Nat × Int × Int => d.2.1) (hdata x)
  have es : ∀ x : Nat, ((anchorStep f i).links[x]!).source = (f.links[x]!).source :=
    fun x => congrArg (fun d : Nat × Nat × Int × Int => d.1) (hdata x)
  constructor
  · intro x
    rw [hnodes, hsize, et x]
    exact h1 x
  · intro x
    rw [hnodes, hsize, es x]
    exact h2 x

/-- One node step of `anchorLinks` does not disturb the `y0` of a link whose source is a
different node. -/
theorem anchorLinks_step_y0 (f : Flow) (i s j : Nat) (hi : i < f.nodes.size)
    (his : i ≠ s) (hj : f.links[j]!.source = s)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k)) :
    (anchorStep f i).links[j]!.y0 = (f.links[j]!).y0 := by
  show ((f.nodes[i]!.incoming.foldl anchorStepIn
    ((f.nodes[i]!.outgoing.foldl anchorStepOut (f, f.nodes[i]!.y0)).1,
      f.nodes[i]!.y0)).1.links[j]!).y0 = _
  have hji : j ∉ f.nodes[i]!.outgoing := by
    intro hmem
    have hiff := (hinc i hi).2 j
    rw [hiff] at hmem
    have hsrc := hmem.2
    rw [hj] at hsrc
    exact his hsrc.symm
  rw [anchorStepIn_y0_fold]
  rw [anchorStepOut_no_touch _ _ _ _ hji]

/-- One node step of `anchorLinks` does not disturb the `y1` of a link whose target is a
different node. -/
theorem anchorLinks_step_y1 (f : Flow) (i t j : Nat) (hi : i < f.nodes.size)
    (hit : i ≠ t) (hj : f.links[j]!.target = t)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k)) :
    (anchorStep f i).links[j]!.y1 = (f.links[j]!).y1 := by
  show ((f.nodes[i]!.incoming.foldl anchorStepIn
    ((f.nodes[i]!.outgoing.foldl anchorStepOut (f, f.nodes[i]!.y0)).1,
      f.nodes[i]!.y0)).1.links[j]!).y1 = _
  have h1 : (((f.nodes[i]!.outgoing.foldl anchorStepOut
      (f, f.nodes[i]!.y0)).1).links[j]!).y1 = (f.links[j]!).y1 :=
    anchorStepOut_y1_fold _ _ _ _
  have hni : j ∉ f.nodes[i]!.incoming := by
    intro hmem
    have hiff := (hinc i hi).1 j
    rw [hiff] at hmem
    have htgt := hmem.2
    rw [hj] at htgt
    exact hit htgt.symm
  rw [anchorStepIn_no_touch _ _ _ _ hni]
  rw [anchorStepOut_y1_fold]

/-- Folding `anchorStep` over a list of nodes that excludes the source `s` leaves the
`y0` of link `j` (whose source is `s`) unchanged. -/
theorem anchorLinks_prefix_y0 (f : Flow) (l : List Nat) (s j : Nat)
    (hj : f.links[j]!.source = s)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k))
    (hlen : ∀ i ∈ l, i < f.nodes.size)
    (hsnot : ∀ i ∈ l, i ≠ s) :
    (l.foldl anchorStep f).links[j]!.y0 = (f.links[j]!).y0 := by
  revert hj hinc hlen hsnot
  induction l generalizing f with
  | nil => intros; rfl
  | cons i rest ih =>
    intro hj hinc hlen hsnot
    rw [List.foldl_cons]
    have hi : i < f.nodes.size := hlen i List.mem_cons_self
    have his : i ≠ s := hsnot i List.mem_cons_self
    have hstep : (anchorStep f i).links[j]!.y0 = (f.links[j]!).y0 :=
      anchorLinks_step_y0 f i s j hi his hj hinc
    have htrans := anchorStep_preserves f i hinc
    obtain ⟨hgnodes, hgsize, hgdata, hincG⟩ := htrans
    have hjG : (anchorStep f i).links[j]!.source = s :=
      (congrArg Prod.fst (hgdata j)).trans hj
    have hlenG : ∀ k ∈ rest, k < (anchorStep f i).nodes.size := by
      intro k hk
      rw [hgnodes]
      exact hlen k (List.mem_cons_of_mem i hk)
    have hsnotG : ∀ k ∈ rest, k ≠ s :=
      fun k hk => hsnot k (List.mem_cons_of_mem i hk)
    have hfin : (rest.foldl anchorStep (anchorStep f i)).links[j]!.y0 =
        ((anchorStep f i).links[j]!).y0 :=
      ih (anchorStep f i) hjG hincG hlenG hsnotG
    rw [hfin]
    exact hstep

/-- Folding `anchorStep` over a list of nodes that excludes the target `t` leaves the
`y1` of link `j` (whose target is `t`) unchanged. -/
theorem anchorLinks_prefix_y1 (f : Flow) (l : List Nat) (t j : Nat)
    (hj : f.links[j]!.target = t)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k))
    (hlen : ∀ i ∈ l, i < f.nodes.size)
    (htnot : ∀ i ∈ l, i ≠ t) :
    (l.foldl anchorStep f).links[j]!.y1 = (f.links[j]!).y1 := by
  revert hj hinc hlen htnot
  induction l generalizing f with
  | nil => intros; rfl
  | cons i rest ih =>
    intro hj hinc hlen htnot
    rw [List.foldl_cons]
    have hi : i < f.nodes.size := hlen i List.mem_cons_self
    have hit : i ≠ t := htnot i List.mem_cons_self
    have hstep : (anchorStep f i).links[j]!.y1 = (f.links[j]!).y1 :=
      anchorLinks_step_y1 f i t j hi hit hj hinc
    have htrans := anchorStep_preserves f i hinc
    obtain ⟨hgnodes, hgsize, hgdata, hincG⟩ := htrans
    have hjG : (anchorStep f i).links[j]!.target = t :=
      (congrArg (fun d : Nat × Nat × Int × Int => d.2.1) (hgdata j)).trans hj
    have hlenG : ∀ k ∈ rest, k < (anchorStep f i).nodes.size := by
      intro k hk
      rw [hgnodes]
      exact hlen k (List.mem_cons_of_mem i hk)
    have htnotG : ∀ k ∈ rest, k ≠ t :=
      fun k hk => htnot k (List.mem_cons_of_mem i hk)
    have hfin : (rest.foldl anchorStep (anchorStep f i)).links[j]!.y1 =
        ((anchorStep f i).links[j]!).y1 :=
      ih (anchorStep f i) hjG hincG hlenG htnotG
    rw [hfin]
    exact hstep

/-- After folding `anchorStep` over any node list containing `s`, the `y0` of a link
sourced at `s` is the outgoing-anchor offset computed from `s`'s outgoing list. -/
theorem anchorLinks_fold_y0_at (f : Flow) (l : List Nat) (s j : Nat)
    (hj : f.links[j]!.source = s) (hjmem : j ∈ f.nodes[s]!.outgoing)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k))
    (hnd : (f.nodes[s]!.outgoing).Nodup)
    (hlen : ∀ i ∈ f.nodes[s]!.outgoing, i < f.links.size)
    (hw : ∀ i ∈ f.nodes[s]!.outgoing, 0 ≤ (f.links[i]!).width)
    (hsum : ((f.nodes[s]!.outgoing.map (fun i => (f.links[i]!).width)).sum ≤
      (f.nodes[s]!).y1 - (f.nodes[s]!).y0))
    (hmem : s ∈ l) (hnodup : l.Nodup) (hlenAll : ∀ i ∈ l, i < f.nodes.size) :
    0 ≤ (l.foldl anchorStep f).links[j]!.y0 - f.nodes[s]!.y0 ∧
      (l.foldl anchorStep f).links[j]!.y0 - f.nodes[s]!.y0 ≤
        (f.nodes[s]!).y1 - (f.nodes[s]!).y0 := by
  revert hj hjmem hinc hnd hlen hw hsum hmem hnodup hlenAll
  induction l generalizing f with
  | nil =>
    intro hj hjmem hinc hnd hlen hw hsum hmem hnodup hlenAll
    simp at hmem
  | cons i rest ih =>
    intro hj hjmem hinc hnd hlen hw hsum hmem hnodup hlenAll
    rw [List.foldl_cons]
    by_cases heq : i = s
    · subst i
      have hnotmem : s ∉ rest := (List.nodup_cons.mp hnodup).1
      have hnodupR : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hlenR : ∀ k ∈ rest, k < f.nodes.size :=
        fun k hk => hlenAll k (List.mem_cons_of_mem s hk)
      have htrans := anchorStep_preserves f s hinc
      obtain ⟨hgnodes, hgsize, hgdata, hincG⟩ := htrans
      have hjG : (anchorStep f s).links[j]!.source = s :=
        (congrArg Prod.fst (hgdata j)).trans hj
      have hlenGR : ∀ k ∈ rest, k < (anchorStep f s).nodes.size := by
        intro k hk
        rw [hgnodes]
        exact hlenR k hk
      have hsnotR : ∀ k ∈ rest, k ≠ s :=
        fun k hk he => hnotmem (he ▸ hk)
      have hsuff : (rest.foldl anchorStep (anchorStep f s)).links[j]!.y0 =
          ((anchorStep f s).links[j]!).y0 :=
        anchorLinks_prefix_y0 _ _ _ _ hjG hincG hlenGR hsnotR
      have hmid : (anchorStep f s).links[j]!.y0 =
          f.nodes[s]!.y0 + widthsBefore f f.nodes[s]!.outgoing j +
            Int.fdiv (f.links[j]!).width 2 := by
        show ((f.nodes[s]!.incoming.foldl anchorStepIn
          ((f.nodes[s]!.outgoing.foldl anchorStepOut (f, f.nodes[s]!.y0)).1,
            f.nodes[s]!.y0)).1.links[j]!).y0 = _
        rw [anchorStepIn_y0_fold]
        rw [anchorStepOut_visit _ _ _ _ hnd hjmem hlen]
      rw [hsuff, hmid]
      have hwj := hw j hjmem
      have hhalf := half_width_inside (f.links[j]!).width hwj
      have hb := widthsBefore_nonneg f _ j hw
      have hsumj := widthsBefore_add_le_sum f _ _ hjmem hw
      constructor <;> omega
    · have hi : i < f.nodes.size := hlenAll i List.mem_cons_self
      have htrans := anchorStep_preserves f i hinc
      obtain ⟨hgnodes, hgsize, hgdata, hincG⟩ := htrans
      have hjG : (anchorStep f i).links[j]!.source = s :=
        (congrArg Prod.fst (hgdata j)).trans hj
      have hjmemG : j ∈ (anchorStep f i).nodes[s]!.outgoing := by
        rw [hgnodes]
        exact hjmem
      have hndG : ((anchorStep f i).nodes[s]!.outgoing).Nodup := by
        rw [hgnodes]
        exact hnd
      have hlenG : ∀ k ∈ (anchorStep f i).nodes[s]!.outgoing,
          k < (anchorStep f i).links.size := by
        intro k hk
        rw [hgsize]
        rw [hgnodes] at hk
        exact hlen k hk
      have hwG : ∀ k ∈ (anchorStep f i).nodes[s]!.outgoing,
          0 ≤ ((anchorStep f i).links[k]!).width := by
        intro k hk
        rw [hgnodes] at hk
        have e : ((anchorStep f i).links[k]!).width = (f.links[k]!).width :=
          congrArg (fun d : Nat × Nat × Int × Int => d.2.2.2) (hgdata k)
        rw [e]
        exact hw k hk
      have hsumG : (((anchorStep f i).nodes[s]!.outgoing.map
          (fun k => ((anchorStep f i).links[k]!).width)).sum ≤
          (anchorStep f i).nodes[s]!.y1 - (anchorStep f i).nodes[s]!.y0) := by
        have e1 : ((anchorStep f i).nodes[s]!.outgoing.map
            (fun k => ((anchorStep f i).links[k]!).width)) =
            (f.nodes[s]!.outgoing.map (fun k => (f.links[k]!).width)) := by
          rw [hgnodes]
          apply List.map_congr_left
          intro k hk
          exact congrArg (fun d : Nat × Nat × Int × Int => d.2.2.2) (hgdata k)
        have e2 : (anchorStep f i).nodes[s]!.y1 - (anchorStep f i).nodes[s]!.y0 =
            (f.nodes[s]!).y1 - (f.nodes[s]!).y0 := by
          rw [hgnodes]
        rw [e1, e2]
        exact hsum
      have hmemG : s ∈ rest := by
        rcases List.mem_cons.mp hmem with he | hm
        · exact absurd he.symm heq
        · exact hm
      have hnodupG : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hlenAllG : ∀ k ∈ rest, k < (anchorStep f i).nodes.size := by
        intro k hk
        rw [hgnodes]
        exact hlenAll k (List.mem_cons_of_mem i hk)
      obtain ⟨hlo, hhi⟩ := ih (anchorStep f i) hjG hjmemG hincG hndG hlenG hwG
        hsumG hmemG hnodupG hlenAllG
      have e : (anchorStep f i).nodes[s]!.y0 = f.nodes[s]!.y0 := by
        rw [hgnodes]
      have e' : (anchorStep f i).nodes[s]!.y1 = f.nodes[s]!.y1 := by
        rw [hgnodes]
      rw [e] at hlo hhi
      rw [e'] at hhi
      exact ⟨hlo, hhi⟩

/-- After folding `anchorStep` over any node list containing `t`, the `y1` of a link
targeted at `t` is the incoming-anchor offset computed from `t`'s incoming list. -/
theorem anchorLinks_fold_y1_at (f : Flow) (l : List Nat) (t j : Nat)
    (hj : f.links[j]!.target = t) (hjmem : j ∈ f.nodes[t]!.incoming)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k))
    (hnd : (f.nodes[t]!.incoming).Nodup)
    (hlen : ∀ i ∈ f.nodes[t]!.incoming, i < f.links.size)
    (hw : ∀ i ∈ f.nodes[t]!.incoming, 0 ≤ (f.links[i]!).width)
    (hsum : ((f.nodes[t]!.incoming.map (fun i => (f.links[i]!).width)).sum ≤
      (f.nodes[t]!).y1 - (f.nodes[t]!).y0))
    (hmem : t ∈ l) (hnodup : l.Nodup) (hlenAll : ∀ i ∈ l, i < f.nodes.size) :
    0 ≤ (l.foldl anchorStep f).links[j]!.y1 - f.nodes[t]!.y0 ∧
      (l.foldl anchorStep f).links[j]!.y1 - f.nodes[t]!.y0 ≤
        (f.nodes[t]!).y1 - (f.nodes[t]!).y0 := by
  revert hj hjmem hinc hnd hlen hw hsum hmem hnodup hlenAll
  induction l generalizing f with
  | nil =>
    intro hj hjmem hinc hnd hlen hw hsum hmem hnodup hlenAll
    simp at hmem
  | cons i rest ih =>
    intro hj hjmem hinc hnd hlen hw hsum hmem hnodup hlenAll
    rw [List.foldl_cons]
    by_cases heq : i = t
    · subst i
      have hnotmem : t ∉ rest := (List.nodup_cons.mp hnodup).1
      have hnodupR : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hlenR : ∀ k ∈ rest, k < f.nodes.size :=
        fun k hk => hlenAll k (List.mem_cons_of_mem t hk)
      have htrans := anchorStep_preserves f t hinc
      obtain ⟨hgnodes, hgsize, hgdata, hincG⟩ := htrans
      have hjG : (anchorStep f t).links[j]!.target = t :=
        (congrArg (fun d : Nat × Nat × Int × Int => d.2.1) (hgdata j)).trans hj
      have hlenGR : ∀ k ∈ rest, k < (anchorStep f t).nodes.size := by
        intro k hk
        rw [hgnodes]
        exact hlenR k hk
      have htnotR : ∀ k ∈ rest, k ≠ t :=
        fun k hk he => hnotmem (he ▸ hk)
      have hsuff : (rest.foldl anchorStep (anchorStep f t)).links[j]!.y1 =
          ((anchorStep f t).links[j]!).y1 :=
        anchorLinks_prefix_y1 _ _ _ _ hjG hincG hlenGR htnotR
      have hGsize : ((((f.nodes[t]!.outgoing.foldl anchorStepOut
          (f, f.nodes[t]!.y0)).1).links.size = f.links.size)) :=
        anchorStepOut_links_size_fold _ _ _
      have hGwidth : ∀ k : Nat, (((f.nodes[t]!.outgoing.foldl anchorStepOut
          (f, f.nodes[t]!.y0)).1).links[k]!).width = (f.links[k]!).width :=
        fun k => anchorStepOut_widths _ _ _ _
      have hlenG : ∀ k ∈ f.nodes[t]!.incoming,
          k < (((f.nodes[t]!.outgoing.foldl anchorStepOut
            (f, f.nodes[t]!.y0)).1).links.size) := by
        intro k hk
        rw [hGsize]
        exact hlen k hk
      have hwG : ∀ k ∈ f.nodes[t]!.incoming,
          0 ≤ (((f.nodes[t]!.outgoing.foldl anchorStepOut
            (f, f.nodes[t]!.y0)).1).links[k]!).width := by
        intro k hk
        rw [hGwidth k]
        exact hw k hk
      have hcongr : widthsBefore
          ((f.nodes[t]!.outgoing.foldl anchorStepOut (f, f.nodes[t]!.y0)).1)
          f.nodes[t]!.incoming j =
          widthsBefore f f.nodes[t]!.incoming j := by
        apply widthsBefore_congr
        intro k _
        exact hGwidth k
      have hwidthj : (((f.nodes[t]!.outgoing.foldl anchorStepOut
          (f, f.nodes[t]!.y0)).1).links[j]!).width = (f.links[j]!).width :=
        hGwidth j
      have hmid : (anchorStep f t).links[j]!.y1 =
          f.nodes[t]!.y0 + widthsBefore f f.nodes[t]!.incoming j +
            Int.fdiv (f.links[j]!).width 2 := by
        show ((f.nodes[t]!.incoming.foldl anchorStepIn
          ((f.nodes[t]!.outgoing.foldl anchorStepOut (f, f.nodes[t]!.y0)).1,
            f.nodes[t]!.y0)).1.links[j]!).y1 = _
        rw [anchorStepIn_visit _ _ _ _ hnd hjmem hlenG]
        rw [hcongr, hwidthj]
      rw [hsuff, hmid]
      have hwj := hw j hjmem
      have hhalf := half_width_inside (f.links[j]!).width hwj
      have hb := widthsBefore_nonneg f _ j hw
      have hsumj := widthsBefore_add_le_sum f _ _ hjmem hw
      constructor <;> omega
    · have hi : i < f.nodes.size := hlenAll i List.mem_cons_self
      have htrans := anchorStep_preserves f i hinc
      obtain ⟨hgnodes, hgsize, hgdata, hincG⟩ := htrans
      have hjG : (anchorStep f i).links[j]!.target = t :=
        (congrArg (fun d : Nat × Nat × Int × Int => d.2.1) (hgdata j)).trans hj
      have hjmemG : j ∈ (anchorStep f i).nodes[t]!.incoming := by
        rw [hgnodes]
        exact hjmem
      have hndG : ((anchorStep f i).nodes[t]!.incoming).Nodup := by
        rw [hgnodes]
        exact hnd
      have hlenG : ∀ k ∈ (anchorStep f i).nodes[t]!.incoming,
          k < (anchorStep f i).links.size := by
        intro k hk
        rw [hgsize]
        rw [hgnodes] at hk
        exact hlen k hk
      have hwG : ∀ k ∈ (anchorStep f i).nodes[t]!.incoming,
          0 ≤ ((anchorStep f i).links[k]!).width := by
        intro k hk
        rw [hgnodes] at hk
        have e : ((anchorStep f i).links[k]!).width = (f.links[k]!).width :=
          congrArg (fun d : Nat × Nat × Int × Int => d.2.2.2) (hgdata k)
        rw [e]
        exact hw k hk
      have hsumG : (((anchorStep f i).nodes[t]!.incoming.map
          (fun k => ((anchorStep f i).links[k]!).width)).sum ≤
          (anchorStep f i).nodes[t]!.y1 - (anchorStep f i).nodes[t]!.y0) := by
        have e1 : ((anchorStep f i).nodes[t]!.incoming.map
            (fun k => ((anchorStep f i).links[k]!).width)) =
            (f.nodes[t]!.incoming.map (fun k => (f.links[k]!).width)) := by
          rw [hgnodes]
          apply List.map_congr_left
          intro k hk
          exact congrArg (fun d : Nat × Nat × Int × Int => d.2.2.2) (hgdata k)
        have e2 : (anchorStep f i).nodes[t]!.y1 - (anchorStep f i).nodes[t]!.y0 =
            (f.nodes[t]!).y1 - (f.nodes[t]!).y0 := by
          rw [hgnodes]
        rw [e1, e2]
        exact hsum
      have hmemG : t ∈ rest := by
        rcases List.mem_cons.mp hmem with he | hm
        · exact absurd he.symm heq
        · exact hm
      have hnodupG : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hlenAllG : ∀ k ∈ rest, k < (anchorStep f i).nodes.size := by
        intro k hk
        rw [hgnodes]
        exact hlenAll k (List.mem_cons_of_mem i hk)
      obtain ⟨hlo, hhi⟩ := ih (anchorStep f i) hjG hjmemG hincG hndG hlenG hwG
        hsumG hmemG hnodupG hlenAllG
      have e : (anchorStep f i).nodes[t]!.y0 = f.nodes[t]!.y0 := by
        rw [hgnodes]
      have e' : (anchorStep f i).nodes[t]!.y1 = f.nodes[t]!.y1 := by
        rw [hgnodes]
      rw [e] at hlo hhi
      rw [e'] at hhi
      exact ⟨hlo, hhi⟩

/-- After `anchorLinks`, the `y0` of a link is the outgoing-anchor offset computed from
its source node's outgoing list. -/
theorem anchorLinks_node_out_y0 (f : Flow) (s j : Nat)
    (hj : f.links[j]!.source = s) (hjmem : j ∈ f.nodes[s]!.outgoing)
    (hs : s < f.nodes.size)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k))
    (hnd : (f.nodes[s]!.outgoing).Nodup)
    (hlen : ∀ i ∈ f.nodes[s]!.outgoing, i < f.links.size)
    (hw : ∀ i ∈ f.nodes[s]!.outgoing, 0 ≤ (f.links[i]!).width)
    (hsum : ((f.nodes[s]!.outgoing.map (fun i => (f.links[i]!).width)).sum ≤
      (f.nodes[s]!).y1 - (f.nodes[s]!).y0)) :
    0 ≤ (anchorLinks f).links[j]!.y0 - f.nodes[s]!.y0 ∧
      (anchorLinks f).links[j]!.y0 - f.nodes[s]!.y0 ≤
        (f.nodes[s]!).y1 - (f.nodes[s]!).y0 := by
  rw [anchorLinks_fold]
  exact anchorLinks_fold_y0_at f _ s j hj hjmem hinc hnd hlen hw hsum
    (List.mem_range.mpr hs) List.nodup_range
    (fun i hi => List.mem_range.mp hi)

/-- After `anchorLinks`, the `y1` of a link is the incoming-anchor offset computed from
its target node's incoming list. -/
theorem anchorLinks_node_in_y1 (f : Flow) (t j : Nat)
    (hj : f.links[j]!.target = t) (hjmem : j ∈ f.nodes[t]!.incoming)
    (ht : t < f.nodes.size)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k))
    (hnd : (f.nodes[t]!.incoming).Nodup)
    (hlen : ∀ i ∈ f.nodes[t]!.incoming, i < f.links.size)
    (hw : ∀ i ∈ f.nodes[t]!.incoming, 0 ≤ (f.links[i]!).width)
    (hsum : ((f.nodes[t]!.incoming.map (fun i => (f.links[i]!).width)).sum ≤
      (f.nodes[t]!).y1 - (f.nodes[t]!).y0)) :
    0 ≤ (anchorLinks f).links[j]!.y1 - f.nodes[t]!.y0 ∧
      (anchorLinks f).links[j]!.y1 - f.nodes[t]!.y0 ≤
        (f.nodes[t]!).y1 - (f.nodes[t]!).y0 := by
  rw [anchorLinks_fold]
  exact anchorLinks_fold_y1_at f _ t j hj hjmem hinc hnd hlen hw hsum
    (List.mem_range.mpr ht) List.nodup_range
    (fun i hi => List.mem_range.mp hi)

/-- Flow preservation across layout stages: node count, per-node adjacency up to
permutation, and per-node values. Link arrays are related separately. -/
def FlowPreserved (f g : Flow) : Prop :=
  g.nodes.size = f.nodes.size ∧
  (∀ k : Nat, ((g.nodes[k]!).outgoing).Perm ((f.nodes[k]!).outgoing)) ∧
  (∀ k : Nat, ((g.nodes[k]!).incoming).Perm ((f.nodes[k]!).incoming)) ∧
  (∀ k : Nat, (g.nodes[k]!).value = (f.nodes[k]!).value)

theorem FlowPreserved_refl (f : Flow) : FlowPreserved f f :=
  ⟨rfl, fun _ => List.Perm.refl _, fun _ => List.Perm.refl _, fun _ => rfl⟩

theorem FlowPreserved_trans {f g h : Flow}
    (h1 : FlowPreserved f g) (h2 : FlowPreserved g h) : FlowPreserved f h := by
  obtain ⟨hs1, ho1, hi1, hv1⟩ := h1
  obtain ⟨hs2, ho2, hi2, hv2⟩ := h2
  refine ⟨hs2.trans hs1, fun k => (ho2 k).trans (ho1 k),
    fun k => (hi2 k).trans (hi1 k), fun k => (hv2 k).trans (hv1 k)⟩

/-- Flows with identical node arrays preserve each other. Covers record updates that
touch only non-node fields (flags, padding, columns). -/
theorem FlowPreserved_of_nodes_eq {f g : Flow} (h : g.nodes = f.nodes) :
    FlowPreserved f g := by
  unfold FlowPreserved
  rw [h]
  exact ⟨rfl, fun _ => List.Perm.refl _, fun _ => List.Perm.refl _, fun _ => rfl⟩

/-- A `nodes.modify` step permutes the projection rebuilt by `upd` and preserves the
projections carried through unchanged. -/
theorem flowModify_perm (g : Flow) (s : Nat) (upd : Node → Node)
    (hup : ∀ n, (upd n).outgoing.Perm n.outgoing)
    (hupIn : ∀ n, (upd n).incoming = n.incoming)
    (hupV : ∀ n, (upd n).value = n.value) (k : Nat) :
    (({ g with nodes := g.nodes.modify s upd }).nodes[k]!.outgoing).Perm
      ((g.nodes[k]!).outgoing) ∧
    (({ g with nodes := g.nodes.modify s upd }).nodes[k]!.incoming) =
      ((g.nodes[k]!).incoming) ∧
    (({ g with nodes := g.nodes.modify s upd }).nodes[k]!.value) =
      ((g.nodes[k]!).value) := by
  dsimp only
  by_cases hk : k < (g.nodes.modify s upd).size
  · have hkold : k < g.nodes.size := by simpa only [Array.size_modify] using hk
    rw [getElem!_pos (g.nodes.modify s upd) k hk, Array.getElem_modify hk,
      getElem!_pos g.nodes k hkold]
    by_cases heq : s = k
    · simp only [heq, ite_true]
      exact ⟨hup _, hupIn _, hupV _⟩
    · simp only [heq, ite_false]
      exact ⟨List.Perm.refl _, True.intro, True.intro⟩
  · have hkold : ¬ k < g.nodes.size := by simpa only [Array.size_modify] using hk
    rw [getElem!_neg (g.nodes.modify s upd) k hk, getElem!_neg g.nodes k hkold]
    exact ⟨List.Perm.refl _, rfl, rfl⟩

theorem flowModify_size (g : Flow) (s : Nat) (upd : Node → Node) :
    ({ g with nodes := g.nodes.modify s upd }).nodes.size = g.nodes.size := by
  dsimp only
  rw [Array.size_modify]

/-- First half of `reorderNodeLinks`: sorting sources' outgoing lists. -/
theorem reorderNodeLinks_first (f : Flow) (l : List Nat) (g : Flow)
    (h : FlowPreserved f g) (hlinks : g.links = f.links) :
    FlowPreserved f (l.foldl (fun g j =>
      { g with nodes := g.nodes.modify (g.links[j]!).source (fun n =>
        { n with outgoing := n.outgoing.mergeSort (byTarget g) }) }) g) ∧
    (l.foldl (fun g j =>
      { g with nodes := g.nodes.modify (g.links[j]!).source (fun n =>
        { n with outgoing := n.outgoing.mergeSort (byTarget g) }) }) g).links =
      f.links := by
  induction l generalizing g with
  | nil => exact ⟨h, hlinks⟩
  | cons j rest ih =>
    rw [List.foldl_cons]
    let upd : Node → Node := fun n =>
      { n with outgoing := n.outgoing.mergeSort (byTarget g) }
    have hstep (k : Nat) := flowModify_perm g (g.links[j]!).source upd
      (fun n => List.mergeSort_perm n.outgoing (byTarget g))
      (fun _ => rfl) (fun _ => rfl) k
    apply ih
    · exact ⟨(flowModify_size g (g.links[j]!).source upd).trans h.1,
        fun k => (hstep k).1.trans (h.2.1 k),
        fun k => (hstep k).2.1.symm ▸ h.2.2.1 k,
        fun k => (hstep k).2.2.trans (h.2.2.2 k)⟩
    · exact hlinks
/-- Mirror of `flowModify_perm`: permutes incoming, preserves outgoing and value. -/
theorem flowModify_perm_in (g : Flow) (s : Nat) (upd : Node → Node)
    (hup : ∀ n, (upd n).incoming.Perm n.incoming)
    (hupOut : ∀ n, (upd n).outgoing = n.outgoing)
    (hupV : ∀ n, (upd n).value = n.value) (k : Nat) :
    (({ g with nodes := g.nodes.modify s upd }).nodes[k]!.incoming).Perm
      ((g.nodes[k]!).incoming) ∧
    (({ g with nodes := g.nodes.modify s upd }).nodes[k]!.outgoing) =
      ((g.nodes[k]!).outgoing) ∧
    (({ g with nodes := g.nodes.modify s upd }).nodes[k]!.value) =
      ((g.nodes[k]!).value) := by
  dsimp only
  by_cases hk : k < (g.nodes.modify s upd).size
  · have hkold : k < g.nodes.size := by simpa only [Array.size_modify] using hk
    rw [getElem!_pos (g.nodes.modify s upd) k hk, Array.getElem_modify hk,
      getElem!_pos g.nodes k hkold]
    by_cases heq : s = k
    · simp only [heq, ite_true]
      exact ⟨hup _, hupOut _, hupV _⟩
    · simp only [heq, ite_false]
      exact ⟨List.Perm.refl _, True.intro, True.intro⟩
  · have hkold : ¬ k < g.nodes.size := by simpa only [Array.size_modify] using hk
    rw [getElem!_neg (g.nodes.modify s upd) k hk, getElem!_neg g.nodes k hkold]
    exact ⟨List.Perm.refl _, rfl, rfl⟩

/-- Second half of `reorderNodeLinks`: sorting targets' incoming lists. -/
theorem reorderNodeLinks_second (f : Flow) (l : List Nat) (g : Flow)
    (h : FlowPreserved f g) (hlinks : g.links = f.links) :
    FlowPreserved f (l.foldl (fun g j =>
      { g with nodes := g.nodes.modify (g.links[j]!).target (fun n =>
        { n with incoming := n.incoming.mergeSort (bySource g) }) }) g) ∧
    (l.foldl (fun g j =>
      { g with nodes := g.nodes.modify (g.links[j]!).target (fun n =>
        { n with incoming := n.incoming.mergeSort (bySource g) }) }) g).links = f.links := by
  induction l generalizing g with
  | nil => exact ⟨h, hlinks⟩
  | cons j rest ih =>
    rw [List.foldl_cons]
    let upd : Node → Node := fun n =>
      { n with incoming := n.incoming.mergeSort (bySource g) }
    have hstep (k : Nat) := flowModify_perm_in g (g.links[j]!).target upd
      (fun n => List.mergeSort_perm n.incoming (bySource g))
      (fun _ => rfl) (fun _ => rfl) k
    apply ih
    · exact ⟨(flowModify_size g (g.links[j]!).target upd).trans h.1,
        fun k => (hstep k).2.1.symm ▸ h.2.1 k,
        fun k => (hstep k).1.trans (h.2.2.1 k),
        fun k => (hstep k).2.2.trans (h.2.2.2 k)⟩
    · exact hlinks

theorem reorderNodeLinks_preserved (f : Flow) (i : Nat) :
    FlowPreserved f (reorderNodeLinks f i) := by
  let g := (f.nodes[i]!).incoming.foldl (fun g j =>
    { g with nodes := g.nodes.modify (g.links[j]!).source (fun n =>
      { n with outgoing := n.outgoing.mergeSort (byTarget g) }) }) f
  have hfirst : FlowPreserved f g ∧ g.links = f.links :=
    reorderNodeLinks_first f (f.nodes[i]!).incoming f (FlowPreserved_refl f) rfl
  have hsecond := reorderNodeLinks_second f (g.nodes[i]!).outgoing g
    hfirst.1 hfirst.2
  exact hsecond.1
/-- A single `nodes.modify` with a y-only update preserves everything `FlowPreserved`
tracks. -/
theorem FlowPreserved_modify_y (f : Flow) (i : Nat) (y0 y1 : Node → Int) :
    FlowPreserved f
      { f with nodes := f.nodes.modify i (fun n => { n with y0 := y0 n, y1 := y1 n }) } := by
  have hstep := flowModify_perm f i (fun n => { n with y0 := y0 n, y1 := y1 n })
    (fun _ => List.Perm.refl _) (fun _ => rfl) (fun _ => rfl)
  refine ⟨flowModify_size _ _ _, fun k => (hstep k).1, ?_, fun k => (hstep k).2.2⟩
  intro k
  rw [(hstep k).2.1]

/-- A single `nodes.set!` with a y-only node preserves everything `FlowPreserved`
tracks. -/
theorem FlowPreserved_set_y (f : Flow) (i : Nat) (y0 y1 : Int) :
    FlowPreserved f
      { f with nodes := f.nodes.set! i { f.nodes[i]! with y0 := y0, y1 := y1 } } := by
  refine ⟨?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · dsimp only
    rw [Array.size_set!]
  · rw [set_preserves_node_projection (List Nat) f.nodes i
      { f.nodes[i]! with y0 := y0, y1 := y1 } Node.outgoing rfl k]
  · rw [set_preserves_node_projection (List Nat) f.nodes i
      { f.nodes[i]! with y0 := y0, y1 := y1 } Node.incoming rfl k]
  · exact set_preserves_node_values f.nodes i
      { f.nodes[i]! with y0 := y0, y1 := y1 } rfl k

theorem shiftNode_preserved (f : Flow) (i : Nat) (y w alpha : Int) :
    FlowPreserved f (shiftNode f i y w alpha) := by
  unfold shiftNode
  split
  · exact FlowPreserved_refl f
  · dsimp only
    refine FlowPreserved_trans ?_ (reorderNodeLinks_preserved _ i)
    exact FlowPreserved_trans (FlowPreserved_of_nodes_eq rfl)
      (FlowPreserved_modify_y _ _ _ _)

theorem pull_preserved (f : Flow) (i : Nat) (alpha : Int) (reverse : Bool) :
    FlowPreserved f (pull f i alpha reverse) := by
  obtain ⟨y, w, safe, hpull⟩ : ∃ (y w : Int) (safe : Bool), pull f i alpha reverse =
    shiftNode { f with arithmeticFailed := f.arithmeticFailed || !safe } i y w alpha :=
    ⟨_, _, _, rfl⟩
  rw [hpull]
  exact FlowPreserved_trans (FlowPreserved_of_nodes_eq rfl)
    (shiftNode_preserved _ _ _ _ _)

/-- A single `nodes.set!` with an arbitrary node preserves `FlowPreserved` when the
replacement agrees on outgoing, incoming, and value. -/
theorem FlowPreserved_set_step (f : Flow) (i : Nat) (n : Node) (a : Bool)
    (hout : n.outgoing = (f.nodes[i]!).outgoing)
    (hin : n.incoming = (f.nodes[i]!).incoming)
    (hv : n.value = (f.nodes[i]!).value) :
    FlowPreserved f { f with nodes := f.nodes.set! i n, arithmeticFailed := a } := by
  refine ⟨?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · dsimp only
    rw [Array.size_set!]
  ·
    have e : (({ f with nodes := f.nodes.set! i n, arithmeticFailed := a }).nodes[k]!.outgoing) =
        ((f.nodes[k]!).outgoing) := by
      show ((f.nodes.set! i n)[k]!.outgoing) = _
      exact set_preserves_node_projection _ _ _ _ _ hout k
    rw [e]
  ·
    have e : (({ f with nodes := f.nodes.set! i n, arithmeticFailed := a }).nodes[k]!.incoming) =
        ((f.nodes[k]!).incoming) := by
      show ((f.nodes.set! i n)[k]!.incoming) = _
      exact set_preserves_node_projection _ _ _ _ _ hin k
    rw [e]
  ·
    have e : (({ f with nodes := f.nodes.set! i n, arithmeticFailed := a }).nodes[k]!.value) =
        ((f.nodes[k]!).value) := by
      show ((f.nodes.set! i n)[k]!).value = _
      exact set_preserves_node_values _ _ _ hv k
    rw [e]

/-- Fold combinator for `Flow × Int` state steps. -/
theorem fold_pair_flowPreserved (step : Flow × Int → Nat → Flow × Int)
    (hs : ∀ (s : Flow × Int) (i : Nat),
      FlowPreserved s.1 ((step s i).1))
    (l : List Nat) (f : Flow) (s : Flow × Int) :
    FlowPreserved f s.1 → FlowPreserved f ((l.foldl step s).1) := by
  induction l generalizing s with
  | nil =>
    intro h
    exact h
  | cons i rest ih =>
    intro h
    rw [List.foldl_cons]
    exact ih _ (FlowPreserved_trans h (hs s i))

theorem pushDown_preserved (f : Flow) (column : List Nat) (y beta : Int) :
    FlowPreserved f (pushDown f column y beta) := by
  have hstep : ∀ (s : Flow × Int) (i : Nat),
      FlowPreserved s.1 ((let n := pushDownNode (s.1.nodes[i]!) s.2 beta
        let old := s.1.nodes[i]!
        let product := (s.2 - old.y0) * beta
        let safe := [product, 2 * product, 2 * product + 65536, n.y0, n.y1,
          n.y1 + s.1.py].all fitsI64
        (({ s.1 with
          nodes := s.1.nodes.set! i n
          arithmeticFailed := s.1.arithmeticFailed || !safe } : Flow), n.y1 + s.1.py)).1) := by
    intro s i
    dsimp only
    exact FlowPreserved_set_step _ _ _ _ rfl rfl rfl
  have hfold := fold_pair_flowPreserved _ hstep column f (f, y)
  unfold pushDown
  exact hfold (FlowPreserved_refl f)

theorem pushUp_preserved (f : Flow) (column : List Nat) (y beta : Int) :
    FlowPreserved f (pushUp f column y beta) := by
  have hstep : ∀ (s : Flow × Int) (i : Nat),
      FlowPreserved s.1 ((let n := s.1.nodes[i]!
        let product := (n.y1 - s.2) * beta
        let dy := max 0 (roundHalfUp product 65536)
        let n := { n with y0 := n.y0 - dy, y1 := n.y1 - dy }
        let safe := [product, 2 * product, 2 * product + 65536, dy, n.y0, n.y1,
          n.y0 - s.1.py].all fitsI64
        (({ s.1 with
          nodes := s.1.nodes.set! i n
          arithmeticFailed := s.1.arithmeticFailed || !safe } : Flow), n.y0 - s.1.py)).1) := by
    intro s i
    dsimp only
    exact FlowPreserved_set_step _ _ _ _ rfl rfl rfl
  have hfold := fold_pair_flowPreserved _ hstep column.reverse f (f, y)
  unfold pushUp
  exact hfold (FlowPreserved_refl f)

theorem resolveCollisions_preserved (f : Flow) (column : List Nat) (beta : Int) :
    FlowPreserved f (resolveCollisions f column beta) := by
  unfold resolveCollisions
  split
  · exact FlowPreserved_refl f
  · dsimp only
    exact FlowPreserved_trans (FlowPreserved_trans (FlowPreserved_trans
      (pushUp_preserved _ _ _ _) (pushDown_preserved _ _ _ _))
      (pushUp_preserved _ _ _ _)) (pushDown_preserved _ _ _ _)

theorem settle_preserved (f : Flow) (c : Nat) (beta : Int) :
    FlowPreserved f (settle f c beta) := by
  obtain ⟨col, hset⟩ : ∃ col, settle f c beta = resolveCollisions
    { f with columns := f.columns.set! c col } col beta :=
    ⟨_, rfl⟩
  rw [hset]
  exact FlowPreserved_trans (FlowPreserved_of_nodes_eq rfl)
    (resolveCollisions_preserved _ _ _)

/-- Fold combinator for plain `Flow` state steps. -/
theorem fold_flowPreserved {α : Type} (step : Flow → α → Flow)
    (hs : ∀ (g : Flow) (i : α), FlowPreserved g (step g i))
    (l : List α) (f g : Flow) :
    FlowPreserved f g → FlowPreserved f (l.foldl step g) := by
  induction l generalizing g with
  | nil =>
    intro h
    exact h
  | cons i rest ih =>
    intro h
    rw [List.foldl_cons]
    exact ih _ (FlowPreserved_trans h (hs g i))

theorem stack_links_size (f : Flow) (column : List Nat) (ky : Int) :
    (stack f column ky).links.size = f.links.size := by
  unfold stack
  dsimp only [Id.run, Bind.bind, Id.instMonad]
  apply id_forIn_invariant (P := fun out : Flow => out.links.size = f.links.size)
  · apply id_forIn_invariant
      (P := fun state : Flow × Int => state.1.links.size = f.links.size)
    · rfl
    · intro i state hstate
      dsimp only [ForInStep.value, Bind.bind, Id.instMonad]
      apply id_forIn_invariant (P := fun out : Flow => out.links.size = f.links.size)
      · exact hstate
      · intro j out hout
        dsimp only [ForInStep.value, Pure.pure, Id.instMonad]
        simpa only [Array.size_set!] using hout
  · intro pair out hout
    exact hout

set_option maxHeartbeats 800000 in
theorem pass_preserved (f : Flow) (alpha beta : Int) (reverse : Bool) :
    FlowPreserved f (pass f alpha beta reverse) := by
  have hstep : ∀ (base g : Flow) (c : Nat), FlowPreserved base g →
      FlowPreserved base (settle
        ((g.columns[c]!).foldl
          (fun (current : Flow) (i : Nat) => pull current i alpha reverse) g) c beta) := by
    intro base g c h
    have hinner : FlowPreserved base
        ((g.columns[c]!).foldl (fun current i => pull current i alpha reverse) g) :=
      fold_flowPreserved (fun g i => pull g i alpha reverse)
        (fun g i => pull_preserved g i alpha reverse) (g.columns[c]!) base g h
    exact FlowPreserved_trans hinner (settle_preserved _ _ _)
  unfold pass
  apply fold_flowPreserved
    (fun g c => settle
      ((g.columns[c]!).foldl (fun current i => pull current i alpha reverse) g) c beta)
    (fun g c => hstep g g c (FlowPreserved_refl g))
    (if reverse then (List.range (f.columns.size - 1)).reverse
      else (List.range f.columns.size).drop 1)
    f f
  exact FlowPreserved_refl f

theorem iteration_preserved (count i : Nat) (f : Flow) :
    FlowPreserved f (iteration count i f) := by
  unfold iteration
  dsimp only
  exact FlowPreserved_trans (pass_preserved _ _ _ _)
    (pass_preserved _ _ _ _)

theorem relax_preserved (count : Nat) (f : Flow) :
    FlowPreserved f (relax count f) := by
  have h := fold_flowPreserved (fun f i => iteration count i f)
    (fun g i => iteration_preserved count i g)
    (List.range count) f f (FlowPreserved_refl f)
  unfold relax
  exact h

theorem countedRelax_preserved (count : Nat) (f : Flow) :
    FlowPreserved f (countedRelax count f).1 := by
  have e : (countedRelax count f).1 = (relax count f) := by
    rw [sankey_passes_exact]
  rw [e]
  exact relax_preserved _ _

theorem withPadding_preserved (f : Flow) : FlowPreserved f (withPadding f) :=
  FlowPreserved_of_nodes_eq rfl

theorem place_preserved (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) : FlowPreserved f out := by
  have hsize : out.nodes.size = f.nodes.size := place_nodes_size f out alignment h
  have hout : ∀ k : Nat, ((out.nodes[k]!).outgoing).Perm ((f.nodes[k]!).outgoing) := by
    intro k
    by_cases hk : k < f.nodes.size
    · rw [(place_node_payload f out alignment h k hk).2.1]
    · have hko : ¬ k < out.nodes.size := by omega
      simp only [getElem!_neg out.nodes k hko, getElem!_neg f.nodes k hk]
      exact List.Perm.refl _
  have hin : ∀ k : Nat, ((out.nodes[k]!).incoming).Perm ((f.nodes[k]!).incoming) := by
    intro k
    by_cases hk : k < f.nodes.size
    · rw [place_preserves_incoming f out alignment h k hk]
    · have hko : ¬ k < out.nodes.size := by omega
      simp only [getElem!_neg out.nodes k hko, getElem!_neg f.nodes k hk]
      exact List.Perm.refl _
  have hval : ∀ k : Nat, (out.nodes[k]!).value = (f.nodes[k]!).value := by
    intro k
    by_cases hk : k < f.nodes.size
    · exact (place_node_payload f out alignment h k hk).1
    · have hko : ¬ k < out.nodes.size := by omega
      simp only [getElem!_neg out.nodes k hko, getElem!_neg f.nodes k hk]
  exact ⟨hsize, hout, hin, hval⟩

theorem stack_preserved (f : Flow) (column : List Nat) (ky : Int) :
    FlowPreserved f (stack f column ky) := by
  have hsize : (stack f column ky).nodes.size = f.nodes.size :=
    stack_nodes_size f column ky
  have hout : ∀ k : Nat, (((stack f column ky).nodes[k]!).outgoing).Perm ((f.nodes[k]!).outgoing) := by
    intro k
    have e : ((stack f column ky).nodes[k]!.outgoing) = ((f.nodes[k]!.outgoing)) :=
      stack_node_outgoing f column ky k
    rw [e]
  have hin : ∀ k : Nat, (((stack f column ky).nodes[k]!).incoming).Perm ((f.nodes[k]!).incoming) := by
    intro k
    have e : ((stack f column ky).nodes[k]!.incoming) = ((f.nodes[k]!.incoming)) :=
      stack_node_incoming f column ky k
    rw [e]
  have hval : ∀ k : Nat, ((stack f column ky).nodes[k]!).value = (f.nodes[k]!).value :=
    stack_node_values f column ky
  exact ⟨hsize, hout, hin, hval⟩

theorem reorderLinks_preserved (f : Flow) (column : List Nat) :
    FlowPreserved f (reorderLinks f column) := by
  refine ⟨?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · exact reorderLinks_nodes_size _ _
  · exact (reorderLinks_adjacency_permutation _ _ k).2
  · exact (reorderLinks_adjacency_permutation _ _ k).1
  · exact reorderLinks_node_values _ _ k

theorem initialise_preserved (f out : Flow) (h : initialise f = .ok out) :
    FlowPreserved f out := by
  unfold initialise at h
  cases hs : scale f with
  | error e => simp [hs, Bind.bind, Except.bind] at h
  | ok ky =>
    simp [hs] at h
    cases h
    have hstep : ∀ (g : Flow) (c : List Nat), FlowPreserved f g →
        FlowPreserved f (reorderLinks (stack g c ky) c) := by
      intro g c h
      exact FlowPreserved_trans (FlowPreserved_trans h (stack_preserved _ _ _))
        (reorderLinks_preserved _ _)
    have hfold : FlowPreserved f ((f.columns.toList).foldl
        (fun g c => reorderLinks (stack g c ky) c) f) :=
      fold_flowPreserved _ (fun g c => FlowPreserved_trans (stack_preserved g c ky)
        (reorderLinks_preserved _ c)) _ f f (FlowPreserved_refl f)
    simpa only [← Array.foldl_toList] using hfold

theorem withPadding_links (f : Flow) : (withPadding f).links = f.links := rfl

theorem withPadding_nodes (f : Flow) : (withPadding f).nodes = f.nodes := rfl

theorem withPadding_columns (f : Flow) : (withPadding f).columns = f.columns := rfl

theorem place_links (f out : Flow) (alignment : String)
    (h : place f alignment = .ok out) : out.links = f.links := by
  unfold place at h
  cases hd : levels f false with
  | error e => simp [hd, Bind.bind, Except.bind] at h
  | ok depths =>
    cases hh : levels f true with
    | error e => simp [hd, hh, Bind.bind, Except.bind] at h
    | ok heights =>
      simp [hd, hh] at h
      cases h
      rfl

theorem fold_links_size (step : Flow → List Nat → Flow)
    (hs : ∀ (g : Flow) (c : List Nat), ((step g c).links.size) = (g.links.size))
    (l : List (List Nat)) (f : Flow) :
    ((l.foldl step f).links.size) = (f.links.size) := by
  induction l generalizing f with
  | nil => rfl
  | cons c rest ih =>
    skip
    rw [List.foldl_cons, ih _]
    exact hs _ _

theorem initialise_links_size (f out : Flow) (h : initialise f = .ok out) :
    out.links.size = f.links.size := by
  unfold initialise at h
  cases hs : scale f with
  | error e => simp [hs, Bind.bind, Except.bind] at h
  | ok ky =>
    simp [hs] at h
    cases h
    have hstep : ∀ (g : Flow) (c : List Nat),
        ((reorderLinks (stack g c ky) c).links.size) = (g.links.size) := by
      intro g c
      rw [reorderLinks_links, stack_links_size]
    have hfold := fold_links_size _ hstep (f.columns.toList) f
    simpa only [← Array.foldl_toList] using hfold

theorem anchorLinks_links_size (f : Flow) :
    (anchorLinks f).links.size = f.links.size := by
  have hfold : ∀ (l : List Nat) (g : Flow),
      ((l.foldl anchorStep g).links.size) = (g.links.size) := by
    intro l
    induction l with
    | nil => intro g; rfl
    | cons i rest ih =>
      intro g
      rw [List.foldl_cons]
      rw [ih _, anchorLinks_step_links_size]
  rw [anchorLinks_fold]
  exact hfold _ _

theorem countedRelax_links_size (count : Nat) (f : Flow) :
    (countedRelax count f).1.links.size = f.links.size := by
  have e : (countedRelax count f).1.links.size = ((relax count f).links.size) := by
    rw [sankey_passes_exact]
  rw [e, relax_links]

theorem initial_link_value_eq (decoded placed initial : Flow) (alignment : String)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hplace : place decoded alignment = .ok placed) (j : Nat) :
    (initial.links[j]!).value = (decoded.links[j]!).value := by
  have e1 := initialise_link_values _ _ hinitial j
  rw [e1, withPadding_links, place_links decoded placed alignment hplace]

/-- Every outgoing link of `s` in the initialised flow carries the scaled width. -/
theorem initial_outgoing_width (decoded placed initial : Flow) (alignment : String)
    (ky : Int)
    (hplace : place decoded alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (s k : Nat) (hs : s < placed.nodes.size)
    (hk : k ∈ (initial.nodes[s]!.outgoing)) :
    (initial.links[k]!).width = Int.fdiv ((initial.links[k]!).value * ky) 65536 := by
  have hperm := (initialise_preserved _ _ hinitial).2.1 s
  have hkmem : k ∈ ((withPadding placed).nodes[s]!.outgoing) :=
    (hperm.mem_iff.mp hk)
  have hkmem' : k ∈ (placed.nodes[s]!.outgoing) := by
    rwa [withPadding_nodes] at hkmem
  obtain ⟨c, hc, hmem⟩ := place_source_column decoded placed alignment hplace s hs
  have hsource : ∃ column ∈ (withPadding placed).columns.toList, s ∈ column := by
    refine ⟨c, ?_, hmem⟩
    rw [withPadding_columns]
    exact hc
  have hlink : k ∈ ((withPadding placed).nodes[s]!.outgoing) := hkmem
  exact Scaling.initialise_scales_link _ _ _ _ _ hscale hinitial hsource hlink

/-- Every node of the initialised flow has the scaled height. -/
theorem initial_node_height (decoded placed initial : Flow) (alignment : String)
    (ky : Int)
    (hplace : place decoded alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (s : Nat) (hs : s < placed.nodes.size) :
    (initial.nodes[s]!).y1 - (initial.nodes[s]!).y0 =
      Int.fdiv ((initial.nodes[s]!).value * ky) 65536 := by
  obtain ⟨c, hc, hmem⟩ := place_source_column decoded placed alignment hplace s hs
  have hsource : ∃ column ∈ (withPadding placed).columns.toList, s ∈ column := by
    refine ⟨c, ?_, hmem⟩
    rw [withPadding_columns]
    exact hc
  exact Scaling.initialise_scales_node _ _ _ _ hscale hinitial hsource

/-- A fold over columns preserves a per-link projection. -/
theorem fold_links_proj (step : Flow → List Nat → Flow) (project : Link → Nat)
    (hs : ∀ (g : Flow) (c : List Nat) (j : Nat),
      project ((step g c).links[j]!) = project (g.links[j]!))
    (l : List (List Nat)) (f : Flow) (j : Nat) :
    project ((l.foldl step f).links[j]!) = project (f.links[j]!) := by
  induction l generalizing f with
  | nil => rfl
  | cons c rest ih =>
    skip
    rw [List.foldl_cons, ih _]
    exact hs f c j

theorem initialise_links_source (f out : Flow) (h : initialise f = .ok out)
    (j : Nat) : (out.links[j]!).source = (f.links[j]!).source := by
  unfold initialise at h
  cases hs : scale f with
  | error e => simp [hs, Bind.bind, Except.bind] at h
  | ok ky =>
    simp [hs] at h
    cases h
    have hstep : ∀ (g : Flow) (c : List Nat) (j : Nat),
        ((reorderLinks (stack g c ky) c).links[j]!).source = ((g.links[j]!).source) := by
      intro g c j
      rw [reorderLinks_links]
      exact stack_links_source _ _ _ _
    have hfold := fold_links_proj _ _ hstep (f.columns.toList) f j
    simpa only [← Array.foldl_toList] using hfold

theorem initialise_links_target (f out : Flow) (h : initialise f = .ok out)
    (j : Nat) : (out.links[j]!).target = (f.links[j]!).target := by
  unfold initialise at h
  cases hs : scale f with
  | error e => simp [hs, Bind.bind, Except.bind] at h
  | ok ky =>
    simp [hs] at h
    cases h
    have hstep : ∀ (g : Flow) (c : List Nat) (j : Nat),
        ((reorderLinks (stack g c ky) c).links[j]!).target = ((g.links[j]!).target) := by
      intro g c j
      rw [reorderLinks_links]
      exact stack_links_target _ _ _ _
    have hfold := fold_links_proj _ _ hstep (f.columns.toList) f j
    simpa only [← Array.foldl_toList] using hfold

/-- Incidence transfers across a node-preserving stage with equal link endpoints. -/
theorem incidence_of_preserved (f g : Flow)
    (hperm : ∀ k : Nat, ((g.nodes[k]!).outgoing).Perm ((f.nodes[k]!).outgoing))
    (hpermIn : ∀ k : Nat, ((g.nodes[k]!).incoming).Perm ((f.nodes[k]!).incoming))
    (hsize : g.links.size = f.links.size)
    (hsrc : ∀ j : Nat, (g.links[j]!).source = (f.links[j]!).source)
    (htgt : ∀ j : Nat, (g.links[j]!).target = (f.links[j]!).target)
    (hinc : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k))
    (hgsize : g.nodes.size = f.nodes.size) :
    ∀ k, k < g.nodes.size →
      (∀ x, x ∈ (g.nodes[k]!).incoming ↔ x < g.links.size ∧ (g.links[x]!).target = k) ∧
      (∀ x, x ∈ (g.nodes[k]!).outgoing ↔ x < g.links.size ∧ (g.links[x]!).source = k) := by
  intro k hk
  have hkf : k < f.nodes.size := by omega
  obtain ⟨h1, h2⟩ := hinc k hkf
  constructor
  · intro x
    constructor
    · intro hmem
      have hmem' : x ∈ (f.nodes[k]!.incoming) := ((hpermIn k).mem_iff.mp hmem)
      obtain ⟨hlt, htg⟩ := (h1 x).mp hmem'
      exact ⟨by simpa only [hsize] using hlt, (htgt x).trans htg⟩
    · intro hmem
      obtain ⟨hlt, htg⟩ := hmem
      have hlt' : x < f.links.size := by omega
      have htg' : (f.links[x]!).target = k := by rw [← htgt x]; exact htg
      exact (hpermIn k).mem_iff.mpr ((h1 x).mpr ⟨hlt', htg'⟩)
  · intro x
    constructor
    · intro hmem
      have hmem' : x ∈ (f.nodes[k]!.outgoing) := ((hperm k).mem_iff.mp hmem)
      obtain ⟨hlt, hsg⟩ := (h2 x).mp hmem'
      exact ⟨by simpa only [hsize] using hlt, (hsrc x).trans hsg⟩
    · intro hmem
      obtain ⟨hlt, hsg⟩ := hmem
      have hlt' : x < f.links.size := by omega
      have hsg' : (f.links[x]!).source = k := by rw [← hsrc x]; exact hsg
      exact (hperm k).mem_iff.mpr ((h2 x).mpr ⟨hlt', hsg'⟩)

theorem withPadding_incidence (f : Flow)
    (hadj : ∀ k, k < f.nodes.size →
      (∀ x, x ∈ (f.nodes[k]!).incoming ↔ x < f.links.size ∧ (f.links[x]!).target = k) ∧
        (∀ x, x ∈ (f.nodes[k]!).outgoing ↔ x < f.links.size ∧ (f.links[x]!).source = k)) :
    ∀ k, k < (withPadding f).nodes.size →
      (∀ x, x ∈ ((withPadding f).nodes[k]!).incoming ↔
        x < (withPadding f).links.size ∧ ((withPadding f).links[x]!).target = k) ∧
      (∀ x, x ∈ ((withPadding f).nodes[k]!).outgoing ↔
        x < (withPadding f).links.size ∧ ((withPadding f).links[x]!).source = k) := by
  intro k hk
  have hkf : k < f.nodes.size := by rwa [withPadding_nodes] at hk
  rw [withPadding_nodes, withPadding_links]
  exact hadj k hkf

theorem sceneOf_routes_spec (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) :
    ∀ r ∈ (sceneOf m f rects labels width height).routes,
      ∃ (i : Nat) (mr : ModelRoute),
        m.routes[i]? = some mr ∧ r.fromId = mr.fromId ∧ r.toId = mr.toId ∧
          r.points =

            [⟨(rects[(f.links[i]!).source]!).x + (rects[(f.links[i]!).source]!).w,
                (f.links[i]!).y0⟩,
              ⟨(rects[(f.links[i]!).target]!).x, (f.links[i]!).y1⟩] := by
  intro r hr
  simp only [sceneOf, List.mem_map] at hr
  obtain ⟨⟨mr, i⟩, hi, rfl⟩ := hr
  exact ⟨i, mr, List.mk_mem_zipIdx_iff_getElem?.mp hi, rfl, rfl, rfl⟩

theorem nodeRects_y (f : Flow) (width nodeWidth : Int) (i : Nat)
    (hi : i < f.nodes.size) :
    ((nodeRects f width nodeWidth)[i]!).y = (f.nodes[i]!).y0 := by
  have hr : i < (nodeRects f width nodeWidth).size := by
    simpa only [nodeRects_size] using hi
  rw [getElem!_pos _ i hr, getElem!_pos f.nodes i hi]
  simp only [nodeRects, Array.getElem_map]

theorem nodeRects_w (f : Flow) (width nodeWidth : Int) (i : Nat)
    (hi : i < f.nodes.size) :
    ((nodeRects f width nodeWidth)[i]!).w = nodeWidth := by
  have hr : i < (nodeRects f width nodeWidth).size := by
    simpa only [nodeRects_size] using hi
  rw [getElem!_pos (nodeRects f width nodeWidth) i hr]
  simp only [nodeRects, Array.getElem_map]

/-- Normalization shifts link and rectangle `y` coordinates by the same amount, and
preserves widths and heights, so `y`-offsets relative to node rectangles cancel. -/
theorem normalization_offset_cancel (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int) (i k : Nat)
    (hi : i < f.links.size) (hk : k < rects.size) :
    (((normalize f rects labels width height).1.links[i]!).y0 -
      ((normalize f rects labels width height).2.1[k]!).y =
      (f.links[i]!).y0 - (rects[k]!).y) ∧
    (((normalize f rects labels width height).1.links[i]!).y1 -
      ((normalize f rects labels width height).2.1[k]!).y =
      (f.links[i]!).y1 - (rects[k]!).y) ∧
    (((normalize f rects labels width height).2.1[k]!).w = (rects[k]!).w) ∧
    (((normalize f rects labels width height).2.1[k]!).h = (rects[k]!).h) := by
  have hi' : i < (normalize f rects labels width height).1.links.size := by
    simpa only [normalize_preserves_link_count] using hi
  have hk' : k < (normalize f rects labels width height).2.1.size := by
    simpa only [normalize_preserves_node_count] using hk
  rw [getElem!_pos (normalize f rects labels width height).1.links i hi',
    getElem!_pos (normalize f rects labels width height).2.1 k hk',
    getElem!_pos f.links i hi, getElem!_pos rects k hk]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [normalize, Array.getElem_map] <;> omega

/-- Full incidence for the initialised flow, transferred from the decoded model. -/
theorem initial_incidence (m : Model) (extent padding : Int)
    (decoded placed : Flow) (alignment : String)
    (hdecode : decode m extent padding = .ok decoded)
    (hplace : place decoded alignment = .ok placed)
    (initial : Flow)
    (hinitial : initialise (withPadding placed) = .ok initial) :
    ∀ k, k < initial.nodes.size →
      (∀ x, x ∈ (initial.nodes[k]!).incoming ↔
        x < initial.links.size ∧ (initial.links[x]!).target = k) ∧
      (∀ x, x ∈ (initial.nodes[k]!).outgoing ↔
        x < initial.links.size ∧ (initial.links[x]!).source = k) := by
  have hdec := decode_adjacency_incidence m extent padding decoded hdecode
  have hpl := place_incidence decoded placed alignment hplace hdec
  have hpw := withPadding_incidence placed hpl
  have hF := initialise_preserved _ _ hinitial
  obtain ⟨hsF, hoF, hiF, hvF⟩ := hF
  have hsrc : ∀ j : Nat, (initial.links[j]!).source = ((withPadding placed).links[j]!).source := by
    intro j
    exact initialise_links_source _ _ hinitial j
  have htgt : ∀ j : Nat, (initial.links[j]!).target = ((withPadding placed).links[j]!).target := by
    intro j
    exact initialise_links_target _ _ hinitial j
  have hsize : initial.links.size = (withPadding placed).links.size :=
    initialise_links_size _ _ hinitial
  have hgsize : initial.nodes.size = (withPadding placed).nodes.size := hsF
  exact incidence_of_preserved _ _ hoF hiF hsize hsrc htgt hpw hgsize

theorem pre_incidence (m : Model) (extent padding : Int)
    (decoded placed initial : Flow) (alignment : String) (ky : Int) (count : Nat)
    (_hdecode : decode m extent padding = .ok decoded)
    (_hplace : place decoded alignment = .ok placed)
    (_hscale : scale (withPadding placed) = .ok ky)
    (_hinitial : initialise (withPadding placed) = .ok initial)
    (hinc0 : ∀ k, k < initial.nodes.size →
      (∀ x, x ∈ (initial.nodes[k]!).incoming ↔
        x < initial.links.size ∧ (initial.links[x]!).target = k) ∧
      (∀ x, x ∈ (initial.nodes[k]!).outgoing ↔
        x < initial.links.size ∧ (initial.links[x]!).source = k)) :
    ∀ k, k < ((countedRelax count initial).1).nodes.size →
      (∀ x, x ∈ (((countedRelax count initial).1).nodes[k]!).incoming ↔
        x < ((countedRelax count initial).1).links.size ∧
          (((countedRelax count initial).1).links[x]!).target = k) ∧
      (∀ x, x ∈ (((countedRelax count initial).1).nodes[k]!).outgoing ↔
        x < ((countedRelax count initial).1).links.size ∧
          (((countedRelax count initial).1).links[x]!).source = k) := by
  have hF := countedRelax_preserved count initial
  obtain ⟨hsF, hoF, hiF, _⟩ := hF
  have hpre : ((countedRelax count initial).1).links = initial.links := by
    rw [show (countedRelax count initial).1 = relax count initial from by
      rw [sankey_passes_exact]]
    exact relax_links _ _
  have hsize : ((countedRelax count initial).1).links.size = initial.links.size := by
    rw [hpre]
  have hsrc : ∀ j : Nat, (((countedRelax count initial).1).links[j]!).source =
      (initial.links[j]!).source := by
    intro j
    rw [hpre]
  have htgt : ∀ j : Nat, (((countedRelax count initial).1).links[j]!).target =
      (initial.links[j]!).target := by
    intro j
    rw [hpre]
  have hgsize : ((countedRelax count initial).1).nodes.size = initial.nodes.size := hsF
  exact incidence_of_preserved _ _ hoF hiF hsize hsrc htgt hinc0 hgsize

/-- Every incoming link of `t` carries the scaled width in the final flow. -/
theorem placed_initialise_final_incoming_link_width (m : Model) (extent padding : Int)
    (f placed initial : Flow) (alignment : String) (ky : Int) (count target j : Nat)
    (hdecode : decode m extent padding = .ok f)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hadj : ∀ k, k < placed.nodes.size →
      (∀ x, x ∈ (placed.nodes[k]!).incoming ↔ x < placed.links.size ∧ (placed.links[x]!).target = k) ∧
        (∀ x, x ∈ (placed.nodes[k]!).outgoing ↔ x < placed.links.size ∧ (placed.links[x]!).source = k))
    (htarget : target < placed.nodes.size)
    (hj : j ∈ (placed.nodes[target]!).incoming) :
    ((anchorLinks (countedRelax count initial).1).links[j]!).width =
      Int.fdiv ((initial.links[j]!).value * ky) 65536 := by
  have hout : ((anchorLinks (countedRelax count initial).1).links[j]!).width =
      (initial.links[j]!).width := by
    have hd := congrArg (fun data : Nat × Nat × Int × Int => data.2.2.2)
      (final_linkData initial count j)
    exact hd
  rw [hout]
  obtain ⟨hlt, hteq⟩ := ((hadj target htarget).1 j).mp hj
  have hjsize : j < f.links.size := by
    have e1 : placed.links.size = f.links.size :=
      congrArg Array.size (place_links f placed alignment hplace)
    omega
  have hsrc_eq : (placed.links[j]!).source = (f.links[j]!).source := by
    rw [place_links f placed alignment hplace]
  have hsb : (f.links[j]!).source < m.boxes.length := by
    have hmem : f.links[j]! ∈ f.links.toList := by
      rw [getElem!_pos f.links j hjsize]
      exact Array.getElem_mem_toList hjsize
    exact (decode_link_bounds m extent padding f hdecode _ hmem).2.1
  have hssize : (placed.links[j]!).source < placed.nodes.size := by
    have e1 : placed.nodes.size = f.nodes.size := place_nodes_size f placed alignment hplace
    have e2 : f.nodes.size = m.boxes.length := decode_nodes_size m extent padding f hdecode
    omega
  obtain ⟨c, hc, hmem⟩ := place_source_column f placed alignment hplace _ hssize
  have hsource : ∃ column ∈ (withPadding placed).columns.toList,
      (placed.links[j]!).source ∈ column := by
    refine ⟨c, ?_, hmem⟩
    rw [withPadding_columns]
    exact hc
  have hlink : j ∈ ((withPadding placed).nodes[(placed.links[j]!).source]!.outgoing) := by
    have e : ((withPadding placed).nodes[(placed.links[j]!).source]!.outgoing) =
        ((placed.nodes[(placed.links[j]!).source]!).outgoing) := by
      rw [withPadding_nodes]
    rw [e]
    exact ((hadj _ hssize).2 j).mpr ⟨hlt, rfl⟩
  exact Scaling.initialise_scales_link _ _ _ _ _ hscale hinitial hsource hlink

theorem placed_initialise_final_incoming_width_sum (m : Model) (extent padding : Int)
    (f placed initial : Flow) (alignment : String) (ky : Int) (count target : Nat)
    (hdecode : decode m extent padding = .ok f)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hadj : ∀ k, k < placed.nodes.size →
      (∀ x, x ∈ (placed.nodes[k]!).incoming ↔ x < placed.links.size ∧ (placed.links[x]!).target = k) ∧
        (∀ x, x ∈ (placed.nodes[k]!).outgoing ↔ x < placed.links.size ∧ (placed.links[x]!).source = k))
    (htarget : target < placed.nodes.size) :
    ((placed.nodes[target]!).incoming.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum =
      scaledSum ((placed.nodes[target]!).incoming.map
        (fun j => (initial.links[j]!).value)) ky := by
  simp only [scaledSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  exact placed_initialise_final_incoming_link_width m extent padding f placed initial
    alignment ky count target j hdecode hplace hscale hinitial hadj htarget hj

theorem placed_initialise_final_incoming_capacity (f placed initial : Flow)
    (alignment : String) (ky : Int) (count target : Nat)
    (_hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (_hinitial : initialise (withPadding placed) = .ok initial)
    (_htarget : target < placed.nodes.size)
    (hwidth : ((placed.nodes[target]!).incoming.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum =
      scaledSum ((placed.nodes[target]!).incoming.map
        (fun j => (initial.links[j]!).value)) ky)
    (hheight : ((anchorLinks (countedRelax count initial).1).nodes[target]!).y1 -
      ((anchorLinks (countedRelax count initial).1).nodes[target]!).y0 =
        Int.fdiv ((initial.nodes[target]!).value * ky) 65536)
    (hvalue : ((placed.nodes[target]!).incoming.map
      (fun j => (initial.links[j]!).value)).sum ≤ (initial.nodes[target]!).value) :
    ((placed.nodes[target]!).incoming.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum ≤
        ((anchorLinks (countedRelax count initial).1).nodes[target]!).y1 -
          ((anchorLinks (countedRelax count initial).1).nodes[target]!).y0 := by
  rw [hwidth, hheight]
  exact linkWidths_le_nodeHeight _ _ ky hvalue
    (scale_nonnegative (withPadding placed) ky hscale)

theorem decode_placed_final_incoming_capacity (m : Model) (extent padding : Int)
    (f placed initial : Flow) (alignment : String) (ky : Int) (count target : Nat)
    (hdecode : decode m extent padding = .ok f)
    (hplace : place f alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (htarget : target < f.nodes.size) :
    ((placed.nodes[target]!).incoming.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum ≤
        ((anchorLinks (countedRelax count initial).1).nodes[target]!).y1 -
          ((anchorLinks (countedRelax count initial).1).nodes[target]!).y0 := by
  have htsize : target < placed.nodes.size := by
    have e := place_nodes_size f placed alignment hplace
    omega
  have hadj := place_incidence f placed alignment hplace
    (decode_adjacency_incidence m extent padding f hdecode)
  have hwidth := placed_initialise_final_incoming_width_sum m extent padding f placed initial
    alignment ky count target hdecode hplace hscale hinitial hadj htsize
  have hheight := placed_initialise_final_node_height f placed initial alignment ky
    count target hplace hscale hinitial (by simpa only [place_nodes_size f placed alignment hplace] using htsize)
  apply placed_initialise_final_incoming_capacity f placed initial alignment ky count target
    hplace hscale hinitial htsize hwidth hheight
  have hp := place_node_payload f placed alignment hplace target htarget
  have hpin := place_preserves_incoming f placed alignment hplace target htarget
  have hv := initialise_node_values (withPadding placed) initial hinitial target
  change (initial.nodes[target]!).value = (placed.nodes[target]!).value at hv
  rw [hv, hp.1]
  have hsum :
      ((placed.nodes[target]!).incoming.map (fun j => (initial.links[j]!).value)).sum =
        ((f.nodes[target]!).incoming.map (fun j => (f.links[j]!).value)).sum := by
    rw [hpin]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    exact initial_link_value_eq f placed initial alignment hinitial hplace j
  rw [hsum]
  exact decode_incoming_value_bound m extent padding f hdecode target htarget

theorem sceneOf_c5 (m : Model) (f : Flow) (rects : Array Rect)
    (labels : List LabelPlacement) (width height : Int)
    (hids : (m.boxes.map (·.id)).Nodup)
    (hsrc : ∀ i, i < m.routes.length → ∀ mr, m.routes[i]? = some mr →
      ∃ s, m.boxes[(f.links[i]!).source]? = some s ∧ s.id = mr.fromId)
    (htgt : ∀ i, i < m.routes.length → ∀ mr, m.routes[i]? = some mr →
      ∃ t, m.boxes[(f.links[i]!).target]? = some t ∧ t.id = mr.toId)
    (hws : ∀ i, i < m.boxes.length → 0 ≤ (rects[i]!).w)
    (hoff : ∀ i, i < m.routes.length →
      0 ≤ (f.links[i]!).y0 - (rects[(f.links[i]!).source]!).y ∧
        (f.links[i]!).y0 - (rects[(f.links[i]!).source]!).y ≤
          (rects[(f.links[i]!).source]!).h ∧
        0 ≤ (f.links[i]!).y1 - (rects[(f.links[i]!).target]!).y ∧
        (f.links[i]!).y1 - (rects[(f.links[i]!).target]!).y ≤
          (rects[(f.links[i]!).target]!).h) :
    Validator.C5 (sceneOf m f rects labels width height).layoutDump := by
  intro r hr
  obtain ⟨i, mr, hget, hfrom, hto, hpts⟩ := sceneOf_routes_spec m f rects labels width height r hr
  have hi : i < m.routes.length := (List.getElem?_eq_some_iff.mp hget).1
  obtain ⟨s, hs, hsid⟩ := hsrc i hi mr hget
  obtain ⟨t, htt, htid⟩ := htgt i hi mr hget
  have hsi : (f.links[i]!).source < m.boxes.length := (List.getElem?_eq_some_iff.mp hs).1
  have hti : (f.links[i]!).target < m.boxes.length := (List.getElem?_eq_some_iff.mp htt).1
  have hoffi := hoff i hi
  obtain ⟨sb, tb, hlookS, hlookT, hbS, hbT⟩ :=
    scene_endpoint_boundaries m f rects labels width height hids s t
      ((f.links[i]!).source) ((f.links[i]!).target) hs htt
      ((f.links[i]!).y0 - (rects[(f.links[i]!).source]!).y)
      ((f.links[i]!).y1 - (rects[(f.links[i]!).target]!).y)
      (hws _ hsi) (hws _ hti)
      ⟨hoffi.1, hoffi.2.1⟩ ⟨hoffi.2.2.1, hoffi.2.2.2⟩
  refine ⟨⟨(rects[(f.links[i]!).source]!).x + (rects[(f.links[i]!).source]!).w,
      (f.links[i]!).y0⟩,
    ⟨(rects[(f.links[i]!).target]!).x, (f.links[i]!).y1⟩, sb, tb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpts]; rfl
  · rw [hpts]; rfl
  · rw [hfrom, ← hsid]; exact hlookS
  · rw [hto, ← htid]; exact hlookT

  · have hp : (⟨(rects[(f.links[i]!).source]!).x + (rects[(f.links[i]!).source]!).w,
        (f.links[i]!).y0⟩ : Point) =
        ⟨(rects[(f.links[i]!).source]!).x + (rects[(f.links[i]!).source]!).w,
          (rects[(f.links[i]!).source]!).y +
            ((f.links[i]!).y0 - (rects[(f.links[i]!).source]!).y)⟩ := by
      congr 1; omega
    rw [hp]; exact hbS
  · have hp : (⟨(rects[(f.links[i]!).target]!).x, (f.links[i]!).y1⟩ : Point) =
        ⟨(rects[(f.links[i]!).target]!).x,
          (rects[(f.links[i]!).target]!).y +
            ((f.links[i]!).y1 - (rects[(f.links[i]!).target]!).y)⟩ := by
      congr 1; omega
    rw [hp]; exact hbT


/-- The outgoing width sum bound transfers from the placed model to the relaxed flow. -/
theorem pre_outgoing_capacity (m : Model) (extent padding : Int)
    (decoded placed initial : Flow) (alignment : String) (ky : Int) (count source : Nat)
    (hdecode : decode m extent padding = .ok decoded)
    (hplace : place decoded alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (hsource : source < decoded.nodes.size) :
    ((countedRelax count initial).1.nodes[source]!.outgoing.map
      (fun j => (countedRelax count initial).1.links[j]!.width)).sum ≤
      (countedRelax count initial).1.nodes[source]!.y1 -
        (countedRelax count initial).1.nodes[source]!.y0 := by
  have hcap := decode_placed_final_outgoing_capacity m extent padding decoded placed
    initial alignment ky count source hdecode hplace hscale hinitial hsource
  have hpre : (countedRelax count initial).1.links = initial.links := by
    rw [show (countedRelax count initial).1 = relax count initial from by
      rw [sankey_passes_exact]]
    exact relax_links _ _
  have hperm1 := (countedRelax_preserved count initial).2.1 source
  have hperm2 := (initialise_preserved _ _ hinitial).2.1 source
  have eN : ((withPadding placed).nodes[source]!.outgoing) =
      ((placed.nodes[source]!.outgoing)) := by
    rw [withPadding_nodes]
  rw [eN] at hperm2
  have hperm : (((countedRelax count initial).1.nodes[source]!).outgoing).Perm
      ((placed.nodes[source]!).outgoing) :=
    hperm1.trans hperm2
  have hW : ∀ j ∈ (countedRelax count initial).1.nodes[source]!.outgoing,
      (countedRelax count initial).1.links[j]!.width =
        ((anchorLinks (countedRelax count initial).1).links[j]!).width := by
    intro j hj
    have e1 : ((countedRelax count initial).1.links[j]!.width = (initial.links[j]!).width) := by
      rw [hpre]
    have e2 : (((anchorLinks (countedRelax count initial).1).links[j]!).width =
        (initial.links[j]!).width) := by
      have hd := congrArg (fun data : Nat × Nat × Int × Int => data.2.2.2)
        (final_linkData initial count j)
      exact hd
    rw [e1, e2]
  have e_sum : ((placed.nodes[source]!).outgoing.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum =
      (((countedRelax count initial).1.nodes[source]!).outgoing.map
      (fun j => ((countedRelax count initial).1.links[j]!).width)).sum := by
    have e1 : (((countedRelax count initial).1.nodes[source]!).outgoing.map
        (fun j => ((countedRelax count initial).1.links[j]!).width)).sum =
        (((countedRelax count initial).1.nodes[source]!).outgoing.map
        (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro j hj
      exact hW j hj
    have e2 := perm_sum_eq (hperm.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width))
    exact (e1.trans e2).symm
  have e_height :
      ((anchorLinks (countedRelax count initial).1).nodes[source]!).y1 -
        ((anchorLinks (countedRelax count initial).1).nodes[source]!).y0 =
      (countedRelax count initial).1.nodes[source]!.y1 -
        (countedRelax count initial).1.nodes[source]!.y0 := by
    rw [anchorLinks_nodes]
  rw [e_sum, e_height] at hcap
  exact hcap

/-- The incoming width sum bound transfers from the placed model to the relaxed flow. -/
theorem pre_incoming_capacity (m : Model) (extent padding : Int)
    (decoded placed initial : Flow) (alignment : String) (ky : Int) (count target : Nat)
    (hdecode : decode m extent padding = .ok decoded)
    (hplace : place decoded alignment = .ok placed)
    (hscale : scale (withPadding placed) = .ok ky)
    (hinitial : initialise (withPadding placed) = .ok initial)
    (htarget : target < decoded.nodes.size) :
    ((countedRelax count initial).1.nodes[target]!.incoming.map
      (fun j => (countedRelax count initial).1.links[j]!.width)).sum ≤
      (countedRelax count initial).1.nodes[target]!.y1 -
        (countedRelax count initial).1.nodes[target]!.y0 := by
  have hcap := decode_placed_final_incoming_capacity m extent padding decoded placed
    initial alignment ky count target hdecode hplace hscale hinitial htarget
  have hpre : (countedRelax count initial).1.links = initial.links := by
    rw [show (countedRelax count initial).1 = relax count initial from by
      rw [sankey_passes_exact]]
    exact relax_links _ _
  have hperm1 := (countedRelax_preserved count initial).2.2.1 target
  have hperm2 := (initialise_preserved _ _ hinitial).2.2.1 target
  have eN : ((withPadding placed).nodes[target]!.incoming) =
      ((placed.nodes[target]!.incoming)) := by
    rw [withPadding_nodes]
  rw [eN] at hperm2
  have hperm : (((countedRelax count initial).1.nodes[target]!).incoming).Perm
      ((placed.nodes[target]!).incoming) :=
    hperm1.trans hperm2
  have hW : ∀ j ∈ (countedRelax count initial).1.nodes[target]!.incoming,
      (countedRelax count initial).1.links[j]!.width =
        ((anchorLinks (countedRelax count initial).1).links[j]!).width := by
    intro j hj
    have e1 : ((countedRelax count initial).1.links[j]!.width = (initial.links[j]!).width) := by
      rw [hpre]
    have e2 : (((anchorLinks (countedRelax count initial).1).links[j]!).width =
        (initial.links[j]!).width) := by
      have hd := congrArg (fun data : Nat × Nat × Int × Int => data.2.2.2)
        (final_linkData initial count j)
      exact hd
    rw [e1, e2]
  have e_sum : ((placed.nodes[target]!).incoming.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum =
      (((countedRelax count initial).1.nodes[target]!).incoming.map
      (fun j => ((countedRelax count initial).1.links[j]!).width)).sum := by
    have e1 : (((countedRelax count initial).1.nodes[target]!).incoming.map
        (fun j => ((countedRelax count initial).1.links[j]!).width)).sum =
        (((countedRelax count initial).1.nodes[target]!).incoming.map
        (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro j hj
      exact hW j hj
    have e2 := perm_sum_eq (hperm.map
      (fun j => ((anchorLinks (countedRelax count initial).1).links[j]!).width))
    exact (e1.trans e2).symm
  have e_height :
      ((anchorLinks (countedRelax count initial).1).nodes[target]!).y1 -
        ((anchorLinks (countedRelax count initial).1).nodes[target]!).y0 =
      (countedRelax count initial).1.nodes[target]!.y1 -
        (countedRelax count initial).1.nodes[target]!.y0 := by
    rw [anchorLinks_nodes]
  rw [e_sum, e_height] at hcap
  exact hcap

theorem run_endpoint_indices (decoded flowed : Flow) (alignment : String) (count : Nat)
    (hrun : run decoded alignment count = .ok flowed) (j : Nat) :
    flowed.links[j]!.source = decoded.links[j]!.source ∧
      flowed.links[j]!.target = decoded.links[j]!.target := by
  obtain ⟨placed, initial, ky, hp, _, hi, _, hout, _, _⟩ :=
    run_common_scale decoded flowed alignment count hrun
  rw [hout]
  have hd := final_linkData initial count j
  have hs := congrArg (fun d : Nat × Nat × Int × Int => d.1) hd
  have ht := congrArg (fun d : Nat × Nat × Int × Int => d.2.1) hd
  dsimp only [linkData] at hs ht
  rw [hs, ht, initialise_links_source _ _ hi,
    initialise_links_target _ _ hi, withPadding_links,
    place_links decoded placed alignment hp]
  exact ⟨rfl, rfl⟩

theorem run_links_size (decoded flowed : Flow) (alignment : String) (count : Nat)
    (hrun : run decoded alignment count = .ok flowed) :
    flowed.links.size = decoded.links.size := by
  obtain ⟨placed, initial, ky, hp, _, hi, _, hout, _, _⟩ :=
    run_common_scale decoded flowed alignment count hrun
  rw [hout, anchorLinks_links_size, countedRelax_links_size,
    initialise_links_size _ _ hi, withPadding_links,
    place_links decoded placed alignment hp]

theorem run_anchor_offsets (m : Model) (extent padding : Int)
    (decoded flowed : Flow) (alignment : String) (count : Nat)
    (hdecode : decode m extent padding = .ok decoded)
    (hrun : run decoded alignment count = .ok flowed)
    (j : Nat) (hj : j < m.routes.length) :
    0 ≤ flowed.links[j]!.y0 - flowed.nodes[flowed.links[j]!.source]!.y0 ∧
      flowed.links[j]!.y0 - flowed.nodes[flowed.links[j]!.source]!.y0 ≤
        flowed.nodes[flowed.links[j]!.source]!.y1 -
          flowed.nodes[flowed.links[j]!.source]!.y0 ∧
      0 ≤ flowed.links[j]!.y1 - flowed.nodes[flowed.links[j]!.target]!.y0 ∧
      flowed.links[j]!.y1 - flowed.nodes[flowed.links[j]!.target]!.y0 ≤
        flowed.nodes[flowed.links[j]!.target]!.y1 -
          flowed.nodes[flowed.links[j]!.target]!.y0 := by
  obtain ⟨placed, initial, ky, hp, hk, hi, hky, hout, _, _⟩ :=
    run_common_scale decoded flowed alignment count hrun
  let pre := (countedRelax count initial).1
  have hprelinks : pre.links = initial.links := by
    dsimp only [pre]
    rw [sankey_passes_exact, relax_links]
  have hpres : FlowPreserved decoded pre :=
    FlowPreserved_trans (place_preserved decoded placed alignment hp)
      (FlowPreserved_trans (withPadding_preserved placed)
        (FlowPreserved_trans (initialise_preserved _ _ hi)
          (countedRelax_preserved count initial)))
  have hps (i : Nat) : pre.links[i]!.source = decoded.links[i]!.source := by
    rw [hprelinks, initialise_links_source _ _ hi, withPadding_links,
      place_links decoded placed alignment hp]
  have hpt (i : Nat) : pre.links[i]!.target = decoded.links[i]!.target := by
    rw [hprelinks, initialise_links_target _ _ hi, withPadding_links,
      place_links decoded placed alignment hp]
  have hls : pre.links.size = decoded.links.size := by
    rw [hprelinks, initialise_links_size _ _ hi, withPadding_links,
      place_links decoded placed alignment hp]
  have hinc := pre_incidence m extent padding decoded placed initial alignment ky count
    hdecode hp hk hi (initial_incidence m extent padding decoded placed alignment
      hdecode hp initial hi)
  change ∀ k, k < pre.nodes.size → _ at hinc
  have hjd : j < decoded.links.size := by
    rw [decode_links_size m extent padding decoded hdecode]
    exact hj
  have hjp : j < pre.links.size := by omega
  have hb := decode_link_bounds m extent padding decoded hdecode
    decoded.links[j] (Array.getElem_mem_toList hjd)
  rw [← getElem!_pos decoded.links j hjd] at hb
  have hns := decode_nodes_size m extent padding decoded hdecode
  have hs : pre.links[j]!.source < pre.nodes.size := by
    rw [hps, hpres.1, hns]
    exact hb.2.1
  have ht : pre.links[j]!.target < pre.nodes.size := by
    rw [hpt, hpres.1, hns]
    exact hb.2.2
  have hnd (k : Nat) (hkn : k < pre.nodes.size) :
      pre.nodes[k]!.incoming.Nodup ∧ pre.nodes[k]!.outgoing.Nodup := by
    have hkd : k < decoded.nodes.size := by
      rw [← hpres.1]
      exact hkn
    have hd := decode_adjacency_nodup m extent padding decoded hdecode
      decoded.nodes[k] (Array.getElem_mem_toList hkd)
    rw [← getElem!_pos decoded.nodes k hkd] at hd
    exact ⟨(hpres.2.2.1 k).nodup_iff.mpr hd.1,
      (hpres.2.1 k).nodup_iff.mpr hd.2⟩
  have hw (i : Nat) (hip : i < pre.links.size) : 0 ≤ pre.links[i]!.width := by
    have hid : i < decoded.links.size := by omega
    have hbi := decode_link_bounds m extent padding decoded hdecode
      decoded.links[i] (Array.getElem_mem_toList hid)
    rw [← getElem!_pos decoded.links i hid] at hbi
    have his : pre.links[i]!.source < pre.nodes.size := by
      rw [hps, hpres.1, hns]
      exact hbi.2.1
    have hmem := ((hinc _ his).2 i).mpr ⟨hip, rfl⟩
    have hmemI : i ∈ initial.nodes[pre.links[i]!.source]!.outgoing :=
      ((countedRelax_preserved count initial).2.1 _).mem_iff.mp hmem
    have hplaceSize := place_nodes_size decoded placed alignment hp
    have hisPlaced : pre.links[i]!.source < placed.nodes.size := by
      rw [hplaceSize, ← hpres.1]
      exact his
    have hwidth := initial_outgoing_width decoded placed initial alignment ky
      hp hk hi _ i hisPlaced hmemI
    rw [hprelinks, hwidth, initial_link_value_eq decoded placed initial alignment hi hp]
    exact rounding_nonnegative _ ky
      (decode_indexed_link_nonnegative m extent padding decoded hdecode i) hky
  have hsD : pre.links[j]!.source < decoded.nodes.size := by
    rw [← hpres.1]
    exact hs
  have htD : pre.links[j]!.target < decoded.nodes.size := by
    rw [← hpres.1]
    exact ht
  have ho := anchorLinks_node_out_y0 pre (pre.links[j]!.source) j rfl
    (((hinc _ hs).2 j).mpr ⟨hjp, rfl⟩) hs hinc (hnd _ hs).2
    (fun i him => (((hinc _ hs).2 i).mp him).1)
    (fun i him => hw i (((hinc _ hs).2 i).mp him).1)
    (pre_outgoing_capacity m extent padding decoded placed initial alignment ky count _
      hdecode hp hk hi hsD)
  have hin := anchorLinks_node_in_y1 pre (pre.links[j]!.target) j rfl
    (((hinc _ ht).1 j).mpr ⟨hjp, rfl⟩) ht hinc (hnd _ ht).1
    (fun i him => (((hinc _ ht).1 i).mp him).1)
    (fun i him => hw i (((hinc _ ht).1 i).mp him).1)
    (pre_incoming_capacity m extent padding decoded placed initial alignment ky count _
      hdecode hp hk hi htD)
  have hfinalS : (anchorLinks pre).links[j]!.source = pre.links[j]!.source :=
    congrArg (fun d : Nat × Nat × Int × Int => d.1) (anchorLinks_linkData pre j)
  have hfinalT : (anchorLinks pre).links[j]!.target = pre.links[j]!.target :=
    congrArg (fun d : Nat × Nat × Int × Int => d.2.1) (anchorLinks_linkData pre j)
  rw [hout]
  change 0 ≤ (anchorLinks pre).links[j]!.y0 - _ ∧ _
  rw [hfinalS, hfinalT, anchorLinks_nodes]
  exact ⟨ho.1, ho.2, hin.1, hin.2⟩

theorem run_normalized_c5 (m : Model) (extent padding : Int)
    (decoded flowed : Flow) (alignment : String) (count : Nat)
    (hdecode : decode m extent padding = .ok decoded)
    (hrun : run decoded alignment count = .ok flowed)
    (hwf : Elegant.WellFormed m) (width height nodeWidth : Int)
    (hwidth : 0 ≤ nodeWidth) (labels : List LabelPlacement) :
    let norm := normalize flowed (nodeRects flowed width nodeWidth) labels width height
    Validator.C5 (sceneOf m norm.1 norm.2.1 norm.2.2.1 norm.2.2.2.1
      norm.2.2.2.2).layoutDump := by
  let rects := nodeRects flowed width nodeWidth
  let norm := normalize flowed rects labels width height
  change Validator.C5 (sceneOf m norm.1 norm.2.1 norm.2.2.1 norm.2.2.2.1
    norm.2.2.2.2).layoutDump
  have hn : flowed.nodes.size = m.boxes.length :=
    (run_nodes_size decoded flowed alignment count hrun).trans
      (decode_nodes_size m extent padding decoded hdecode)
  have hl : flowed.links.size = m.routes.length :=
    (run_links_size decoded flowed alignment count hrun).trans
      (decode_links_size m extent padding decoded hdecode)
  have hnorm (i : Nat) (hi : i < m.routes.length) :
      norm.1.links[i]!.source = flowed.links[i]!.source ∧
        norm.1.links[i]!.target = flowed.links[i]!.target := by
    have hi' : i < flowed.links.size := by omega
    have hd := normalize_linkData flowed rects labels width height i hi'
    exact ⟨congrArg (fun d : Nat × Nat × Int × Int => d.1) hd,
      congrArg (fun d : Nat × Nat × Int × Int => d.2.1) hd⟩
  have hidx (i : Nat) (hi : i < m.routes.length) :
      norm.1.links[i]!.source = nodeIndex m (m.routes[i]).fromId ∧
        norm.1.links[i]!.target = nodeIndex m (m.routes[i]).toId := by
    have hd := decode_link_endpoints m extent padding decoded hdecode i hi
    have hr := run_endpoint_indices decoded flowed alignment count hrun i
    exact ⟨(hnorm i hi).1.trans (hr.1.trans hd.1),
      (hnorm i hi).2.trans (hr.2.trans hd.2)⟩
  apply sceneOf_c5 m norm.1 norm.2.1 norm.2.2.1 norm.2.2.2.1 norm.2.2.2.2
    (Model.boxIds_nodup hwf)
  · intro i hi mr hget
    have heq : m.routes[i] = mr := (List.getElem?_eq_some_iff.mp hget).2
    have hm : mr ∈ m.routes := by
      rw [← heq]
      exact List.getElem_mem hi
    have hex := (wellFormed_route_endpoints m hwf mr hm).1
    have hs : norm.1.links[i]!.source = nodeIndex m mr.fromId := by
      rw [(hidx i hi).1, heq]
    refine ⟨m.boxes[nodeIndex m mr.fromId]'(nodeIndex_lt m mr.fromId hex), ?_,
      nodeIndex_id m mr.fromId hex⟩
    rw [hs]
    exact List.getElem?_eq_some_iff.mpr ⟨nodeIndex_lt m mr.fromId hex, rfl⟩
  · intro i hi mr hget
    have heq : m.routes[i] = mr := (List.getElem?_eq_some_iff.mp hget).2
    have hm : mr ∈ m.routes := by
      rw [← heq]
      exact List.getElem_mem hi
    have hex := (wellFormed_route_endpoints m hwf mr hm).2
    have ht : norm.1.links[i]!.target = nodeIndex m mr.toId := by
      rw [(hidx i hi).2, heq]
    refine ⟨m.boxes[nodeIndex m mr.toId]'(nodeIndex_lt m mr.toId hex), ?_,
      nodeIndex_id m mr.toId hex⟩
    rw [ht]
    exact List.getElem?_eq_some_iff.mpr ⟨nodeIndex_lt m mr.toId hex, rfl⟩
  · intro i hi
    have hif : i < flowed.nodes.size := by omega
    have hir : i < rects.size := by simpa only [rects, nodeRects_size] using hif
    have hin : i < norm.2.1.size := by
      simpa only [norm, normalize_preserves_node_count] using hir
    have hw : 0 ≤ (rects[i]!).w := by
      rw [nodeRects_w flowed width nodeWidth i hif]
      exact hwidth
    rw [getElem!_pos norm.2.1 i hin]
    simpa only [norm, normalize, Array.getElem_map, getElem!_pos rects i hir] using hw
  · intro i hi
    have hif : i < flowed.links.size := by omega
    have hiD : i < decoded.links.size := by
      rw [decode_links_size m extent padding decoded hdecode]
      exact hi
    have hb := decode_link_bounds m extent padding decoded hdecode
      decoded.links[i] (Array.getElem_mem_toList hiD)
    rw [← getElem!_pos decoded.links i hiD] at hb
    have hr := run_endpoint_indices decoded flowed alignment count hrun i
    have hs : flowed.links[i]!.source < flowed.nodes.size := by
      rw [hr.1, hn]
      exact hb.2.1
    have ht : flowed.links[i]!.target < flowed.nodes.size := by
      rw [hr.2, hn]
      exact hb.2.2
    have hsr : flowed.links[i]!.source < rects.size := by
      simpa only [rects, nodeRects_size] using hs
    have htr : flowed.links[i]!.target < rects.size := by
      simpa only [rects, nodeRects_size] using ht
    have hso := normalization_offset_cancel flowed rects labels width height i
      flowed.links[i]!.source hif hsr
    have hto := normalization_offset_cancel flowed rects labels width height i
      flowed.links[i]!.target hif htr
    have ho := run_anchor_offsets m extent padding decoded flowed alignment count
      hdecode hrun i hi
    change
      (norm.1.links[i]!.y0 - norm.2.1[flowed.links[i]!.source]!.y =
        flowed.links[i]!.y0 - rects[flowed.links[i]!.source]!.y) ∧ _ at hso
    change
      (norm.1.links[i]!.y0 - norm.2.1[flowed.links[i]!.target]!.y =
        flowed.links[i]!.y0 - rects[flowed.links[i]!.target]!.y) ∧ _ at hto
    have hyS := nodeRects_y flowed width nodeWidth _ hs
    have hyT := nodeRects_y flowed width nodeWidth _ ht
    have hhS := nodeRects_height flowed width nodeWidth _ hs
    have hhT := nodeRects_height flowed width nodeWidth _ ht
    change (rects[flowed.links[i]!.source]!).y = _ at hyS
    change (rects[flowed.links[i]!.target]!).y = _ at hyT
    change (rects[flowed.links[i]!.source]!).h = _ at hhS
    change (rects[flowed.links[i]!.target]!).h = _ at hhT
    rw [hyS, hhS] at hso
    rw [hyT, hhT] at hto
    rw [(hnorm i hi).1, (hnorm i hi).2]
    obtain ⟨hloS, hhiS, hloT, hhiT⟩ := ho
    obtain ⟨hys, _, _, hhs⟩ := hso
    obtain ⟨_, hyt, _, hht⟩ := hto
    dsimp only [norm] at hys hhs hyt hht ⊢
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem layoutCore_c5 (m : Model) (s : Scene) (hwf : Elegant.WellFormed m)
    (h : layoutCore m = .ok s) : Validator.C5 s.layoutDump := by
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
        have hc5 := run_normalized_c5 m height padding decoded flowed _ _ hd hr hwf
          width height (LayoutConst.sankey_node_width.get .vector)
          (by decide) labels
        simp only [width, height, padding, rects] at hd hr hl hc5
        simp only [hd, hr, hl, Bind.bind, Except.bind] at h
        repeat' (split at h <;> try contradiction)
        cases h
        exact hc5

theorem layout_c5 (m : Model) (s : Scene) (hwf : Elegant.WellFormed m)
    (h : layout m = .ok s) : Validator.C5 s.layoutDump :=
  layoutCore_c5 m s hwf (layout_core_success m s h)

theorem sankey_valid {m : Model} {scene : Scene}
    (hwf : Elegant.WellFormed m) (_hl : WithinLimits m)
    (h : layout m = .ok scene) : HardConstraints scene.layoutDump := by
  obtain ⟨hc2, hc3, hc4, hc6, hc7, hc8⟩ := layout_metadata_clauses m scene h
  exact ⟨layout_canvas m scene h, hc2, hc3, hc4,
    layout_c5 m scene hwf h, hc6, hc7, hc8⟩

end Elegant.Chart.Sankey
