import Elegant.Layered.Normalize
import Elegant.Layered.Route

set_option autoImplicit false

namespace Elegant.Layered

structure EdgeLabelSize where
  edge : Nat
  width : Int
  height : Int
  deriving DecidableEq, Repr

namespace Labels

def addLabelNode (g : Graph) (p : Proper) (label : EdgeLabelSize) :
    Except LayoutError Proper :=
  if label.width < 0 ∨ label.height < 0 then .error .domain
  else if I32_MAX < label.width ∨ I32_MAX < label.height then .error .overflow
  else match g.edges[label.edge]? with
  | none => .error .domain
  | some edge =>
    if edge.tail = edge.head then .ok p
    else
      let tailRank := rk p.rank edge.tail
      let span := rk p.rank edge.head - tailRank
      if span < 2 then .error .domain
      else
        let labelRank := tailRank + Int.fdiv span 2
        match p.nodes.zipIdx.find? (fun q =>
            q.1.edge == some label.edge && rk p.rank q.2 == labelRank) with
        | none => .error .domain
        | some q =>
          match p.nodes[q.2]? with
          | none => .error .domain
          | some nd =>
            .ok { p with nodes := p.nodes.set q.2 ({ nd with
              node := { nd.node with w := label.width, h := label.height }, label := true }) }

def addLabelNodes (g : Graph) (p : Proper) (labels : List EdgeLabelSize) :
    Except LayoutError Proper :=
  match labels with
  | [] => .ok p
  | label :: rest => do
    let p' ← addLabelNode g p label
    addLabelNodes g p' rest

theorem addLabelNode_metadata {g : Graph} {p p' : Proper} {label : EdgeLabelSize}
    (h : addLabelNode g p label = .ok p') :
    p'.edges = p.edges ∧ p'.rank = p.rank ∧ p'.chains = p.chains ∧
      ∀ v : Nat, (p'.nodes[v]?).map ProperNode.dummy = (p.nodes[v]?).map ProperNode.dummy := by
  unfold addLabelNode at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
        · dsimp only at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · next q hq =>
              split at h
              · simp at h
              · next nd hnd =>
                simp only [Except.ok.injEq] at h
                subst h
                refine ⟨rfl, rfl, rfl, ?_⟩
                intro v
                have hlen := (List.getElem?_eq_some_iff.mp hnd).1
                by_cases hv : q.2 = v <;> simp_all

theorem addLabelNodes_metadata {g : Graph} {p p' : Proper} {labels : List EdgeLabelSize}
    (h : addLabelNodes g p labels = .ok p') :
    p'.edges = p.edges ∧ p'.rank = p.rank ∧ p'.chains = p.chains ∧
      ∀ v : Nat, (p'.nodes[v]?).map ProperNode.dummy = (p.nodes[v]?).map ProperNode.dummy := by
  induction labels generalizing p with
  | nil =>
    simp only [addLabelNodes, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | cons label rest ih =>
    simp only [addLabelNodes] at h
    cases he : addLabelNode g p label with
    | error e => simp [he, bind, Except.bind] at h
    | ok q =>
      simp only [he, bind, Except.bind] at h
      obtain ⟨he₁, hr₁, hc₁, hd₁⟩ := addLabelNode_metadata he
      obtain ⟨he₂, hr₂, hc₂, hd₂⟩ := ih h
      exact ⟨he₂.trans he₁, hr₂.trans hr₁, hc₂.trans hc₁,
        fun v => (hd₂ v).trans (hd₁ v)⟩

def labelRect (centre top width height : Int) : Rect :=
  ⟨centre - Int.fdiv width 2, top, width, height⟩

def rectAt (p : Proper) (xs ys : List Int) (v : Nat) : Rect :=
  labelRect (RouteImpl.xAt xs v) (RouteImpl.yAt ys v)
    (RouteImpl.nodeW p v) (RouteImpl.nodeH p v)

def textRectAt (p : Proper) (xs ys : List Int) (v : Nat) (gutter : Int) : Rect :=
  let r := rectAt p xs ys v
  ⟨r.x + gutter, r.y, r.w - gutter, r.h⟩

def stackRects (x y gap : Int) : List (Int × Int) → List Rect
  | [] => []
  | size :: rest => ⟨x, y, size.1, size.2⟩ :: stackRects x (y + size.2 + gap) gap rest

theorem stackRects_lower (x gap : Int) (hg : 0 ≤ gap) :
    ∀ (sizes : List (Int × Int)) (y : Int),
      (∀ size ∈ sizes, 0 ≤ size.2) → ∀ r ∈ stackRects x y gap sizes, y ≤ r.y := by
  intro sizes
  induction sizes with
  | nil => simp [stackRects]
  | cons size rest ih =>
    intro y hs r hr
    simp only [stackRects, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Int.le_refl _
    · have hheight := hs size (by simp)
      have htail := ih (y + size.2 + gap) (fun s h => hs s (by simp [h])) r hr
      omega

theorem stackRects_disjoint (x gap : Int) (hg : 0 ≤ gap) :
    ∀ (sizes : List (Int × Int)) (y : Int),
      (∀ size ∈ sizes, 0 ≤ size.2) →
      (stackRects x y gap sizes).Pairwise (fun a b => ¬ Rect.meetsInterior a b) := by
  intro sizes
  induction sizes with
  | nil => simp [stackRects]
  | cons size rest ih =>
    intro y hs
    simp only [stackRects, List.pairwise_cons]
    refine ⟨?_, ih (y + size.2 + gap) (fun s h => hs s (by simp [h]))⟩
    intro r hr
    have htail := stackRects_lower x gap hg rest (y + size.2 + gap)
      (fun s h => hs s (by simp [h])) r hr
    simp only [Rect.meetsInterior]
    omega

/-- Fold map lemma: foldl over a mapped list equals foldl with the mapped function. -/
theorem foldl_map {α β γ : Type} (f : α → β) (g : γ → β → γ) (init : γ) (xs : List α) :
    (xs.map f).foldl g init = xs.foldl (fun acc x => g acc (f x)) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x rest ih => exact ih (g init (f x))

/-- Width of a stack of labels: the maximum width among elements (or 0 if empty). -/
def stackWidth (sizes : List (Int × Int)) : Int :=
  sizes.foldl (fun w s => max w s.1) 0

/-- Sum of label heights. -/
def sumHeights (sizes : List (Int × Int)) : Int :=
  sizes.foldl (fun h s => h + s.2) 0

/-- Total height of a stack of labels: sum of heights plus gap between consecutive elements.
When the list has length n, there are (n - 1) gaps. For an empty list, (0 - 1 = 0 in Nat), so gap * 0 = 0. -/
def stackHeight (gap : Int) (sizes : List (Int × Int)) : Int :=
  sumHeights sizes + gap * ((sizes.length - 1 : Nat) : Int)

/-- Envelope rectangle spanning the stacked labels from (x, y) with dimensions (stackWidth, stackHeight). -/
def stackEnvelope (x y gap : Int) (sizes : List (Int × Int)) : Rect :=
  ⟨x, y, stackWidth sizes, stackHeight gap sizes⟩

/-- `stackWidth` over mapped items matches `foldl max` on the width field. -/
theorem stackWidth_map {α : Type} (f : α → Int × Int) (xs : List α) :
    stackWidth (xs.map f) = xs.foldl (fun w x => max w (f x).1) 0 :=
  foldl_map f (fun w s => max w s.1) 0 xs

/-- `sumHeights` over mapped items matches `foldl +` on the height field. -/
theorem sumHeights_map {α : Type} (f : α → Int × Int) (xs : List α) :
    sumHeights (xs.map f) = xs.foldl (fun h x => h + (f x).2) 0 :=
  foldl_map f (fun h s => h + s.2) 0 xs

/-- `stackHeight` over mapped items matches `foldl +` on height plus gap * (length - 1). -/
theorem stackHeight_map {α : Type} (gap : Int) (f : α → Int × Int) (xs : List α) :
    stackHeight gap (xs.map f) =
      xs.foldl (fun h x => h + (f x).2) 0 + gap * ((xs.length - 1 : Nat) : Int) := by
  simp only [stackHeight, sumHeights_map, List.length_map]

/-- Syntactic bridge for pair mapping to `stackWidth`. -/
theorem stackWidth_map_pair {α : Type} (wFn hFn : α → Int) (xs : List α) :
    stackWidth (xs.map fun x => (wFn x, hFn x)) = xs.foldl (fun w x => max w (wFn x)) 0 :=
  stackWidth_map (fun x => (wFn x, hFn x)) xs

/-- Syntactic bridge for pair mapping to `stackHeight`. -/
theorem stackHeight_map_pair {α : Type} (gap : Int) (wFn hFn : α → Int) (xs : List α) :
    stackHeight gap (xs.map fun x => (wFn x, hFn x)) =
      xs.foldl (fun h x => h + hFn x) 0 + gap * ((xs.length - 1 : Nat) : Int) :=
  stackHeight_map gap (fun x => (wFn x, hFn x)) xs

/-- Every produced rectangle has x equal to the starting x and dimensions coming from an element in sizes. -/
theorem stackRects_mem (x gap : Int) :
    ∀ (sizes : List (Int × Int)) (y : Int) (r : Rect),
      r ∈ stackRects x y gap sizes →
      r.x = x ∧ ∃ s ∈ sizes, r.w = s.1 ∧ r.h = s.2 := by
  intro sizes
  induction sizes with
  | nil => simp [stackRects]
  | cons size rest ih =>
    intro y r hr
    simp only [stackRects, List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨rfl, size, by simp, rfl, rfl⟩
    · obtain ⟨hx, s, hs, hw, hh⟩ := ih (y + size.2 + gap) r hr
      exact ⟨hx, s, by simp [hs], hw, hh⟩

/-- Every produced rectangle has non-negative dimensions when input sizes are non-negative. -/
theorem stackRects_dims (x gap : Int) :
    ∀ (sizes : List (Int × Int)) (y : Int),
      (∀ size ∈ sizes, 0 ≤ size.1 ∧ 0 ≤ size.2) →
      ∀ r ∈ stackRects x y gap sizes,
        0 ≤ r.w ∧ 0 ≤ r.h ∧ r.x = x := by
  intro sizes y hs r hr
  obtain ⟨hx, s, hmem, hw, hh⟩ := stackRects_mem x gap sizes y r hr
  have hpos := hs s hmem
  rw [hw, hh, hx]
  exact ⟨hpos.1, hpos.2, rfl⟩

/-- The accumulator lower bounds the result of foldl with max. -/
theorem foldl_max_ge_init (sizes : List (Int × Int)) (acc : Int) :
    acc ≤ sizes.foldl (fun w s => max w s.1) acc := by
  induction sizes generalizing acc with
  | nil => exact Int.le_refl acc
  | cons s rest ih =>
    dsimp only [List.foldl]
    exact Int.le_trans (Int.le_max_left acc s.1) (ih (max acc s.1))

/-- Any element's width is bounded by foldl max. -/
theorem mem_le_foldl_max (sizes : List (Int × Int)) (acc : Int) {s : Int × Int}
    (hs : s ∈ sizes) :
    s.1 ≤ sizes.foldl (fun w s => max w s.1) acc := by
  induction sizes generalizing acc with
  | nil => contradiction
  | cons a rest ih =>
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · dsimp only [List.foldl]
      exact Int.le_trans (Int.le_max_right acc s.1) (foldl_max_ge_init rest (max acc s.1))
    · dsimp only [List.foldl]
      exact ih (max acc a.1) hs

/-- Nonnegativity of `stackWidth`. -/
theorem stackWidth_nonneg (sizes : List (Int × Int)) :
    0 ≤ stackWidth sizes :=
  foldl_max_ge_init sizes 0

/-- Every rectangle produced by `stackRects` has width bounded by `stackWidth`. -/
theorem stackRects_width_le (x gap : Int) :
    ∀ (sizes : List (Int × Int)) (y : Int),
      ∀ r ∈ stackRects x y gap sizes,
        r.w ≤ stackWidth sizes ∧ r.x + r.w ≤ x + stackWidth sizes := by
  intro sizes y r hr
  obtain ⟨hx, s, hmem, hw, _⟩ := stackRects_mem x gap sizes y r hr
  have hle : s.1 ≤ stackWidth sizes := mem_le_foldl_max sizes 0 hmem
  rw [hw, hx]
  exact ⟨hle, by omega⟩

/-- The accumulator distributes out of integer addition foldl. -/
theorem foldl_add_eq (sizes : List (Int × Int)) (acc : Int) :
    sizes.foldl (fun h s => h + s.2) acc = acc + sumHeights sizes := by
  induction sizes generalizing acc with
  | nil => simp [sumHeights]
  | cons s rest ih =>
    dsimp only [List.foldl]
    rw [ih (acc + s.2)]
    have h1 : rest.foldl (fun h s => h + s.2) s.2 = s.2 + sumHeights rest := ih s.2
    have h0 : sumHeights (s :: rest) = s.2 + sumHeights rest := by
      change rest.foldl (fun h s => h + s.2) (0 + s.2) = s.2 + sumHeights rest
      rw [show (0 : Int) + s.2 = s.2 by omega]
      exact h1
    rw [h0]
    omega

/-- `sumHeights` on a cons cell unrolls as `s.2 + sumHeights rest`. -/
theorem sumHeights_cons (s : Int × Int) (rest : List (Int × Int)) :
    sumHeights (s :: rest) = s.2 + sumHeights rest := by
  change rest.foldl (fun h s => h + s.2) (0 + s.2) = s.2 + sumHeights rest
  rw [show (0 : Int) + s.2 = s.2 by omega]
  exact foldl_add_eq rest s.2

/-- Nonnegativity of `sumHeights`. -/
theorem sumHeights_nonneg {sizes : List (Int × Int)} (hs : ∀ s ∈ sizes, 0 ≤ s.2) :
    0 ≤ sumHeights sizes := by
  induction sizes with
  | nil => simp [sumHeights]
  | cons s rest ih =>
    rw [sumHeights_cons]
    have h1 := hs s (by simp)
    have h2 := ih (fun x hx => hs x (by simp [hx]))
    omega

/-- `stackHeight` of a singleton is just its height. -/
theorem stackHeight_singleton (gap : Int) (s : Int × Int) :
    stackHeight gap [s] = s.2 := by
  dsimp [stackHeight]
  rw [sumHeights_cons]
  dsimp [sumHeights]
  omega

/-- Inductive step for `stackHeight` when the tail is nonempty. -/
theorem stackHeight_cons_of_nonempty (gap : Int) (s : Int × Int) {rest : List (Int × Int)}
    (hne : rest ≠ []) :
    stackHeight gap (s :: rest) = s.2 + gap + stackHeight gap rest := by
  have hpos : 0 < rest.length := List.length_pos_iff.mpr hne
  have hcast : (rest.length : Int) = ((rest.length - 1 : Nat) : Int) + 1 := by
    omega
  dsimp [stackHeight]
  rw [sumHeights_cons, hcast, Int.mul_add, Int.mul_one]
  omega

/-- Nonnegativity of `stackHeight`. -/
theorem stackHeight_nonneg (gap : Int) (hg : 0 ≤ gap) {sizes : List (Int × Int)}
    (hs : ∀ s ∈ sizes, 0 ≤ s.2) :
    0 ≤ stackHeight gap sizes := by
  dsimp [stackHeight]
  have h1 := sumHeights_nonneg hs
  have h2 : 0 ≤ ((sizes.length - 1 : Nat) : Int) := by omega
  have h3 : 0 ≤ gap * ((sizes.length - 1 : Nat) : Int) := Int.mul_nonneg hg h2
  omega

/-- Upper bound on the vertical extent of every rectangle produced by `stackRects`. -/
theorem stackRects_upper (x gap : Int) (hg : 0 ≤ gap) :
    ∀ (sizes : List (Int × Int)) (y : Int),
      (∀ size ∈ sizes, 0 ≤ size.2) →
      ∀ r ∈ stackRects x y gap sizes,
        r.y + r.h ≤ y + stackHeight gap sizes := by
  intro sizes
  induction sizes with
  | nil => simp [stackRects]
  | cons size rest ih =>
    intro y hs r hr
    simp only [stackRects, List.mem_cons] at hr
    have hrest_nonneg : ∀ s ∈ rest, 0 ≤ s.2 := fun s h => hs s (by simp [h])
    rcases hr with rfl | hr
    · dsimp only
      by_cases hrest : rest = []
      · subst hrest
        rw [stackHeight_singleton]
        omega
      · rw [stackHeight_cons_of_nonempty gap size hrest]
        have hhn := stackHeight_nonneg gap hg hrest_nonneg
        omega
    · by_cases hrest : rest = []
      · subst hrest
        simp [stackRects] at hr
      · rw [stackHeight_cons_of_nonempty gap size hrest]
        have htail := ih (y + size.2 + gap) hrest_nonneg r hr
        omega

/-- The bottom of the last rectangle in `stackRects` exactly achieves the `y + stackHeight` bound. -/
theorem stackRects_last_bottom (x gap : Int) :
    ∀ (sizes : List (Int × Int)) (y : Int) (r : Rect),
      (stackRects x y gap sizes).getLast? = some r →
        r.y + r.h = y + stackHeight gap sizes
  | [], y, r, hr => by
    simp [stackRects] at hr
  | [s], y, r, hr => by
    have hlast : (stackRects x y gap [s]).getLast? = some ⟨x, y, s.1, s.2⟩ := rfl
    rw [hlast] at hr
    cases hr
    dsimp only
    rw [stackHeight_singleton]
  | s :: s' :: rest, y, r, hr => by
    have hlast : (stackRects x y gap (s :: s' :: rest)).getLast? =
        (stackRects x (y + s.2 + gap) gap (s' :: rest)).getLast? := rfl
    rw [hlast] at hr
    have ih := stackRects_last_bottom x gap (s' :: rest) (y + s.2 + gap) r hr
    have hne : s' :: rest ≠ [] := by simp
    rw [stackHeight_cons_of_nonempty gap s hne]
    omega

/-- Every rectangle in `stackRects` is contained within any envelope enclosing the stack. -/
theorem stackRects_contained_at {x y gap : Int} (envelope : Rect) (hg : 0 ≤ gap)
    {sizes : List (Int × Int)}
    (hs : ∀ s ∈ sizes, 0 ≤ s.1 ∧ 0 ≤ s.2)
    (hx : envelope.x ≤ x)
    (hw : x + stackWidth sizes ≤ envelope.x + envelope.w)
    (hy : envelope.y ≤ y)
    (hh : y + stackHeight gap sizes ≤ envelope.y + envelope.h) :
    ∀ r ∈ stackRects x y gap sizes,
      0 ≤ r.w ∧ 0 ≤ r.h ∧ envelope.Contained r := by
  intro r hr
  have hdims := stackRects_dims x gap sizes y hs r hr
  have hw_le := stackRects_width_le x gap sizes y r hr
  have hs_h : ∀ s ∈ sizes, 0 ≤ s.2 := fun s hs_s => (hs s hs_s).2
  have hy_lower := stackRects_lower x gap hg sizes y hs_h r hr
  have hy_upper := stackRects_upper x gap hg sizes y hs_h r hr
  refine ⟨hdims.1, hdims.2.1, ?_⟩
  unfold Rect.Contained
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdims.2.2]
    exact hx
  · rw [hdims.2.2]
    omega
  · omega
  · omega

/-- Containment when the stack starts at the envelope's top-left corner (as in Pipeline.placedLabels). -/
theorem stackRects_contained (envelope : Rect) (gap : Int) (hg : 0 ≤ gap)
    {sizes : List (Int × Int)}
    (hs : ∀ s ∈ sizes, 0 ≤ s.1 ∧ 0 ≤ s.2)
    (hw : stackWidth sizes ≤ envelope.w)
    (hh : stackHeight gap sizes ≤ envelope.h) :
    ∀ r ∈ stackRects envelope.x envelope.y gap sizes,
      0 ≤ r.w ∧ 0 ≤ r.h ∧ envelope.Contained r :=
  stackRects_contained_at envelope hg hs (Int.le_refl _) (by omega) (Int.le_refl _) (by omega)

/-- Containment within the canonical `stackEnvelope`. -/
theorem stackEnvelope_contained (x y gap : Int) (hg : 0 ≤ gap)
    {sizes : List (Int × Int)}
    (hs : ∀ s ∈ sizes, 0 ≤ s.1 ∧ 0 ≤ s.2) :
    ∀ r ∈ stackRects x y gap sizes,
      0 ≤ r.w ∧ 0 ≤ r.h ∧ (stackEnvelope x y gap sizes).Contained r :=
  stackRects_contained (stackEnvelope x y gap sizes) gap hg hs (Int.le_refl _) (Int.le_refl _)

/-- Second projection membership in zipped lists. -/
theorem mem_zip_snd {α β : Type} {a : α} {b : β} :
    ∀ {l1 : List α} {l2 : List β}, (a, b) ∈ l1.zip l2 → b ∈ l2
  | [], _, h => by simp at h
  | _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.zip_cons_cons, List.mem_cons] at h
    rcases h with heq | htail
    · injection heq with _ h2
      subst h2
      simp
    · exact List.mem_cons_of_mem y (mem_zip_snd htail)

/-- First projection membership in zipped lists. -/
theorem mem_zip_fst {α β : Type} {a : α} {b : β} :
    ∀ {l1 : List α} {l2 : List β}, (a, b) ∈ l1.zip l2 → a ∈ l1
  | [], _, h => by simp at h
  | _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.zip_cons_cons, List.mem_cons] at h
    rcases h with heq | htail
    · injection heq with h1 _
      subst h1
      simp
    · exact List.mem_cons_of_mem x (mem_zip_fst htail)

end Labels

theorem rectAt_eq_box (p : Proper) (xs ys : List Int) (v : Nat) :
    Labels.rectAt p xs ys v =
      ⟨RouteImpl.leftOf p xs v, RouteImpl.yAt ys v, RouteImpl.nodeW p v, RouteImpl.nodeH p v⟩ :=
  rfl

/-- The actual midpoint-node rectangles used by the pipeline are disjoint within a rank.
The result applies to every pair of distinct nodes, hence also to the subset that carries labels. -/
theorem labels_disjoint {p : Proper} {layers : List (List Nat)} {xs ys top : List Int}
    {routing : Routing} {gap slot : Int} {rankGap : Nat → Int}
    (hrLayers : RouteImpl.layersOk p layers = true)
    (hcoords : CoordFacts p layers xs ys top routing gap rankGap slot)
    {u v : Nat} (hu : u < p.nodes.length) (hv : v < p.nodes.length)
    (hrank : rk p.rank u = rk p.rank v) (hne : u ≠ v) :
    ¬ Rect.meetsInterior (Labels.rectAt p xs ys u) (Labels.rectAt p xs ys v) := by
  rw [rectAt_eq_box, rectAt_eq_box]
  exact RouteImpl.boxRect_disjoint hrLayers hcoords hu hv hrank hne

theorem label_text_disjoint {p : Proper} {layers : List (List Nat)} {xs ys top : List Int}
    {routing : Routing} {gap slot gutter : Int} {rankGap : Nat → Int}
    (hrLayers : RouteImpl.layersOk p layers = true)
    (hcoords : CoordFacts p layers xs ys top routing gap rankGap slot)
    {u v : Nat} (hu : u < p.nodes.length) (hv : v < p.nodes.length)
    (hrank : rk p.rank u = rk p.rank v) (hne : u ≠ v) (hg : 0 ≤ gutter) :
    ¬ Rect.meetsInterior (Labels.textRectAt p xs ys u gutter)
      (Labels.textRectAt p xs ys v gutter) := by
  have h := RouteImpl.boxRect_disjoint hrLayers hcoords hu hv hrank hne
  simp only [Labels.textRectAt, rectAt_eq_box, Rect.meetsInterior] at h ⊢
  omega

end Elegant.Layered
