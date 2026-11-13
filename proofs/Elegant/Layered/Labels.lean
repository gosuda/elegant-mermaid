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
