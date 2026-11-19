import ElegantGeometry.Basic

set_option autoImplicit false

/-! Lean reference of the tree layout family for `mindmap` (`spec/layout/tree.md`, tree-10 and
tree-45): the non-layered tidy tree of the Go package `internal/layout/tree`. A subtree is placed
relative to its root (`u` measures the distance from the root's near edge, `y` from its centre).
The children of one parent are stacked in declaration order below the widened contour of the
earlier siblings, the stack is centred on the parent, and the root splits its children between a
right and a left side by the parity of their position. The recursion runs on the subtree of a node,
so a placement depends on the placements of its descendants only. -/

namespace Elegant
namespace Tree

/-! ### Input -/

structure Node where
  parent : Option Nat
  width : Int
  height : Int
  deriving DecidableEq, Repr

structure Gaps where
  level : Int
  sibling : Int
  deriving DecidableEq, Repr

def parentOf (ns : List Node) (c : Nat) : Option Nat := (ns[c]?).bind (·.parent)

/-- The children of `v` in declaration order. -/
def kidsOf (ns : List Node) (v : Nat) : List Nat :=
  (List.range' (v + 1) (ns.length - v - 1)).filter fun c => parentOf ns c == some v

theorem kidsOf_mem {ns : List Node} {v c : Nat} (h : c ∈ kidsOf ns v) :
    v < c ∧ c < ns.length ∧ parentOf ns c = some v := by
  unfold kidsOf at h
  rw [List.mem_filter, List.mem_range'_1] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨by omega, by omega, by simpa using h3⟩

/-! ### Validation: sizes, gaps and the preorder shape of the parents -/

def unwind (parent : Nat) : List Nat → List Nat
  | [] => []
  | x :: rest => if x = parent then x :: rest else unwind parent rest

/-- Go's `link`: every size is positive, the root has no parent, every other parent lies on the
path of open ancestors (the last node and its ancestors). -/
def linkAux : Nat → List Node → List Nat → Bool
  | _, [], _ => true
  | i, n :: rest, path =>
    if n.width < 1 || n.height < 1 then false
    else if i = 0 then
      match n.parent with
      | none => linkAux 1 rest [0]
      | some _ => false
    else
      match n.parent with
      | none => false
      | some p =>
        match unwind p path with
        | [] => false
        | path' => linkAux (i + 1) rest (i :: path')

def link (ns : List Node) : Bool := linkAux 0 ns []

def gapsValid (g : Gaps) : Bool := decide (0 ≤ g.level ∧ 1 ≤ g.sibling)

/-! ### The relative placement of a subtree -/

structure Ent where
  idx : Nat
  u : Int
  y : Int
  w : Int
  h : Int
  deriving DecidableEq, Repr

/-- The widened box of Go's `contour`: its horizontal range is widened by the level gap towards
the parent, so a route in the gap of a box counts as part of the box. -/
structure Contour where
  u0 : Int
  u1 : Int
  top : Int
  bottom : Int
  deriving DecidableEq, Repr

def Ent.top (e : Ent) : Int := e.y - Int.fdiv e.h 2

def Ent.bottom (e : Ent) : Int := e.top + e.h

def Ent.contour (g : Gaps) (e : Ent) : Contour :=
  ⟨e.u - g.level, e.u + e.w, e.top, e.bottom⟩

def Contour.shift (y : Int) (c : Contour) : Contour :=
  { c with top := c.top + y, bottom := c.bottom + y }

def Contour.overlaps (a b : Contour) : Bool := decide (a.u0 < b.u1 ∧ b.u0 < a.u1)

/-- The offsets that the boxes of `cand` need below the boxes of `frame`. -/
def needs (g : Gaps) (frame cand : List Contour) : List Int :=
  cand.flatMap fun b => frame.filterMap fun a =>
    if a.overlaps b then some (a.bottom - b.top + g.sibling) else none

def separation (g : Gaps) (frame cand : List Contour) : Int :=
  match needs g frame cand with
  | [] => 0
  | x :: xs => xs.foldl max x

/-- The offsets of the sibling subtrees, the first at zero. -/
def stackYs (g : Gaps) : List Contour → List (List Contour) → List Int
  | _, [] => []
  | frame, cs :: rest =>
    let y := separation g frame cs
    y :: stackYs g (frame ++ cs.map (Contour.shift y)) rest

def centreOf (ys : List Int) : Int :=
  match ys.head?, ys.getLast? with
  | some a, some b => Int.fdiv (a + b) 2
  | _, _ => 0

/-- The offsets of the siblings from the centre of their stack. -/
def dysOf (g : Gaps) (rels : List (List Ent)) : List Int :=
  let ys := stackYs g [] (rels.map (·.map (Ent.contour g)))
  ys.map (· - centreOf ys)

structure Sub where
  me : Ent
  rest : List Ent
  edges : List (Ent × Ent)
  deriving DecidableEq, Repr

def Sub.ents (s : Sub) : List Ent := s.me :: s.rest

def Ent.shift (du dy : Int) (e : Ent) : Ent := { e with u := e.u + du, y := e.y + dy }

def Ent.shiftEdge (du dy : Int) (pc : Ent × Ent) : Ent × Ent :=
  (Ent.shift du dy pc.1, Ent.shift du dy pc.2)

def buildSub (g : Gaps) (me : Ent) (kids : List Sub) : Sub :=
  let dys := dysOf g (kids.map Sub.ents)
  let st := me.w + g.level
  { me := me
    rest := (kids.zip dys).flatMap fun kd => kd.1.ents.map (Ent.shift st kd.2)
    edges := (kids.zip dys).flatMap fun kd =>
      (me, Ent.shift st kd.2 kd.1.me) :: kd.1.edges.map (Ent.shiftEdge st kd.2) }

def entOf (ns : List Node) (v : Nat) : Ent :=
  match ns[v]? with
  | some n => ⟨v, 0, 0, n.width, n.height⟩
  | none => ⟨v, 0, 0, 0, 0⟩

def sub (ns : List Node) (g : Gaps) (v : Nat) : Sub :=
  buildSub g (entOf ns v) ((kidsOf ns v).attach.map fun c => sub ns g c.1)
termination_by ns.length - v
decreasing_by
  have h := kidsOf_mem c.2
  omega

/-! ### Absolute placement: the root and its two sides -/

/-- A placed node: its left edge, its centre line and its size. -/
structure AEnt where
  idx : Nat
  x : Int
  y : Int
  w : Int
  h : Int
  deriving DecidableEq, Repr

def AEnt.top (e : AEnt) : Int := e.y - Int.fdiv e.h 2

structure AEdge where
  right : Bool
  p : AEnt
  c : AEnt
  deriving DecidableEq, Repr

/-- A relative entry in the plane. The right side measures `u` from the root's left edge. The
left side mirrors it about the root's right edge, so the root maps onto itself. -/
def Ent.orient (right : Bool) (root : AEnt) (o : Ent) : AEnt :=
  if right then ⟨o.idx, root.x + o.u, o.y, o.w, o.h⟩
  else ⟨o.idx, root.x + root.w - o.u - o.w, o.y, o.w, o.h⟩

/-- Go's `sides`: even positions go right, odd positions go left. -/
def splitSides (ks : List Nat) : List Nat × List Nat :=
  (ks.zipIdx.filterMap fun ci => if ci.2 % 2 == 0 then some ci.1 else none,
   ks.zipIdx.filterMap fun ci => if ci.2 % 2 == 1 then some ci.1 else none)

def sideEdges (g : Gaps) (me : Ent) (root : AEnt) (right : Bool) (subs : List Sub) : List AEdge :=
  (buildSub g me subs).edges.map fun pc => ⟨right, pc.1.orient right root, pc.2.orient right root⟩

def rootOf (ns : List Node) : AEnt :=
  let me := entOf ns 0
  ⟨0, -Int.fdiv me.w 2, 0, me.w, me.h⟩

def placedEdges (ns : List Node) (g : Gaps) : List AEdge :=
  let sides := splitSides (kidsOf ns 0)
  sideEdges g (entOf ns 0) (rootOf ns) true (sides.1.map (sub ns g)) ++
    sideEdges g (entOf ns 0) (rootOf ns) false (sides.2.map (sub ns g))

/-! ### Boxes and routes -/

structure Layout where
  boxes : List Rect
  routes : List (List Point)
  deriving DecidableEq, Repr

def inLimit (v : Int) : Bool := decide (-COORD_LIMIT ≤ v ∧ v ≤ COORD_LIMIT)

def AEnt.rect? (e : AEnt) : Option Rect :=
  if inLimit e.x && inLimit e.top && inLimit (e.x + e.w) && inLimit (e.top + e.h) then
    some ⟨e.x, e.top, e.w, e.h⟩
  else none

def elbow (x0 x1 trunk y0 y1 : Int) : List Point :=
  if y0 == y1 then [⟨x0, y0⟩, ⟨x1, y1⟩]
  else [⟨x0, y0⟩, ⟨trunk, y0⟩, ⟨trunk, y1⟩, ⟨x1, y1⟩]

/-- The route of an edge: out of the near side of the parent, through a trunk in the middle of the
level gap, into the near side of the child. -/
def AEdge.route (g : Gaps) (e : AEdge) : List Point :=
  let half := Int.fdiv g.level 2
  if e.right then elbow (e.p.x + e.p.w) e.c.x (e.p.x + e.p.w + half) e.p.y e.c.y
  else elbow e.p.x (e.c.x + e.c.w) (e.p.x - half) e.p.y e.c.y

def boxEnt (root : AEnt) (edges : List AEdge) (i : Nat) : Option AEnt :=
  if i = 0 then some root else (edges.find? fun e => e.c.idx == i).map (·.c)

def boxRect (root : AEnt) (edges : List AEdge) (i : Nat) : Except LayoutError Rect :=
  match boxEnt root edges i with
  | none => .error .domain
  | some e =>
    match e.rect? with
    | none => .error .overflow
    | some r => .ok r

def routeAt (g : Gaps) (edges : List AEdge) (i : Nat) : List Point :=
  if i = 0 then []
  else
    match edges.find? fun e => e.c.idx == i with
    | none => []
    | some e => e.route g

def boxRects (root : AEnt) (edges : List AEdge) : List Nat → Except LayoutError (List Rect)
  | [] => .ok []
  | i :: is =>
    match boxRect root edges i with
    | .error e => .error e
    | .ok r =>
      match boxRects root edges is with
      | .error e => .error e
      | .ok rs => .ok (r :: rs)

def layoutRaw (ns : List Node) (g : Gaps) : Except LayoutError Layout :=
  let edges := placedEdges ns g
  match boxRects (rootOf ns) edges (List.range ns.length) with
  | .error e => .error e
  | .ok boxes => .ok ⟨boxes, (List.range ns.length).map (routeAt g edges)⟩

/-- Go's `Mindmap`: an empty input has no boxes. -/
def mindmap (ns : List Node) (g : Gaps) : Except LayoutError Layout :=
  if ns.isEmpty then .ok ⟨[], []⟩
  else if !gapsValid g || !link ns then .error .domain
  else layoutRaw ns g

/-! ### Normalisation -/

structure Bounds where
  minX : Int
  minY : Int
  maxX : Int
  maxY : Int

def Bounds.include (b : Bounds) (x y : Int) : Bounds :=
  ⟨min b.minX x, min b.minY y, max b.maxX x, max b.maxY y⟩

def Layout.bounds (l : Layout) : Bounds :=
  let first := l.boxes.headD ⟨0, 0, 0, 0⟩
  let b0 : Bounds := ⟨first.x, first.y, first.x, first.y⟩
  let b1 := l.boxes.foldl (fun b r => (b.include r.x r.y).include (r.x + r.w) (r.y + r.h)) b0
  l.routes.foldl (fun b route => route.foldl (fun b p => b.include p.x p.y) b) b1

def Layout.translate (dx dy : Int) (l : Layout) : Layout :=
  ⟨l.boxes.map fun r => { r with x := r.x + dx, y := r.y + dy },
   l.routes.map fun route => route.map fun p => ⟨p.x + dx, p.y + dy⟩⟩

/-- Go's `Normalize`: move the layout so that the margin surrounds it, and return the canvas. -/
def normalize (margin : Int) (l : Layout) : Except LayoutError (Size × Layout) :=
  if l.boxes.isEmpty then .ok (⟨2 * margin, 2 * margin⟩, l)
  else
    let b := l.bounds
    let w := b.maxX - b.minX + 2 * margin
    let h := b.maxY - b.minY + 2 * margin
    if COORD_LIMIT < w ∨ COORD_LIMIT < h then .error .overflow
    else .ok (⟨w, h⟩, l.translate (margin - b.minX) (margin - b.minY))

/-! ### The contour walk -/

def stackFrame (g : Gaps) : List Contour → List (List Contour) → List Contour
  | frame, [] => frame
  | frame, cs :: rest => stackFrame g (frame ++ cs.map (Contour.shift (separation g frame cs))) rest

theorem stackYs_length (g : Gaps) : ∀ (rels : List (List Contour)) (frame : List Contour),
    (stackYs g frame rels).length = rels.length
  | [], _ => rfl
  | _ :: rest, frame => by
    simp only [stackYs, List.length_cons, stackYs_length g rest]

theorem stackFrame_length (g : Gaps) : ∀ (rels : List (List Contour)) (frame : List Contour),
    (stackFrame g frame rels).length = frame.length + (rels.map List.length).sum
  | [], frame => by simp [stackFrame]
  | cs :: rest, frame => by
    rw [stackFrame, stackFrame_length g rest]
    simp only [List.length_append, List.length_map, List.map_cons, List.sum_cons]
    omega

theorem needs_length_le (g : Gaps) (frame : List Contour) :
    ∀ cand : List Contour, (needs g frame cand).length ≤ cand.length * frame.length
  | [] => by simp [needs]
  | b :: cs => by
    have ih := needs_length_le g frame cs
    have h1 := List.length_filterMap_le
      (fun a => if a.overlaps b then some (a.bottom - b.top + g.sibling) else none) frame
    unfold needs at ih ⊢
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The walk visits every sibling once, its frame holds one contour per box of the earlier
siblings, and a candidate box is compared once with each frame box. -/
theorem mindmap_contour_walk_fuel (g : Gaps) (frame : List Contour) (rels : List (List Contour)) :
    (stackYs g frame rels).length = rels.length ∧
    (stackFrame g frame rels).length = frame.length + (rels.map List.length).sum ∧
    ∀ cand : List Contour, (needs g frame cand).length ≤ cand.length * frame.length :=
  ⟨stackYs_length g rels frame, stackFrame_length g rels frame, needs_length_le g frame⟩

/-! ### Separation of siblings -/

theorem le_foldl_max : ∀ (l : List Int) (x0 x : Int), x ∈ x0 :: l → x ≤ l.foldl max x0
  | [], x0, x, h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    simp [h]
  | y :: ys, x0, x, h => by
    simp only [List.foldl_cons]
    have ih := le_foldl_max ys (max x0 y)
    have hm := ih (max x0 y) List.mem_cons_self
    rcases List.mem_cons.mp h with rfl | h2
    · omega
    · rcases List.mem_cons.mp h2 with rfl | h3
      · omega
      · exact ih x (List.mem_cons_of_mem _ h3)

theorem le_separation {g : Gaps} {frame cand : List Contour} {a b : Contour}
    (ha : a ∈ frame) (hb : b ∈ cand) (ho : a.overlaps b = true) :
    a.bottom - b.top + g.sibling ≤ separation g frame cand := by
  have hmem : a.bottom - b.top + g.sibling ∈ needs g frame cand := by
    unfold needs
    rw [List.mem_flatMap]
    refine ⟨b, hb, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨a, ha, by simp [ho]⟩
  unfold separation
  split
  · rename_i h
    rw [h] at hmem
    simp at hmem
  · rename_i x xs h
    rw [h] at hmem
    exact le_foldl_max xs x _ hmem

theorem fdiv2 (a : Int) : Int.fdiv a 2 = a / 2 := Int.fdiv_eq_ediv_of_nonneg a (by decide)

theorem Contour.overlaps_shift (y : Int) (a b : Contour) :
    (a.shift y).overlaps b = a.overlaps b := rfl

/-- Two placed sibling subtrees: every overlapping pair of boxes keeps the sibling gap, the box
of the later subtree below the box of the earlier one. -/
def SiblingSep (sib : Int) (p q : List Contour × Int) : Prop :=
  ∀ a ∈ p.1, ∀ b ∈ q.1, a.overlaps b = true → a.bottom + p.2 + sib ≤ q.2 + b.top

theorem stackYs_pairwise (g : Gaps) : ∀ (cs : List (List Contour)) (frame : List Contour),
    (cs.zip (stackYs g frame cs)).Pairwise (SiblingSep g.sibling) ∧
    ∀ q ∈ cs.zip (stackYs g frame cs), ∀ a ∈ frame, ∀ b ∈ q.1,
      a.overlaps b = true → a.bottom + g.sibling ≤ q.2 + b.top
  | [], frame => ⟨List.Pairwise.nil, by intro q hq; simp [stackYs] at hq⟩
  | c :: rest, frame => by
    obtain ⟨ih1, ih2⟩ :=
      stackYs_pairwise g rest (frame ++ c.map (Contour.shift (separation g frame c)))
    have hz : (c :: rest).zip (stackYs g frame (c :: rest)) =
        (c, separation g frame c) ::
          rest.zip (stackYs g (frame ++ c.map (Contour.shift (separation g frame c))) rest) := rfl
    rw [hz]
    refine ⟨List.Pairwise.cons ?_ ih1, ?_⟩
    · intro q hq a ha b hb hov
      have h := ih2 q hq (a.shift (separation g frame c))
        (List.mem_append_right _ (List.mem_map_of_mem ha)) b hb hov
      show a.bottom + separation g frame c + g.sibling ≤ q.2 + b.top
      exact h
    · intro q hq a ha b hb hov
      rcases List.mem_cons.mp hq with hq0 | hq'
      · rw [hq0] at hb ⊢
        have h := le_separation (g := g) (cand := c) ha hb hov
        show a.bottom + g.sibling ≤ separation g frame c + b.top
        omega
      · exact ih2 q hq' a (List.mem_append_left _ ha) b hb hov

theorem dysOf_length (g : Gaps) (rels : List (List Ent)) :
    (dysOf g rels).length = rels.length := by
  unfold dysOf
  simp only [List.length_map]
  rw [stackYs_length, List.length_map]

/-- The siblings of one stack keep the sibling gap below the widened contours of the earlier
siblings (tree-10). -/
theorem mindmap_siblings_separated (g : Gaps) (rels : List (List Ent)) :
    (rels.zip (dysOf g rels)).Pairwise (fun p q =>
      ∀ a ∈ p.1, ∀ b ∈ q.1, (a.contour g).overlaps (b.contour g) = true →
        (a.contour g).bottom + p.2 + g.sibling ≤ q.2 + (b.contour g).top) := by
  have h := (stackYs_pairwise g (rels.map (·.map (Ent.contour g))) []).1
  unfold dysOf
  dsimp only
  generalize stackYs g [] (rels.map (·.map (Ent.contour g))) = ys at h ⊢
  rw [List.zip_map_left, List.pairwise_map] at h
  rw [List.zip_map_right, List.pairwise_map]
  refine List.Pairwise.imp ?_ h
  intro p q hpq a ha b hb hov
  have h1 := hpq (a.contour g) (List.mem_map_of_mem ha) (b.contour g) (List.mem_map_of_mem hb) hov
  show (a.contour g).bottom + (p.2 - centreOf ys) + g.sibling ≤
    (q.2 - centreOf ys) + (b.contour g).top
  have h2 : (a.contour g).bottom + p.2 + g.sibling ≤ q.2 + (b.contour g).top := h1
  omega

/-- The stack is centred on the parent: the first and last siblings sit symmetrically up to
one unit (tree-10, parent centre). -/
theorem mindmap_parent_centred {g : Gaps} {rels : List (List Ent)} {a b : Int}
    (ha : (dysOf g rels).head? = some a) (hb : (dysOf g rels).getLast? = some b) :
    0 ≤ a + b ∧ a + b ≤ 1 := by
  unfold dysOf at ha hb
  generalize stackYs g [] (rels.map (·.map (Ent.contour g))) = ys at ha hb
  rw [List.head?_map, Option.map_eq_some_iff] at ha
  rw [List.getLast?_map, Option.map_eq_some_iff] at hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨z, hz, rfl⟩ := hb
  have hc : centreOf ys = Int.fdiv (x + z) 2 := by
    unfold centreOf
    rw [hx, hz]
  rw [hc, fdiv2]
  omega

/-- The siblings are stacked in declaration order: their offsets strictly increase. -/
theorem mindmap_child_order {g : Gaps} {rels : List (List Ent)}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling)
    (hroot : ∀ r ∈ rels, ∃ me rest, r = me :: rest ∧ me.u = 0 ∧ me.y = 0 ∧ 0 < me.w ∧ 0 ≤ me.h) :
    (dysOf g rels).Pairwise (· < ·) := by
  have hp := mindmap_siblings_separated g rels
  have hlen := dysOf_length g rels
  have h2 : (rels.zip (dysOf g rels)).Pairwise (fun p q => p.2 < q.2) := by
    refine List.Pairwise.imp_of_mem ?_ hp
    intro p q hpm hqm hsep
    obtain ⟨me, rest, hme, hu, hy, hw, hh⟩ := hroot p.1 (List.of_mem_zip hpm).1
    obtain ⟨me', rest', hme', hu', hy', hw', hh'⟩ := hroot q.1 (List.of_mem_zip hqm).1
    have := hsep me (by rw [hme]; exact List.mem_cons_self)
      me' (by rw [hme']; exact List.mem_cons_self)
      (by unfold Contour.overlaps; apply decide_eq_true; simp only [Ent.contour]; omega)
    simp only [Ent.contour, Ent.top, Ent.bottom, hy, hy', fdiv2] at this
    omega
  have h3 := List.Pairwise.map Prod.snd (fun p q h => h) h2
  rwa [List.map_snd_zip (by omega)] at h3

/-! ### Smoke tests against the Go unit tests -/

private def leaf (parent : Option Nat) (w h : Int) : Node := ⟨parent, w, h⟩

#guard (mindmap [leaf none 11 7] ⟨40, 10⟩).toOption.map (·.boxes) = some [⟨-5, -3, 11, 7⟩]

#guard (mindmap [leaf none 10 6, leaf (some 0) 8 4, leaf (some 0) 6 4] ⟨4, 2⟩).toOption =
  some ⟨[⟨-5, -3, 10, 6⟩, ⟨9, -2, 8, 4⟩, ⟨-15, -2, 6, 4⟩],
    [[], [⟨5, 0⟩, ⟨9, 0⟩], [⟨-5, 0⟩, ⟨-9, 0⟩]]⟩

#guard (mindmap [leaf none 10 6, leaf (some 0) 8 4, leaf (some 0) 6 4, leaf (some 0) 8 4]
    ⟨4, 2⟩).toOption.map (fun l => (l.boxes[1]?, l.boxes[3]?, l.routes[1]?, l.routes[3]?)) =
  some (some ⟨9, -5, 8, 4⟩, some ⟨9, 1, 8, 4⟩,
    some [⟨5, 0⟩, ⟨7, 0⟩, ⟨7, -3⟩, ⟨9, -3⟩], some [⟨5, 0⟩, ⟨7, 0⟩, ⟨7, 3⟩, ⟨9, 3⟩])

private def deeper (w : Int) : List Node :=
  [leaf none 10 6, leaf (some 0) 4 2, leaf (some 1) 20 20, leaf (some 0) 4 2, leaf (some 0) w 2]

#guard (mindmap (deeper 10) ⟨3, 2⟩).toOption.map (fun l =>
  ((l.boxes[4]?).map (·.y) |>.getD 0) - ((l.boxes[1]?).map (·.y) |>.getD 0)) = some 13

#guard (mindmap (deeper 4) ⟨3, 2⟩).toOption.map (fun l =>
  ((l.boxes[4]?).map (·.y) |>.getD 0) - ((l.boxes[1]?).map (·.y) |>.getD 0)) = some 4

#guard (mindmap [leaf none 10 6, leaf none 4 4] ⟨4, 2⟩).toOption = none
#guard (mindmap [leaf none 10 6, leaf (some 0) 0 4] ⟨4, 2⟩).toOption = none
#guard (mindmap [leaf none 10 6, leaf (some 0) 4 4] ⟨4, 0⟩).toOption = none

end Tree
end Elegant
