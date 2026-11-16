import Elegant.TreeFacts
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

/-! Validity of the placed mindmap: the boxes of the tidy tree are pairwise disjoint, every route is
an orthogonal elbow from the near side of the parent to the near side of the child, and no route
reaches a box that is neither its parent nor its child. -/

namespace Elegant
namespace Tree

/-! ### Every node is placed -/

theorem Under.snoc {ns : List Node} {v p d : Nat} (h : Under ns v p)
    (hd : parentOf ns d = some p) : Under ns v d := by
  induction h with
  | refl => exact Under.step hd (Under.refl d)
  | step hp _ ih => exact Under.step hp (ih hd)

theorem under_zero {ns : List Node} (hv : Valid ns) (i : Nat) :
    i < ns.length → Under ns 0 i := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    cases i with
    | zero => exact Under.refl 0
    | succ i =>
      obtain ⟨p, hp⟩ := hv.hasParent (i + 1) (by omega) hi
      have hlt := hv.parentLt _ _ hp
      exact (ih p hlt (by omega)).snoc hp

theorem mem_kidsOf {ns : List Node} {v c : Nat} (h1 : v < c) (h2 : c < ns.length)
    (h3 : parentOf ns c = some v) : c ∈ kidsOf ns v := by
  unfold kidsOf
  rw [List.mem_filter, List.mem_range'_1]
  exact ⟨⟨by omega, by omega⟩, by simpa using h3⟩

theorem under_first {ns : List Node} (hv : Valid ns) {v d : Nat} (h : Under ns v d)
    (hd : d < ns.length) : v = d ∨ ∃ c ∈ kidsOf ns v, Under ns c d := by
  cases h with
  | refl => exact Or.inl rfl
  | @step _ c _ hp hu =>
    right
    have hlt := hv.parentLt _ _ hp
    have hle := hu.le hv.parentLt
    exact ⟨c, mem_kidsOf hlt (by omega) hp, hu⟩

theorem mem_splitSides {ks : List Nat} {c : Nat} (h : c ∈ ks) :
    c ∈ (splitSides ks).1 ∨ c ∈ (splitSides ks).2 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
  · exact Or.inl (mem_splitSides_fst.mpr ⟨i, hi, h0⟩)
  · exact Or.inr (mem_splitSides_snd.mpr ⟨i, hi, h1⟩)

theorem exists_pair {α β : Type} (x : α) :
    ∀ (l : List α) (m : List β), l.length = m.length → x ∈ l → ∃ y, (x, y) ∈ l.zip m
  | [], _, _, h => by simp at h
  | a :: as, [], hl, _ => by simp at hl
  | a :: as, b :: bs, hl, hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨b, by simp⟩
    · obtain ⟨y, hy⟩ := exists_pair x as bs (by simpa using hl) hx'
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

theorem sub_mem_zip {ns : List Node} {g : Gaps} {ks : List Nat} {c : Nat} (hc : c ∈ ks) :
    ∃ y, (sub ns g c, y) ∈ (ks.map (sub ns g)).zip (dysOf g ((ks.map (sub ns g)).map Sub.ents)) := by
  apply exists_pair
  · rw [dysOf_length]
    simp
  · exact List.mem_map_of_mem hc

theorem sub_cover {ns : List Node} {g : Gaps} (hv : Valid ns) {v d : Nat} (h : Under ns v d) :
    d < ns.length → ∃ e ∈ (sub ns g v).ents, e.idx = d := by
  induction h with
  | refl =>
    intro _
    refine ⟨entOf ns _, ?_, entOf_idx _ _⟩
    rw [sub]
    exact mem_ents_buildSub.mpr (Or.inl rfl)
  | @step v c d hp hu ih =>
    intro hd
    obtain ⟨e, he, hei⟩ := ih hd
    have hlt := hv.parentLt _ _ hp
    have hle := hu.le hv.parentLt
    have hc : c ∈ kidsOf ns v := mem_kidsOf hlt (by omega) hp
    have hk : sub ns g c ∈ ((kidsOf ns v).attach.map fun c => sub ns g c.1) :=
      List.mem_map.mpr ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩
    obtain ⟨y, hy⟩ := exists_pair (sub ns g c)
      ((kidsOf ns v).attach.map fun c => sub ns g c.1)
      (dysOf g (((kidsOf ns v).attach.map fun c => sub ns g c.1).map Sub.ents))
      (by rw [dysOf_length]; simp) hk
    refine ⟨Ent.shift ((entOf ns v).w + g.level) y e, ?_, hei⟩
    rw [sub]
    exact mem_ents_buildSub.mpr (Or.inr (mem_rest_buildSub.mpr ⟨_, hy, e, he, rfl⟩))

theorem cover_side {ns : List Node} {g : Gaps} (hv : Valid ns) (me : Ent) {ks : List Nat}
    (hg : Good g (buildSub g me (ks.map (sub ns g)))) {c i : Nat} (hc : c ∈ ks)
    (hu : Under ns c i) (hi : i < ns.length) :
    ∃ pc ∈ (buildSub g me (ks.map (sub ns g))).edges, pc.2.idx = i := by
  obtain ⟨e, he, hei⟩ := sub_cover (g := g) hv hu hi
  obtain ⟨y, hy⟩ := sub_mem_zip (ns := ns) (g := g) hc
  have hr : Ent.shift (me.w + g.level) y e ∈ (buildSub g me (ks.map (sub ns g))).rest :=
    mem_rest_buildSub.mpr ⟨_, hy, e, he, rfl⟩
  obtain ⟨pc, hpc, hpc2⟩ := hg.closed2 _ hr
  exact ⟨pc, hpc, by rw [hpc2]; exact hei⟩

/-! ### Orientation -/

theorem orient_idx (right : Bool) (root : AEnt) (o : Ent) : (o.orient right root).idx = o.idx := by
  unfold Ent.orient
  split <;> rfl

theorem orient_y (right : Bool) (root : AEnt) (o : Ent) : (o.orient right root).y = o.y := by
  unfold Ent.orient
  split <;> rfl

theorem orient_w (right : Bool) (root : AEnt) (o : Ent) : (o.orient right root).w = o.w := by
  unfold Ent.orient
  split <;> rfl

theorem orient_h (right : Bool) (root : AEnt) (o : Ent) : (o.orient right root).h = o.h := by
  unfold Ent.orient
  split <;> rfl

theorem orient_top (right : Bool) (root : AEnt) (o : Ent) : (o.orient right root).top = o.top := by
  unfold AEnt.top Ent.top
  rw [orient_y, orient_h]

theorem orient_x_right (root : AEnt) (o : Ent) : (o.orient true root).x = root.x + o.u := rfl

theorem orient_x_left (root : AEnt) (o : Ent) :
    (o.orient false root).x = root.x + root.w - o.u - o.w := rfl

def AEnt.rect (e : AEnt) : Rect := ⟨e.x, e.top, e.w, e.h⟩

/-- The boxes of two placed nodes share no interior point. -/
def AEnt.Apart (a b : AEnt) : Prop :=
  a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x ∨ a.top + a.h ≤ b.top ∨ b.top + b.h ≤ a.top

theorem AEnt.Apart.symm {a b : AEnt} (h : a.Apart b) : b.Apart a := by
  unfold AEnt.Apart at h ⊢
  omega

theorem AEnt.disjoint_of_apart {a b : AEnt} (h : a.Apart b) : Disjoint a.rect b.rect := by
  unfold AEnt.Apart at h
  unfold Disjoint Rect.meetsInterior AEnt.rect
  intro hm
  simp only at hm
  omega

theorem orient_apart (right : Bool) (root : AEnt) {a b : Ent} (h : a.Apart b) :
    (a.orient right root).Apart (b.orient right root) := by
  unfold Ent.Apart Ent.bottom at h
  unfold AEnt.Apart
  rw [orient_top, orient_top, orient_w, orient_w, orient_h, orient_h]
  cases right with
  | true =>
    rw [orient_x_right, orient_x_right]
    omega
  | false =>
    rw [orient_x_left, orient_x_left]
    omega

theorem AEnt.ext' {a b : AEnt} (h1 : a.idx = b.idx) (h2 : a.x = b.x) (h3 : a.y = b.y)
    (h4 : a.w = b.w) (h5 : a.h = b.h) : a = b := by
  cases a
  cases b
  simp_all

/-- The orientation maps the root onto itself. -/
theorem orient_me (right : Bool) (root : AEnt) (me : Ent) (hi : me.idx = root.idx)
    (hu : me.u = 0) (hy : me.y = 0) (hw : me.w = root.w) (hh : me.h = root.h)
    (hry : root.y = 0) : me.orient right root = root := by
  apply AEnt.ext'
  · rw [orient_idx]
    exact hi
  · cases right with
    | true =>
      rw [orient_x_right]
      omega
    | false =>
      rw [orient_x_left]
      omega
  · rw [orient_y]
    omega
  · rw [orient_w]
    exact hw
  · rw [orient_h]
    exact hh

/-! ### Routes -/

theorem mem_elbow {x0 x1 t y0 y1 : Int} {q : Point} (h : q ∈ elbow x0 x1 t y0 y1) :
    (q.x = x0 ∨ q.x = x1 ∨ q.x = t) ∧ (q.y = y0 ∨ q.y = y1) := by
  unfold elbow at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp

theorem isOrthogonal_elbow (x0 x1 t y0 y1 : Int) :
    Polyline.isOrthogonal (elbow x0 x1 t y0 y1) = true := by
  unfold elbow
  split
  · rename_i h
    have := beq_iff_eq.mp h
    simp [Polyline.isOrthogonal, this]
  · simp [Polyline.isOrthogonal]

theorem elbow_head (x0 x1 t y0 y1 : Int) :
    (elbow x0 x1 t y0 y1).head? = some ⟨x0, y0⟩ := by
  unfold elbow
  split <;> rfl

theorem elbow_last (x0 x1 t y0 y1 : Int) :
    (elbow x0 x1 t y0 y1).getLast? = some ⟨x1, y1⟩ := by
  unfold elbow
  split <;> simp

theorem route_right {g : Gaps} {e : AEdge} (h : e.right = true) :
    e.route g = elbow (e.p.x + e.p.w) e.c.x (e.p.x + e.p.w + Int.fdiv g.level 2) e.p.y e.c.y := by
  simp [AEdge.route, h]

theorem route_left {g : Gaps} {e : AEdge} (h : e.right = false) :
    e.route g = elbow e.p.x (e.c.x + e.c.w) (e.p.x - Int.fdiv g.level 2) e.p.y e.c.y := by
  simp [AEdge.route, h]

def AEdge.xlo (e : AEdge) : Int := if e.right then e.p.x + e.p.w else e.c.x + e.c.w

def AEdge.xhi (e : AEdge) : Int := if e.right then e.c.x else e.p.x

/-- The child lies one level gap beyond the parent, on the side of the edge. -/
structure AEdge.Linked (g : Gaps) (e : AEdge) : Prop where
  right : e.right = true → e.c.x = e.p.x + e.p.w + g.level
  left : e.right = false → e.c.x + e.c.w = e.p.x - g.level

theorem route_range {g : Gaps} {e : AEdge} (hL : 0 ≤ g.level) (hl : e.Linked g) :
    ∀ q ∈ e.route g, e.xlo ≤ q.x ∧ q.x ≤ e.xhi ∧ min e.p.y e.c.y ≤ q.y ∧ q.y ≤ max e.p.y e.c.y := by
  intro q hq
  have h0 : 0 ≤ Int.fdiv g.level 2 := by rw [fdiv2]; omega
  have h1 : Int.fdiv g.level 2 ≤ g.level := by rw [fdiv2]; omega
  cases hr : e.right with
  | true =>
    rw [route_right hr] at hq
    have hc := hl.right hr
    have hm := mem_elbow hq
    have hlo : e.xlo = e.p.x + e.p.w := by simp [AEdge.xlo, hr]
    have hhi : e.xhi = e.c.x := by simp [AEdge.xhi, hr]
    rw [hlo, hhi]
    omega
  | false =>
    rw [route_left hr] at hq
    have hc := hl.left hr
    have hm := mem_elbow hq
    have hlo : e.xlo = e.c.x + e.c.w := by simp [AEdge.xlo, hr]
    have hhi : e.xhi = e.p.x := by simp [AEdge.xhi, hr]
    rw [hlo, hhi]
    omega

theorem route_orth (g : Gaps) (e : AEdge) : Polyline.isOrthogonal (e.route g) = true := by
  cases hr : e.right with
  | true =>
    rw [route_right hr]
    exact isOrthogonal_elbow _ _ _ _ _
  | false =>
    rw [route_left hr]
    exact isOrthogonal_elbow _ _ _ _ _

theorem port_on_rect {a : AEnt} (hw : 0 ≤ a.w) (hh : 0 ≤ a.h) {px : Int}
    (hx : px = a.x ∨ px = a.x + a.w) : Validator.onBoundary ⟨px, a.y⟩ a.rect := by
  have h2 := fdiv2 a.h
  unfold Validator.onBoundary AEnt.rect AEnt.top
  simp only
  rw [h2]
  omega

theorem route_ports {g : Gaps} {e : AEdge} (hp : 0 ≤ e.p.w ∧ 0 ≤ e.p.h) (hc : 0 ≤ e.c.w ∧ 0 ≤ e.c.h) :
    ∃ a b : Point, (e.route g).head? = some a ∧ (e.route g).getLast? = some b ∧
      Validator.onBoundary a e.p.rect ∧ Validator.onBoundary b e.c.rect := by
  cases hr : e.right with
  | true =>
    rw [route_right hr]
    exact ⟨_, _, elbow_head _ _ _ _ _, elbow_last _ _ _ _ _,
      port_on_rect hp.1 hp.2 (Or.inr rfl), port_on_rect hc.1 hc.2 (Or.inl rfl)⟩
  | false =>
    rw [route_left hr]
    exact ⟨_, _, elbow_head _ _ _ _ _, elbow_last _ _ _ _ _,
      port_on_rect hp.1 hp.2 (Or.inl rfl), port_on_rect hc.1 hc.2 (Or.inr rfl)⟩

/-! ### Clearance of a route from a box -/

/-- Every point of the polyline lies on one side of the rectangle. -/
def Aside (pts : List Point) (r : Rect) : Prop :=
  (∀ p ∈ pts, p.x ≤ r.x) ∨ (∀ p ∈ pts, r.x + r.w ≤ p.x) ∨
    (∀ p ∈ pts, p.y ≤ r.y) ∨ (∀ p ∈ pts, r.y + r.h ≤ p.y)

theorem allSegsMiss_of_aside : ∀ (pts : List Point) (r : Rect), Aside pts r →
    Polyline.allSegsMiss pts r
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | p :: q :: rest, r, h => by
    have hp : p ∈ p :: q :: rest := List.mem_cons_self
    have hq : q ∈ p :: q :: rest := List.mem_cons_of_mem _ List.mem_cons_self
    show Polyline.segMisses p q r ∧ Polyline.allSegsMiss (q :: rest) r
    refine ⟨?_, allSegsMiss_of_aside (q :: rest) r ?_⟩
    · rcases h with h | h | h | h
      · have := h p hp
        have := h q hq
        exact Or.inl (by omega)
      · have := h p hp
        have := h q hq
        exact Or.inr (Or.inl (by omega))
      · have := h p hp
        have := h q hq
        exact Or.inr (Or.inr (Or.inl (by omega)))
      · have := h p hp
        have := h q hq
        exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · rcases h with h | h | h | h
      · exact Or.inl fun z hz => h z (List.mem_cons_of_mem _ hz)
      · exact Or.inr (Or.inl fun z hz => h z (List.mem_cons_of_mem _ hz))
      · exact Or.inr (Or.inr (Or.inl fun z hz => h z (List.mem_cons_of_mem _ hz)))
      · exact Or.inr (Or.inr (Or.inr fun z hz => h z (List.mem_cons_of_mem _ hz)))

theorem not_hits_of_aside {pts : List Point} {r : Rect} (h : Aside pts r) :
    ¬ Polyline.hitsRect pts r :=
  Polyline.not_hits_of_allMiss (allSegsMiss_of_aside pts r h)

theorem Aside.map_translate {pts : List Point} {r : Rect} (h : Aside pts r) (dx dy : Int) :
    Aside (pts.map fun p => (⟨p.x + dx, p.y + dy⟩ : Point))
      (⟨r.x + dx, r.y + dy, r.w, r.h⟩ : Rect) := by
  unfold Aside at h ⊢
  simp only [List.mem_map]
  rcases h with h | h | h | h
  · refine Or.inl ?_
    rintro _ ⟨p, hp, rfl⟩
    have := h p hp
    show p.x + dx ≤ r.x + dx
    omega
  · refine Or.inr (Or.inl ?_)
    rintro _ ⟨p, hp, rfl⟩
    have := h p hp
    show r.x + dx + r.w ≤ p.x + dx
    omega
  · refine Or.inr (Or.inr (Or.inl ?_))
    rintro _ ⟨p, hp, rfl⟩
    have := h p hp
    show p.y + dy ≤ r.y + dy
    omega
  · refine Or.inr (Or.inr (Or.inr ?_))
    rintro _ ⟨p, hp, rfl⟩
    have := h p hp
    show r.y + dy + r.h ≤ p.y + dy
    omega

/-- A box that the route clears, by the clearance of the relative entries. -/
theorem aside_of_clear {g : Gaps} {e : AEdge} (hL : 0 ≤ g.level) (hl : e.Linked g) {o : AEnt}
    (h : o.x + o.w ≤ e.xlo ∨ e.xhi ≤ o.x ∨ max e.p.y e.c.y ≤ o.top ∨ o.top + o.h ≤ min e.p.y e.c.y) :
    Aside (e.route g) o.rect := by
  have hr := route_range hL hl
  unfold Aside AEnt.rect
  simp only
  rcases h with h | h | h | h
  · refine Or.inr (Or.inl fun q hq => ?_)
    have := (hr q hq).1
    omega
  · refine Or.inl fun q hq => ?_
    have := (hr q hq).2.1
    omega
  · refine Or.inr (Or.inr (Or.inl fun q hq => ?_))
    have := (hr q hq).2.2.2
    omega
  · refine Or.inr (Or.inr (Or.inr fun q hq => ?_))
    have := (hr q hq).2.2.1
    omega

theorem orient_linked {g : Gaps} {p c : Ent}
    (h : c.u = p.u + p.w + g.level) (right : Bool) (root : AEnt) :
    (⟨right, p.orient right root, c.orient right root⟩ : AEdge).Linked g := by
  cases right with
  | true =>
    constructor
    · intro _
      simp only [orient_x_right, orient_w]
      omega
    · intro hfalse
      cases hfalse
  | false =>
    constructor
    · intro hfalse
      cases hfalse
    · intro _
      simp only [orient_x_left, orient_w]
      omega

theorem sideEdges_linked {g : Gaps} {me : Ent} {root : AEnt}
    {right : Bool} {subs : List Sub} (hg : Good g (buildSub g me subs)) :
    ∀ e ∈ sideEdges g me root right subs, e.Linked g := by
  intro e he
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp he
  exact orient_linked (hg.edge_u pc hpc) right root

theorem mindmap_routes_orthogonal (ns : List Node) (g : Gaps) :
    ∀ e ∈ placedEdges ns g, Polyline.isOrthogonal (e.route g) = true := by
  intro e _
  exact route_orth g e

theorem orient_clear {g : Gaps} {p c o : Ent}
    (hL : 0 ≤ g.level) (hl : c.u = p.u + p.w + g.level)
    (hc : Ent.Clear p c o) (right : Bool) (root : AEnt) :
    Aside ((⟨right, p.orient right root, c.orient right root⟩ : AEdge).route g)
      (o.orient right root).rect := by
  apply aside_of_clear hL (orient_linked hl right root)
  unfold Ent.Clear Ent.bottom Ent.top at hc
  cases right with
  | true =>
    simp [AEdge.xlo, AEdge.xhi, Ent.orient, AEnt.top]
    omega
  | false =>
    simp [AEdge.xlo, AEdge.xhi, Ent.orient, AEnt.top]
    omega

theorem side_clear {g : Gaps} {s : Sub} (hL : 0 ≤ g.level) (hg : Good g s)
    {pc : Ent × Ent} (hpc : pc ∈ s.edges) {o : Ent} (ho : o ∈ s.ents)
    (hp : o.idx ≠ pc.1.idx) (hc : o.idx ≠ pc.2.idx) (right : Bool) (root : AEnt) :
    ¬ Polyline.hitsRect
      ((⟨right, pc.1.orient right root, pc.2.orient right root⟩ : AEdge).route g)
      (o.orient right root).rect :=
  not_hits_of_aside (orient_clear hL (hg.edge_u pc hpc) (hg.clear pc hpc o ho hp hc)
    right root)

theorem side_boxes_disjoint {g : Gaps} {s : Sub} (hg : Good g s)
    {a b : Ent} (ha : a ∈ s.ents) (hb : b ∈ s.ents) (hab : a.idx ≠ b.idx)
    (right : Bool) (root : AEnt) :
    Disjoint (a.orient right root).rect (b.orient right root).rect :=
  AEnt.disjoint_of_apart (orient_apart right root (hg.apart a ha b hb hab))

/-- Opposite-side descendants occupy the two exterior half-planes of the root. -/
theorem opposite_boxes_disjoint {g : Gaps} {s t : Sub} {root : AEnt}
    (hL : 0 ≤ g.level) (hs : Good g s) (ht : Good g t)
    (hw : s.me.w = t.me.w) (hr : s.me.w = root.w) :
    ∀ a ∈ s.rest, ∀ b ∈ t.rest,
      Disjoint (a.orient true root).rect (b.orient false root).rect := by
  intro a ha b hb
  apply AEnt.disjoint_of_apart
  have hau := hs.rest_u a ha
  have hbu := ht.rest_u b hb
  have hbw := (ht.rest_dims b hb).1
  have hmw := hs.me_w
  unfold AEnt.Apart
  simp [Ent.orient, AEnt.top]
  omega

theorem Good.right_edge {g : Gaps} {s : Sub} (hg : Good g s) (hL : 0 ≤ g.level)
    {p : Ent} (hp : p ∈ s.ents) : s.me.w ≤ p.u + p.w := by
  rcases List.mem_cons.mp hp with rfl | hp
  · rw [hg.me_u]
    omega
  · have hu := hg.rest_u p hp
    have hw := (hg.rest_dims p hp).1
    omega

theorem opposite_route_clear {g : Gaps} {s t : Sub} {root : AEnt}
    (hL : 0 ≤ g.level) (hs : Good g s) (ht : Good g t)
    (hw : s.me.w = t.me.w) (hr : s.me.w = root.w)
    {pc : Ent × Ent} (hpc : pc ∈ s.edges) {o : Ent} (ho : o ∈ t.rest)
    (right : Bool) :
    ¬ Polyline.hitsRect
      ((⟨right, pc.1.orient right root, pc.2.orient right root⟩ : AEdge).route g)
      (o.orient (!right) root).rect := by
  apply not_hits_of_aside
  apply aside_of_clear hL (orient_linked (hs.edge_u pc hpc) right root)
  have hpu := hs.ents_u hL pc.1 (hs.closed1 pc hpc).1
  have hpw := hs.right_edge hL (hs.closed1 pc hpc).1
  have hcu := hs.rest_u pc.2 (hs.closed1 pc hpc).2
  have hcw := (hs.rest_dims pc.2 (hs.closed1 pc hpc).2).1
  have hou := ht.rest_u o ho
  have how := (ht.rest_dims o ho).1
  have hmw := hs.me_w
  cases right with
  | true =>
    simp [AEdge.xlo, AEdge.xhi, Ent.orient, AEnt.top]
    omega
  | false =>
    simp [AEdge.xlo, AEdge.xhi, Ent.orient, AEnt.top]
    omega

def Bounds.Covers (b : Bounds) (x y : Int) : Prop :=
  b.minX ≤ x ∧ x ≤ b.maxX ∧ b.minY ≤ y ∧ y ≤ b.maxY

theorem Bounds.include_self (b : Bounds) (x y : Int) : (b.include x y).Covers x y := by
  unfold Bounds.include Bounds.Covers
  dsimp only
  omega

theorem Bounds.include_keeps {b : Bounds} {x y : Int} (h : b.Covers x y) (u v : Int) :
    (b.include u v).Covers x y := by
  unfold Bounds.include Bounds.Covers at *
  dsimp only at *
  omega

theorem foldl_preserves {α β : Type} (f : α → β → α) (P : α → Prop)
    (hf : ∀ a b, P a → P (f a b)) :
    ∀ (xs : List β) (a : α), P a → P (xs.foldl f a)
  | [], _, h => h
  | x :: xs, a, h => foldl_preserves f P hf xs (f a x) (hf a x h)

theorem foldl_member {α β : Type} (f : α → β → α) (P : α → Prop) (b : β)
    (hf : ∀ a x, P a → P (f a x)) (hb : ∀ a, P (f a b)) :
    ∀ (xs : List β) (a : α), b ∈ xs → P (xs.foldl f a)
  | [], _, h => by cases h
  | x :: xs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_preserves f P hf xs (f a b) (hb a)
    · exact foldl_member f P b hf hb xs (f a x) h

theorem route_bounds_keeps {b : Bounds} {x y : Int} (h : b.Covers x y)
    (pts : List Point) :
    (pts.foldl (fun b p => b.include p.x p.y) b).Covers x y :=
  foldl_preserves _ (fun b => b.Covers x y)
    (fun _ p hp => Bounds.include_keeps hp p.x p.y) pts b h

theorem Layout.bounds_box (l : Layout) {r : Rect} (hr : r ∈ l.boxes) :
    l.bounds.Covers r.x r.y ∧ l.bounds.Covers (r.x + r.w) (r.y + r.h) := by
  let first := l.boxes.headD ⟨0, 0, 0, 0⟩
  let b0 : Bounds := ⟨first.x, first.y, first.x, first.y⟩
  let step := fun (b : Bounds) (r : Rect) =>
    (b.include r.x r.y).include (r.x + r.w) (r.y + r.h)
  have keeps : ∀ (x y : Int) (b : Bounds) (r : Rect),
      b.Covers x y → (step b r).Covers x y := by
    intro x y b r h
    exact Bounds.include_keeps (Bounds.include_keeps h _ _) _ _
  have hnear : (l.boxes.foldl step b0).Covers r.x r.y :=
    foldl_member step (fun b => b.Covers r.x r.y) r (keeps _ _)
      (fun b => Bounds.include_keeps (b.include_self r.x r.y) _ _) l.boxes b0 hr
  have hfar : (l.boxes.foldl step b0).Covers (r.x + r.w) (r.y + r.h) :=
    foldl_member step (fun b => b.Covers (r.x + r.w) (r.y + r.h)) r (keeps _ _)
      (fun b => (b.include r.x r.y).include_self _ _) l.boxes b0 hr
  exact ⟨foldl_preserves _ (fun (b : Bounds) => b.Covers r.x r.y)
      (fun _ pts h => route_bounds_keeps h pts) l.routes _ hnear,
    foldl_preserves _ (fun (b : Bounds) => b.Covers (r.x + r.w) (r.y + r.h))
      (fun _ pts h => route_bounds_keeps h pts) l.routes _ hfar⟩

theorem Layout.bounds_point (l : Layout) {pts : List Point} (hr : pts ∈ l.routes)
    {p : Point} (hp : p ∈ pts) : l.bounds.Covers p.x p.y := by
  unfold Layout.bounds
  apply foldl_member _ (fun (b : Bounds) => b.Covers p.x p.y) pts
    (fun _ route h => route_bounds_keeps h route) ?_ l.routes _ hr
  intro b
  exact foldl_member _ (fun (b : Bounds) => b.Covers p.x p.y) p
    (fun _ q h => Bounds.include_keeps h q.x q.y)
    (fun b => b.include_self p.x p.y) pts b hp

theorem normalized_box_inside {l : Layout} {margin : Int} {canvas : Size} {out : Layout}
    (hm : 0 ≤ margin) (hn : normalize margin l = .ok (canvas, out))
    {r : Rect} (hr : r ∈ out.boxes) :
    Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ r := by
  unfold normalize at hn
  split at hn
  · have he := Except.ok.inj hn
    cases he
    simp_all
  · dsimp only at hn
    split at hn
    · cases hn
    · have he := Except.ok.inj hn
      cases he
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      have h := l.bounds_box hr0
      unfold Bounds.Covers at h
      unfold Rect.Contained
      simp only
      omega

def sideSub (ns : List Node) (g : Gaps) (right : Bool) : Sub :=
  buildSub g (entOf ns 0)
    ((if right then (splitSides (kidsOf ns 0)).1 else (splitSides (kidsOf ns 0)).2).map
      (sub ns g))

theorem sideSub_good {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (right : Bool) : Good g (sideSub ns g right) := by
  have h := mindmap_sides_valid hL hs hv h0
  cases right with
  | true => exact h.1.good
  | false => exact h.2.good

theorem sideSub_me (ns : List Node) (g : Gaps) (right : Bool) :
    (sideSub ns g right).me = entOf ns 0 := by
  unfold sideSub buildSub
  rfl

theorem sideSub_root {ns : List Node} {g : Gaps} {right : Bool}
    (hg : Good g (sideSub ns g right)) :
    ((sideSub ns g right).me.orient right (rootOf ns)) = rootOf ns := by
  apply orient_me right (rootOf ns) _ (by rw [sideSub_me]; exact entOf_idx _ _)
    hg.me_u hg.me_y
  · rw [sideSub_me]
    rfl
  · rw [sideSub_me]
    rfl
  · rfl

def PlacedEnt (ns : List Node) (g : Gaps) (e : AEnt) : Prop :=
  e = rootOf ns ∨ ∃ right o, o ∈ (sideSub ns g right).rest ∧
    e = o.orient right (rootOf ns)

theorem placedEdges_origin {ns : List Node} {g : Gaps} {e : AEdge}
    (he : e ∈ placedEdges ns g) :
    ∃ right pc, pc ∈ (sideSub ns g right).edges ∧
      e = ⟨right, pc.1.orient right (rootOf ns), pc.2.orient right (rootOf ns)⟩ := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨pc, hp, rfl⟩ := List.mem_map.mp he
    exact ⟨true, pc, hp, rfl⟩
  · obtain ⟨pc, hp, rfl⟩ := List.mem_map.mp he
    exact ⟨false, pc, hp, rfl⟩

theorem placedEdges_child {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {e : AEdge} (he : e ∈ placedEdges ns g) : PlacedEnt ns g e.c := by
  obtain ⟨right, pc, hp, rfl⟩ := placedEdges_origin he
  exact Or.inr ⟨right, pc.2, (sideSub_good hL hs hv h0 right).closed1 pc hp |>.2, rfl⟩

theorem placedEnt_dims {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {e : AEnt} (he : PlacedEnt ns g e) : 0 < e.w ∧ 0 ≤ e.h := by
  have hd := entOf_facts hv.dims h0
  rcases he with rfl | ⟨right, o, ho, rfl⟩
  · exact hd.2.2
  · simpa only [orient_w, orient_h] using
      (sideSub_good hL hs hv h0 right).rest_dims o ho

theorem placedEnt_apart {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {a b : AEnt} (ha : PlacedEnt ns g a) (hb : PlacedEnt ns g b) (hab : a.idx ≠ b.idx) :
    Disjoint a.rect b.rect := by
  rcases ha with rfl | ⟨ra, oa, hoa, rfl⟩
  · rcases hb with rfl | ⟨rb, ob, hob, rfl⟩
    · exact False.elim (hab rfl)
    · have hg := sideSub_good hL hs hv h0 rb
      have hi : (sideSub ns g rb).me.idx = (rootOf ns).idx := by
        rw [sideSub_me]
        exact entOf_idx _ _
      simpa only [sideSub_root hg] using
        side_boxes_disjoint hg List.mem_cons_self (List.mem_cons_of_mem _ hob)
          (by simpa only [hi, orient_idx] using hab) rb (rootOf ns)
  · rcases hb with rfl | ⟨rb, ob, hob, rfl⟩
    · have hg := sideSub_good hL hs hv h0 ra
      have hi : (sideSub ns g ra).me.idx = (rootOf ns).idx := by
        rw [sideSub_me]
        exact entOf_idx _ _
      simpa only [sideSub_root hg] using
        side_boxes_disjoint hg (List.mem_cons_of_mem _ hoa) List.mem_cons_self
          (by simpa only [hi, orient_idx] using hab) ra (rootOf ns)
    · by_cases hr : ra = rb
      · subst rb
        exact side_boxes_disjoint (sideSub_good hL hs hv h0 ra)
          (List.mem_cons_of_mem _ hoa) (List.mem_cons_of_mem _ hob)
          (by simpa only [orient_idx] using hab) ra (rootOf ns)
      · cases ra <;> cases rb
        · exact False.elim (hr rfl)
        · apply (Rect.disjoint_comm _ _).mp
          exact opposite_boxes_disjoint hL (sideSub_good hL hs hv h0 true)
            (sideSub_good hL hs hv h0 false)
            (by rw [sideSub_me, sideSub_me]) (by rw [sideSub_me]; rfl) ob hob oa hoa
        · exact opposite_boxes_disjoint hL (sideSub_good hL hs hv h0 true)
            (sideSub_good hL hs hv h0 false)
            (by rw [sideSub_me, sideSub_me]) (by rw [sideSub_me]; rfl) oa hoa ob hob
        · exact False.elim (hr rfl)

theorem placedEdges_parent {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {e : AEdge} (he : e ∈ placedEdges ns g) : PlacedEnt ns g e.p := by
  obtain ⟨right, pc, hp, rfl⟩ := placedEdges_origin he
  have hg := sideSub_good hL hs hv h0 right
  rcases List.mem_cons.mp (hg.closed1 pc hp).1 with hme | hrest
  · left
    rw [hme]
    exact sideSub_root hg
  · exact Or.inr ⟨right, pc.1, hrest, rfl⟩

theorem placedEdges_clear {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {e : AEdge} (he : e ∈ placedEdges ns g) {o : AEnt} (ho : PlacedEnt ns g o)
    (hp : o.idx ≠ e.p.idx) (hc : o.idx ≠ e.c.idx) :
    ¬ Polyline.hitsRect (e.route g) o.rect := by
  obtain ⟨right, pc, hpc, rfl⟩ := placedEdges_origin he
  have hg := sideSub_good hL hs hv h0 right
  rcases ho with rfl | ⟨ro, o, ho, rfl⟩
  · have hi : (sideSub ns g right).me.idx = (rootOf ns).idx := by
      rw [sideSub_me]
      exact entOf_idx _ _
    simpa only [sideSub_root hg] using
      side_clear hL hg hpc List.mem_cons_self
        (by simpa only [hi, orient_idx] using hp)
        (by simpa only [hi, orient_idx] using hc) right (rootOf ns)
  · by_cases hr : right = ro
    · subst ro
      exact side_clear hL hg hpc (List.mem_cons_of_mem _ ho)
        (by simpa only [orient_idx] using hp)
        (by simpa only [orient_idx] using hc) right (rootOf ns)
    · have hro : ro = !right := by cases right <;> cases ro <;> simp_all
      subst ro
      exact opposite_route_clear hL hg (sideSub_good hL hs hv h0 (!right))
        (by rw [sideSub_me, sideSub_me]) (by rw [sideSub_me]; rfl) hpc ho right

theorem placedEdges_ports {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {e : AEdge} (he : e ∈ placedEdges ns g) :
    ∃ a b : Point, (e.route g).head? = some a ∧ (e.route g).getLast? = some b ∧
      Validator.onBoundary a e.p.rect ∧ Validator.onBoundary b e.c.rect := by
  have hp := placedEnt_dims hL hs hv h0 (placedEdges_parent hL hs hv h0 he)
  have hc := placedEnt_dims hL hs hv h0 (placedEdges_child hL hs hv h0 he)
  exact route_ports ⟨by omega, hp.2⟩ ⟨by omega, hc.2⟩

theorem sideSub_ok {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (right : Bool) :
    SideOK ns g (if right then (splitSides (kidsOf ns 0)).1
      else (splitSides (kidsOf ns 0)).2) := by
  have h := mindmap_sides_valid hL hs hv h0
  cases right with
  | true => exact h.1
  | false => exact h.2

theorem sideSub_rest_positive {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {right : Bool} {o : Ent} (ho : o ∈ (sideSub ns g right).rest) : 0 < o.idx := by
  obtain ⟨c, hc, hu⟩ := (sideSub_ok hL hs hv h0 right).under o ho
  have hk : c ∈ kidsOf ns 0 := by
    cases right with
    | true => exact (splitSides_fst_sublist _).subset hc
    | false => exact (splitSides_snd_sublist _).subset hc
  have hcp := (kidsOf_mem hk).1
  have hle := hu.le hv.parentLt
  omega

theorem sideSub_opposite_indices {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {a b : Ent} (ha : a ∈ (sideSub ns g true).rest)
    (hb : b ∈ (sideSub ns g false).rest) : a.idx ≠ b.idx := by
  intro he
  obtain ⟨ca, hca, hua⟩ := (sideSub_ok hL hs hv h0 true).under a ha
  obtain ⟨cb, hcb, hub⟩ := (sideSub_ok hL hs hv h0 false).under b hb
  have hka := (splitSides_fst_sublist _).subset hca
  have hkb := (splitSides_snd_sublist _).subset hcb
  have heq := under_child_unique hv.parentLt (kidsOf_mem hka).2.2
    (kidsOf_mem hkb).2.2 a.idx a.idx (Nat.le_refl _) hua (by rw [he]; exact hub)
  rw [← heq] at hcb
  exact splitSides_disjoint (kidsOf_nodup ns 0) hca hcb

theorem placedEnt_ext {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {a b : AEnt} (ha : PlacedEnt ns g a) (hb : PlacedEnt ns g b) (hab : a.idx = b.idx) :
    a = b := by
  rcases ha with rfl | ⟨ra, oa, hoa, rfl⟩
  · rcases hb with rfl | ⟨rb, ob, hob, rfl⟩
    · rfl
    · have hi := sideSub_rest_positive hL hs hv h0 hob
      have he : 0 = ob.idx := by simpa only [orient_idx, rootOf] using hab
      omega
  · rcases hb with rfl | ⟨rb, ob, hob, rfl⟩
    · have hi := sideSub_rest_positive hL hs hv h0 hoa
      have he : oa.idx = 0 := by simpa only [orient_idx, rootOf] using hab
      omega
    · have he : oa.idx = ob.idx := by simpa only [orient_idx] using hab
      by_cases hr : ra = rb
      · subst rb
        have hn := (sideSub_ok hL hs hv h0 ra).nodup
        by_cases ho : oa = ob
        · rw [ho]
        · have ht := pairwise_total _ hn oa (List.mem_cons_of_mem _ hoa)
            ob (List.mem_cons_of_mem _ hob) ho
          exact False.elim (ht.elim (fun h => h he) (fun h => h he.symm))
      · cases ra <;> cases rb
        · exact False.elim (hr rfl)
        · exact False.elim (sideSub_opposite_indices hL hs hv h0 hob hoa he.symm)
        · exact False.elim (sideSub_opposite_indices hL hs hv h0 hoa hob he)
        · exact False.elim (hr rfl)

theorem boxEnt_spec {root : AEnt} {edges : List AEdge} {i : Nat} {a : AEnt}
    (hroot : root.idx = 0) (h : boxEnt root edges i = some a) :
    a.idx = i ∧ (a = root ∨ ∃ e ∈ edges, a = e.c) := by
  unfold boxEnt at h
  split at h
  · rename_i hi
    have he := Option.some.inj h
    subst a
    exact ⟨hroot.trans hi.symm, Or.inl rfl⟩
  · cases hf : edges.find? (fun e => e.c.idx == i) with
    | none => simp [hf] at h
    | some e =>
      have he : e.c = a := by simpa only [hf, Option.map_some, Option.some.injEq] using h
      subst a
      exact ⟨by simpa using List.find?_some hf,
        Or.inr ⟨e, List.mem_of_find?_eq_some hf, rfl⟩⟩

theorem boxRect_spec {root : AEnt} {edges : List AEdge} {i : Nat} {r : Rect}
    (hroot : root.idx = 0) (h : boxRect root edges i = .ok r) :
    ∃ a, boxEnt root edges i = some a ∧ a.idx = i ∧ a.rect = r ∧
      (a = root ∨ ∃ e ∈ edges, a = e.c) := by
  unfold boxRect at h
  cases he : boxEnt root edges i with
  | none => simp [he] at h
  | some a =>
    rw [he] at h
    cases hr : a.rect? with
    | none => simp [hr] at h
    | some rr =>
      have heq : rr = r := by simpa only [hr, Except.ok.injEq] using h
      subst rr
      have hs := boxEnt_spec hroot he
      refine ⟨a, rfl, hs.1, ?_, hs.2⟩
      unfold AEnt.rect? at hr
      split at hr
      · exact Option.some.inj hr
      · cases hr

theorem boxRects_record {root : AEnt} {edges : List AEdge} :
    ∀ (is : List Nat) (rs : List Rect), boxRects root edges is = .ok rs →
      is.length = rs.length ∧
      ∀ (k i : Nat) (r : Rect), is[k]? = some i → rs[k]? = some r →
        boxRect root edges i = .ok r := by
  intro is
  induction is with
  | nil =>
    intro rs h
    have he := Except.ok.inj h
    subst rs
    exact ⟨rfl, by intro k i r hi; simp at hi⟩
  | cons i is ih =>
    intro rs h
    unfold boxRects at h
    cases hi : boxRect root edges i with
    | error e => simp [hi] at h
    | ok r =>
      rw [hi] at h
      cases ht : boxRects root edges is with
      | error e => simp [ht] at h
      | ok tail =>
        have he : r :: tail = rs := by simpa only [ht, Except.ok.injEq] using h
        subst rs
        obtain ⟨hlen, hget⟩ := ih tail ht
        refine ⟨by simp [hlen], ?_⟩
        intro k j s hj hs
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hs
          subst j
          subst s
          exact hi
        | succ k =>
          exact hget k j s hj hs

theorem layoutRaw_record {ns : List Node} {g : Gaps} {l : Layout}
    (h : layoutRaw ns g = .ok l) :
    l.boxes.length = ns.length ∧
    l.routes = (List.range ns.length).map (routeAt g (placedEdges ns g)) ∧
    ∀ (i : Nat) (r : Rect), l.boxes[i]? = some r →
      boxRect (rootOf ns) (placedEdges ns g) i = .ok r := by
  unfold layoutRaw at h
  cases hb : boxRects (rootOf ns) (placedEdges ns g) (List.range ns.length) with
  | error e => simp [hb] at h
  | ok boxes =>
    have he : (⟨boxes, (List.range ns.length).map (routeAt g (placedEdges ns g))⟩ : Layout) = l := by
      simpa only [hb, Except.ok.injEq] using h
    subst l
    obtain ⟨hlen, hget⟩ := boxRects_record _ _ hb
    refine ⟨by simpa using hlen.symm, rfl, ?_⟩
    intro i r hr
    have hi : i < ns.length := by
      have hib : i < boxes.length := (List.getElem?_eq_some_iff.mp hr).1
      have hlen' : ns.length = boxes.length := by simpa only [List.length_range] using hlen
      omega
    exact hget i i r (by simp [hi]) hr

theorem placedEdges_parent_index {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {e : AEdge} (he : e ∈ placedEdges ns g) :
    parentOf ns e.c.idx = some e.p.idx := by
  obtain ⟨right, pc, hp, rfl⟩ := placedEdges_origin he
  simpa only [orient_idx] using (sideSub_ok hL hs hv h0 right).par pc hp

theorem layoutRaw_box_ent {ns : List Node} {g : Gaps} {l : Layout}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (h : layoutRaw ns g = .ok l) {i : Nat} {r : Rect} (hr : l.boxes[i]? = some r) :
    ∃ a, a.idx = i ∧ a.rect = r ∧ PlacedEnt ns g a := by
  obtain ⟨a, _, hi, ha, ho⟩ := boxRect_spec rfl ((layoutRaw_record h).2.2 i r hr)
  refine ⟨a, hi, ha, ?_⟩
  rcases ho with rfl | ⟨e, he, rfl⟩
  · exact Or.inl rfl
  · exact placedEdges_child hL hs hv h0 he

theorem layoutRaw_lookup {ns : List Node} {g : Gaps} {l : Layout}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (h : layoutRaw ns g = .ok l) {a : AEnt} (ha : PlacedEnt ns g a)
    (hi : a.idx < ns.length) : l.boxes[a.idx]? = some a.rect := by
  have hb : a.idx < l.boxes.length := by rw [(layoutRaw_record h).1]; exact hi
  have hget := List.getElem?_eq_getElem hb
  obtain ⟨b, hbi, hbr, hbp⟩ := layoutRaw_box_ent hL hs hv h0 h hget
  have he := placedEnt_ext hL hs hv h0 hbp ha hbi
  rw [he] at hbr
  rw [hget, ← hbr]

theorem layoutRaw_disjoint {ns : List Node} {g : Gaps} {l : Layout}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (h : layoutRaw ns g = .ok l) {i j : Nat} {a b : Rect}
    (ha : l.boxes[i]? = some a) (hb : l.boxes[j]? = some b) (hij : i ≠ j) :
    Disjoint a b := by
  obtain ⟨ea, hei, her, hep⟩ := layoutRaw_box_ent hL hs hv h0 h ha
  obtain ⟨eb, hfi, hfr, hfp⟩ := layoutRaw_box_ent hL hs hv h0 h hb
  rw [← her, ← hfr]
  exact placedEnt_apart hL hs hv h0 hep hfp (by rw [hei, hfi]; exact hij)

theorem layoutRaw_route_spec {ns : List Node} {g : Gaps} {l : Layout}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (h : layoutRaw ns g = .ok l) {i p : Nat} (hi : i < ns.length)
    (hp : parentOf ns i = some p) :
    ∃ e ∈ placedEdges ns g, e.c.idx = i ∧ e.p.idx = p ∧
      l.routes[i]? = some (e.route g) := by
  have hn : i ≠ 0 := by have := hv.parentLt i p hp; omega
  have hbi : i < l.boxes.length := by rw [(layoutRaw_record h).1]; exact hi
  have hbr := (layoutRaw_record h).2.2 i _ (List.getElem?_eq_getElem hbi)
  obtain ⟨a, he, _, _, _⟩ := boxRect_spec rfl hbr
  unfold boxEnt at he
  rw [ite_eq_right hn] at he
  cases hf : (placedEdges ns g).find? (fun e => e.c.idx == i) with
  | none => simp [hf] at he
  | some e =>
    have hem := List.mem_of_find?_eq_some hf
    have hei : e.c.idx = i := by simpa using List.find?_some hf
    have hpi := placedEdges_parent_index hL hs hv h0 hem
    rw [hei, hp] at hpi
    refine ⟨e, hem, hei, (Option.some.inj hpi).symm, ?_⟩
    rw [(layoutRaw_record h).2.1]
    simp [hi, routeAt, hn, hf]

theorem mindmap_nonempty {ns : List Node} {g : Gaps} {l : Layout}
    (h0 : 0 < ns.length) (h : mindmap ns g = .ok l) :
    Valid ns ∧ layoutRaw ns g = .ok l := by
  have hn : ns.isEmpty = false := by cases ns <;> simp_all
  unfold mindmap at h
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  · rename_i hb
    have hl : link ns = true := by cases he : link ns <;> simp_all
    exact ⟨link_valid hl, h⟩

theorem raw_route_ports {ns : List Node} {g : Gaps} {l : Layout}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (h : layoutRaw ns g = .ok l) {i p : Nat} (hi : i < ns.length)
    (hp : parentOf ns i = some p) :
    ∃ pts a b pr cr, l.routes[i]? = some pts ∧
      l.boxes[p]? = some pr ∧ l.boxes[i]? = some cr ∧
      pts.head? = some a ∧ pts.getLast? = some b ∧
      Validator.onBoundary a pr ∧ Validator.onBoundary b cr ∧
      Polyline.isOrthogonal pts = true := by
  obtain ⟨e, he, hei, hep, her⟩ := layoutRaw_route_spec hL hs hv h0 h hi hp
  obtain ⟨a, b, ha, hb, hpa, hpb⟩ := placedEdges_ports hL hs hv h0 he
  have hpar : p < ns.length := by have := hv.parentLt i p hp; omega
  have hpr := layoutRaw_lookup hL hs hv h0 h (placedEdges_parent hL hs hv h0 he)
    (by rw [hep]; exact hpar)
  have hcr := layoutRaw_lookup hL hs hv h0 h (placedEdges_child hL hs hv h0 he)
    (by rw [hei]; exact hi)
  rw [hep] at hpr
  rw [hei] at hcr
  exact ⟨e.route g, a, b, e.p.rect, e.c.rect, her, hpr, hcr,
    ha, hb, hpa, hpb, route_orth g e⟩

theorem raw_route_clear {ns : List Node} {g : Gaps} {l : Layout}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (h : layoutRaw ns g = .ok l) {i p k : Nat} (hi : i < ns.length)
    (hp : parentOf ns i = some p) {pts : List Point} (hr : l.routes[i]? = some pts)
    {r : Rect} (hb : l.boxes[k]? = some r) (hkp : k ≠ p) (hki : k ≠ i) :
    ¬ Polyline.hitsRect pts r := by
  obtain ⟨e, he, hei, hep, her⟩ := layoutRaw_route_spec hL hs hv h0 h hi hp
  have hepts := Option.some.inj (hr.symm.trans her)
  obtain ⟨a, hai, har, hap⟩ := layoutRaw_box_ent hL hs hv h0 h hb
  rw [hepts, ← har]
  exact placedEdges_clear hL hs hv h0 he hap
    (by rw [hai, hep]; exact hkp) (by rw [hai, hei]; exact hki)

theorem placedEdges_aside {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    {e : AEdge} (he : e ∈ placedEdges ns g) {o : AEnt} (ho : PlacedEnt ns g o)
    (hp : o.idx ≠ e.p.idx) (hc : o.idx ≠ e.c.idx) :
    Aside (e.route g) o.rect := by
  obtain ⟨right, pc, hpc, rfl⟩ := placedEdges_origin he
  have hg := sideSub_good hL hs hv h0 right
  rcases ho with rfl | ⟨ro, o, ho, rfl⟩
  · have hi : (sideSub ns g right).me.idx = (rootOf ns).idx := by
      rw [sideSub_me]
      exact entOf_idx _ _
    simpa only [sideSub_root hg] using
      orient_clear hL (hg.edge_u pc hpc)
        (hg.clear pc hpc _ List.mem_cons_self
          (by simpa only [hi, orient_idx] using hp)
          (by simpa only [hi, orient_idx] using hc)) right (rootOf ns)
  · by_cases hr : right = ro
    · subst ro
      exact orient_clear hL (hg.edge_u pc hpc)
        (hg.clear pc hpc o (List.mem_cons_of_mem _ ho)
          (by simpa only [orient_idx] using hp)
          (by simpa only [orient_idx] using hc)) right (rootOf ns)
    · have hro : ro = !right := by cases right <;> cases ro <;> simp_all
      subst ro
      apply aside_of_clear hL (orient_linked (hg.edge_u pc hpc) right (rootOf ns))
      have ht := sideSub_good hL hs hv h0 (!right)
      have hpw := hg.right_edge hL (hg.closed1 pc hpc).1
      have hou := ht.rest_u o ho
      have hmw := hg.me_w
      have hw : (sideSub ns g right).me.w = (rootOf ns).w := by rw [sideSub_me]; rfl
      have htw : (sideSub ns g (!right)).me.w = (rootOf ns).w := by rw [sideSub_me]; rfl
      cases right <;>
        simp [AEdge.xlo, AEdge.xhi, Ent.orient, AEnt.top] <;> omega

theorem raw_route_aside {ns : List Node} {g : Gaps} {l : Layout}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length)
    (h : layoutRaw ns g = .ok l) {i p k : Nat} (hi : i < ns.length)
    (hp : parentOf ns i = some p) {pts : List Point} (hr : l.routes[i]? = some pts)
    {r : Rect} (hb : l.boxes[k]? = some r) (hkp : k ≠ p) (hki : k ≠ i) :
    Aside pts r := by
  obtain ⟨e, he, hei, hep, her⟩ := layoutRaw_route_spec hL hs hv h0 h hi hp
  have hepts := Option.some.inj (hr.symm.trans her)
  obtain ⟨a, hai, har, hap⟩ := layoutRaw_box_ent hL hs hv h0 h hb
  rw [hepts, ← har]
  exact placedEdges_aside hL hs hv h0 he hap
    (by rw [hai, hep]; exact hkp) (by rw [hai, hei]; exact hki)

theorem disjoint_translate_raw {a b : Rect} (h : Disjoint a b) (dx dy : Int) :
    Disjoint (a.translateRaw dx dy) (b.translateRaw dx dy) := by
  unfold Disjoint Rect.meetsInterior Rect.translateRaw at *
  dsimp only at *
  omega

theorem boundary_translate_raw {p : Point} {r : Rect} (h : Validator.onBoundary p r)
    (dx dy : Int) :
    Validator.onBoundary ⟨p.x + dx, p.y + dy⟩ (r.translateRaw dx dy) := by
  unfold Validator.onBoundary Rect.translateRaw at *
  dsimp only at *
  omega

theorem orthogonal_translate (dx dy : Int) : ∀ pts : List Point,
    Polyline.isOrthogonal (pts.map fun p => ⟨p.x + dx, p.y + dy⟩) =
      Polyline.isOrthogonal pts
  | [] => rfl
  | [_] => rfl
  | p :: q :: rest => by
    change ((decide (p.x + dx = q.x + dx) || decide (p.y + dy = q.y + dy)) &&
      Polyline.isOrthogonal ((q :: rest).map fun r => ⟨r.x + dx, r.y + dy⟩)) =
      ((decide (p.x = q.x) || decide (p.y = q.y)) && Polyline.isOrthogonal (q :: rest))
    rw [orthogonal_translate dx dy (q :: rest)]
    simp

theorem normalize_translate {margin : Int} {l out : Layout} {canvas : Size}
    (h : normalize margin l = .ok (canvas, out)) :
    ∃ dx dy, out = l.translate dx dy := by
  unfold normalize at h
  split at h
  · have he := Except.ok.inj h
    cases he
    exact ⟨0, 0, by cases l; simp [Layout.translate]⟩
  · dsimp only at h
    split at h
    · cases h
    · have he := Except.ok.inj h
      cases he
      exact ⟨_, _, rfl⟩

end Tree
end Elegant
