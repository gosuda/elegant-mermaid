import Elegant.Tree

set_option autoImplicit false

/-! Facts about the tree family of `Elegant.Tree`: the invariant `Good` of a placed subtree (its
boxes are pairwise apart, and the bounding box of the route of every edge misses every other
box), and its preservation by `buildSub`. The invariant is what the validity theorem of the
mindmap layout is built from. -/

namespace Elegant
namespace Tree

theorem pairwise_total {α : Type} {R : α → α → Prop} :
    ∀ (l : List α), l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y ∨ R y x
  | [], _, x, hx, _, _, _ => by simp at hx
  | z :: zs, h, x, hx, y, hy, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hne
      · exact Or.inl (h.1 y hy')
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact Or.inr (h.1 x hx')
      · exact pairwise_total zs h.2 x hx' y hy' hne

/-! ### Shifted entries -/

theorem Ent.shift_top (du dy : Int) (e : Ent) : (e.shift du dy).top = e.top + dy := by
  unfold Ent.top
  show e.y + dy - Int.fdiv e.h 2 = e.y - Int.fdiv e.h 2 + dy
  omega

theorem Ent.shift_bottom (du dy : Int) (e : Ent) : (e.shift du dy).bottom = e.bottom + dy := by
  unfold Ent.bottom
  rw [Ent.shift_top]
  show e.top + dy + e.h = e.top + e.h + dy
  omega

/-- The boxes of two entries share no interior point. -/
def Ent.Apart (a b : Ent) : Prop :=
  a.u + a.w ≤ b.u ∨ b.u + b.w ≤ a.u ∨ a.bottom ≤ b.top ∨ b.bottom ≤ a.top

theorem Ent.Apart.symm {a b : Ent} (h : a.Apart b) : b.Apart a := by
  unfold Ent.Apart at h ⊢
  omega

theorem Ent.apart_shift {a b : Ent} (du dy : Int) (h : a.Apart b) :
    (a.shift du dy).Apart (b.shift du dy) := by
  unfold Ent.Apart at h ⊢
  show a.u + du + a.w ≤ b.u + du ∨ b.u + du + b.w ≤ a.u + du ∨
    (a.shift du dy).bottom ≤ (b.shift du dy).top ∨ (b.shift du dy).bottom ≤ (a.shift du dy).top
  rw [Ent.shift_bottom, Ent.shift_top, Ent.shift_bottom, Ent.shift_top]
  omega

/-- The bounding box of the route of the edge `p → c` misses the box of `e`. -/
def Ent.Clear (p c e : Ent) : Prop :=
  e.u + e.w ≤ p.u + p.w ∨ c.u ≤ e.u ∨ max p.y c.y ≤ e.top ∨ e.bottom ≤ min p.y c.y

theorem Ent.clear_shift {p c e : Ent} (du dy : Int) (h : Ent.Clear p c e) :
    Ent.Clear (p.shift du dy) (c.shift du dy) (e.shift du dy) := by
  unfold Ent.Clear at h ⊢
  show e.u + du + e.w ≤ p.u + du + p.w ∨ c.u + du ≤ e.u + du ∨
    max (p.y + dy) (c.y + dy) ≤ (e.shift du dy).top ∨
      (e.shift du dy).bottom ≤ min (p.y + dy) (c.y + dy)
  rw [Ent.shift_top, Ent.shift_bottom]
  omega

theorem overlaps_iff (g : Gaps) (a b : Ent) :
    (a.contour g).overlaps (b.contour g) = true ↔
      a.u - g.level < b.u + b.w ∧ b.u - g.level < a.u + a.w := by
  unfold Contour.overlaps Ent.contour
  simp only [decide_eq_true_eq]

/-- Two entries placed at the same column, at the offsets `da` and `db`, are apart when their
widened contours keep the sibling gap, or do not overlap. -/
theorem apart_of_sep {g : Gaps} (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) {a b : Ent}
    {st da db : Int}
    (h : (a.contour g).overlaps (b.contour g) = true →
      (a.contour g).bottom + da + g.sibling ≤ db + (b.contour g).top) :
    (a.shift st da).Apart (b.shift st db) := by
  unfold Ent.Apart
  rw [Ent.shift_bottom, Ent.shift_top]
  by_cases hov : (a.contour g).overlaps (b.contour g) = true
  · have h1 := h hov
    have h2 : a.bottom + da + g.sibling ≤ db + b.top := h1
    show _ ∨ _ ∨ a.bottom + da ≤ b.top + db ∨ _
    omega
  · rw [overlaps_iff] at hov
    show a.u + st + a.w ≤ b.u + st ∨ b.u + st + b.w ≤ a.u + st ∨ _ ∨ _
    omega

/-! ### The invariant of a placed subtree -/

structure Good (g : Gaps) (s : Sub) : Prop where
  me_u : s.me.u = 0
  me_y : s.me.y = 0
  me_w : 0 < s.me.w
  me_h : 0 ≤ s.me.h
  rest_dims : ∀ e ∈ s.rest, 0 < e.w ∧ 0 ≤ e.h
  rest_u : ∀ e ∈ s.rest, s.me.w + g.level ≤ e.u
  apart : ∀ a ∈ s.ents, ∀ b ∈ s.ents, a.idx ≠ b.idx → a.Apart b
  closed1 : ∀ pc ∈ s.edges, pc.1 ∈ s.ents ∧ pc.2 ∈ s.rest
  closed2 : ∀ o ∈ s.rest, ∃ pc ∈ s.edges, pc.2 = o
  edge_u : ∀ pc ∈ s.edges, pc.2.u = pc.1.u + pc.1.w + g.level
  clear : ∀ pc ∈ s.edges, ∀ e ∈ s.ents, e.idx ≠ pc.1.idx → e.idx ≠ pc.2.idx →
    Ent.Clear pc.1 pc.2 e

theorem Good.ents_dims {g : Gaps} {s : Sub} (h : Good g s) : ∀ e ∈ s.ents, 0 < e.w ∧ 0 ≤ e.h := by
  intro e he
  rcases List.mem_cons.mp he with rfl | hr
  · exact ⟨h.me_w, h.me_h⟩
  · exact h.rest_dims e hr

theorem Good.ents_u {g : Gaps} {s : Sub} (h : Good g s) (hL : 0 ≤ g.level) :
    ∀ e ∈ s.ents, 0 ≤ e.u := by
  intro e he
  rcases List.mem_cons.mp he with rfl | hr
  · have := h.me_u
    omega
  · have := h.rest_u e hr
    have := h.me_w
    omega

/-! ### Membership in a built subtree -/

theorem mem_ents_buildSub {g : Gaps} {me : Ent} {kids : List Sub} {e : Ent} :
    e ∈ (buildSub g me kids).ents ↔ e = me ∨ e ∈ (buildSub g me kids).rest := by
  unfold Sub.ents
  rw [List.mem_cons]
  rfl

theorem mem_rest_buildSub {g : Gaps} {me : Ent} {kids : List Sub} {e : Ent} :
    e ∈ (buildSub g me kids).rest ↔
      ∃ kd ∈ kids.zip (dysOf g (kids.map Sub.ents)),
        ∃ o ∈ kd.1.ents, Ent.shift (me.w + g.level) kd.2 o = e := by
  unfold buildSub
  simp only [List.mem_flatMap, List.mem_map]

theorem mem_edges_buildSub {g : Gaps} {me : Ent} {kids : List Sub} {pc : Ent × Ent} :
    pc ∈ (buildSub g me kids).edges ↔
      ∃ kd ∈ kids.zip (dysOf g (kids.map Sub.ents)),
        pc = (me, Ent.shift (me.w + g.level) kd.2 kd.1.me) ∨
        ∃ pc' ∈ kd.1.edges, Ent.shiftEdge (me.w + g.level) kd.2 pc' = pc := by
  unfold buildSub
  simp only [List.mem_flatMap, List.mem_cons, List.mem_map]

theorem buildSub_good {g : Gaps} {me : Ent} {kids : List Sub}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling)
    (hu : me.u = 0) (hy : me.y = 0) (hw : 0 < me.w) (hh : 0 ≤ me.h)
    (hk : ∀ k ∈ kids, Good g k) : Good g (buildSub g me kids) := by
  have hsep : (kids.zip (dysOf g (kids.map Sub.ents))).Pairwise (fun p q =>
      ∀ a ∈ p.1.ents, ∀ b ∈ q.1.ents, (a.contour g).overlaps (b.contour g) = true →
        (a.contour g).bottom + p.2 + g.sibling ≤ q.2 + (b.contour g).top) := by
    have h := mindmap_siblings_separated g (kids.map Sub.ents)
    rw [List.zip_map_left, List.pairwise_map] at h
    exact h
  refine ⟨hu, hy, hw, hh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp he
    exact (hk kd.1 (List.of_mem_zip hkd).1).ents_dims o ho
  · intro e he
    obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp he
    have := (hk kd.1 (List.of_mem_zip hkd).1).ents_u hL o ho
    show me.w + g.level ≤ o.u + (me.w + g.level)
    omega
  · intro a ha b hb hne
    rcases mem_ents_buildSub.mp ha with rfl | har <;> rcases mem_ents_buildSub.mp hb with rfl | hbr
    · exact absurd rfl hne
    · obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp hbr
      have := (hk kd.1 (List.of_mem_zip hkd).1).ents_u hL o ho
      unfold Ent.Apart
      left
      show a.u + a.w ≤ o.u + (a.w + g.level)
      omega
    · obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp har
      have := (hk kd.1 (List.of_mem_zip hkd).1).ents_u hL o ho
      unfold Ent.Apart
      right; left
      show b.u + b.w ≤ o.u + (b.w + g.level)
      omega
    · obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp har
      obtain ⟨kd', hkd', o', ho', rfl⟩ := mem_rest_buildSub.mp hbr
      by_cases hkk : kd = kd'
      · subst hkk
        have hne' : o.idx ≠ o'.idx := hne
        exact Ent.apart_shift _ _
          ((hk kd.1 (List.of_mem_zip hkd).1).apart o ho o' ho' hne')
      · rcases pairwise_total _ hsep kd hkd kd' hkd' hkk with hlt | hgt
        · exact apart_of_sep hL hs (hlt o ho o' ho')
        · exact (apart_of_sep hL hs (hgt o' ho' o ho)).symm
  · intro pc hpc
    obtain ⟨kd, hkd, h | ⟨pc', hpc', rfl⟩⟩ := mem_edges_buildSub.mp hpc
    · subst h
      exact ⟨mem_ents_buildSub.mpr (Or.inl rfl),
        mem_rest_buildSub.mpr ⟨kd, hkd, kd.1.me, List.mem_cons_self, rfl⟩⟩
    · have hg := (hk kd.1 (List.of_mem_zip hkd).1).closed1 pc' hpc'
      exact ⟨mem_ents_buildSub.mpr (Or.inr (mem_rest_buildSub.mpr ⟨kd, hkd, pc'.1, hg.1, rfl⟩)),
        mem_rest_buildSub.mpr ⟨kd, hkd, pc'.2, List.mem_cons_of_mem _ hg.2, rfl⟩⟩
  · intro o' ho'
    obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp ho'
    rcases List.mem_cons.mp ho with rfl | hor
    · exact ⟨_, mem_edges_buildSub.mpr ⟨kd, hkd, Or.inl rfl⟩, rfl⟩
    · obtain ⟨pc', hpc', hpc2⟩ := (hk kd.1 (List.of_mem_zip hkd).1).closed2 o hor
      refine ⟨Ent.shiftEdge (me.w + g.level) kd.2 pc', mem_edges_buildSub.mpr ⟨kd, hkd, Or.inr ⟨pc', hpc', rfl⟩⟩, ?_⟩
      show Ent.shift _ _ pc'.2 = _
      rw [hpc2]
  · intro pc hpc
    obtain ⟨kd, hkd, h | ⟨pc', hpc', rfl⟩⟩ := mem_edges_buildSub.mp hpc
    · subst h
      have := (hk kd.1 (List.of_mem_zip hkd).1).me_u
      show kd.1.me.u + (me.w + g.level) = me.u + me.w + g.level
      omega
    · have := (hk kd.1 (List.of_mem_zip hkd).1).edge_u pc' hpc'
      show pc'.2.u + (me.w + g.level) = pc'.1.u + (me.w + g.level) + pc'.1.w + g.level
      omega
  · intro pc hpc e he hep hec
    obtain ⟨kd, hkd, h | ⟨pc', hpc', rfl⟩⟩ := mem_edges_buildSub.mp hpc
    · subst h
      rcases mem_ents_buildSub.mp he with rfl | her
      · exact absurd rfl hep
      · obtain ⟨kd', hkd', o', ho', rfl⟩ := mem_rest_buildSub.mp her
        have h1 := (hk kd.1 (List.of_mem_zip hkd).1).me_u
        have h2 := (hk kd'.1 (List.of_mem_zip hkd').1).ents_u hL o' ho'
        unfold Ent.Clear
        right; left
        show kd.1.me.u + (me.w + g.level) ≤ o'.u + (me.w + g.level)
        omega
    · have hg := hk kd.1 (List.of_mem_zip hkd).1
      have hcl := hg.closed1 pc' hpc'
      have hdp := hg.ents_dims pc'.1 hcl.1
      have hdc := hg.ents_dims pc'.2 (List.mem_cons_of_mem _ hcl.2)
      have hup := hg.ents_u hL pc'.1 hcl.1
      have heu := hg.edge_u pc' hpc'
      rcases mem_ents_buildSub.mp he with rfl | her
      · unfold Ent.Clear
        left
        show e.u + e.w ≤ pc'.1.u + (e.w + g.level) + pc'.1.w
        omega
      · obtain ⟨kd', hkd', o', ho', rfl⟩ := mem_rest_buildSub.mp her
        by_cases hkk : kd = kd'
        · subst hkk
          exact Ent.clear_shift _ _ (hg.clear pc' hpc' o' ho' hep hec)
        · have hp0 := hcl.1
          have hc0 : pc'.2 ∈ kd.1.ents := List.mem_cons_of_mem _ hcl.2
          have hdo := (hk kd'.1 (List.of_mem_zip hkd').1).ents_dims o' ho'
          unfold Ent.Clear
          by_cases hA : o'.u + o'.w ≤ pc'.1.u + pc'.1.w
          · left
            show o'.u + (me.w + g.level) + o'.w ≤ pc'.1.u + (me.w + g.level) + pc'.1.w
            omega
          by_cases hB : pc'.2.u ≤ o'.u
          · right; left
            show pc'.2.u + (me.w + g.level) ≤ o'.u + (me.w + g.level)
            omega
          have ovpe : (pc'.1.contour g).overlaps (o'.contour g) = true :=
            (overlaps_iff g _ _).mpr ⟨by omega, by omega⟩
          have ovep : (o'.contour g).overlaps (pc'.1.contour g) = true :=
            (overlaps_iff g _ _).mpr ⟨by omega, by omega⟩
          have ovce : (pc'.2.contour g).overlaps (o'.contour g) = true :=
            (overlaps_iff g _ _).mpr ⟨by omega, by omega⟩
          have ovec : (o'.contour g).overlaps (pc'.2.contour g) = true :=
            (overlaps_iff g _ _).mpr ⟨by omega, by omega⟩
          rcases pairwise_total _ hsep kd hkd kd' hkd' hkk with hlt | hgt
          · have h1 := hlt pc'.1 hp0 o' ho' ovpe
            have h2 := hlt pc'.2 hc0 o' ho' ovce
            right; right; left
            show max (pc'.1.y + kd.2) (pc'.2.y + kd.2) ≤ (Ent.shift _ kd'.2 o').top
            rw [Ent.shift_top]
            simp only [Ent.contour, Ent.top, Ent.bottom, fdiv2] at h1 h2 ⊢
            omega
          · have h1 := hgt o' ho' pc'.1 hp0 ovep
            have h2 := hgt o' ho' pc'.2 hc0 ovec
            right; right; right
            show (Ent.shift _ kd'.2 o').bottom ≤ min (pc'.1.y + kd.2) (pc'.2.y + kd.2)
            rw [Ent.shift_bottom]
            simp only [Ent.contour, Ent.top, Ent.bottom, fdiv2] at h1 h2 ⊢
            omega
  
/-! ### The link check -/

theorem unwind_cons {p : Nat} : ∀ {path : List Nat} {x : Nat} {rest : List Nat},
    unwind p path = x :: rest → x = p ∧ x ∈ path
  | [], _, _, h => by simp [unwind] at h
  | y :: ys, x, rest, h => by
    by_cases hy : y = p
    · have h' : y :: ys = x :: rest := by simpa [unwind, hy] using h
      have hx : y = x := (List.cons.inj h').1
      exact ⟨by rw [← hx]; exact hy, by rw [← hx]; exact List.mem_cons_self⟩
    · have h' : unwind p ys = x :: rest := by simpa [unwind, hy] using h
      have := unwind_cons h'
      exact ⟨this.1, List.mem_cons_of_mem _ this.2⟩

theorem unwind_subset {p : Nat} : ∀ {path : List Nat} {z : Nat}, z ∈ unwind p path → z ∈ path
  | [], _, h => by simp [unwind] at h
  | y :: ys, z, h => by
    by_cases hy : y = p
    · have h' : z ∈ y :: ys := by simpa [unwind, hy] using h
      exact h'
    · have h' : z ∈ unwind p ys := by simpa [unwind, hy] using h
      exact List.mem_cons_of_mem _ (unwind_subset h')

theorem linkAux_sound : ∀ (ns : List Node) (i : Nat) (path : List Nat), (∀ x ∈ path, x < i) →
    linkAux i ns path = true →
    (∀ n ∈ ns, 1 ≤ n.width ∧ 1 ≤ n.height) ∧
      (∀ (k : Nat) (n : Node) (p : Nat), ns[k]? = some n → n.parent = some p → p < i + k) ∧
      ∀ (k : Nat) (n : Node), ns[k]? = some n → n.parent = none → i + k = 0
  | [], i, path, _, _ => ⟨by simp, by intro k n p h; simp at h, by intro k n h; simp at h⟩
  | n :: rest, i, path, hp, h => by
    have hsz : 1 ≤ n.width ∧ 1 ≤ n.height := by
      by_cases hc : 1 ≤ n.width ∧ 1 ≤ n.height
      · exact hc
      · have hc' : n.width < 1 ∨ n.height < 1 := by omega
        simp [linkAux, hc'] at h
    obtain ⟨hw, hh⟩ := hsz
    have h1 : ¬ n.width < 1 := by omega
    have h2 : ¬ n.height < 1 := by omega
    by_cases hi0 : i = 0
    · subst hi0
      cases hpar : n.parent with
      | some q => simp [linkAux, h1, h2, hpar] at h
      | none =>
        simp [linkAux, h1, h2, hpar] at h
        have ih := linkAux_sound rest 1 [0] (by simp) h
        refine ⟨?_, ?_, ?_⟩
        · intro m hm
          rcases List.mem_cons.mp hm with rfl | hr
          · exact ⟨hw, hh⟩
          · exact ih.1 m hr
        · intro k m p hk hm
          cases k with
          | zero =>
            simp at hk
            subst hk
            rw [hpar] at hm
            simp at hm
          | succ k =>
            have := ih.2.1 k m p (by simpa using hk) hm
            omega
        · intro k m hk hm
          cases k with
          | zero => rfl
          | succ k =>
            have := ih.2.2 k m (by simpa using hk) hm
            omega
    · cases hpar : n.parent with
      | none => simp [linkAux, h1, h2, hi0, hpar] at h
      | some q =>
        cases hu : unwind q path with
        | nil => simp [linkAux, h1, h2, hi0, hpar, hu] at h
        | cons x xs =>
          simp [linkAux, h1, h2, hi0, hpar, hu] at h
          have hxq := unwind_cons hu
          have hxlt : x < i := hp x hxq.2
          have hq : q < i := by rw [← hxq.1]; exact hxlt
          have ih := linkAux_sound rest (i + 1) (i :: x :: xs) (by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz'
            · omega
            · have := hp z (unwind_subset (by rw [hu]; exact hz'))
              omega) h
          refine ⟨?_, ?_, ?_⟩
          · intro m hm
            rcases List.mem_cons.mp hm with rfl | hr
            · exact ⟨hw, hh⟩
            · exact ih.1 m hr
          · intro k m p hk hm
            cases k with
            | zero =>
              simp at hk
              subst hk
              rw [hpar] at hm
              simp at hm
              omega
            | succ k =>
              have := ih.2.1 k m p (by simpa using hk) hm
              omega
          · intro k m hk hm
            cases k with
            | zero =>
              simp at hk
              subst hk
              rw [hpar] at hm
              simp at hm
            | succ k =>
              have := ih.2.2 k m (by simpa using hk) hm
              omega

/-- What a successful link check gives: positive sizes, a root without a parent, and for every
other node a parent that precedes it. -/
structure Valid (ns : List Node) : Prop where
  dims : ∀ n ∈ ns, 1 ≤ n.width ∧ 1 ≤ n.height
  parentLt : ∀ c p, parentOf ns c = some p → p < c
  rootNone : parentOf ns 0 = none
  hasParent : ∀ c, 0 < c → c < ns.length → ∃ p, parentOf ns c = some p

theorem link_valid {ns : List Node} (h : link ns = true) : Valid ns := by
  have hs := linkAux_sound ns 0 [] (by simp) h
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · intro c p hc
    unfold parentOf at hc
    cases hn : ns[c]? with
    | none => simp [hn] at hc
    | some n =>
      rw [hn] at hc
      have := hs.2.1 c n p hn (by simpa using hc)
      omega
  · unfold parentOf
    cases hn : ns[0]? with
    | none => rfl
    | some n =>
      cases hp : n.parent with
      | none => simp [hp]
      | some p =>
        have := hs.2.1 0 n p hn hp
        omega
  · intro c hc0 hcn
    obtain ⟨n, hn⟩ : ∃ n, ns[c]? = some n := ⟨ns[c], List.getElem?_eq_getElem hcn⟩
    cases hp : n.parent with
    | none =>
      have := hs.2.2 c n hn hp
      omega
    | some p =>
      exact ⟨p, by simp [parentOf, hn, hp]⟩

/-! ### `sub` is good -/

theorem entOf_idx (ns : List Node) (v : Nat) : (entOf ns v).idx = v := by
  unfold entOf
  split <;> rfl

theorem sub_me (ns : List Node) (g : Gaps) (v : Nat) : (sub ns g v).me = entOf ns v := by
  rw [sub] <;> rfl

theorem sub_good {ns : List Node} {g : Gaps} (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling)
    (hd : ∀ n ∈ ns, 1 ≤ n.width ∧ 1 ≤ n.height) :
    ∀ (m v : Nat), ns.length - v ≤ m → v < ns.length → Good g (sub ns g v)
  | 0, v, hm, hv => absurd hm (by omega)
  | m + 1, v, hm, hv => by
    obtain ⟨n, hn⟩ : ∃ n, ns[v]? = some n := ⟨ns[v], List.getElem?_eq_getElem hv⟩
    have hnd := hd n (List.mem_of_getElem? hn)
    have he : entOf ns v = ⟨v, 0, 0, n.width, n.height⟩ := by
      unfold entOf
      rw [hn]
    rw [sub]
    apply buildSub_good hL hs
    · rw [he]
    · rw [he]
    · rw [he]
      show 0 < n.width
      omega
    · rw [he]
      show 0 ≤ n.height
      omega
    · intro k hk
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hk
      have hc := kidsOf_mem c.2
      exact sub_good hL hs hd m c.1 (by omega) hc.2.1

/-! ### Descendants and the uniqueness of indices -/

inductive Under (ns : List Node) : Nat → Nat → Prop
  | refl (v : Nat) : Under ns v v
  | step {v c d : Nat} : parentOf ns c = some v → Under ns c d → Under ns v d

theorem Under.le {ns : List Node} (hlt : ∀ c p, parentOf ns c = some p → p < c) {v d : Nat}
    (h : Under ns v d) : v ≤ d := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step v c d hp _ ih =>
    have := hlt _ _ hp
    omega

theorem Under.last {ns : List Node} {v d : Nat} (h : Under ns v d) :
    v = d ∨ ∃ p, parentOf ns d = some p ∧ Under ns v p := by
  induction h with
  | refl => exact Or.inl rfl
  | @step v c d hp hu ih =>
    rcases ih with rfl | ⟨q, hq, huq⟩
    · exact Or.inr ⟨v, hp, Under.refl v⟩
    · exact Or.inr ⟨q, hq, Under.step hp huq⟩

theorem under_child_unique {ns : List Node} (hlt : ∀ c p, parentOf ns c = some p → p < c)
    {v c c' : Nat} (hc : parentOf ns c = some v) (hc' : parentOf ns c' = some v) :
    ∀ (m d : Nat), d ≤ m → Under ns c d → Under ns c' d → c = c'
  | 0, d, hm, h, h' => by
    rcases h.last with hcd | ⟨p, hp, hup⟩
    · rcases h'.last with heq | ⟨q, hq, huq⟩
      · exact hcd.trans heq.symm
      · have hqv : q = v := by
          rw [hcd] at hc
          rw [hc] at hq
          exact (Option.some.inj hq).symm
        have h1 := huq.le hlt
        have h2 := hlt _ _ hc'
        omega
    · rcases h'.last with heq | ⟨q, hq, huq⟩
      · have hpv : p = v := by
          rw [heq] at hc'
          rw [hc'] at hp
          exact (Option.some.inj hp).symm
        have h1 := hup.le hlt
        have h2 := hlt _ _ hc
        omega
      · have hpq : p = q := by
          rw [hp] at hq
          exact Option.some.inj hq
        have h3 := hlt _ _ hp
        omega
  | m + 1, d, hm, h, h' => by
    rcases h.last with hcd | ⟨p, hp, hup⟩
    · rcases h'.last with heq | ⟨q, hq, huq⟩
      · exact hcd.trans heq.symm
      · have hqv : q = v := by
          rw [hcd] at hc
          rw [hc] at hq
          exact (Option.some.inj hq).symm
        have h1 := huq.le hlt
        have h2 := hlt _ _ hc'
        omega
    · rcases h'.last with heq | ⟨q, hq, huq⟩
      · have hpv : p = v := by
          rw [heq] at hc'
          rw [hc'] at hp
          exact (Option.some.inj hp).symm
        have h1 := hup.le hlt
        have h2 := hlt _ _ hc
        omega
      · have hpq : p = q := by
          rw [hp] at hq
          exact Option.some.inj hq
        subst hpq
        have h3 := hlt _ _ hp
        exact under_child_unique hlt hc hc' m p (by omega) hup huq

theorem kidsOf_nodup (ns : List Node) (v : Nat) : (kidsOf ns v).Nodup :=
  List.Nodup.sublist List.filter_sublist (List.nodup_range' 1 (by omega))

theorem sub_under_aux {ns : List Node} {g : Gaps} (v : Nat)
    (ih : ∀ c, c ∈ kidsOf ns v → ∀ e ∈ (sub ns g c).ents, Under ns c e.idx) :
    ∀ e ∈ (sub ns g v).ents, Under ns v e.idx := by
  intro e he
  rw [sub] at he
  rcases mem_ents_buildSub.mp he with rfl | her
  · rw [entOf_idx]
    exact Under.refl v
  · obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp her
    obtain ⟨c, _, hc⟩ := List.mem_map.mp (List.of_mem_zip hkd).1
    have hcm := kidsOf_mem c.2
    rw [← hc] at ho
    exact Under.step hcm.2.2 (ih c.1 c.2 o ho)

theorem sub_under {ns : List Node} {g : Gaps} : ∀ (m v : Nat), ns.length - v ≤ m →
    ∀ e ∈ (sub ns g v).ents, Under ns v e.idx
  | 0, v, hm => sub_under_aux v (fun c hc => by
      exfalso
      have := kidsOf_mem hc
      omega)
  | m + 1, v, hm => sub_under_aux v (fun c hc =>
      sub_under m c (by have := kidsOf_mem hc; omega))

/-! ### The two sides of the root -/

theorem filterMap_zipIdx_sublist (f : Nat → Bool) :
    ∀ (ks : List Nat) (k : Nat),
      List.Sublist ((ks.zipIdx k).filterMap fun ci => if f ci.2 then some ci.1 else none) ks
  | [], k => by simp
  | a :: as, k => by
    simp only [List.zipIdx_cons, List.filterMap_cons]
    cases hf : f k with
    | true =>
      simp only [ite_true]
      exact List.Sublist.cons_cons _ (filterMap_zipIdx_sublist f as (k + 1))
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact List.Sublist.cons _ (filterMap_zipIdx_sublist f as (k + 1))

theorem splitSides_fst_sublist (ks : List Nat) : List.Sublist (splitSides ks).1 ks :=
  filterMap_zipIdx_sublist (fun i => i % 2 == 0) ks 0

theorem splitSides_snd_sublist (ks : List Nat) : List.Sublist (splitSides ks).2 ks :=
  filterMap_zipIdx_sublist (fun i => i % 2 == 1) ks 0

theorem mem_splitSides_fst {ks : List Nat} {c : Nat} :
    c ∈ (splitSides ks).1 ↔ ∃ i, ks[i]? = some c ∧ i % 2 = 0 := by
  unfold splitSides
  simp only [List.mem_filterMap, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨c', i⟩, hmem, hf⟩
    by_cases hi : i % 2 = 0
    · simp [hi] at hf
      subst hf
      exact ⟨i, hmem, hi⟩
    · simp [hi] at hf
  · rintro ⟨i, hi, hpar⟩
    exact ⟨⟨c, i⟩, hi, by simp [hpar]⟩

theorem mem_splitSides_snd {ks : List Nat} {c : Nat} :
    c ∈ (splitSides ks).2 ↔ ∃ i, ks[i]? = some c ∧ i % 2 = 1 := by
  unfold splitSides
  simp only [List.mem_filterMap, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨c', i⟩, hmem, hf⟩
    by_cases hi : i % 2 = 1
    · simp [hi] at hf
      subst hf
      exact ⟨i, hmem, hi⟩
    · simp [hi] at hf
  · rintro ⟨i, hi, hpar⟩
    exact ⟨⟨c, i⟩, hi, by simp [hpar]⟩

theorem nodup_getElem?_inj {α : Type} : ∀ {l : List α}, l.Nodup → ∀ {i j : Nat} {c : α},
    l[i]? = some c → l[j]? = some c → i = j
  | [], _, i, j, c, h, _ => by simp at h
  | a :: as, hnd, i, j, c, hi, hj => by
    rw [List.nodup_cons] at hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp at hi hj
        subst hi
        exact absurd (List.mem_of_getElem? hj) hnd.1
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj
        subst hj
        exact absurd (List.mem_of_getElem? hi) hnd.1
      | succ j =>
        simp at hi hj
        have := nodup_getElem?_inj hnd.2 hi hj
        omega

theorem splitSides_disjoint {ks : List Nat} (hnd : ks.Nodup) {c : Nat}
    (h1 : c ∈ (splitSides ks).1) (h2 : c ∈ (splitSides ks).2) : False := by
  obtain ⟨i, hi, hpi⟩ := mem_splitSides_fst.mp h1
  obtain ⟨j, hj, hpj⟩ := mem_splitSides_snd.mp h2
  have := nodup_getElem?_inj hnd hi hj
  omega

/-! ### Distinct indices -/

def IdxDistinct (l : List Ent) : Prop := l.Pairwise (fun a b => a.idx ≠ b.idx)

theorem pairwise_zip_left {α β : Type} {R : α → α → Prop} :
    ∀ (l : List α) (m : List β), l.Pairwise R → (l.zip m).Pairwise (fun p q => R p.1 q.1)
  | [], _, _ => by simp
  | a :: as, [], _ => by simp
  | a :: as, b :: bs, h => by
    rw [List.pairwise_cons] at h
    simp only [List.zip_cons_cons, List.pairwise_cons]
    refine ⟨?_, pairwise_zip_left as bs h.2⟩
    intro q hq
    exact h.1 q.1 (List.of_mem_zip hq).1

theorem buildSub_idx_nodup {ns : List Node} {g : Gaps} {me : Ent} {kids : List Sub}
    (hlt : ∀ c p, parentOf ns c = some p → p < c)
    (hkn : ∀ k ∈ kids, IdxDistinct k.ents)
    (hku : ∀ k ∈ kids, ∀ e ∈ k.ents, Under ns k.me.idx e.idx)
    (hkp : ∀ k ∈ kids, parentOf ns k.me.idx = some me.idx)
    (hroots : kids.Pairwise (fun a b => a.me.idx ≠ b.me.idx)) :
    IdxDistinct (buildSub g me kids).ents := by
  unfold IdxDistinct
  rw [show (buildSub g me kids).ents = me :: (buildSub g me kids).rest from rfl,
    List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp hb
    have hk := (List.of_mem_zip hkd).1
    have h1 := (hku kd.1 hk o ho).le hlt
    have h2 := hlt _ _ (hkp kd.1 hk)
    show me.idx ≠ o.idx
    omega
  · have hP := pairwise_zip_left kids (dysOf g (kids.map Sub.ents)) hroots
    show (buildSub g me kids).rest.Pairwise _
    unfold buildSub
    dsimp only
    rw [List.pairwise_flatMap]
    refine ⟨?_, ?_⟩
    · intro kd hkd
      rw [List.pairwise_map]
      exact hkn kd.1 (List.of_mem_zip hkd).1
    · refine List.Pairwise.imp_of_mem ?_ hP
      intro kd kd' hkd hkd' hne a ha b hb heq
      rw [List.mem_map] at ha hb
      obtain ⟨o, ho, rfl⟩ := ha
      obtain ⟨o', ho', rfl⟩ := hb
      have hk := (List.of_mem_zip hkd).1
      have hk' := (List.of_mem_zip hkd').1
      have heq' : o.idx = o'.idx := heq
      apply hne
      exact under_child_unique hlt (hkp kd.1 hk) (hkp kd'.1 hk') o.idx o.idx (Nat.le_refl _)
        (hku kd.1 hk o ho) (by rw [heq']; exact hku kd'.1 hk' o' ho')

theorem kids_roots (ns : List Node) (g : Gaps) (v : Nat) :
    (((kidsOf ns v).attach.map fun c => sub ns g c.1).map fun k => k.me.idx) = kidsOf ns v := by
  rw [List.map_map]
  have : ((fun k : Sub => k.me.idx) ∘ fun c : {x // x ∈ kidsOf ns v} => sub ns g c.1) =
      Subtype.val := by
    funext c
    simp only [Function.comp_apply, sub_me, entOf_idx]
  rw [this, List.attach_map_subtype_val]

theorem sub_nodup_aux {ns : List Node} {g : Gaps}
    (hlt : ∀ c p, parentOf ns c = some p → p < c) (v : Nat)
    (ih : ∀ c ∈ kidsOf ns v, IdxDistinct (sub ns g c).ents) :
    IdxDistinct (sub ns g v).ents := by
  rw [sub]
  apply buildSub_idx_nodup hlt
  · intro k hk
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hk
    exact ih c.1 c.2
  · intro k hk e he
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hk
    rw [sub_me, entOf_idx]
    exact sub_under ns.length c.1 (by omega) e he
  · intro k hk
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hk
    rw [sub_me, entOf_idx, entOf_idx]
    exact (kidsOf_mem c.2).2.2
  · have h : (((kidsOf ns v).attach.map fun c => sub ns g c.1).map fun k => k.me.idx).Nodup := by
      rw [kids_roots]
      exact kidsOf_nodup ns v
    exact List.pairwise_map.mp h

theorem sub_nodup {ns : List Node} {g : Gaps}
    (hlt : ∀ c p, parentOf ns c = some p → p < c) :
    ∀ (m v : Nat), ns.length - v ≤ m → IdxDistinct (sub ns g v).ents
  | 0, v, hm => sub_nodup_aux hlt v (fun c hc => by
      exfalso
      have := kidsOf_mem hc
      omega)
  | m + 1, v, hm => sub_nodup_aux hlt v (fun c hc =>
      sub_nodup hlt m c (by have := kidsOf_mem hc; omega))

/-! ### Parents of the placed edges -/

def Par (ns : List Node) (s : Sub) : Prop :=
  ∀ pc ∈ s.edges, parentOf ns pc.2.idx = some pc.1.idx

theorem buildSub_par {ns : List Node} {g : Gaps} {me : Ent} {kids : List Sub}
    (hk : ∀ k ∈ kids, Par ns k) (hkp : ∀ k ∈ kids, parentOf ns k.me.idx = some me.idx) :
    Par ns (buildSub g me kids) := by
  intro pc hpc
  obtain ⟨kd, hkd, h | ⟨pc', hpc', rfl⟩⟩ := mem_edges_buildSub.mp hpc
  · subst h
    exact hkp kd.1 (List.of_mem_zip hkd).1
  · exact hk kd.1 (List.of_mem_zip hkd).1 pc' hpc'

theorem sub_par_aux {ns : List Node} {g : Gaps} (v : Nat)
    (ih : ∀ c ∈ kidsOf ns v, Par ns (sub ns g c)) : Par ns (sub ns g v) := by
  rw [sub]
  refine buildSub_par ?_ ?_
  · intro k hk
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hk
    exact ih c.1 c.2
  · intro k hk
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hk
    rw [sub_me, entOf_idx, entOf_idx]
    exact (kidsOf_mem c.2).2.2

theorem sub_par {ns : List Node} {g : Gaps} :
    ∀ (m v : Nat), ns.length - v ≤ m → Par ns (sub ns g v)
  | 0, v, hm => sub_par_aux v (fun c hc => by
      exfalso
      have := kidsOf_mem hc
      omega)
  | m + 1, v, hm => sub_par_aux v (fun c hc =>
      sub_par m c (by have := kidsOf_mem hc; omega))

theorem entOf_eq {ns : List Node} {v : Nat} {n : Node} (hn : ns[v]? = some n) :
    entOf ns v = ⟨v, 0, 0, n.width, n.height⟩ := by
  unfold entOf
  rw [hn]

theorem entOf_facts {ns : List Node} (hd : ∀ n ∈ ns, 1 ≤ n.width ∧ 1 ≤ n.height) {v : Nat}
    (hv : v < ns.length) :
    (entOf ns v).u = 0 ∧ (entOf ns v).y = 0 ∧ 0 < (entOf ns v).w ∧ 0 ≤ (entOf ns v).h := by
  obtain ⟨n, hn⟩ : ∃ n, ns[v]? = some n := ⟨ns[v], List.getElem?_eq_getElem hv⟩
  have hnd := hd n (List.mem_of_getElem? hn)
  rw [entOf_eq hn]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show 0 < n.width
    omega
  · show 0 ≤ n.height
    omega

/-- One side of the root: the subtrees of a sublist of the root's children, under the root. -/
structure SideOK (ns : List Node) (g : Gaps) (ks : List Nat) : Prop where
  good : Good g (buildSub g (entOf ns 0) (ks.map (sub ns g)))
  nodup : IdxDistinct (buildSub g (entOf ns 0) (ks.map (sub ns g))).ents
  par : Par ns (buildSub g (entOf ns 0) (ks.map (sub ns g)))
  under : ∀ e ∈ (buildSub g (entOf ns 0) (ks.map (sub ns g))).rest,
    ∃ c ∈ ks, Under ns c e.idx

theorem sideOK {ns : List Node} {g : Gaps} (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling)
    (hv : Valid ns) (h0 : 0 < ns.length) {ks : List Nat}
    (hks : List.Sublist ks (kidsOf ns 0)) : SideOK ns g ks := by
  have hkm : ∀ c ∈ ks, c ∈ kidsOf ns 0 := fun c hc => hks.subset hc
  have hme := entOf_facts hv.dims h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine buildSub_good hL hs hme.1 hme.2.1 hme.2.2.1 hme.2.2.2 ?_
    intro k hk
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    exact sub_good hL hs hv.dims ns.length c (by omega) (kidsOf_mem (hkm c hc)).2.1
  · refine buildSub_idx_nodup hv.parentLt ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      exact sub_nodup hv.parentLt ns.length c (by omega)
    · intro k hk e he
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      rw [sub_me, entOf_idx]
      exact sub_under ns.length c (by omega) e he
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      rw [sub_me, entOf_idx, entOf_idx]
      exact (kidsOf_mem (hkm c hc)).2.2
    · have hnd : ks.Nodup := List.Nodup.sublist hks (kidsOf_nodup ns 0)
      rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ hnd
      intro a b hab
      rw [sub_me, sub_me, entOf_idx, entOf_idx]
      exact hab
  · refine buildSub_par ?_ ?_
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      exact sub_par ns.length c (by omega)
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      rw [sub_me, entOf_idx, entOf_idx]
      exact (kidsOf_mem (hkm c hc)).2.2
  · intro e he
    obtain ⟨kd, hkd, o, ho, rfl⟩ := mem_rest_buildSub.mp he
    obtain ⟨c, hc, hcd⟩ := List.mem_map.mp (List.of_mem_zip hkd).1
    refine ⟨c, hc, ?_⟩
    rw [← hcd] at ho
    exact sub_under ns.length c (by omega) o ho

/-- The root's children alternate sides by declaration position. Each descendant is placed by
`sub` within that child's side; the orientation is applied once to the entire subtree. -/
theorem mindmap_side_rule (ks : List Nat) :
    (∀ c, c ∈ (splitSides ks).1 ↔ ∃ i, ks[i]? = some c ∧ i % 2 = 0) ∧
    (∀ c, c ∈ (splitSides ks).2 ↔ ∃ i, ks[i]? = some c ∧ i % 2 = 1) :=
  ⟨fun _ => mem_splitSides_fst, fun _ => mem_splitSides_snd⟩

/-- Both alternating stacks satisfy the same contour, identity, and parent invariants. -/
theorem mindmap_sides_valid {ns : List Node} {g : Gaps}
    (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns) (h0 : 0 < ns.length) :
    SideOK ns g (splitSides (kidsOf ns 0)).1 ∧
    SideOK ns g (splitSides (kidsOf ns 0)).2 :=
  ⟨sideOK hL hs hv h0 (splitSides_fst_sublist _),
   sideOK hL hs hv h0 (splitSides_snd_sublist _)⟩

end Tree
end Elegant
