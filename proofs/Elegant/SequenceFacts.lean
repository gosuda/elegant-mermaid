import Elegant.Sequence

set_option autoImplicit false

/-! Theorems of the sequence family (`spec/layout/sequence.md`, sequence-42 to sequence-54).
The columns, the rows, the activations, and the frames are stated over the definitions of
`Elegant.Sequence`. -/

namespace Elegant
namespace Sequence

/-! ### Sums over a slice -/

theorem sum_map_le {α : Type} (l : List α) (f g : α → Int) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (List.mem_cons_self)
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    omega

theorem sum_range_add (n : Nat) (a b : Nat → Int) (c : Int) :
    ((List.range n).map fun t => a t + c + b t).sum =
      ((List.range n).map a).sum + (n : Int) * c + ((List.range n).map b).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_append,
      List.sum_append]
    push_cast
    rw [Int.add_mul]
    omega

theorem sum_range_lt (n r : Nat) :
    ((List.range n).map fun t => if t < r then (1 : Int) else 0).sum = (min r n : Nat) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases h : n < r
    · simp [h]; omega
    · simp [h]; omega

/-! ### Widening -/

/-- Pointwise order of two gap lists of one length. -/
def GapsGe (g g' : List Int) : Prop := g.length = g'.length ∧ ∀ i, g.getD i 0 ≤ g'.getD i 0

theorem GapsGe.refl (g : List Int) : GapsGe g g := ⟨rfl, fun _ => Int.le_refl _⟩

theorem GapsGe.trans {a b c : List Int} (h1 : GapsGe a b) (h2 : GapsGe b c) : GapsGe a c :=
  ⟨h1.1.trans h2.1, fun i => Int.le_trans (h1.2 i) (h2.2 i)⟩

theorem ssum_mono {g g' : List Int} (h : GapsGe g g') (lo hi : Nat) : ssum g lo hi ≤ ssum g' lo hi :=
  sum_map_le _ _ _ fun k _ => h.2 k

theorem getD_mapIdx (g : List Int) (f : Nat → Int → Int) (i : Nat) (h : i < g.length) :
    (g.mapIdx f).getD i 0 = f i (g.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_mapIdx, List.getElem?_eq_getElem h]

theorem getD_of_ge (g : List Int) (i : Nat) (h : g.length ≤ i) : g.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem fdiv_split (extra span : Int) (hs : 0 < span) :
    0 ≤ extra - Int.fdiv extra span * span ∧ extra - Int.fdiv extra span * span < span := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hs)]
  have h1 := Int.emod_def extra span
  have h2 := Int.emod_nonneg extra (Int.ne_of_gt hs)
  have h3 := Int.emod_lt_of_pos extra hs
  have h4 : (extra / span) * span = span * (extra / span) := Int.mul_comm _ _
  omega

theorem widen_length (g : List Int) (lo hi : Nat) (need : Int) :
    (widen g lo hi need).length = g.length := by
  unfold widen
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp [List.length_mapIdx]

theorem widen_ge (g : List Int) (lo hi : Nat) (need : Int) : GapsGe g (widen g lo hi need) := by
  refine ⟨(widen_length g lo hi need).symm, ?_⟩
  intro i
  unfold widen
  split
  · exact Int.le_refl _
  · dsimp only
    split
    · exact Int.le_refl _
    · rename_i hc hextra
      by_cases hi' : i < g.length
      · rw [getD_mapIdx _ _ _ hi']
        have hspan : (0 : Int) < ((hi - lo : Nat) : Int) := by omega
        have hshare : 0 ≤ Int.fdiv (need - ssum g lo hi) ((hi - lo : Nat) : Int) :=
          Int.fdiv_nonneg (by omega) (Int.le_of_lt hspan)
        split
        · split <;> omega
        · exact Int.le_refl _
      · rw [getD_of_ge g i (by omega), getD_of_ge _ i (by simp; omega)]
        exact Int.le_refl _

theorem ssum_bump (g : List Int) (lo hi : Nat) (share rem : Int) (hhi : hi ≤ g.length)
    (hr0 : 0 ≤ rem) (hrn : rem < ((hi - lo : Nat) : Int)) :
    ssum (g.mapIdx fun i x =>
        if lo ≤ i ∧ i < hi then x + share + (if ((i - lo : Nat) : Int) < rem then 1 else 0) else x) lo hi
      = ssum g lo hi + ((hi - lo : Nat) : Int) * share + rem := by
  unfold ssum
  have hmap : (List.range' lo (hi - lo)).map (fun k => (g.mapIdx fun i x =>
        if lo ≤ i ∧ i < hi then x + share + (if ((i - lo : Nat) : Int) < rem then 1 else 0) else x).getD k 0)
      = (List.range (hi - lo)).map (fun t =>
        g.getD (lo + t) 0 + share + (if t < rem.toNat then (1 : Int) else 0)) := by
    rw [List.range'_eq_map_range, List.map_map]
    apply List.map_congr_left
    intro t ht
    have ht' : t < hi - lo := List.mem_range.mp ht
    simp only [Function.comp]
    rw [getD_mapIdx _ _ _ (by omega)]
    have h1 : lo ≤ lo + t ∧ lo + t < hi := by omega
    have h2 : ((lo + t - lo : Nat) : Int) < rem ↔ t < rem.toNat := by omega
    simp only [h1, and_self, ite_true, Nat.add_sub_cancel_left]
    simp only [Nat.add_sub_cancel_left] at h2
    by_cases h3 : (t : Int) < rem
    · simp [h3, h2.mp h3]
    · simp [h3]
  rw [hmap, sum_range_add, sum_range_lt]
  have h4 : (min rem.toNat (hi - lo) : Nat) = rem.toNat := by omega
  rw [h4]
  have h5 : ((List.range (hi - lo)).map fun t => g.getD (lo + t) 0).sum =
      ((List.range' lo (hi - lo)).map fun k => g.getD k 0).sum := by
    rw [List.range'_eq_map_range, List.map_map]
    rfl
  rw [h5]
  omega

theorem widen_covers (g : List Int) (lo hi : Nat) (need : Int) (h1 : lo < hi) (h2 : hi ≤ g.length) :
    need ≤ ssum (widen g lo hi need) lo hi := by
  unfold widen
  have hc0 : ¬ (hi ≤ lo ∨ g.length < hi) := by omega
  simp only [hc0, ↓reduceIte]
  split
  · rename_i h; omega
  · rename_i h
    have hspan : (0 : Int) < ((hi - lo : Nat) : Int) := by omega
    have hsplit := fdiv_split (need - ssum g lo hi) _ hspan
    have hc := Int.mul_comm (Int.fdiv (need - ssum g lo hi) ((hi - lo : Nat) : Int)) ((hi - lo : Nat) : Int)
    rw [ssum_bump g lo hi _ _ h2 hsplit.1 hsplit.2]
    omega

/-! ### Plans -/

/-- A plan whose constants have the signs of `Consts.Pos` and whose actor widths are not negative. -/
structure Plan.Wf (pl : Plan) : Prop where
  pos : pl.c.Pos
  widths : ∀ k, 0 ≤ pl.widths.getD k 0
  heights : ∀ k, 0 ≤ pl.heights.getD k 0

theorem half_nonneg {v : Int} (h : 0 ≤ v) : 0 ≤ half v := Int.fdiv_nonneg h (by decide)

theorem half_le {v : Int} (h : 0 ≤ v) : half v ≤ v := by
  unfold half
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem half_mono {a b : Int} (h : a ≤ b) : half a ≤ half b := by
  unfold half
  have h1 := Int.fdiv_eq_ediv_of_nonneg a (show (0 : Int) ≤ 2 by decide)
  have h2 := Int.fdiv_eq_ediv_of_nonneg b (show (0 : Int) ≤ 2 by decide)
  omega

theorem baseGaps_length (c : Consts) (ws : List Int) : (baseGaps c ws).length = ws.length - 1 := by
  simp [baseGaps]

theorem baseGaps_getD (c : Consts) (ws : List Int) (i : Nat) (h : i < ws.length - 1) :
    (baseGaps c ws).getD i 0 = half (ws.getD i 0 + ws.getD (i + 1) 0) + c.actorMargin := by
  simp [baseGaps, List.getD_eq_getElem?_getD, h]

theorem baseGaps_ge (c : Consts) (ws : List Int) (hw : ∀ k, 0 ≤ ws.getD k 0)
    (i : Nat) (h : i < ws.length - 1) : c.actorMargin ≤ (baseGaps c ws).getD i 0 := by
  rw [baseGaps_getD c ws i h]
  have := half_nonneg (Int.add_nonneg (hw i) (hw (i + 1)))
  omega

theorem bumpGap_ge (g : List Int) (k : Nat) (v : Int) (hv : 0 ≤ v) : GapsGe g (bumpGap g k v) := by
  refine ⟨by simp [bumpGap], fun i => ?_⟩
  by_cases hi : i < g.length
  · unfold bumpGap
    rw [getD_mapIdx _ _ _ hi]
    split <;> omega
  · rw [getD_of_ge g i (by omega), getD_of_ge _ i (by simp [bumpGap]; omega)]
    exact Int.le_refl _

theorem widenWhen_ge (cond : Bool) (g : List Int) (lo hi : Nat) (need : Int) :
    GapsGe g (widenWhen cond g lo hi need) := by
  unfold widenWhen
  split
  · exact widen_ge _ _ _ _
  · exact GapsGe.refl _

theorem reachWhen_ge (cond : Bool) (pl : Plan) (g : List Int) (gap : Nat) (reach : Int) :
    GapsGe g (reachWhen cond pl g gap reach) := by
  unfold reachWhen widenForReach
  split
  · exact widen_ge _ _ _ _
  · exact GapsGe.refl _

theorem foldl_gapsGe {α : Type} (f : List Int → α → List Int) (hf : ∀ g a, GapsGe g (f g a))
    (l : List α) (g : List Int) : GapsGe g (l.foldl f g) := by
  induction l generalizing g with
  | nil => exact GapsGe.refl g
  | cons a t ih => exact (hf g a).trans (ih (f g a))

theorem widenForMessage_ge (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (g : List Int)
    (bits src dst route : Nat) : GapsGe g (widenForMessage pl g bits src dst route) := by
  unfold widenForMessage
  dsimp only
  split
  · refine GapsGe.trans ?_ (bumpGap_ge _ _ _ (half_nonneg (hw dst)))
    split
    · exact widenWhen_ge _ _ _ _ _
    · exact widen_ge _ _ _ _
  · split
    · exact widenWhen_ge _ _ _ _ _
    · exact widen_ge _ _ _ _

theorem widenForNote_ge (pl : Plan) (g : List Int) (placement a b box : Nat) :
    GapsGe g (widenForNote pl g placement a b box) := by
  unfold widenForNote
  dsimp only
  split
  · exact (widenWhen_ge _ _ _ _ _).trans (widenWhen_ge _ _ _ _ _)
  · split
    · exact widen_ge _ _ _ _
    · split
      · exact widenWhen_ge _ _ _ _ _
      · exact widenWhen_ge _ _ _ _ _

theorem widenStep_ge (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (g : List Int) (s : Step) :
    GapsGe g (widenStep pl g s) := by
  cases s with
  | message bits src dst route destroyed => exact widenForMessage_ge pl hw g bits src dst route
  | note placement a b box => exact widenForNote_ge pl g placement a b box
  | fragmentStart _ _ => exact GapsGe.refl g
  | fragmentElse _ _ => exact GapsGe.refl g
  | fragmentEnd => exact GapsGe.refl g
  | activateStart _ => exact GapsGe.refl g
  | activateEnd _ => exact GapsGe.refl g

theorem widenSteps_ge (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (steps : List Step)
    (g : List Int) : GapsGe g (widenSteps pl steps g) :=
  foldl_gapsGe _ (widenStep_ge pl hw) steps g

theorem clearStep_ge (pl : Plan) (frames : List PFrame) (g : List Int) (f : PFrame) :
    GapsGe g (clearStep pl frames g f) := by
  unfold clearStep
  dsimp only
  exact (reachWhen_ge _ _ _ _ _).trans (reachWhen_ge _ _ _ _ _)

theorem clearParticipantBoxes_ge (pl : Plan) (frames : List PFrame) (g : List Int) :
    GapsGe g (clearParticipantBoxes pl frames g) :=
  foldl_gapsGe _ (clearStep_ge pl frames) frames g

theorem columnGaps_ge (pl : Plan) (steps : List Step) :
    GapsGe (widenSteps pl steps (baseGaps pl.c pl.widths)) (columnGaps pl steps) := by
  unfold columnGaps
  dsimp only
  exact clearParticipantBoxes_ge _ _ _

theorem columnGaps_ge_base (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (steps : List Step) :
    GapsGe (baseGaps pl.c pl.widths) (columnGaps pl steps) :=
  (widenSteps_ge pl hw steps _).trans (columnGaps_ge pl steps)

/-! ### Columns -/

theorem ssum_split (g : List Int) (lo mid hi : Nat) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    ssum g lo hi = ssum g lo mid + ssum g mid hi := by
  unfold ssum
  have h : List.range' lo (hi - lo) = List.range' lo (mid - lo) ++ List.range' mid (hi - mid) := by
    have := @List.range'_append lo (mid - lo) (hi - mid) 1
    have e1 : lo + 1 * (mid - lo) = mid := by omega
    have e2 : mid - lo + (hi - mid) = hi - lo := by omega
    rw [e1, e2] at this
    exact this.symm
  rw [h, List.map_append, List.sum_append]

theorem ssum_lower_aux (g : List Int) (a : Int) (lo m : Nat)
    (h : ∀ k, lo ≤ k → k < lo + m → a ≤ g.getD k 0) :
    (m : Int) * a ≤ ((List.range' lo m).map fun k => g.getD k 0).sum := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    rw [List.range'_succ]
    simp only [List.map_cons, List.sum_cons]
    have h1 := h lo (Nat.le_refl _) (by omega)
    have h2 := ih (lo + 1) (fun k hk hk' => h k (by omega) (by omega))
    push_cast
    rw [Int.add_mul, Int.one_mul]
    omega

theorem ssum_lower (g : List Int) (a : Int) (lo hi : Nat)
    (h : ∀ k, lo ≤ k → k < hi → a ≤ g.getD k 0) :
    ((hi - lo : Nat) : Int) * a ≤ ssum g lo hi :=
  ssum_lower_aux g a lo (hi - lo) fun k hk hk' => h k hk (by omega)

theorem ssum_single (g : List Int) (i : Nat) : ssum g i (i + 1) = g.getD i 0 := by
  simp [ssum]

theorem centre_getD (widths gaps : List Int) (i : Nat) (hi : i < widths.length) :
    (lifelineCentres widths gaps).getD i 0 = half (widths.getD 0 0) + ssum gaps 0 i := by
  cases widths with
  | nil => simp at hi
  | cons w t =>
    simp only [lifelineCentres, List.length_cons] at hi ⊢
    simp [List.getD_eq_getElem?_getD, hi]

theorem centre_diff (widths gaps : List Int) (i j : Nat) (hij : i ≤ j) (hj : j < widths.length) :
    (lifelineCentres widths gaps).getD j 0 - (lifelineCentres widths gaps).getD i 0 = ssum gaps i j := by
  rw [centre_getD widths gaps j hj, centre_getD widths gaps i (by omega), ssum_split gaps 0 i j (by omega) hij]
  omega

theorem columnGaps_length (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (steps : List Step) :
    (columnGaps pl steps).length = pl.widths.length - 1 := by
  have := (columnGaps_ge_base pl hw steps).1
  rw [baseGaps_length] at this
  omega

theorem columnGaps_margin (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (steps : List Step)
    (i : Nat) (h : i < pl.widths.length - 1) : pl.c.actorMargin ≤ (columnGaps pl steps).getD i 0 :=
  Int.le_trans (baseGaps_ge pl.c pl.widths hw i h) ((columnGaps_ge_base pl hw steps).2 i)

theorem sequence_columns_ordered (pl : Plan) (hwf : pl.Wf) (steps : List Step) (i j : Nat) (hij : i < j)
    (hj : j < pl.widths.length) :
    (columns pl steps).getD i 0 < (columns pl steps).getD j 0 := by
  have hd := centre_diff pl.widths (columnGaps pl steps) i j (Nat.le_of_lt hij) hj
  have hl := ssum_lower (columnGaps pl steps) pl.c.actorMargin i j
    (fun k hk hk' => columnGaps_margin pl hwf.widths steps k (by omega))
  have hp : (0 : Int) < ((j - i : Nat) : Int) := by omega
  have hm := Int.mul_pos hp hwf.pos.margin
  unfold columns
  omega

theorem sequence_columns_separated (pl : Plan) (hwf : pl.Wf) (steps : List Step) (i : Nat)
    (hi : i + 1 < pl.widths.length) :
    (columns pl steps).getD (i + 1) 0 - (columns pl steps).getD i 0 = (columnGaps pl steps).getD i 0 ∧
      pl.c.actorMargin ≤ (columnGaps pl steps).getD i 0 := by
  refine ⟨?_, columnGaps_margin pl hwf.widths steps i (by omega)⟩
  unfold columns
  rw [centre_diff pl.widths _ i (i + 1) (by omega) hi, ssum_single]

/-! ### Message and note spans -/

theorem foldl_covers {α : Type} (f : List Int → α → List Int) (hf : ∀ g a, GapsGe g (f g a))
    (l : List α) (g0 : List Int) (a : α) (ha : a ∈ l) (P : List Int → Prop)
    (hmono : ∀ g g', GapsGe g g' → P g → P g') (hP : ∀ g, GapsGe g0 g → P (f g a)) :
    P (l.foldl f g0) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rw [List.foldl_append, List.foldl_cons]
  exact hmono _ _ (foldl_gapsGe f hf t _) (hP _ (foldl_gapsGe f hf s g0))

theorem widenForMessage_covers (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (g : List Int)
    (hg : g.length = pl.widths.length - 1) (bits src dst route : Nat) (hne : src ≠ dst)
    (hlt : max src dst < pl.widths.length) :
    pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding + pl.c.actorMargin ≤
      ssum (widenForMessage pl g bits src dst route) (min src dst) (max src dst) := by
  have hlt' : min src dst < max src dst := by omega
  have hcov := widen_covers g (min src dst) (max src dst)
    (pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding + pl.c.actorMargin) hlt' (by omega)
  unfold widenForMessage
  dsimp only
  have hb : (src == dst) = false := by simpa using hne
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  split
  · exact Int.le_trans hcov (ssum_mono (bumpGap_ge _ _ _ (half_nonneg (hw dst))) _ _)
  · exact hcov

theorem widenForMessage_self_covers (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (g : List Int)
    (hg : g.length = pl.widths.length - 1) (bits i route : Nat) (hi : i + 1 < pl.widths.length) :
    max (half (pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding)) pl.c.selfLoopMinDx +
        pl.c.actorMargin ≤ ssum (widenForMessage pl g bits i i route) i (i + 1) := by
  have hcov := widen_covers g i (i + 1)
    (max (half (pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding)) pl.c.selfLoopMinDx +
      pl.c.actorMargin) (by omega) (by omega)
  unfold widenForMessage
  dsimp only
  have hc : i < g.length := by omega
  simp only [beq_self_eq_true, ↓reduceIte, widenWhen, hc, decide_true]
  split
  · exact Int.le_trans hcov (ssum_mono (bumpGap_ge _ _ _ (half_nonneg (hw i))) _ _)
  · exact hcov

theorem sequence_span_label_fits (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (steps : List Step)
    (bits src dst route : Nat) (destroyed : Int)
    (hs : Step.message bits src dst route destroyed ∈ steps) (hne : src ≠ dst)
    (hlt : max src dst < pl.widths.length) :
    pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding + pl.c.actorMargin ≤
      (columns pl steps).getD (max src dst) 0 - (columns pl steps).getD (min src dst) 0 := by
  have hd := centre_diff pl.widths (columnGaps pl steps) (min src dst) (max src dst) (by omega) hlt
  have hcov : pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding + pl.c.actorMargin ≤
      ssum (widenSteps pl steps (baseGaps pl.c pl.widths)) (min src dst) (max src dst) := by
    refine foldl_covers (widenStep pl) (widenStep_ge pl hw) steps _ _ hs
      (fun g => pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding + pl.c.actorMargin ≤
        ssum g (min src dst) (max src dst)) ?_ ?_
    · intro g g' hgg hp
      exact Int.le_trans hp (ssum_mono hgg _ _)
    · intro g hgg
      have hlen : g.length = pl.widths.length - 1 := by
        rw [← hgg.1, baseGaps_length]
      exact widenForMessage_covers pl hw g hlen bits src dst route hne hlt
  have := ssum_mono (columnGaps_ge pl steps) (min src dst) (max src dst)
  unfold columns
  omega

theorem sequence_gap_covers_labels (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (steps : List Step)
    (bits src dst route : Nat) (destroyed : Int)
    (hs : Step.message bits src dst route destroyed ∈ steps) (hne : src ≠ dst)
    (hadj : max src dst = min src dst + 1) (hlt : max src dst < pl.widths.length) :
    pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding + pl.c.actorMargin ≤
      (columnGaps pl steps).getD (min src dst) 0 := by
  have h := sequence_span_label_fits pl hw steps bits src dst route destroyed hs hne hlt
  have hd := centre_diff pl.widths (columnGaps pl steps) (min src dst) (max src dst) (by omega) hlt
  rw [hadj, ssum_single] at hd
  unfold columns at h
  rw [hadj] at h
  omega

theorem sequence_self_loop_clear (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (steps : List Step)
    (bits i route : Nat) (destroyed : Int) (hs : Step.message bits i i route destroyed ∈ steps)
    (hi : i + 1 < pl.widths.length) :
    (columns pl steps).getD i 0 +
        max (half (pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding)) pl.c.selfLoopMinDx +
        pl.c.actorMargin ≤ (columns pl steps).getD (i + 1) 0 := by
  have hd := centre_diff pl.widths (columnGaps pl steps) i (i + 1) (by omega) hi
  have hcov : max (half (pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding)) pl.c.selfLoopMinDx +
        pl.c.actorMargin ≤ ssum (widenSteps pl steps (baseGaps pl.c pl.widths)) i (i + 1) := by
    refine foldl_covers (widenStep pl) (widenStep_ge pl hw) steps _ _ hs
      (fun g => max (half (pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding))
        pl.c.selfLoopMinDx + pl.c.actorMargin ≤ ssum g i (i + 1)) ?_ ?_
    · intro g g' hgg hp
      exact Int.le_trans hp (ssum_mono hgg _ _)
    · intro g hgg
      have hlen : g.length = pl.widths.length - 1 := by
        rw [← hgg.1, baseGaps_length]
      exact widenForMessage_self_covers pl hw g hlen bits i route hi

  have := ssum_mono (columnGaps_ge pl steps) i (i + 1)
  unfold columns
  omega

/-! ### Rows -/

theorem addMember_cursor (w : Walk) (r : Rect) : (addMember w r).cursor = w.cursor := by
  unfold addMember; split <;> rfl

theorem addMember_bottom (w : Walk) (r : Rect) : (addMember w r).bottom = w.bottom := by
  unfold addMember; split <;> rfl

theorem addMember_boxRects (w : Walk) (r : Rect) : (addMember w r).boxRects = w.boxRects := by
  unfold addMember; split <;> rfl

theorem addMember_labelRects (w : Walk) (r : Rect) : (addMember w r).labelRects = w.labelRects := by
  unfold addMember; split <;> rfl

theorem addMember_routeRuns (w : Walk) (r : Rect) : (addMember w r).routeRuns = w.routeRuns := by
  unfold addMember; split <;> rfl

theorem addMember_closed (w : Walk) (r : Rect) : (addMember w r).closed = w.closed := by
  unfold addMember; split <;> rfl

theorem addMember_openBars (w : Walk) (r : Rect) : (addMember w r).openBars = w.openBars := by
  unfold addMember; split <;> rfl

theorem addMember_bars (w : Walk) (r : Rect) : (addMember w r).bars = w.bars := by
  unfold addMember; split <;> rfl

theorem addMember_barDepths (w : Walk) (r : Rect) : (addMember w r).barDepths = w.barDepths := by
  unfold addMember; split <;> rfl

theorem addMember_destroyedY (w : Walk) (r : Rect) : (addMember w r).destroyedY = w.destroyedY := by
  unfold addMember; split <;> rfl

/-- `addMember` on the fragment list. -/
def fragsAdd (fs : List FragRun) (r : Rect) : List FragRun :=
  match fs with
  | [] => []
  | f :: rest => { f with members := f.members ++ [r] } :: rest

theorem addMember_fragments (w : Walk) (r : Rect) :
    (addMember w r).fragments = fragsAdd w.fragments r := by
  unfold addMember fragsAdd
  cases hf : w.fragments <;> simp [hf]

theorem createdRect_spec (pl : Plan) (cs : List Int) (bits dst : Nat) (y : Int) (b : Nat) (r : Rect)
    (h : createdRect pl cs bits dst y = some (b, r)) :
    r = ⟨cs.getD dst 0 - half (pl.widths.getD dst 0), y, pl.widths.getD dst 0, pl.heights.getD dst 0⟩ := by
  unfold createdRect at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h

theorem createdBox_cursor (pl : Plan) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) :
    (createdBox pl cs w bits dst y).1.cursor = w.cursor := by
  unfold createdBox
  split
  · simp [addMember_cursor]
  · rfl

theorem createdBox_routeRuns (pl : Plan) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) :
    (createdBox pl cs w bits dst y).1.routeRuns = w.routeRuns := by
  unfold createdBox
  split
  · simp [addMember_routeRuns]
  · rfl

theorem createdBox_nonneg (pl : Plan) (hpl : pl.Wf) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) :
    0 ≤ (createdBox pl cs w bits dst y).2 := by
  unfold createdBox
  split
  · rename_i b r hr
    rw [createdRect_spec pl cs bits dst y b r hr]
    exact Int.add_nonneg (hpl.heights dst) (Int.le_of_lt hpl.pos.boxMargin)
  · exact Int.le_refl _


theorem linesAt_routeLabel (pl : Plan) (route : Nat) :
    pl.linesAt (messageLabelAt pl route) = pl.linesAt (routeLabelPos pl.m route) := by
  unfold messageLabelAt
  cases hp : routeLabelPos pl.m route with
  | none => simp
  | some p =>
    by_cases h : p < pl.labelLines.length
    · simp [h]
    · simp [h, Plan.linesAt, List.getD_eq_getElem?_getD]

theorem advance_cursor (w : Walk) (r : Int) : (w.advance r).cursor = w.cursor + r := rfl

theorem advance_bottom (w : Walk) (r : Int) : (w.advance r).bottom = max w.bottom (w.cursor + r) := rfl

theorem markDestroyed_cursor (w : Walk) (bits : Nat) (destroyed y : Int) :
    (markDestroyed w bits destroyed y).cursor = w.cursor := by
  unfold markDestroyed; split <;> rfl

theorem markDestroyed_routeRuns (w : Walk) (bits : Nat) (destroyed y : Int) :
    (markDestroyed w bits destroyed y).routeRuns = w.routeRuns := by
  unfold markDestroyed; split <;> rfl

theorem placeLabel_cursor (w : Walk) (pos : Option Nat) (r : Rect) :
    (w.placeLabel pos r).cursor = w.cursor := by
  unfold Walk.placeLabel; split <;> rfl

theorem placeLabel_routeRuns (w : Walk) (pos : Option Nat) (r : Rect) :
    (w.placeLabel pos r).routeRuns = w.routeRuns := by
  unfold Walk.placeLabel; split <;> rfl

theorem stepMessage_cursor (pl : Plan) (hpl : pl.Wf) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (destroyed : Int) :
    w.cursor + pl.c.messageTop ≤ (stepMessage pl cs w bits src dst route destroyed).cursor := by
  unfold stepMessage
  simp only [Walk.advance, addMember_cursor, placeLabel_cursor, markDestroyed_cursor, createdBox_cursor]
  have h2 : ∀ y, 0 ≤ (createdBox pl cs w bits dst y).2 := fun y => createdBox_nonneg pl hpl cs w bits dst y
  have h3 := Int.mul_nonneg (Int.natCast_nonneg (pl.linesAt (messageLabelAt pl route)).length)
    hpl.pos.lineHeight
  have h4 := hpl.pos.boxMargin
  have h5 := hpl.pos.selfLoopDepth
  have h6 := h2 (w.cursor + pl.c.messageTop + ((pl.linesAt (messageLabelAt pl route)).length : Int) *
    pl.c.lineHeight)
  split <;> omega

theorem noteTextHeight_nonneg (pl : Plan) (hpl : pl.Wf) (box : Nat) : 0 ≤ noteTextHeight pl box := by
  unfold noteTextHeight
  split
  · exact Int.mul_nonneg (Int.natCast_nonneg _) hpl.pos.lineHeight
  · exact Int.le_refl _

theorem stepNote_cursor (pl : Plan) (hpl : pl.Wf) (cs : List Int) (w : Walk) (placement a b box : Nat) :
    w.cursor < (stepNote pl cs w placement a b box).cursor := by
  unfold stepNote
  simp only [Walk.advance, addMember_cursor, placeLabel_cursor]
  have := noteTextHeight_nonneg pl hpl box
  have := hpl.pos.boxMargin
  have := hpl.pos.noteMargin
  omega

theorem sectionHeight_pos (pl : Plan) (hpl : pl.Wf) (lines : Nat) : 0 < sectionHeight pl.c lines := by
  unfold sectionHeight
  have := hpl.pos.boxMargin
  have := hpl.pos.boxTextMargin
  have := hpl.pos.labelBoxHeight
  omega

theorem fragmentAdvance_pos (pl : Plan) (hpl : pl.Wf) (kind box : Nat) : 0 < fragmentAdvance pl kind box := by
  unfold fragmentAdvance
  have := hpl.pos.boxMargin
  split
  · omega
  · exact sectionHeight_pos pl hpl _

theorem stepFragmentStart_cursor (pl : Plan) (hpl : pl.Wf) (w : Walk) (kind box : Nat) :
    w.cursor < (stepFragmentStart pl w kind box).cursor := by
  unfold stepFragmentStart
  have := fragmentAdvance_pos pl hpl kind box
  show w.cursor < w.cursor + fragmentAdvance pl kind box
  omega

theorem stepFragmentElse_cursor (pl : Plan) (hpl : pl.Wf) (w : Walk) (box sect : Nat) :
    w.cursor < (stepFragmentElse pl w box sect).cursor := by
  unfold stepFragmentElse
  have := sectionHeight_pos pl hpl (pl.linesAt (sectionLabel pl box sect)).length
  show w.cursor < w.cursor + sectionHeight pl.c (pl.linesAt (sectionLabel pl box sect)).length
  omega

theorem foldl_max_ge_init {α : Type} (g : α → Int) (l : List α) (b : Int) :
    b ≤ l.foldl (fun acc d => max acc (g d)) b := by
  induction l generalizing b with
  | nil => exact Int.le_refl _
  | cons a t ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

theorem foldl_max_ge_mem {α : Type} (g : α → Int) (l : List α) (b : Int) (k : α) (hk : k ∈ l) :
    g k ≤ l.foldl (fun acc d => max acc (g d)) b := by
  induction l generalizing b with
  | nil => simp at hk
  | cons a t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hk with rfl | hk'
    · exact Int.le_trans (Int.le_max_right _ _) (foldl_max_ge_init g t _)
    · exact ih _ hk'

theorem foldl_min_le_init {α : Type} (g : α → Int) (l : List α) (b : Int) :
    l.foldl (fun acc d => min acc (g d)) b ≤ b := by
  induction l generalizing b with
  | nil => exact Int.le_refl _
  | cons a t ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (ih _) (Int.min_le_left _ _)

theorem foldl_min_le_mem {α : Type} (g : α → Int) (l : List α) (b : Int) (k : α) (hk : k ∈ l) :
    l.foldl (fun acc d => min acc (g d)) b ≤ g k := by
  induction l generalizing b with
  | nil => simp at hk
  | cons a t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hk with rfl | hk'
    · exact Int.le_trans (foldl_min_le_init g t _) (Int.min_le_right _ _)
    · exact ih _ hk'

theorem rectSpan_mem (rs : List Rect) (r : Rect) (hr : r ∈ rs) :
    (rectSpan rs).1 ≤ r.x ∧ r.x + r.w ≤ (rectSpan rs).2 := by
  cases rs with
  | nil => simp at hr
  | cons r0 rest =>
    unfold rectSpan
    simp only []
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨foldl_min_le_init Rect.x rest _, foldl_max_ge_init (fun k => k.x + k.w) rest _⟩
    · exact ⟨foldl_min_le_mem Rect.x rest _ r hr', foldl_max_ge_mem (fun k => k.x + k.w) rest _ r hr'⟩

theorem rectSpan_ordered (rs : List Rect) (h : ∀ r ∈ rs, 0 ≤ r.w) :
    (rectSpan rs).1 ≤ (rectSpan rs).2 := by
  cases rs with
  | nil => simp [rectSpan]
  | cons r0 rest =>
    have := rectSpan_mem (r0 :: rest) r0 (List.mem_cons_self)
    have := h r0 (List.mem_cons_self)
    omega

theorem fragmentWidth_ge (pl : Plan) (run : FragRun) (natural width : Int)
    (h : fragmentWidth pl run natural = .ok width) : natural ≤ width := by
  unfold fragmentWidth at h
  split at h

  · simp only [pure, Except.pure] at h
    cases h
    exact Int.le_refl _
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · cases h
      exact Int.le_trans (Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _))
        (foldl_max_ge_init (fun d : Divider => pl.labelWidth d.label + 2 * pl.c.boxMargin) run.dividers _)

theorem closeFragment_eq (pl : Plan) (w : Walk) (run : FragRun) (w' : Walk)
    (h : closeFragment pl w run = .ok w') :
    ∃ width, (rectSpan run.members).2 - (rectSpan run.members).1 + 2 * pl.c.boxMargin ≤ width ∧
      w' = closeWith pl w run width := by
  unfold closeFragment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i width hw
    cases h
    exact ⟨width, fragmentWidth_ge _ _ _ _ hw, rfl⟩

theorem closeWith_cursor (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (closeWith pl w run width).cursor = w.cursor + pl.c.boxMargin := by
  unfold closeWith
  simp [addMember_cursor]

theorem closeWith_fragments (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (closeWith pl w run width).fragments = fragsAdd w.fragments (frameRect pl w run width) := by
  unfold closeWith
  simp [addMember_fragments]

theorem closeWith_boxRects (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (closeWith pl w run width).boxRects = w.boxRects.set run.box (frameRect pl w run width) := by
  unfold closeWith
  simp [addMember_boxRects]

/-! ### Fragment invariant -/

/-- The fragment stack at cursor `c`: no fragment starts after the cursor, an enclosing fragment
starts no later than an enclosed one, and every member box lies between its fragment's top and the
cursor. -/
def FragInv (fs : List FragRun) (c : Int) : Prop :=
  (∀ f ∈ fs, f.top ≤ c) ∧ fs.Pairwise (fun f g => g.top ≤ f.top) ∧
    ∀ f ∈ fs, ∀ r ∈ f.members, f.top ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ c

theorem FragInv.mono {fs : List FragRun} {c c' : Int} (h : FragInv fs c) (hc : c ≤ c') :
    FragInv fs c' :=
  ⟨fun f hf => Int.le_trans (h.1 f hf) hc, h.2.1, fun f hf r hr =>
    ⟨(h.2.2 f hf r hr).1, (h.2.2 f hf r hr).2.1, (h.2.2 f hf r hr).2.2.1,
      Int.le_trans (h.2.2 f hf r hr).2.2.2 hc⟩⟩

theorem fragsAdd_head (fs : List FragRun) (r : Rect) (y : Int) :
    (∀ f ∈ (fragsAdd fs r).head?, f.top ≤ y) ↔ ∀ f ∈ fs.head?, f.top ≤ y := by
  cases fs <;> simp [fragsAdd]

theorem fragsAdd_inv {fs : List FragRun} {c : Int} (h : FragInv fs c) (r : Rect)
    (hy : ∀ f ∈ fs.head?, f.top ≤ r.y) (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) (hb : r.y + r.h ≤ c) :
    FragInv (fragsAdd fs r) c := by
  cases fs with
  | nil => exact h
  | cons f rest =>
    obtain ⟨h1, h2, h3⟩ := h
    have h2' := List.pairwise_cons.mp h2
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact h1 f List.mem_cons_self
      · exact h1 g (List.mem_cons_of_mem _ hg)
    · exact List.pairwise_cons.mpr ⟨fun g hg => h2'.1 g hg, h2'.2⟩
    · intro g hg r' hr'
      rcases List.mem_cons.mp hg with rfl | hg
      · have hr'' : r' ∈ f.members ++ [r] := hr'
        rcases List.mem_append.mp hr'' with hr | hr
        · exact h3 f List.mem_cons_self r' hr
        · have : r' = r := by simpa using hr
          subst this
          exact ⟨hy f (by simp), hw, hh, hb⟩
      · exact h3 g (List.mem_cons_of_mem _ hg) r' hr'

theorem markDestroyed_fragments (w : Walk) (bits : Nat) (destroyed y : Int) :
    (markDestroyed w bits destroyed y).fragments = w.fragments := by
  unfold markDestroyed; split <;> rfl

theorem placeLabel_fragments (w : Walk) (pos : Option Nat) (r : Rect) :
    (w.placeLabel pos r).fragments = w.fragments := by
  unfold Walk.placeLabel; split <;> rfl

theorem widest_nonneg (lines : List Measure.Line) : 0 ≤ widest lines := by
  unfold widest
  exact foldl_max_ge_init (fun l : Measure.Line => l.width) lines 0

theorem createdBox_inv (pl : Plan) (hpl : pl.Wf) (cs : List Int) (w : Walk) (bits dst : Nat) (y b : Int)
    (hi : FragInv w.fragments w.cursor) (hy : w.cursor ≤ y) (hby : b ≤ y)
    (hhead : ∀ f ∈ w.fragments.head?, f.top ≤ b)
    (c' : Int) (hc : y + (createdBox pl cs w bits dst y).2 ≤ c') :
    FragInv (createdBox pl cs w bits dst y).1.fragments c' ∧
      ∀ f ∈ (createdBox pl cs w bits dst y).1.fragments.head?, f.top ≤ b := by
  cases hcr : createdRect pl cs bits dst y with
  | none =>
    simp only [createdBox, hcr] at hc ⊢
    exact ⟨hi.mono (by omega), hhead⟩
  | some pr =>
    obtain ⟨bx, r⟩ := pr
    have hr := createdRect_spec pl cs bits dst y bx r hcr
    simp only [createdBox, hcr, addMember_fragments] at hc ⊢
    have hh := hpl.heights dst
    have hw := hpl.widths dst
    have hm := hpl.pos.boxMargin
    subst hr
    refine ⟨?_, (fragsAdd_head _ _ _).mpr hhead⟩
    refine fragsAdd_inv (hi.mono (by simp only [] at hc; omega)) _ ?_ hw hh (by simp only [] at hc ⊢; omega)
    intro f hf
    exact Int.le_trans (hhead f hf) hby

theorem stepMessage_inv (pl : Plan) (hpl : pl.Wf) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (destroyed : Int) (hi : FragInv w.fragments w.cursor) :
    FragInv (stepMessage pl cs w bits src dst route destroyed).fragments
      (stepMessage pl cs w bits src dst route destroyed).cursor := by
  unfold stepMessage
  simp only [Walk.advance, addMember_fragments, addMember_cursor, placeLabel_fragments, placeLabel_cursor,
    markDestroyed_fragments, markDestroyed_cursor, createdBox_cursor]
  generalize hn : ((pl.linesAt (messageLabelAt pl route)).length : Int) * pl.c.lineHeight = n
  generalize hlw : widest (pl.linesAt (messageLabelAt pl route)) = lw
  have hn0 : 0 ≤ n := hn ▸ Int.mul_nonneg (Int.natCast_nonneg _) hpl.pos.lineHeight
  have hlw0 : 0 ≤ lw := hlw ▸ widest_nonneg _
  have hmt := hpl.pos.messageTop
  have hbm := hpl.pos.boxMargin
  have hsd := hpl.pos.selfLoopDepth
  have hwp := hpl.pos.wrapPadding
  have hhead : ∀ f ∈ w.fragments.head?, f.top ≤ w.cursor := fun f hf => hi.1 f (List.mem_of_mem_head? hf)
  have key := createdBox_inv pl hpl cs w bits dst (w.cursor + pl.c.messageTop + n) w.cursor hi
    (by omega) (by omega) hhead
  have hnn := createdBox_nonneg pl hpl cs w bits dst (w.cursor + pl.c.messageTop + n)
  generalize createdBox pl cs w bits dst (w.cursor + pl.c.messageTop + n) = cb at key hnn ⊢
  have hdx : 0 ≤ (if src == dst then max (half (lw + 2 * pl.c.wrapPadding)) pl.c.selfLoopMinDx else 0) := by
    split
    · exact Int.le_trans (half_nonneg (by omega)) (Int.le_max_left _ _)
    · exact Int.le_refl _
  have hrow : pl.c.messageTop + n ≤ (if src == dst then pl.c.messageTop + n + pl.c.boxMargin + pl.c.selfLoopDepth
      else pl.c.messageTop + n + pl.c.boxMargin) := by
    split <;> omega
  generalize (if src == dst then max (half (lw + 2 * pl.c.wrapPadding)) pl.c.selfLoopMinDx else 0) = dx at hdx ⊢
  generalize (if src == dst then pl.c.messageTop + n + pl.c.boxMargin + pl.c.selfLoopDepth
      else pl.c.messageTop + n + pl.c.boxMargin) = rs at hrow ⊢
  have hk := key (w.cursor + (rs + cb.2)) (by omega)
  refine fragsAdd_inv hk.1 _ hk.2 ?_ ?_ ?_
  · dsimp only; omega
  · dsimp only; omega
  · dsimp only; omega

theorem noteSpan_width_nonneg (pl : Plan) (hpl : pl.Wf) (cs : List Int) (placement a b box : Nat) :
    0 ≤ (noteSpan pl cs placement a b box).2 := by
  unfold noteSpan
  have h1 := hpl.widths a
  have h2 := widest_nonneg (pl.titleLines box)
  have h3 := hpl.pos.noteMargin
  split
  · exact Int.le_trans h1 (Int.le_max_left _ _)
  · split
    · exact Int.le_trans (by omega) (Int.le_max_right _ _)
    · split <;> exact Int.le_trans h1 (Int.le_max_left _ _)

theorem stepNote_inv (pl : Plan) (hpl : pl.Wf) (cs : List Int) (w : Walk) (placement a b box : Nat)
    (hi : FragInv w.fragments w.cursor) :
    FragInv (stepNote pl cs w placement a b box).fragments (stepNote pl cs w placement a b box).cursor := by
  unfold stepNote
  simp only [Walk.advance, addMember_fragments, addMember_cursor, placeLabel_fragments, placeLabel_cursor]
  have h1 := noteTextHeight_nonneg pl hpl box
  have h2 := noteSpan_width_nonneg pl hpl cs placement a b box
  have h3 := hpl.pos.boxMargin
  have h4 := hpl.pos.noteMargin
  refine fragsAdd_inv (hi.mono (by omega)) _ ?_ h2 (by dsimp only; omega) (by dsimp only; omega)
  intro f hf
  have := hi.1 f (List.mem_of_mem_head? hf)
  dsimp only
  omega

theorem FragInv.push {fs : List FragRun} {c c' : Int} (h : FragInv fs c) (hc : c ≤ c') (box kind : Nat) :
    FragInv (⟨box, kind, c, [], []⟩ :: fs) c' := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hc
    · exact Int.le_trans (h.1 f hf) hc
  · exact List.pairwise_cons.mpr ⟨fun g hg => h.1 g hg, h.2.1⟩
  · intro f hf r hr
    rcases List.mem_cons.mp hf with rfl | hf
    · simp at hr
    · have := h.2.2 f hf r hr
      exact ⟨this.1, this.2.1, this.2.2.1, Int.le_trans this.2.2.2 hc⟩

theorem FragInv.tail {f : FragRun} {rest : List FragRun} {c : Int} (h : FragInv (f :: rest) c) :
    FragInv rest c :=
  ⟨fun g hg => h.1 g (List.mem_cons_of_mem _ hg), (List.pairwise_cons.mp h.2.1).2,
    fun g hg r hr => h.2.2 g (List.mem_cons_of_mem _ hg) r hr⟩

theorem FragInv.setHead {f f' : FragRun} {rest : List FragRun} {c : Int} (h : FragInv (f :: rest) c)
    (ht : f'.top = f.top) (hm : f'.members = f.members) : FragInv (f' :: rest) c := by
  obtain ⟨h1, h2, h3⟩ := h
  have h2' := List.pairwise_cons.mp h2
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [ht]; exact h1 f List.mem_cons_self
    · exact h1 g (List.mem_cons_of_mem _ hg)
  · exact List.pairwise_cons.mpr ⟨fun g hg => by rw [ht]; exact h2'.1 g hg, h2'.2⟩
  · intro g hg r hr
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [hm] at hr
      have := h3 f List.mem_cons_self r hr
      rw [ht]; exact this
    · exact h3 g (List.mem_cons_of_mem _ hg) r hr

theorem stepFragmentStart_inv (pl : Plan) (hpl : pl.Wf) (w : Walk) (kind box : Nat)
    (hi : FragInv w.fragments w.cursor) :
    FragInv (stepFragmentStart pl w kind box).fragments (stepFragmentStart pl w kind box).cursor := by
  have hs := fragmentAdvance_pos pl hpl kind box
  unfold stepFragmentStart
  refine FragInv.push hi ?_ box kind
  show w.cursor ≤ w.cursor + fragmentAdvance pl kind box
  omega

theorem stepFragmentElse_inv (pl : Plan) (hpl : pl.Wf) (w : Walk) (box sect : Nat)
    (hi : FragInv w.fragments w.cursor) :
    FragInv (stepFragmentElse pl w box sect).fragments (stepFragmentElse pl w box sect).cursor := by
  unfold stepFragmentElse
  cases hf : w.fragments with
  | nil => exact ⟨by simp, List.Pairwise.nil, by simp⟩
  | cons f rest =>
    rw [hf] at hi
    dsimp only
    refine FragInv.mono (c := w.cursor) ?_ ?_
    · exact FragInv.setHead hi rfl rfl
    · have := sectionHeight_pos pl hpl (pl.linesAt (sectionLabel pl box sect)).length
      show w.cursor ≤ w.cursor + sectionHeight pl.c (pl.linesAt (sectionLabel pl box sect)).length
      omega

theorem closePop_inv (pl : Plan) (hpl : pl.Wf) (w : Walk) (run : FragRun) (rest : List FragRun) (w1 : Walk)
    (hf : w.fragments = run :: rest) (hi : FragInv w.fragments w.cursor)
    (h : closeFragment pl { w with fragments := rest } run = .ok w1) :
    FragInv w1.fragments w1.cursor := by
  obtain ⟨width, hge, rfl⟩ := closeFragment_eq pl _ run w1 h
  rw [closeWith_fragments, closeWith_cursor]
  rw [hf] at hi
  have hrest := hi.tail
  have hmem := hi.2.2 run List.mem_cons_self
  have hord := (List.pairwise_cons.mp hi.2.1).1
  have htop := hi.1 run List.mem_cons_self
  have hbm := hpl.pos.boxMargin
  have hspan := rectSpan_ordered run.members (fun r hr => (hmem r hr).2.1)
  dsimp only
  refine fragsAdd_inv (hrest.mono (by omega)) _ ?_ ?_ ?_ ?_
  · intro g hg
    exact hord g (List.mem_of_mem_head? hg)
  · unfold frameRect; dsimp only; omega
  · unfold frameRect; dsimp only; omega
  · unfold frameRect; dsimp only; omega

theorem stepFragmentEnd_inv (pl : Plan) (hpl : pl.Wf) (w w' : Walk) (hi : FragInv w.fragments w.cursor)
    (h : stepFragmentEnd pl w = .ok w') : FragInv w'.fragments w'.cursor := by
  unfold stepFragmentEnd at h
  cases hf : w.fragments with
  | nil =>
    rw [hf] at h
    simp only [pure, Except.pure] at h
    cases h
    exact hi
  | cons run rest =>
    rw [hf] at h
    exact closePop_inv pl hpl w run rest w' hf hi h

theorem closeAll_inv (pl : Plan) (hpl : pl.Wf) :
    ∀ (n : Nat) (w w' : Walk), FragInv w.fragments w.cursor → closeAll pl w n = .ok w' →
      FragInv w'.fragments w'.cursor := by
  intro n
  induction n with
  | zero =>
    intro w w' hi h
    simp only [closeAll, pure, Except.pure] at h
    cases h
    exact hi
  | succ n ih =>
    intro w w' hi h
    unfold closeAll at h
    cases hf : w.fragments with
    | nil =>
      rw [hf] at h
      simp only [pure, Except.pure] at h
      cases h
      exact hi
    | cons run rest =>
      rw [hf] at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i w1 hw1
        exact ih w1 w' (closePop_inv pl hpl w run rest w1 hf hi hw1) h

theorem stepActivateStart_keep (pl : Plan) (cs : List Int) (w : Walk) (actor : Nat) :
    (stepActivateStart pl cs w actor).fragments = w.fragments ∧
      (stepActivateStart pl cs w actor).cursor = w.cursor := ⟨rfl, rfl⟩

theorem stepActivateEnd_keep (pl : Plan) (w : Walk) (actor : Nat) :
    (stepActivateEnd pl w actor).fragments = w.fragments ∧
      (stepActivateEnd pl w actor).cursor = w.cursor := by
  unfold stepActivateEnd
  constructor <;> (dsimp only; split <;> rfl)

/-- A step that draws a row: a message, a note, or the start of a fragment or of one of its sections. -/
def Step.isRow : Step → Bool
  | .message .. => true
  | .note .. => true
  | .fragmentStart .. => true
  | .fragmentElse .. => true
  | _ => false

theorem stepWalk_inv (pl : Plan) (hpl : pl.Wf) (cs : List Int) (w w' : Walk) (s : Step)
    (hi : FragInv w.fragments w.cursor) (h : stepWalk pl cs w s = .ok w') :
    FragInv w'.fragments w'.cursor ∧ w.cursor ≤ w'.cursor := by
  cases s with
  | message bits src dst route destroyed =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨stepMessage_inv pl hpl cs w bits src dst route destroyed hi, by
      have := stepMessage_cursor pl hpl cs w bits src dst route destroyed
      have := hpl.pos.messageTop
      omega⟩
  | note placement a b box =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨stepNote_inv pl hpl cs w placement a b box hi,
      Int.le_of_lt (stepNote_cursor pl hpl cs w placement a b box)⟩
  | fragmentStart kind box =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨stepFragmentStart_inv pl hpl w kind box hi, Int.le_of_lt (stepFragmentStart_cursor pl hpl w kind box)⟩
  | fragmentElse box sect =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨stepFragmentElse_inv pl hpl w box sect hi, Int.le_of_lt (stepFragmentElse_cursor pl hpl w box sect)⟩
  | fragmentEnd =>
    simp only [stepWalk] at h
    refine ⟨stepFragmentEnd_inv pl hpl w w' hi h, ?_⟩
    unfold stepFragmentEnd at h
    cases hf : w.fragments with
    | nil =>
      rw [hf] at h
      simp only [pure, Except.pure] at h
      cases h
      exact Int.le_refl _
    | cons run rest =>
      rw [hf] at h
      obtain ⟨width, _, rfl⟩ := closeFragment_eq pl _ run w' h
      rw [closeWith_cursor]
      have := hpl.pos.boxMargin
      show w.cursor ≤ w.cursor + pl.c.boxMargin
      omega
  | activateStart actor =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    have hk := stepActivateStart_keep pl cs w actor
    rw [hk.1, hk.2]
    exact ⟨hi, Int.le_refl _⟩
  | activateEnd actor =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    have hk := stepActivateEnd_keep pl w actor
    rw [hk.1, hk.2]
    exact ⟨hi, Int.le_refl _⟩

theorem steps_inv (pl : Plan) (hpl : pl.Wf) (cs : List Int) :
    ∀ (steps : List Step) (w w' : Walk), FragInv w.fragments w.cursor →
      steps.foldlM (stepWalk pl cs) w = .ok w' → FragInv w'.fragments w'.cursor ∧ w.cursor ≤ w'.cursor := by
  intro steps
  induction steps with
  | nil =>
    intro w w' hi h
    simp only [List.foldlM, pure, Except.pure] at h
    cases h
    exact ⟨hi, Int.le_refl _⟩
  | cons s t ih =>
    intro w w' hi h
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w1 hw1
      have h1 := stepWalk_inv pl hpl cs w w1 s hi hw1
      have h2 := ih w1 w' h1.1 h
      exact ⟨h2.1, Int.le_trans h1.2 h2.2⟩

/-! ### Rows and frames -/

/-- Every row-drawing event moves the cursor strictly down, and an event that draws no row leaves it
where it is (`sequence-49`). -/
theorem sequence_rows_strictly_increasing (pl : Plan) (hpl : pl.Wf) (cs : List Int) (w w' : Walk) (s : Step)
    (h : stepWalk pl cs w s = .ok w') :
    (s.isRow = true → w.cursor < w'.cursor) ∧
      (s = .fragmentEnd → w.fragments ≠ [] → w.cursor < w'.cursor) ∧
      (∀ a, s = .activateStart a ∨ s = .activateEnd a → w'.cursor = w.cursor) := by
  have hm := hpl.pos.messageTop
  have hb := hpl.pos.boxMargin
  cases s with
  | message bits src dst route destroyed =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    have := stepMessage_cursor pl hpl cs w bits src dst route destroyed
    refine ⟨fun _ => by omega, by simp, by simp⟩
  | note placement a b box =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨fun _ => stepNote_cursor pl hpl cs w placement a b box, by simp, by simp⟩
  | fragmentStart kind box =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨fun _ => stepFragmentStart_cursor pl hpl w kind box, by simp, by simp⟩
  | fragmentElse box sect =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨fun _ => stepFragmentElse_cursor pl hpl w box sect, by simp, by simp⟩
  | fragmentEnd =>
    simp only [stepWalk] at h
    refine ⟨by simp [Step.isRow], fun _ hf => ?_, by simp⟩
    unfold stepFragmentEnd at h
    cases hfr : w.fragments with
    | nil => exact absurd hfr hf
    | cons run rest =>
      rw [hfr] at h
      obtain ⟨width, _, rfl⟩ := closeFragment_eq pl _ run w' h
      rw [closeWith_cursor]
      show w.cursor < w.cursor + pl.c.boxMargin
      omega
  | activateStart actor =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    refine ⟨by simp [Step.isRow], by simp, fun a ha => ?_⟩
    exact (stepActivateStart_keep pl cs w actor).2
  | activateEnd actor =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    refine ⟨by simp [Step.isRow], by simp, fun a ha => ?_⟩
    exact (stepActivateEnd_keep pl w actor).2

theorem initWalk_inv (pl : Plan) (cs : List Int) :
    FragInv (initWalk pl cs).fragments (initWalk pl cs).cursor :=
  ⟨fun f hf => by simp [initWalk] at hf, List.Pairwise.nil, fun f hf => by simp [initWalk] at hf⟩

theorem frameRect_x (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (frameRect pl w run width).x = (rectSpan run.members).1 - pl.c.boxMargin -
      half (width - ((rectSpan run.members).2 - (rectSpan run.members).1 + 2 * pl.c.boxMargin)) := rfl

theorem frameRect_y (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (frameRect pl w run width).y = run.top := rfl

theorem frameRect_w (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (frameRect pl w run width).w = width := rfl

theorem frameRect_h (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (frameRect pl w run width).h = w.cursor + pl.c.boxMargin - run.top := rfl


theorem list_getD_set_self (l : List Rect) (i : Nat) (r d : Rect) (h : i < l.length) :
    (l.set i r).getD i d = r := by
  simp [List.getD_eq_getElem?_getD, h]

/-- When a fragment closes, its frame contains every member box: the message rows, the notes, the
created actors, and the frames of the fragments nested in it (`sequence-52`). The state before the
closing event is any state that the events `pre` reach from the first row. -/
theorem sequence_frames_contain_members (pl : Plan) (hpl : pl.Wf) (cs : List Int) (pre : List Step)
    (w1 w2 : Walk) (run : FragRun) (rest : List FragRun)
    (hpre : pre.foldlM (stepWalk pl cs) (initWalk pl cs) = .ok w1)
    (hf : w1.fragments = run :: rest) (hb : run.box < w1.boxRects.length)
    (hend : stepFragmentEnd pl w1 = .ok w2) :
    ∀ r ∈ run.members, (w2.boxRects.getD run.box rectZero).Contained r := by
  have hi := (steps_inv pl hpl cs pre (initWalk pl cs) w1 (initWalk_inv pl cs) hpre).1
  unfold stepFragmentEnd at hend
  rw [hf] at hend
  obtain ⟨width, hge, rfl⟩ := closeFragment_eq pl _ run w2 hend
  rw [closeWith_boxRects, list_getD_set_self _ _ _ _ (by simpa using hb)]
  rw [hf] at hi
  have hmem := hi.2.2 run List.mem_cons_self
  have hbm := hpl.pos.boxMargin
  intro r hr
  have h1 := hmem r hr
  have h2 := rectSpan_mem run.members r hr
  have h3 : 0 ≤ half (width - ((rectSpan run.members).2 - (rectSpan run.members).1 + 2 * pl.c.boxMargin)) :=
    half_nonneg (by omega)
  have h4 := half_le (v := width - ((rectSpan run.members).2 - (rectSpan run.members).1 + 2 * pl.c.boxMargin))
    (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [frameRect_x, frameRect_y, frameRect_w, frameRect_h] <;> omega

/-- The frame of a closed fragment is a member of the enclosing fragment, so the enclosing frame
contains it as well. -/
theorem closed_frame_is_member (pl : Plan) (w : Walk) (run g : FragRun) (rest : List FragRun) (width : Int) :
    ∃ g', (closeWith pl { w with fragments := g :: rest } run width).fragments.head? = some g' ∧
      frameRect pl { w with fragments := g :: rest } run width ∈ g'.members := by
  rw [closeWith_fragments]
  exact ⟨{ g with members := g.members ++ [frameRect pl { w with fragments := g :: rest } run width] },
    rfl, by simp⟩

/-! ### Notes over lifelines -/

theorem widenForNote_covers (pl : Plan) (g : List Int) (hg : g.length = pl.widths.length - 1)
    (a b box : Nat) (hne : a ≠ b) (hlt : max a b < pl.widths.length) :
    widest (pl.titleLines box) + 2 * pl.c.noteMargin + pl.c.actorMargin ≤
      ssum (widenForNote pl g 2 a b box) (min a b) (max a b) := by
  have hcov := widen_covers g (min a b) (max a b)
    (widest (pl.titleLines box) + 2 * pl.c.noteMargin + pl.c.actorMargin) (by omega) (by omega)
  unfold widenForNote
  dsimp only
  have hb : (a == b) = false := by simpa using hne
  simp [hb]
  exact hcov

theorem note_span_fits (pl : Plan) (hw : ∀ k, 0 ≤ pl.widths.getD k 0) (steps : List Step)
    (a b box : Nat) (hs : Step.note 2 a b box ∈ steps) (hne : a ≠ b)
    (hlt : max a b < pl.widths.length) :
    widest (pl.titleLines box) + 2 * pl.c.noteMargin + pl.c.actorMargin ≤
      (columns pl steps).getD (max a b) 0 - (columns pl steps).getD (min a b) 0 := by
  have hd := centre_diff pl.widths (columnGaps pl steps) (min a b) (max a b) (by omega) hlt
  have hcov : widest (pl.titleLines box) + 2 * pl.c.noteMargin + pl.c.actorMargin ≤
      ssum (widenSteps pl steps (baseGaps pl.c pl.widths)) (min a b) (max a b) := by
    refine foldl_covers (widenStep pl) (widenStep_ge pl hw) steps _ _ hs
      (fun g => widest (pl.titleLines box) + 2 * pl.c.noteMargin + pl.c.actorMargin ≤
        ssum g (min a b) (max a b)) ?_ ?_
    · intro g g' hgg hp
      exact Int.le_trans hp (ssum_mono hgg _ _)
    · intro g hgg
      have hlen : g.length = pl.widths.length - 1 := by
        rw [← hgg.1, baseGaps_length]
      exact widenForNote_covers pl g hlen a b box hne hlt
  have := ssum_mono (columnGaps_ge pl steps) (min a b) (max a b)
  unfold columns
  omega

theorem columns_minmax (pl : Plan) (hwf : pl.Wf) (steps : List Step) (a b : Nat) (hne : a ≠ b)
    (hlt : max a b < pl.widths.length) :
    min ((columns pl steps).getD a 0) ((columns pl steps).getD b 0) = (columns pl steps).getD (min a b) 0 ∧
      max ((columns pl steps).getD a 0) ((columns pl steps).getD b 0) = (columns pl steps).getD (max a b) 0 := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := sequence_columns_ordered pl hwf steps a b h (by omega)
    have e1 : min a b = a := Nat.min_eq_left (Nat.le_of_lt h)
    have e2 : max a b = b := Nat.max_eq_right (Nat.le_of_lt h)
    rw [e1, e2]
    exact ⟨Int.min_eq_left (Int.le_of_lt this), Int.max_eq_right (Int.le_of_lt this)⟩
  · have := sequence_columns_ordered pl hwf steps b a h (by omega)
    have e1 : min a b = b := Nat.min_eq_right (Nat.le_of_lt h)
    have e2 : max a b = a := Nat.max_eq_left (Nat.le_of_lt h)
    rw [e1, e2]
    exact ⟨Int.min_eq_right (Int.le_of_lt this), Int.max_eq_left (Int.le_of_lt this)⟩

/-- A note over two lifelines lies within the lifelines, widened by half the actor margin, because the
columns were widened to hold its text (`sequence-53`). The note over one lifeline is not covered: its
width can exceed the margin. -/
theorem sequence_notes_contain_span (pl : Plan) (hwf : pl.Wf) (steps : List Step) (a b box : Nat)
    (hs : Step.note 2 a b box ∈ steps) (hne : a ≠ b) (hlt : max a b < pl.widths.length) :
    (columns pl steps).getD (min a b) 0 - half pl.c.actorMargin ≤
        (noteSpan pl (columns pl steps) 2 a b box).1 ∧
      (noteSpan pl (columns pl steps) 2 a b box).1 + (noteSpan pl (columns pl steps) 2 a b box).2 ≤
        (columns pl steps).getD (max a b) 0 + half pl.c.actorMargin := by
  have hfit := note_span_fits pl hwf.widths steps a b box hs hne hlt
  have hmm := columns_minmax pl hwf steps a b hne hlt
  have hb : (a == b) = false := by simpa using hne
  have c1 : ¬ ((2 : Nat) == 2 ∧ a == b) := by simp [hb]
  have c2 : ((2 : Nat) == 2) = true := by simp
  unfold noteSpan
  dsimp only
  split
  · rename_i h
    exact absurd h c1
  · dsimp only
    have hh : 0 ≤ half pl.c.actorMargin := half_nonneg (Int.le_of_lt hwf.pos.margin)
    have hAB : widest (pl.titleLines box) + 2 * pl.c.noteMargin ≤
        max ((columns pl steps).getD a 0) ((columns pl steps).getD b 0) + half pl.c.actorMargin -
          (min ((columns pl steps).getD a 0) ((columns pl steps).getD b 0) - half pl.c.actorMargin) := by
      have := hwf.pos.margin
      omega
    rw [Int.max_eq_left hAB]
    omega

/-! ### Messages -/

/-- The bottom edge of the header box of lifeline `o` in the walk `w`. -/
def headerBottom (pl : Plan) (w : Walk) (o : Nat) : Int :=
  let b := w.boxRects.getD ((pl.actorBoxes[o]?).getD 0) rectZero
  b.y + b.h

theorem messageRun_points_cross (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat) (y dx : Int)
    (hne : src ≠ dst) :
    (messageRun pl cs w bits src dst route y dx).points =
      [⟨cs.getD src 0, headerBottom pl w src⟩, ⟨cs.getD src 0, y⟩, ⟨cs.getD dst 0, y⟩,
        ⟨cs.getD dst 0, headerBottom pl w dst⟩] := by
  unfold messageRun headerBottom
  have hb : (src == dst) = false := by simpa using hne
  simp [hb]

theorem messageRun_points_self (pl : Plan) (cs : List Int) (w : Walk) (bits src route : Nat) (y dx : Int) :
    (messageRun pl cs w bits src src route y dx).points =
      [⟨cs.getD src 0, headerBottom pl w src⟩, ⟨cs.getD src 0, y⟩, ⟨cs.getD src 0 + dx, y⟩,
        ⟨cs.getD src 0 + dx, y + pl.c.selfLoopDepth⟩, ⟨cs.getD src 0, y + pl.c.selfLoopDepth⟩,
        ⟨cs.getD src 0, headerBottom pl w src⟩] := by
  unfold messageRun headerBottom
  simp

/-- A message that spans two lifelines leaves the first lifeline and arrives on the second; a
message to the same lifeline leaves it, loops `dx` to the right, and returns (`sequence-47`). -/
theorem sequence_message_at_lifeline (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (destroyed : Int) :
    ∃ run, (stepMessage pl cs w bits src dst route destroyed).routeRuns = w.routeRuns ++ [run] ∧
      (src ≠ dst → run.points.map (·.x) =
        [cs.getD src 0, cs.getD src 0, cs.getD dst 0, cs.getD dst 0]) ∧
      (src = dst → run.points.map (·.x) =
        [cs.getD src 0, cs.getD src 0,
          cs.getD src 0 + max (half (pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding))
            pl.c.selfLoopMinDx,
          cs.getD src 0 + max (half (pl.labelWidth (routeLabelPos pl.m route) + 2 * pl.c.wrapPadding))
            pl.c.selfLoopMinDx, cs.getD src 0, cs.getD src 0]) := by
  unfold stepMessage
  simp only [Walk.advance, addMember_routeRuns, placeLabel_routeRuns, markDestroyed_routeRuns,
    createdBox_routeRuns]
  refine ⟨_, rfl, fun hne => ?_, fun heq => ?_⟩
  · rw [messageRun_points_cross _ _ _ _ _ _ _ _ _ hne]
    simp
  · subst heq
    rw [messageRun_points_self]
    simp [linesAt_routeLabel, Plan.labelWidth]

/-! ### Activations -/

theorem extractFirst_some {α : Type} (p : α → Bool) :
    ∀ (l : List α) (y : α) (ys : List α), extractFirst p l = some (y, ys) →
      p y = true ∧ ∃ pre suf, l = pre ++ y :: suf ∧ ys = pre ++ suf := by
  intro l
  induction l with
  | nil => intro y ys h; simp [extractFirst] at h
  | cons x xs ih =>
    intro y ys h
    unfold extractFirst at h
    by_cases hx : p x = true
    · simp only [hx, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hx, [], xs, rfl, rfl⟩
    · simp only [hx] at h
      cases hr : extractFirst p xs with
      | none => rw [hr] at h; simp at h
      | some r =>
        obtain ⟨y', ys'⟩ := r
        rw [hr] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hp, pre, suf, hl, hys⟩ := ih y' ys' hr
        exact ⟨hp, x :: pre, suf, by simp [hl], by simp [hys]⟩

theorem extractFirst_none {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = false) → extractFirst p l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    unfold extractFirst
    have hx := h x List.mem_cons_self
    simp [hx, ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem extractFirst_exists {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∃ x ∈ l, p x = true) → ∃ y ys, extractFirst p l = some (y, ys) := by
  intro l
  induction l with
  | nil => intro h; obtain ⟨x, hx, _⟩ := h; simp at hx
  | cons x xs ih =>
    intro h
    unfold extractFirst
    by_cases hx : p x = true
    · simp [hx]
    · obtain ⟨z, hz, hpz⟩ := h
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact absurd hpz hx
      · obtain ⟨y, ys, hr⟩ := ih ⟨z, hz', hpz⟩
        simp [hx, hr]

theorem getD_set_int (l : List Int) (i j : Nat) (v : Int) :
    (l.set i v).getD j 0 = if i = j ∧ i < l.length then v else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases h2 : i < l.length <;> simp [h2]
  · simp [h]

/-- The open activation bars are a stack on each lifeline: a lifeline whose counter is `d` has exactly
one open bar at each depth `1` to `d`, and no other. -/
def BarInv (w : Walk) : Prop :=
  (∀ a, 0 ≤ w.barDepths.getD a 0) ∧
  (∀ b ∈ w.openBars, 1 ≤ b.depth ∧ b.actor < w.barDepths.length) ∧
  (w.openBars.map fun b => (b.actor, b.depth)).Nodup ∧
  ∀ (a : Nat) (k : Int), 1 ≤ k →
    (k ≤ w.barDepths.getD a 0 ↔ ∃ b ∈ w.openBars, b.actor = a ∧ b.depth = k)

theorem initWalk_barInv (pl : Plan) (cs : List Int) : BarInv (initWalk pl cs) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp only [initWalk, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp
  · intro b hb
    simp [initWalk] at hb
  · simp [initWalk]
  · intro a k hk
    simp only [initWalk, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp <;> omega

theorem stepActivateStart_barInv (pl : Plan) (cs : List Int) (w : Walk) (actor : Nat) (hi : BarInv w)
    (ha : actor < w.barDepths.length) : BarInv (stepActivateStart pl cs w actor) := by
  obtain ⟨h1, h2, h3, h4⟩ := hi
  unfold stepActivateStart
  dsimp only
  have hD := h1 actor
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    rw [getD_set_int]
    split
    · omega
    · exact h1 a
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [List.length_set]
      omega
    · have := h2 b hb
      simpa only [List.length_set] using this
  · simp only [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, h3⟩
    intro hmem
    obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at hbe
    have := (h4 actor (w.barDepths.getD actor 0 + 1) (by omega)).mpr ⟨b, hb, hbe.1, hbe.2⟩
    omega
  · intro a k hk
    rw [getD_set_int]
    by_cases hae : actor = a
    · subst hae
      simp only [ha, and_self, ↓reduceIte]
      constructor
      · intro hk'
        by_cases hkd : k ≤ w.barDepths.getD actor 0
        · obtain ⟨b, hb, hb1, hb2⟩ := (h4 actor k hk).mp hkd
          exact ⟨b, List.mem_cons_of_mem _ hb, hb1, hb2⟩
        · exact ⟨_, List.mem_cons_self, rfl, by show w.barDepths.getD actor 0 + 1 = k; omega⟩
      · rintro ⟨b, hb, hb1, hb2⟩
        rcases List.mem_cons.mp hb with rfl | hb'
        · dsimp only at hb1 hb2
          omega
        · have := (h4 actor k hk).mpr ⟨b, hb', hb1, hb2⟩
          omega
    · simp only [hae, false_and, ↓reduceIte]
      constructor
      · intro hk'
        obtain ⟨b, hb, hb1, hb2⟩ := (h4 a k hk).mp hk'
        exact ⟨b, List.mem_cons_of_mem _ hb, hb1, hb2⟩
      · rintro ⟨b, hb, hb1, hb2⟩
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd hb1 hae
        · exact (h4 a k hk).mpr ⟨b, hb', hb1, hb2⟩

theorem nodup_remove {β γ : Type} (f : β → γ) (pre suf : List β) (y : β)
    (h : (List.map f (pre ++ y :: suf)).Nodup) :
    (List.map f (pre ++ suf)).Nodup ∧ ∀ z ∈ pre ++ suf, f z ≠ f y := by
  rw [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at h
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := h
  constructor
  · rw [List.map_append, List.nodup_append]
    refine ⟨h1, h3, ?_⟩
    intro a ha b hb
    exact h4 a ha b (List.mem_cons_of_mem _ hb)
  · intro z hz hfz
    rcases List.mem_append.mp hz with hz | hz
    · exact h4 (f z) (List.mem_map_of_mem hz) (f y) List.mem_cons_self hfz
    · exact h2 (hfz ▸ List.mem_map_of_mem hz)

theorem mem_remove {β : Type} {pre suf : List β} {y z : β} (h : z ∈ pre ++ y :: suf) (hne : z ≠ y) :
    z ∈ pre ++ suf := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact Or.inl h
  · exact absurd h hne
  · exact Or.inr h

theorem mem_of_mem_remove {β : Type} {pre suf : List β} {y z : β} (h : z ∈ pre ++ suf) :
    z ∈ pre ++ y :: suf := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem stepActivateEnd_barInv (pl : Plan) (w : Walk) (actor : Nat) (hi : BarInv w) :
    BarInv (stepActivateEnd pl w actor) := by
  obtain ⟨h1, h2, h3, h4⟩ := hi
  unfold stepActivateEnd
  dsimp only
  have hD := h1 actor
  by_cases hz : w.barDepths.getD actor 0 = 0
  · have hn : extractFirst (fun b : BarRun => b.actor == actor && b.depth == max (w.barDepths.getD actor 0 - 1) 0 + 1)
        w.openBars = none := by
      apply extractFirst_none
      intro b hb
      by_cases hpb : (b.actor == actor && b.depth == max (w.barDepths.getD actor 0 - 1) 0 + 1) = true
      · have hpb' : b.actor = actor ∧ b.depth = max (w.barDepths.getD actor 0 - 1) 0 + 1 := by
          simpa using hpb
        have := (h4 actor b.depth (by omega)).mpr ⟨b, hb, hpb'.1, rfl⟩
        omega
      · simpa using hpb
    rw [hn]
    dsimp only
    refine ⟨?_, ?_, h3, ?_⟩
    · intro a
      rw [getD_set_int]
      split
      · omega
      · exact h1 a
    · intro b hb
      have := h2 b hb
      simpa only [List.length_set] using this
    · intro a k hk
      rw [getD_set_int]
      by_cases hae : actor = a
      · subst hae
        split
        · rw [← h4 actor k hk]; omega
        · exact h4 actor k hk
      · simp only [hae, false_and, ↓reduceIte]
        exact h4 a k hk
  · have hpos : 1 ≤ w.barDepths.getD actor 0 := by omega
    obtain ⟨y0, hy0, hy0a, hy0d⟩ := (h4 actor (w.barDepths.getD actor 0) hpos).mp (Int.le_refl _)
    have hex : ∃ x ∈ w.openBars,
        (fun b : BarRun => b.actor == actor && b.depth == max (w.barDepths.getD actor 0 - 1) 0 + 1) x = true := by
      refine ⟨y0, hy0, ?_⟩
      show (y0.actor == actor && y0.depth == max (w.barDepths.getD actor 0 - 1) 0 + 1) = true
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr hy0a, beq_iff_eq.mpr (by omega)⟩
    obtain ⟨y, ys, hr⟩ := extractFirst_exists _ w.openBars hex
    rw [hr]
    dsimp only
    obtain ⟨hp, pre, suf, hl, hys⟩ := extractFirst_some _ w.openBars y ys hr
    have hpy : y.actor = actor ∧ y.depth = w.barDepths.getD actor 0 := by
      have : y.actor = actor ∧ y.depth = max (w.barDepths.getD actor 0 - 1) 0 + 1 := by simpa using hp
      omega
    have hnd := nodup_remove (fun b : BarRun => (b.actor, b.depth)) pre suf y (hl ▸ h3)
    have hyl : y ∈ w.openBars := by rw [hl]; simp
    have hlen : actor < w.barDepths.length := hpy.1 ▸ (h2 y hyl).2
    have hsub : ∀ z ∈ ys, z ∈ w.openBars := fun z hz => by
      rw [hl]; rw [hys] at hz; exact mem_of_mem_remove hz
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      rw [getD_set_int]
      split
      · omega
      · exact h1 a
    · intro b hb
      have := h2 b (hsub b hb)
      simpa only [List.length_set] using this
    · rw [hys]
      exact hnd.1
    · intro a k hk
      rw [getD_set_int]
      by_cases hae : actor = a
      · subst hae
        simp only [hlen, and_self, ↓reduceIte]
        constructor
        · intro hk'
          obtain ⟨b, hb, hb1, hb2⟩ := (h4 actor k hk).mp (by omega)
          have hby : b ≠ y := fun hh => by subst hh; omega
          refine ⟨b, ?_, hb1, hb2⟩
          rw [hys]
          rw [hl] at hb
          exact mem_remove hb hby
        · rintro ⟨b, hb, hb1, hb2⟩
          have hbl := hsub b hb
          have hk2 := (h4 actor k hk).mpr ⟨b, hbl, hb1, hb2⟩
          by_cases hkc : k ≤ max (w.barDepths.getD actor 0 - 1) 0
          · exact hkc
          · have hkd : k = w.barDepths.getD actor 0 := by omega
            rw [hys] at hb
            exact absurd (by simp [hb1, hb2, hkd, hpy.1, hpy.2]) (hnd.2 b hb)
      · simp only [hae, false_and, ↓reduceIte]
        constructor
        · intro hk'
          obtain ⟨b, hb, hb1, hb2⟩ := (h4 a k hk).mp hk'
          have hby : b ≠ y := fun hh => by subst hh; exact hae (hpy.1.symm.trans hb1)
          refine ⟨b, ?_, hb1, hb2⟩
          rw [hys]
          rw [hl] at hb
          exact mem_remove hb hby
        · rintro ⟨b, hb, hb1, hb2⟩
          exact (h4 a k hk).mpr ⟨b, hsub b hb, hb1, hb2⟩

/-- Ending an activation on a lifeline with an open bar removes the bar of the greatest depth: the most
recently opened bar of that lifeline that is still open. -/
theorem stepActivateEnd_closes (pl : Plan) (w : Walk) (actor : Nat) (hi : BarInv w)
    (hpos : 1 ≤ w.barDepths.getD actor 0) :
    ∃ y pre suf, w.openBars = pre ++ y :: suf ∧ y.actor = actor ∧ y.depth = w.barDepths.getD actor 0 ∧
      (stepActivateEnd pl w actor).openBars = pre ++ suf := by
  obtain ⟨h1, h2, h3, h4⟩ := hi
  obtain ⟨y0, hy0, hy0a, hy0d⟩ := (h4 actor (w.barDepths.getD actor 0) hpos).mp (Int.le_refl _)
  have hex : ∃ x ∈ w.openBars,
      (fun b : BarRun => b.actor == actor && b.depth == max (w.barDepths.getD actor 0 - 1) 0 + 1) x = true := by
    refine ⟨y0, hy0, ?_⟩
    show (y0.actor == actor && y0.depth == max (w.barDepths.getD actor 0 - 1) 0 + 1) = true
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hy0a, beq_iff_eq.mpr (by omega)⟩
  obtain ⟨y, ys, hr⟩ := extractFirst_exists _ w.openBars hex
  obtain ⟨hp, pre, suf, hl, hys⟩ := extractFirst_some _ w.openBars y ys hr
  have hpy : y.actor = actor ∧ y.depth = w.barDepths.getD actor 0 := by
    have : y.actor = actor ∧ y.depth = max (w.barDepths.getD actor 0 - 1) 0 + 1 := by simpa using hp
    omega
  refine ⟨y, pre, suf, hl, hpy.1, hpy.2, ?_⟩
  unfold stepActivateEnd
  dsimp only
  rw [hr]
  dsimp only
  exact hys

/-- Activations nest: a deactivation never ends a bar that encloses another open bar of the same
lifeline. A bar of smaller depth is still open after the deactivation, so the inner bar closes first
(`sequence-50`). The statement over the order of the opening and closing rows is false when two
activations open on one row, because their rows tie. -/
theorem sequence_activations_nest (pl : Plan) (w : Walk) (hi : BarInv w) (a b : BarRun) (ha : a ∈ w.openBars)
    (hb : b ∈ w.openBars) (hact : a.actor = b.actor) (hd : a.depth < b.depth) :
    a ∈ (stepActivateEnd pl w a.actor).openBars := by
  have hbd : b.depth ≤ w.barDepths.getD a.actor 0 := by
    have := (hi.2.2.2 a.actor b.depth (hi.2.1 b hb).1).mpr ⟨b, hb, hact.symm, rfl⟩
    exact this
  have hpos : 1 ≤ w.barDepths.getD a.actor 0 := Int.le_trans (hi.2.1 b hb).1 hbd
  obtain ⟨y, pre, suf, hl, hya, hyd, hres⟩ := stepActivateEnd_closes pl w a.actor hi hpos
  rw [hres]
  have hne : a ≠ y := fun h => by subst h; omega
  rw [hl] at ha
  exact mem_remove ha hne

/-- The deactivation closes the deepest open bar of its lifeline. -/
theorem activation_close_innermost (pl : Plan) (w : Walk) (actor : Nat) (hi : BarInv w)
    (hpos : 1 ≤ w.barDepths.getD actor 0) :
    ∃ y, y ∈ w.openBars ∧ y.actor = actor ∧ y ∉ (stepActivateEnd pl w actor).openBars ∧
      ∀ b ∈ w.openBars, b.actor = actor → b.depth ≤ y.depth := by
  obtain ⟨y, pre, suf, hl, hya, hyd, hres⟩ := stepActivateEnd_closes pl w actor hi hpos
  refine ⟨y, by rw [hl]; simp, hya, ?_, ?_⟩
  · rw [hres]
    intro hmem
    have hnd := nodup_remove (fun b : BarRun => (b.actor, b.depth)) pre suf y (hl ▸ hi.2.2.1)
    exact hnd.2 y hmem rfl
  · intro b hb hba
    have := (hi.2.2.2 actor b.depth (hi.2.1 b hb).1).mpr ⟨b, hb, hba, rfl⟩
    omega

theorem activation_bar_x (pl : Plan) (cs : List Int) (w : Walk) (actor : Nat) :
    ∃ bar, (stepActivateStart pl cs w actor).openBars = bar :: w.openBars ∧ bar.actor = actor ∧
      bar.depth = w.barDepths.getD actor 0 + 1 ∧
      bar.x = cs.getD actor 0 + (bar.depth - 1) * half pl.c.activationWidth := by
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  show cs.getD actor 0 + w.barDepths.getD actor 0 * half pl.c.activationWidth =
    cs.getD actor 0 + (w.barDepths.getD actor 0 + 1 - 1) * half pl.c.activationWidth
  rw [Int.add_sub_cancel]

/-- A deeper bar on a lifeline sits to the right of a shallower one when `half activationWidth` is
positive, which holds for the vector profile (`vector_activation_step_pos`). The cell profile has
`half activationWidth = 0`, so its nested bars share one column (`sequence-51`). -/
theorem sequence_activation_depth_offset (c h : Int) (hh : 0 < h) (a b : BarRun)
    (ha : a.x = c + (a.depth - 1) * h) (hb : b.x = c + (b.depth - 1) * h) (hd : a.depth < b.depth) :
    a.x < b.x := by
  have := Int.mul_lt_mul_of_pos_right (show a.depth - 1 < b.depth - 1 by omega) hh
  omega

/-! ### Activation stacks along the walk -/

theorem markDestroyed_bars (w : Walk) (bits : Nat) (destroyed y : Int) :
    (markDestroyed w bits destroyed y).openBars = w.openBars ∧
      (markDestroyed w bits destroyed y).barDepths = w.barDepths := by
  unfold markDestroyed; split <;> exact ⟨rfl, rfl⟩

theorem placeLabel_bars (w : Walk) (pos : Option Nat) (r : Rect) :
    (w.placeLabel pos r).openBars = w.openBars ∧ (w.placeLabel pos r).barDepths = w.barDepths := by
  unfold Walk.placeLabel; split <;> exact ⟨rfl, rfl⟩

theorem createdBox_bars (pl : Plan) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) :
    (createdBox pl cs w bits dst y).1.openBars = w.openBars ∧
      (createdBox pl cs w bits dst y).1.barDepths = w.barDepths := by
  unfold createdBox
  split
  · simp [addMember_openBars, addMember_barDepths]
  · exact ⟨rfl, rfl⟩

theorem closeWith_bars (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (closeWith pl w run width).openBars = w.openBars ∧
      (closeWith pl w run width).barDepths = w.barDepths := by
  unfold closeWith
  simp [addMember_openBars, addMember_barDepths]

theorem stepWalk_bars (pl : Plan) (cs : List Int) (w w' : Walk) (s : Step)
    (h : stepWalk pl cs w s = .ok w') (hs : ∀ a, s ≠ .activateStart a ∧ s ≠ .activateEnd a) :
    w'.openBars = w.openBars ∧ w'.barDepths = w.barDepths := by
  cases s with
  | message bits src dst route destroyed =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    unfold stepMessage
    simp only [Walk.advance, addMember_openBars, addMember_barDepths, (placeLabel_bars _ _ _).1,
      (placeLabel_bars _ _ _).2, (markDestroyed_bars _ _ _ _).1, (markDestroyed_bars _ _ _ _).2,
      (createdBox_bars _ _ _ _ _ _).1, (createdBox_bars _ _ _ _ _ _).2]
    exact ⟨trivial, trivial⟩
  | note placement a b box =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    unfold stepNote
    simp only [Walk.advance, addMember_openBars, addMember_barDepths, (placeLabel_bars _ _ _).1,
      (placeLabel_bars _ _ _).2]
    exact ⟨trivial, trivial⟩
  | fragmentStart kind box =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨rfl, rfl⟩
  | fragmentElse box sect =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    exact ⟨rfl, rfl⟩
  | fragmentEnd =>
    simp only [stepWalk] at h
    unfold stepFragmentEnd at h
    cases hf : w.fragments with
    | nil =>
      rw [hf] at h
      simp only [pure, Except.pure] at h
      cases h
      exact ⟨rfl, rfl⟩
    | cons run rest =>
      rw [hf] at h
      obtain ⟨width, _, rfl⟩ := closeFragment_eq pl _ run w' h
      exact closeWith_bars pl _ run width
  | activateStart a => exact absurd rfl (hs a).1
  | activateEnd a => exact absurd rfl (hs a).2

theorem barDepths_length_step (pl : Plan) (cs : List Int) (w w' : Walk) (s : Step)
    (h : stepWalk pl cs w s = .ok w') : w'.barDepths.length = w.barDepths.length := by
  cases s with
  | activateStart a =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    simp [stepActivateStart]
  | activateEnd a =>
    simp only [stepWalk, pure, Except.pure] at h
    cases h
    unfold stepActivateEnd
    dsimp only
    split <;> simp
  | message bits src dst route destroyed =>
    rw [(stepWalk_bars pl cs w w' _ h (fun a => ⟨by simp, by simp⟩)).2]
  | note placement a b box =>
    rw [(stepWalk_bars pl cs w w' _ h (fun a => ⟨by simp, by simp⟩)).2]
  | fragmentStart kind box =>
    rw [(stepWalk_bars pl cs w w' _ h (fun a => ⟨by simp, by simp⟩)).2]
  | fragmentElse box sect =>
    rw [(stepWalk_bars pl cs w w' _ h (fun a => ⟨by simp, by simp⟩)).2]
  | fragmentEnd =>
    rw [(stepWalk_bars pl cs w w' _ h (fun a => ⟨by simp, by simp⟩)).2]

/-- Every state that the events reach has the activation stacks of `BarInv`, when every activation names
a lifeline. -/
theorem steps_barInv (pl : Plan) (cs : List Int) :
    ∀ (steps : List Step) (w w' : Walk), BarInv w →
      (∀ a, Step.activateStart a ∈ steps → a < w.barDepths.length) →
      steps.foldlM (stepWalk pl cs) w = .ok w' → BarInv w' ∧ w'.barDepths.length = w.barDepths.length := by
  intro steps
  induction steps with
  | nil =>
    intro w w' hi _ h
    simp only [List.foldlM, pure, Except.pure] at h
    cases h
    exact ⟨hi, rfl⟩
  | cons s t ih =>
    intro w w' hi hact h
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w1 hw1
      have hlen := barDepths_length_step pl cs w w1 s hw1
      have hi1 : BarInv w1 := by
        cases s with
        | activateStart a =>
          simp only [stepWalk, pure, Except.pure] at hw1
          cases hw1
          exact stepActivateStart_barInv pl cs w a hi (hact a (List.mem_cons_self))
        | activateEnd a =>
          simp only [stepWalk, pure, Except.pure] at hw1
          cases hw1
          exact stepActivateEnd_barInv pl w a hi
        | message bits src dst route destroyed =>
          have hb := stepWalk_bars pl cs w w1 _ hw1 (fun a => ⟨by simp, by simp⟩)
          unfold BarInv at hi ⊢
          rw [hb.1, hb.2]
          exact hi
        | note placement a b box =>
          have hb := stepWalk_bars pl cs w w1 _ hw1 (fun a => ⟨by simp, by simp⟩)
          unfold BarInv at hi ⊢
          rw [hb.1, hb.2]
          exact hi
        | fragmentStart kind box =>
          have hb := stepWalk_bars pl cs w w1 _ hw1 (fun a => ⟨by simp, by simp⟩)
          unfold BarInv at hi ⊢
          rw [hb.1, hb.2]
          exact hi
        | fragmentElse box sect =>
          have hb := stepWalk_bars pl cs w w1 _ hw1 (fun a => ⟨by simp, by simp⟩)
          unfold BarInv at hi ⊢
          rw [hb.1, hb.2]
          exact hi
        | fragmentEnd =>
          have hb := stepWalk_bars pl cs w w1 _ hw1 (fun a => ⟨by simp, by simp⟩)
          unfold BarInv at hi ⊢
          rw [hb.1, hb.2]
          exact hi
      have h2 := ih w1 w' hi1 (fun a ha => by rw [hlen]; exact hact a (List.mem_cons_of_mem _ ha)) h
      exact ⟨h2.1, h2.2.trans hlen⟩

/-! ### The plan of a layout -/

theorem getD_map_nonneg {α : Type} (l : List α) (f : α → Int) (hf : ∀ a ∈ l, 0 ≤ f a) (k : Nat) :
    0 ≤ (l.map f).getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hk : l[k]? with
  | none => simp
  | some a =>
    have := hf a (List.mem_of_getElem? hk)
    simpa using this

theorem actorSize_nonneg (c : Consts) (hc : c.Pos) (shared : Bool) (b : ModelBox)
    (lines : List Measure.Line) :
    0 ≤ (actorSize c shared b lines).1 ∧ 0 ≤ (actorSize c shared b lines).2 := by
  unfold actorSize
  have h1 := hc.actorWidth
  have h2 := hc.boxTextMargin
  have h3 := Int.mul_nonneg (Int.natCast_nonneg lines.length) hc.lineHeight
  dsimp only
  constructor
  · split
    · exact Int.le_of_lt h1
    · exact Int.le_trans (Int.le_of_lt h1) (Int.le_max_left _ _)
  · exact Int.le_trans (by omega) (Int.le_max_right _ _)

/-- The plan that the layout builds has the signs that the theorems read. -/
theorem Plan.build_wf (m : Model) (pl : Plan) (h : Plan.build m = .ok pl) : pl.Wf := by
  unfold Plan.build at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · rename_i actorLines _
      split at h
      · cases h
      · rename_i labelLines _
        cases h
        have hp := load_pos hc
        refine ⟨hp, fun k => ?_, fun k => ?_⟩
        · refine getD_map_nonneg _ _ (fun s hs => ?_) k
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
          obtain ⟨b, lines⟩ := x
          exact (actorSize_nonneg c hp _ b lines).1
        · refine getD_map_nonneg _ _ (fun s hs => ?_) k
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
          obtain ⟨b, lines⟩ := x
          exact (actorSize_nonneg c hp _ b lines).2

/-! ### Message ends and actor headers -/

/-- A message starts on the bottom edge of the header box of its sender and ends on the bottom edge of
the header box of its receiver (`sequence-48`). -/
theorem sequence_message_ends_on_headers (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (y dx : Int) :
    (messageRun pl cs w bits src dst route y dx).points.head?.map (·.y) = some (headerBottom pl w src) ∧
      (messageRun pl cs w bits src dst route y dx).points.getLast?.map (·.y) =
        some (headerBottom pl w dst) := by
  by_cases h : src = dst
  · subst h
    rw [messageRun_points_self]
    simp
  · rw [messageRun_points_cross _ _ _ _ _ _ _ _ _ h]
    simp

theorem half_eq (v : Int) (_h : 0 ≤ v) : half v = v / 2 := by
  unfold half
  exact Int.fdiv_eq_ediv_of_nonneg v (by decide)

/-- The header boxes of two lifelines do not overlap: the right edge of the left box is not past the
left edge of the right box (the disjointness that `sequence-54` needs for the exclusive actors). -/
theorem actor_headers_disjoint (pl : Plan) (hwf : pl.Wf) (steps : List Step) (i j : Nat) (hij : i < j)
    (hj : j < pl.widths.length) :
    (columns pl steps).getD i 0 + (pl.widths.getD i 0 - half (pl.widths.getD i 0)) ≤
      (columns pl steps).getD j 0 - half (pl.widths.getD j 0) := by
  have hwi := hwf.widths i
  have hwj := hwf.widths j
  have hmg := hwf.pos.margin
  have hd := centre_diff pl.widths (columnGaps pl steps) i j (Nat.le_of_lt hij) hj
  have hgap : ∀ k, k < pl.widths.length - 1 →
      half (pl.widths.getD k 0 + pl.widths.getD (k + 1) 0) + pl.c.actorMargin ≤
        (columnGaps pl steps).getD k 0 := by
    intro k hk
    rw [← baseGaps_getD pl.c pl.widths k hk]
    exact (columnGaps_ge_base pl hwf.widths steps).2 k
  have hgi := hgap i (by omega)
  rw [half_eq _ (Int.add_nonneg hwi (hwf.widths (i + 1)))] at hgi
  rw [half_eq _ hwi, half_eq _ hwj]
  have hwi1 := hwf.widths (i + 1)
  unfold columns
  rcases Nat.lt_or_ge (i + 1) j with h | h
  · have hgj := hgap (j - 1) (by omega)
    have e : j - 1 + 1 = j := by omega
    rw [e, half_eq _ (Int.add_nonneg (hwf.widths (j - 1)) hwj)] at hgj
    have hw1 := hwf.widths (j - 1)
    have s1 := ssum_split (columnGaps pl steps) i (i + 1) j (by omega) (by omega)
    have s2 := ssum_split (columnGaps pl steps) (i + 1) (j - 1) j (by omega) (by omega)
    have s3 := ssum_single (columnGaps pl steps) i
    have s4 : ssum (columnGaps pl steps) (j - 1) j = (columnGaps pl steps).getD (j - 1) 0 := by
      have := ssum_single (columnGaps pl steps) (j - 1)
      rwa [e] at this
    have s5 := ssum_lower (columnGaps pl steps) 0 (i + 1) (j - 1)
      (fun k hk hk' => Int.le_trans (Int.le_of_lt hmg)
        (columnGaps_margin pl hwf.widths steps k (by omega)))
    have s6 : ((j - 1 - (i + 1) : Nat) : Int) * 0 = 0 := Int.mul_zero _
    omega
  · have e : j = i + 1 := by omega
    subst e
    have s3 := ssum_single (columnGaps pl steps) i
    omega
end Sequence
end Elegant
