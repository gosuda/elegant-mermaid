import Elegant.Layered.RegionBucketBounds
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.RegionFlatC8a
import Elegant.Layered.RegionSiblingAllRanks

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem bindOk {α β : Type} {input : Except LayoutError α}
    {next : α → Except LayoutError β} {out : β} (h : input.bind next = .ok out) :
    ∃ a, input = .ok a ∧ next a = .ok out := by
  cases input with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem foldOkInv {α β : Type} {f : α → β → Except LayoutError α}
    {I : α → Prop} {xs : List β} {a b : α}
    (hi : I a) (hs : ∀ a x b, I a → x ∈ xs → f a x = .ok b → I b)
    (h : xs.foldlM f a = .ok b) : I b := by
  induction xs generalizing a with
  | nil =>
    change Except.ok a = Except.ok b at h
    exact (Except.ok.inj h) ▸ hi
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hm, ht⟩ := bindOk h
    exact ih (hs a x mid hi (List.Mem.head _) hm)
      (fun a y b ha hy hb => hs a y b ha (List.Mem.tail _ hy) hb) ht

private theorem setAt_length {α : Type} (xs : List α) (i : Nat) (a : α) :
    (setAt xs i a).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem setAt_getD {α : Type} (xs : List α) (i j : Nat) (a d : α) :
    (setAt xs i a).getD j d = if j = i ∧ i < xs.length then a else xs.getD j d := by
  induction xs generalizing i j with
  | nil => simp [setAt]
  | cons x xs ih =>
    cases i with
    | zero => cases j <;> simp [setAt]
    | succ i =>
      cases j with
      | zero => simp [setAt]
      | succ j => simpa [setAt, List.getD_cons_succ] using ih i j

private theorem setAt_replicate_same {α : Type} (n i : Nat) (a : α) :
    setAt (List.replicate n a) i a = List.replicate n a := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => cases i <;> simp [List.replicate_succ, setAt, ih]

private theorem replicate_getD_same {α : Type} (n i : Nat) (a : α) :
    (List.replicate n a).getD i a = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

private def UniformOrigin (n : Nat) (inset : Int) (book : RegionWorkbook) : Prop :=
  book.origins = List.replicate n inset ∧ book.inset = inset ∧
  book.lefts.length = book.reserved.length ∧
  (∀ g, 0 ≤ book.lefts.getD g 0) ∧
  ∀ g, book.reserved.getD g false = true → book.lefts.getD g 0 = 0

private theorem foldReservations_uniform {n : Nat} {inset : Int} {res : List RegionReservation}
    {book out : RegionWorkbook} (hzero : ∀ r ∈ res, r.left = 0)
    (hi : UniformOrigin n inset book) (h : foldReservations book res = .ok out) :
    UniformOrigin n inset out := by
  unfold foldReservations at h
  refine foldOkInv hi ?_ h
  intro b r b' hb hr hstep
  change (if r.group ≥ b.widths.length ∨ r.left > r.right ∨ r.span.first < 0 ∨
      r.span.first > r.span.last then (Except.error .domain : Except LayoutError RegionWorkbook)
    else .ok _) = .ok b' at hstep
  split at hstep
  · cases hstep
  · rw [← Except.ok.inj hstep]
    obtain ⟨ho, hi, hlen, hl, hz⟩ := hb
    let left := min (b.lefts.getD r.group 0) r.left
    have hleft : left = 0 := by
      change min (b.lefts.getD r.group 0) r.left = 0
      rw [hzero r hr]
      exact Int.min_eq_right (hl r.group)
    refine ⟨ho, hi, ?_, ?_, ?_⟩
    · change (setAt b.lefts r.group left).length = (setAt b.reserved r.group true).length
      simpa only [setAt_length] using hlen
    · intro g
      change 0 ≤ (setAt b.lefts r.group left).getD g 0
      rw [setAt_getD, hleft]
      split
      · exact Int.le_refl 0
      · exact hl g
    · intro g hreserved
      change (setAt b.reserved r.group true).getD g false = true at hreserved
      change (setAt b.lefts r.group left).getD g 0 = 0
      rw [setAt_getD, ← hlen] at hreserved
      rw [setAt_getD, hleft]
      split
      · rfl
      · rename_i hg
        rw [ite_eq_right hg] at hreserved
        exact hz g hreserved

private theorem absorbFootprint_uniform {n g : Nat} {inset : Int} {book out : RegionWorkbook}
    (hi : UniformOrigin n inset book) (h : absorbFootprint g book = .ok out) :
    UniformOrigin n inset out := by
  unfold absorbFootprint at h
  split at h
  · exact (Except.ok.inj h) ▸ hi
  · rename_i hkeep
    have hreserved : book.reserved.getD g false = true := by
      cases hg : book.reserved.getD g false with
      | false => exact False.elim (hkeep (by simp only [hg, Bool.not_false]))
      | true => rfl
    rw [← Except.ok.inj h]
    obtain ⟨ho, hi, hlen, hl, hz⟩ := hi
    refine ⟨?_, hi, hlen, hl, hz⟩
    change setAt book.origins g (book.inset - book.lefts.getD g 0) = _
    rw [hz g hreserved, ho, hi, Int.sub_zero, setAt_replicate_same]

private theorem absorbChildren_uniform {n g : Nat} {inset : Int} {book out : RegionWorkbook}
    (hi : UniformOrigin n inset book) (h : absorbChildren g book = .ok out) :
    UniformOrigin n inset out := by
  unfold absorbChildren at h
  obtain ⟨_, _, h⟩ := bindOk h
  rw [← Except.ok.inj h]
  exact hi

private theorem layOutRegions_uniform {n g : Nat} {inset : Int} {sets : List LocalRegionSet}
    {book out : RegionWorkbook} (hi : UniformOrigin n inset book)
    (h : layOutRegions sets g book = .ok out) : UniformOrigin n inset out := by
  unfold layOutRegions at h
  dsimp only at h
  split at h
  · exact (Except.ok.inj h) ▸ hi
  · obtain ⟨_, _, h⟩ := bindOk h
    rw [← Except.ok.inj h]
    exact hi

private theorem resolveNestedExtents_uniform {n : Nat} {inset : Int}
    {sets : List LocalRegionSet} {book out : RegionWorkbook}
    (hi : UniformOrigin n inset book) (h : resolveNestedExtents sets book = .ok out) :
    UniformOrigin n inset out := by
  unfold resolveNestedExtents at h
  refine foldOkInv hi ?_ h
  intro b g b' hb _ hstep
  obtain ⟨foot, hf, hstep⟩ := bindOk hstep
  obtain ⟨children, hc, hstep⟩ := bindOk hstep
  exact layOutRegions_uniform (absorbChildren_uniform (absorbFootprint_uniform hb hf) hc) hstep

private theorem shareCommonSpans_uniform {n : Nat} {inset : Int} (sets : List LocalRegionSet)
    {book : RegionWorkbook} (hi : UniformOrigin n inset book) :
    UniformOrigin n inset (shareCommonSpans sets book) := by
  unfold shareCommonSpans
  refine OrderImpl.foldl_inv (UniformOrigin n inset) _ _ _ hi ?_
  intro b hb g _
  dsimp only
  split <;> exact hb

private theorem frameMinimum_fst {m : FrameMinima} {out : Int × Int}
    (h : frameMinimum m = .ok out) : out.1 = m.border + m.padding := by
  unfold frameMinimum at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact (congrArg Prod.fst (Except.ok.inj h)).symm

theorem solveRegions_zero_left_origins {parents : List Int} {sets : List LocalRegionSet}
    {res : List RegionReservation} {minima : FrameMinima} {out : RegionConstraints}
    (hzero : ∀ r ∈ res, r.left = 0)
    (h : solveRegions parents sets res minima = .ok out) :
    out.origins = List.replicate parents.length (minima.border + minima.padding) := by
  unfold solveRegions at h
  obtain ⟨⟨inset, minimum⟩, hm, h⟩ := bindOk h
  obtain ⟨⟨children, roots⟩, _, h⟩ := bindOk h
  obtain ⟨order, _, h⟩ := bindOk h
  obtain ⟨⟨byParent, bandCount⟩, _, h⟩ := bindOk h
  obtain ⟨book, hb, h⟩ := bindOk h
  obtain ⟨nested, hn, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  have hi : UniformOrigin parents.length inset
      (newRegionWorkbook parents.length children order byParent bandCount inset minimum) := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · simp only [newRegionWorkbook, List.length_replicate]
    · intro g
      change 0 ≤ (List.replicate parents.length (2147483647 : Int)).getD g 0
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> decide
    · intro g hreserved
      change (List.replicate parents.length false).getD g false = true at hreserved
      rw [replicate_getD_same] at hreserved
      cases hreserved
  have hout := shareCommonSpans_uniform sets
    (resolveNestedExtents_uniform (foldReservations_uniform hzero hi hb) hn)
  rw [← Except.ok.inj h, ← frameMinimum_fst hm]
  exact hout.1

theorem constrainR_origins {rm : ComponentRegions} {P : Params} {p : Proper}
    {minimum : RegionConstraints} (h : constrainR rm P p = .ok minimum) :
    minimum.origins = List.replicate rm.parents.length (regionInsetOf P) := by
  unfold constrainR at h
  obtain ⟨rows, hr, h⟩ := bindOk h
  unfold rowReservationsR at hr
  obtain ⟨entries, _, hr⟩ := bindOk hr
  have hzero : ∀ r ∈ rows, r.left = 0 := by
    rw [← Except.ok.inj hr]
    intro r hmem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hmem
    rfl
  have ho := solveRegions_zero_left_origins (h := h) (by
    intro r hr
    rcases List.mem_append.mp hr with hc | hw
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc
      rfl
    · exact hzero r hw)
  simpa only [regionInsetOf, Int.add_comm] using ho

theorem activeRegion_parent_count {P : Params} {s : RegionSpec} {inp : Input} {cg : Graph}
    {rm : ComponentRegions} (h : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    rm.parents.length = rm.clusters.length := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bindOk h
    split at h
    · cases h
    · rw [← Option.some.inj (Except.ok.inj h)]
      exact List.length_map _

private def widthStep (pl : RegionPlacement) (P : Params) (w : List Int) (g : Nat) :
    List Int :=
  let base := (pl.children.getD g []).foldl (fun z c => z + w.getD c 0)
    (pl.buckets.widths.getD g 0) + laneExtentOf pl.buckets P.slot g
  let inset := regionInsetOf P
  let width := if g != pl.rm.clusters.length then
    max (max (base + 2 * inset) (pl.minimum.widths.getD g 0))
      ((pl.rm.clusters.map (·.titleW)).getD g 0 + 2 * inset)
    else base
  setAt w g (width + pl.buckets.loopWidth.getD g 0)

private theorem childWidthSum (children : List Nat) (w : List Int) (own : Int) :
    children.foldl (fun z c => z + w.getD c 0) own =
      own + (children.map fun c => w.getD c 0).sum := by
  induction children generalizing own with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, Int.add_assoc]

private theorem widthFold_lookup {pl : RegionPlacement} {P : Params} {order : List Nat}
    {w : List Int} {g : Nat} (h : g ∉ order) :
    (order.foldl (widthStep pl P) w).getD g 0 = w.getD g 0 := by
  induction order generalizing w with
  | nil => rfl
  | cons d ds ih =>
    rw [List.foldl_cons, ih (fun hd => h (List.Mem.tail _ hd))]
    unfold widthStep
    dsimp only
    rw [setAt_getD, ite_eq_right]
    intro he
    apply h
    rw [he.1]
    exact List.Mem.head ds

theorem reserveWidths_nonnegative {pl : RegionPlacement} {P : Params}
    (hinset : 0 ≤ regionInsetOf P)
    (hown : ∀ g, 0 ≤ pl.buckets.widths.getD g 0)
    (hlane : ∀ g, 0 ≤ laneExtentOf pl.buckets P.slot g)
    (hloop : ∀ g, 0 ≤ pl.buckets.loopWidth.getD g 0) :
    ∀ g, 0 ≤ (reserveWidths pl P).getD g 0 := by
  change ∀ g, 0 ≤ (pl.order.reverse.foldl (widthStep pl P)
    (List.replicate (pl.rm.clusters.length + 1) 0)).getD g 0
  refine OrderImpl.foldl_inv (fun w : List Int => ∀ g, 0 ≤ w.getD g 0) _ _ _ ?_ ?_
  · intro g
    simpa only [replicate_getD_same] using (Int.le_refl 0)
  · intro w hw k _ g
    have hsum : 0 ≤ (pl.children.getD k []).foldl (fun z c => z + w.getD c 0)
        (pl.buckets.widths.getD k 0) :=
      OrderImpl.foldl_inv (fun z : Int => 0 ≤ z) _ _ _ (hown k)
        (fun z hz c _ => Int.add_nonneg hz (hw c))
    have hbase := Int.add_nonneg hsum (hlane k)
    unfold widthStep
    dsimp only
    rw [setAt_getD]
    split
    · split
      · have hpad := Int.add_nonneg hbase (Int.mul_nonneg (by decide : 0 ≤ (2 : Int)) hinset)
        exact Int.add_nonneg
          (Int.le_trans hpad (Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)))
          (hloop k)
      · exact Int.add_nonneg hbase (hloop k)
    · exact hw g

theorem reserveWidths_room_from_last_writes {pl : RegionPlacement} {P : Params}
    {g : Nat} {pre post : List Nat}
    (horder : pl.order.reverse = pre ++ g :: post)
    (hg : g < pl.rm.clusters.length)
    (hfinal : g ∉ post)
    (hchildren : ∀ c ∈ pl.children.getD g [], c ∉ g :: post) :
    let w := reserveWidths pl P
    2 * regionInsetOf P + pl.buckets.widths.getD g 0 +
        ((pl.children.getD g []).map fun c => w.getD c 0).sum +
        laneExtentOf pl.buckets P.slot g ≤ w.getD g 0 - pl.buckets.loopWidth.getD g 0 := by
  let initial : List Int := List.replicate (pl.rm.clusters.length + 1) 0
  let before := pre.foldl (widthStep pl P) initial
  let w := reserveWidths pl P
  have hw : w = (g :: post).foldl (widthStep pl P) before := by
    change pl.order.reverse.foldl (widthStep pl P) initial = _
    rw [horder, List.foldl_append]
  have hb : before.length = pl.rm.clusters.length + 1 := by
    refine OrderImpl.foldl_inv (fun ws : List Int => ws.length = pl.rm.clusters.length + 1)
      _ _ _ (by simp [initial]) ?_
    intro ws hs i _
    unfold widthStep
    dsimp only
    rwa [setAt_length]
  have hchildLookups : ∀ c ∈ pl.children.getD g [], w.getD c 0 = before.getD c 0 := by
    intro c hc
    rw [hw]
    exact widthFold_lookup (hchildren c hc)
  have hmap : ((pl.children.getD g []).map fun c => w.getD c 0) =
      ((pl.children.getD g []).map fun c => before.getD c 0) :=
    List.map_congr_left hchildLookups
  have hframe : w.getD g 0 = (widthStep pl P before g).getD g 0 := by
    rw [hw, List.foldl_cons]
    exact widthFold_lookup hfinal
  let base := pl.buckets.widths.getD g 0 +
    ((pl.children.getD g []).map fun c => before.getD c 0).sum +
    laneExtentOf pl.buckets P.slot g
  have hraw : base + 2 * regionInsetOf P + pl.buckets.loopWidth.getD g 0 ≤ w.getD g 0 := by
    rw [hframe]
    unfold widthStep
    dsimp only
    rw [setAt_getD, ite_eq_left (show g = g ∧ g < before.length from ⟨rfl, by omega⟩),
      ite_eq_left (bne_iff_ne.mpr (Nat.ne_of_lt hg)), childWidthSum]
    change base + 2 * regionInsetOf P + _ ≤
      max (max (base + 2 * regionInsetOf P) _) _ + _
    exact Int.add_le_add_right (Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)) _
  change 2 * regionInsetOf P + pl.buckets.widths.getD g 0 +
      ((pl.children.getD g []).map fun c => w.getD c 0).sum +
      laneExtentOf pl.buckets P.slot g ≤ w.getD g 0 - pl.buckets.loopWidth.getD g 0
  rw [hmap]
  dsimp only [base] at hraw
  omega

theorem reserveWidths_title_from_last_write {pl : RegionPlacement} {P : Params}
    {g : Nat} {c : RegionCluster} {pre post : List Nat}
    (hc : pl.rm.clusters[g]? = some c)
    (horder : pl.order.reverse = pre ++ g :: post) (hfinal : g ∉ post) :
    c.titleW + 2 * regionInsetOf P ≤
      (reserveWidths pl P).getD g 0 - pl.buckets.loopWidth.getD g 0 := by
  let initial : List Int := List.replicate (pl.rm.clusters.length + 1) 0
  let before := pre.foldl (widthStep pl P) initial
  have hbound := (List.getElem?_eq_some_iff.mp hc).1
  have hlen : before.length = pl.rm.clusters.length + 1 := by
    refine OrderImpl.foldl_inv (fun ws : List Int => ws.length = pl.rm.clusters.length + 1)
      _ _ _ (by simp [initial]) ?_
    intro ws hs i _
    unfold widthStep
    dsimp only
    rwa [setAt_length]
  have hwrite : (reserveWidths pl P).getD g 0 = (widthStep pl P before g).getD g 0 := by
    change (pl.order.reverse.foldl (widthStep pl P) initial).getD g 0 = _
    rw [horder, List.foldl_append, List.foldl_cons]
    exact widthFold_lookup hfinal
  have htitle : (pl.rm.clusters.map (·.titleW)).getD g 0 = c.titleW := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hc, Option.map_some,
      Option.getD_some]
  rw [hwrite]
  unfold widthStep
  dsimp only
  rw [setAt_getD, ite_eq_left (show g = g ∧ g < before.length from ⟨rfl, by omega⟩),
    ite_eq_left (bne_iff_ne.mpr (Nat.ne_of_lt hbound)), htitle]
  have hle := Int.le_max_right
    (max ((pl.children.getD g []).foldl (fun z k => z + before.getD k 0)
      (pl.buckets.widths.getD g 0) + laneExtentOf pl.buckets P.slot g + 2 * regionInsetOf P)
      (pl.minimum.widths.getD g 0))
    (c.titleW + 2 * regionInsetOf P)
  omega

private def ValidSetMembers (parents : List Int) (s : LocalRegionSet) : Prop :=
  s.regions.Nodup ∧ ∀ r ∈ s.regions, r < parents.length ∧ parents.getD r 0 = (s.parent : Int)

private def markSetOwner (parents : List Int) (s : LocalRegionSet) (index : Nat)
    (owner : List Int) (r : Nat) : Except LayoutError (List Int) :=
  if parents.length ≤ r ∨ parents.getD r 0 != s.parent ∨ 0 ≤ owner.getD r (-1)
  then .error .domain
  else .ok (setAt owner r (index : Int))

private theorem markSetOwners_success {parents : List Int} {s : LocalRegionSet}
    {index : Nat} {regions : List Nat} {owner out : List Int}
    (hlen : owner.length = parents.length)
    (h : regions.foldlM (markSetOwner parents s index) owner = .ok out) :
    out.length = parents.length ∧ regions.Nodup ∧
      ∀ r ∈ regions, r < parents.length ∧ parents.getD r 0 = (s.parent : Int) ∧
        owner.getD r (-1) < 0 := by
  induction regions generalizing owner with
  | nil =>
    change Except.ok owner = Except.ok out at h
    rw [← Except.ok.inj h]
    exact ⟨hlen, List.nodup_nil, fun r hr => (List.not_mem_nil hr).elim⟩
  | cons r rs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hm, ht⟩ := bindOk h
    unfold markSetOwner at hm
    split at hm
    · cases hm
    · rename_i hguard
      have hrBound : r < parents.length :=
        Nat.lt_of_not_ge fun hh => hguard (Or.inl hh)
      have hrParent : parents.getD r 0 = (s.parent : Int) := by
        apply Classical.byContradiction
        intro hh
        exact hguard (Or.inr (Or.inl (bne_iff_ne.mpr hh)))
      have hrSign : owner.getD r (-1) < 0 :=
        Int.lt_of_not_ge fun hh => hguard (Or.inr (Or.inr hh))
      have hm' : mid = setAt owner r (index : Int) := (Except.ok.inj hm).symm
      obtain ⟨hout, hd, hmembers⟩ :=
        ih (by rw [hm', setAt_length, hlen]) ht
      have hnot : r ∉ rs := by
        intro hr
        have hh := (hmembers r hr).2.2
        rw [hm', setAt_getD, ite_eq_left ⟨rfl, by rwa [hlen]⟩] at hh
        exact (Int.not_lt.mpr (Int.natCast_nonneg _)) hh
      refine ⟨hout, List.nodup_cons.mpr ⟨hnot, hd⟩, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hrBound, hrParent, hrSign⟩
      · obtain ⟨hcBound, hcParent, hcSign⟩ := hmembers c hc
        have hne : c ≠ r := fun he => hnot (he ▸ hc)
        rw [hm', setAt_getD, ite_eq_right (fun hh => hne hh.1)] at hcSign
        exact ⟨hcBound, hcParent, hcSign⟩

private def indexSetStep (parents : List Int) (acc : List Int × List Int × Nat)
    (q : LocalRegionSet × Nat) : Except LayoutError (List Int × List Int × Nat) := do
  let s := q.1
  if parents.length ≤ s.parent ∨ s.regions.isEmpty ∨ 0 ≤ acc.1.getD s.parent (-1) then
    throw .domain
  else
    let byParent := setAt acc.1 s.parent (q.2 : Int)
    let owner ← s.regions.foldlM (markSetOwner parents s q.2) acc.2.1
    pure (byParent, owner, acc.2.2 + s.regions.length)

private theorem indexSetSteps_success {parents : List Int} {jobs : List (LocalRegionSet × Nat)}
    {initial out : List Int × List Int × Nat} (hsize : initial.2.1.length = parents.length)
    (h : jobs.foldlM (indexSetStep parents) initial = .ok out) :
    ∀ q ∈ jobs, ValidSetMembers parents q.1 := by
  induction jobs generalizing initial with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hm, ht⟩ := bindOk h
    unfold indexSetStep at hm
    dsimp only at hm
    split at hm
    · cases hm
    · obtain ⟨own, ho, hm⟩ := bindOk hm
      have hm' := (Except.ok.inj hm).symm
      obtain ⟨hlen, hnodup, hmembers⟩ := markSetOwners_success hsize ho
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hnodup, fun r hr => ⟨(hmembers r hr).1, (hmembers r hr).2.1⟩⟩
      · exact ih (by rw [hm']; exact hlen) ht x hx

private theorem solveRegions_set_members {parents : List Int} {sets : List LocalRegionSet}
    {res : List RegionReservation} {minima : FrameMinima} {out : RegionConstraints}
    (h : solveRegions parents sets res minima = .ok out) :
    ∀ q ∈ sets.zipIdx, ValidSetMembers parents q.1 := by
  unfold solveRegions at h
  obtain ⟨⟨_, _⟩, _, h⟩ := bindOk h
  obtain ⟨⟨_, _⟩, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, hindex, _⟩ := bindOk h
  unfold indexRegionSets at hindex
  obtain ⟨_, hfold, _⟩ := bindOk hindex
  exact indexSetSteps_success (by simp) hfold

private theorem constrainR_set_members {rm : ComponentRegions} {P : Params} {p : Proper}
    {minimum : RegionConstraints} (h : constrainR rm P p = .ok minimum) :
    ∀ q ∈ rm.sets.zipIdx, ValidSetMembers rm.parents q.1 := by
  unfold constrainR at h
  obtain ⟨_, _, h⟩ := bindOk h
  exact solveRegions_set_members h

private def ChildRowsShape (rm : ComponentRegions) (rows : List (List Nat)) : Prop :=
  rows.length = rm.clusters.length + 1 ∧
    ∀ g, (rows.getD g []).Nodup ∧
      ∀ c ∈ rows.getD g [], c < rm.clusters.length ∧ parentGroup rm c = g

private def insertChild (rm : ComponentRegions) (rows : List (List Nat)) (c : Nat) :
    List (List Nat) :=
  let g := parentGroup rm c
  setAt rows g (rows.getD g [] ++ [c])

private theorem insertChildren_shape {rm : ComponentRegions} {rows : List (List Nat)}
    {keys : List Nat} (hs : ChildRowsShape rm rows)
    (hkeys : keys.Nodup) (hbound : ∀ c ∈ keys, c < rm.clusters.length)
    (hnew : ∀ c ∈ keys, ∀ g, c ∉ rows.getD g []) :
    ChildRowsShape rm (keys.foldl (insertChild rm) rows) := by
  induction keys generalizing rows with
  | nil => exact hs
  | cons c cs ih =>
    obtain ⟨hcCS, hcs⟩ := List.nodup_cons.mp hkeys
    have hcb := hbound c (List.Mem.head cs)
    have hcn := hnew c (List.Mem.head cs)
    rw [List.foldl_cons]
    refine ih ⟨by simpa only [insertChild, setAt_length] using hs.1, ?_⟩ hcs
      (fun x hx => hbound x (List.Mem.tail c hx)) ?_
    · intro g
      unfold insertChild
      dsimp only
      rw [setAt_getD]
      split
      · rename_i hrow
        rw [hrow.1]
        refine ⟨List.nodup_append.mpr ⟨(hs.2 _).1, by simp, ?_⟩, ?_⟩
        · intro x hx y hy hxy
          have hyc : y = c := List.mem_singleton.mp hy
          exact hcn _ ((hxy.trans hyc) ▸ hx)
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact (hs.2 _).2 x hx
          · rw [List.mem_singleton.mp hx]
            exact ⟨hcb, rfl⟩
      · exact hs.2 g
    · intro x hx g hxrow
      unfold insertChild at hxrow
      dsimp only at hxrow
      rw [setAt_getD] at hxrow
      split at hxrow
      · rcases List.mem_append.mp hxrow with hm | hm
        · exact hnew x (List.Mem.tail c hx) _ hm
        · exact hcCS ((List.mem_singleton.mp hm) ▸ hx)
      · exact hnew x (List.Mem.tail c hx) g hxrow

private theorem regionOwner_marks {root index : Nat} {regions : List Nat} {owner : List Nat}
    (hsize : owner.length = root) (hbound : ∀ r ∈ regions, r < root) :
    ∀ r ∈ regions, (regions.foldl (fun ow k => setAt ow k index) owner).getD r root = index := by
  induction regions generalizing owner with
  | nil => simp
  | cons k ks ih =>
    intro r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with hkr | hr
    · subst r
      refine OrderImpl.foldl_inv (fun ow : List Nat => ow.getD k root = index) _ _ _ ?_ ?_
      · rw [setAt_getD, ite_eq_left ⟨rfl, by rw [hsize]; exact hbound k (List.Mem.head ks)⟩]
      · intro ow hw x _
        rw [setAt_getD]
        split
        · rfl
        · exact hw
    · exact ih (by rwa [setAt_length]) (fun x hx => hbound x (List.Mem.tail k hx)) r hr

private theorem regionChildren_rows_shape {rm : ComponentRegions} {P : Params} {p : Proper}
    {minimum : RegionConstraints} {children : List (List Nat)}
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) (h : regionChildren rm = .ok children) :
    ChildRowsShape rm children := by
  let n := rm.clusters.length
  let start : List (List Nat) := List.replicate (n + 1) []
  have hstart : ChildRowsShape rm start := by
    refine ⟨by simp [start, n], ?_⟩
    intro g
    change (start.getD g []).Nodup ∧ ∀ c ∈ start.getD g [], _
    rw [show start.getD g [] = [] from replicate_getD_same _ _ _]
    simp
  have hbase : ChildRowsShape rm ((List.range n).foldl (insertChild rm) start) :=
    insertChildren_shape hstart List.nodup_range (fun _ hc => List.mem_range.mp hc)
      (fun _ _ g => by
        rw [show start.getD g [] = [] from replicate_getD_same _ _ _]
        exact List.not_mem_nil)
  unfold regionChildren at h
  refine foldOkInv hbase ?_ h
  intro rows q out hs hq hstep
  dsimp only at hstep
  split at hstep
  · cases hstep
  · obtain ⟨hnodup, hmembers⟩ := constrainR_set_members hmin q hq
    have hparent : ∀ r ∈ q.1.regions, r < n ∧ parentGroup rm r = q.1.parent := by
      intro r hr
      obtain ⟨hb, hp⟩ := hmembers r hr
      refine ⟨by rwa [hparents] at hb, ?_⟩
      unfold parentGroup
      have hsame : rm.parents.getD r (-1) = rm.parents.getD r 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
      rw [hsame, hp, ite_eq_left (Int.natCast_nonneg _), Int.toNat_natCast]
    let owner : List Nat := q.1.regions.foldl (fun ow r => setAt ow r q.2) (List.replicate n n)
    let owned (g : Nat) : Bool := owner.getD g n == q.2
    let kept := (rows.getD q.1.parent []).filter fun g => !owned g
    have hmarked : ∀ r ∈ q.1.regions, owned r = true := by
      intro r hr
      unfold owned owner
      rw [regionOwner_marks List.length_replicate (fun r hr => (hparent r hr).1) r hr]
      exact beq_self_eq_true _
    rename_i first _
    have hfinish : out = setAt rows q.1.parent (kept.take first ++ q.1.regions ++ kept.drop first) :=
      (Except.ok.inj hstep).symm
    rw [hfinish]
    refine ⟨(setAt_length _ _ _).trans hs.1, ?_⟩
    intro g
    rw [setAt_getD]
    split
    · rename_i hg
      have hkept : kept.Nodup := List.Pairwise.filter _ (hs.2 q.1.parent).1
      have hsep : ∀ a ∈ kept, ∀ b ∈ q.1.regions, a ≠ b := by
        intro a ha b hb hab
        have hkeep := (List.mem_filter.mp ha).2
        change (!owned a) = true at hkeep
        rw [hab, hmarked b hb] at hkeep
        cases hkeep
      have hsepParts := List.nodup_append.mp
        (show (kept.take first ++ kept.drop first).Nodup by rwa [List.take_append_drop])
      refine ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
        ⟨hsepParts.1, hnodup, fun a ha b hb => hsep a (List.mem_of_mem_take ha) b hb⟩,
        hsepParts.2.1, ?_⟩, ?_⟩
      · intro a ha b hb
        rcases List.mem_append.mp ha with ht | hr
        · exact hsepParts.2.2 a ht b hb
        · exact Ne.symm (hsep b (List.mem_of_mem_drop hb) a hr)
      · intro c hc
        have hbaseMem : ∀ x ∈ kept, x < n ∧ parentGroup rm x = g := by
          intro x hx
          rw [hg.1]
          exact (hs.2 q.1.parent).2 x (List.mem_filter.mp hx).1
        rcases List.mem_append.mp hc with hc | hc
        · rcases List.mem_append.mp hc with hc | hc
          · exact hbaseMem c (List.mem_of_mem_take hc)
          · rw [hg.1]
            exact hparent c hc
        · exact hbaseMem c (List.mem_of_mem_drop hc)
    · exact hs.2 g

private structure VisitFrontier (rm : ComponentRegions) (rows : List (List Nat))
    (visited pending : List Nat) : Prop where
  unique : (visited ++ pending).Nodup
  introduced : ∀ c ∈ visited ++ pending, c = rm.clusters.length ∨
    (c < rm.clusters.length ∧ ∃ g ∈ visited, c ∈ rows.getD g [])
  ordered : visited.Pairwise (fun a b => a ∉ rows.getD b [])
  noSelf : ∀ g ∈ visited, g ∉ rows.getD g []

private theorem childPreorder_frontier {rm : ComponentRegions} {rows : List (List Nat)}
    (hrows : ChildRowsShape rm rows) (fuel : Nat) {visited pending : List Nat}
    (h : VisitFrontier rm rows visited pending) :
    VisitFrontier rm rows (childPreorderGo rows fuel pending visited) [] := by
  induction fuel generalizing visited pending with
  | zero =>
    change VisitFrontier rm rows visited []
    exact ⟨by simpa using (List.nodup_append.mp h.unique).1,
      fun c hc => h.introduced c (List.mem_append_left _ (by simpa using hc)),
      h.ordered, h.noSelf⟩
  | succ fuel ih =>
    cases hv : pending.getLast? with
    | none =>
      have he := List.getLast?_eq_none_iff.mp hv
      subst pending
      change VisitFrontier rm rows visited []
      exact h
    | some g =>
      obtain ⟨pending, rfl⟩ := List.getLast?_eq_some_iff.mp hv
      rw [childPreorderGo, hv, List.dropLast_concat]
      have hgPending : g ∈ pending ++ [g] := List.mem_append_right _ (by simp)
      have hgNew : g ∉ visited := by
        intro hg
        exact (List.nodup_append.mp h.unique).2.2 g hg g hgPending rfl
      have hFresh : ∀ c ∈ rows.getD g [], c ∉ visited ++ (pending ++ [g]) := by
        intro c hc hold
        obtain ⟨hb, hp⟩ := (hrows.2 g).2 c hc
        rcases h.introduced c hold with hroot | ⟨_, par, hpar, hchild⟩
        · omega
        · have he := ((hrows.2 par).2 c hchild).2
          exact hgNew ((he.symm.trans hp) ▸ hpar)
      have hprev : ∀ c ∈ (visited ++ [g]) ++ pending, c ∈ visited ++ (pending ++ [g]) := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · rcases List.mem_append.mp hc with hc | hc
          · exact List.mem_append_left _ hc
          · exact List.mem_append_right _ (List.mem_append_right _ hc)
        · exact List.mem_append_right _ (List.mem_append_left _ hc)
      have hpre : ((visited ++ [g]) ++ pending).Nodup := by
        apply List.Perm.nodup _ h.unique
        simpa only [List.append_assoc] using
          (List.Perm.append_left visited (List.perm_append_comm (l₁ := pending) (l₂ := [g])))
      have hrow : (rows.getD g []).reverse.Nodup := by
        apply List.pairwise_reverse.mpr
        exact List.Pairwise.imp (fun hn => Ne.symm hn) (hrows.2 g).1
      refine ih ⟨?_, ?_, ?_, ?_⟩
      · simp only [← List.append_assoc]
        refine List.nodup_append.mpr ⟨hpre, hrow, ?_⟩
        intro a ha b hb hab
        exact hFresh b (List.mem_reverse.mp hb) (hab ▸ hprev a ha)
      · intro c hc
        simp only [← List.append_assoc] at hc
        rcases List.mem_append.mp hc with hc | hc
        · rcases h.introduced c (hprev c hc) with hh | ⟨hb, par, hpar, hcp⟩
          · exact Or.inl hh
          · exact Or.inr ⟨hb, par, List.mem_append_left _ hpar, hcp⟩
        · have hmem := List.mem_reverse.mp hc
          exact Or.inr ⟨((hrows.2 g).2 c hmem).1, g, List.mem_append_right _ (by simp), hmem⟩
      · refine List.pairwise_append.mpr ⟨h.ordered, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton.mp hb]
        exact fun hmem => hFresh a hmem (List.mem_append_left _ ha)
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact h.noSelf i hi
        · rw [List.mem_singleton.mp hi]
          exact fun hself => hFresh g hself (List.mem_append_right _ hgPending)

theorem RegionCrossAllocationStages.reservation_order {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) :
    (∀ g, (stages.placement.children.getD g []).Nodup) ∧
    ∀ g ≤ rm.clusters.length, ∃ pre post, stages.placement.order.reverse = pre ++ g :: post ∧
      g ∉ post ∧ ∀ c ∈ stages.placement.children.getD g [], c ∉ g :: post := by
  let children := stages.children
  let n := rm.clusters.length
  let order := childPreorderGo children (children.length + 1) [n] []
  have hrows : ChildRowsShape rm children := regionChildren_rows_shape hparents hmin stages.hChildren
  have hinit : VisitFrontier rm children [] [n] :=
    ⟨by simp, fun c hc => Or.inl (by simpa using hc), by simp, fun c hc => (List.not_mem_nil hc).elim⟩
  have hwalk : VisitFrontier rm children order [] := childPreorder_frontier hrows _ hinit
  have hlen : order.length = n + 1 := stages.hTraversal.trans hrows.1
  have hnodup : order.Nodup := by simpa using hwalk.unique
  have hbounds : ∀ c ∈ order, c < n + 1 := by
    intro c hc
    have hi := hwalk.introduced c (List.mem_append_left _ hc)
    rcases hi with hh | ⟨hb, _⟩
    · change c = n at hh
      omega
    · change c < n at hb
      omega
  have hrev : order.reverse.Nodup := by
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.imp (fun hn => Ne.symm hn) hnodup
  have hparentsLater : order.reverse.Pairwise (fun a b => b ∉ children.getD a []) :=
    List.pairwise_reverse.mpr hwalk.ordered
  rw [stages.hPlacement]
  refine ⟨fun g => (hrows.2 g).1, ?_⟩
  intro g hg
  change ∃ (pre post : List Nat), order.reverse = pre ++ g :: post ∧
    g ∉ post ∧ ∀ c ∈ children.getD g [], c ∉ g :: post
  have hmem : g ∈ order := by
    apply Classical.byContradiction
    intro hnot
    have hsubset : g :: order ⊆ List.range (n + 1) := by
      intro c hc
      apply List.mem_range.mpr
      rcases List.mem_cons.mp hc with he | hc
      · rw [he]
        exact Nat.lt_succ_of_le hg
      · exact hbounds c hc
    have hcard := (List.nodup_cons.mpr ⟨hnot, hnodup⟩).length_le_of_subset hsubset
    simp only [List.length_cons, List.length_range, hlen] at hcard
    omega
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp (List.mem_reverse.mpr hmem)
  refine ⟨pre, post, hsplit, ?_, ?_⟩
  · rw [hsplit] at hrev
    exact (List.nodup_cons.mp (List.nodup_append.mp hrev).2.1).1
  · rw [hsplit] at hparentsLater
    have htail := (List.pairwise_cons.mp (List.pairwise_append.mp hparentsLater).2.1).1
    intro c hc hin
    rcases List.mem_cons.mp hin with hcg | ht
    · exact hwalk.noSelf g hmem (hcg ▸ hc)
    · exact htail c ht hc

theorem RegionCrossAllocationStages.allocation_preorder {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) :
    ∀ g < rm.clusters.length, ∃ pre post : List Nat,
      stages.placement.order = pre ++ g :: post ∧
      g ∉ post ∧ ∀ later ∈ post, g ∉ stages.placement.children.getD later [] := by
  have hrows : ChildRowsShape rm stages.children :=
    regionChildren_rows_shape hparents hmin stages.hChildren
  have hinit : VisitFrontier rm stages.children [] [rm.clusters.length] :=
    ⟨by simp, fun c hc => Or.inl (by simpa using hc), by simp, fun c hc => (List.not_mem_nil hc).elim⟩
  have hwalk : VisitFrontier rm stages.placement.children stages.placement.order [] := by
    rw [stages.hPlacement]
    exact childPreorder_frontier hrows _ hinit
  intro g hg
  obtain ⟨revPre, revPost, hrev, _, _⟩ := (stages.reservation_order hparents hmin).2 g (Nat.le_of_lt hg)
  have hmember : g ∈ stages.placement.order :=
    List.mem_reverse.mp (List.mem_iff_append.mpr ⟨revPre, revPost, hrev⟩)
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hmember
  have hnodup : stages.placement.order.Nodup := by
    simpa only [List.append_nil] using hwalk.unique
  have hord := hwalk.ordered
  rw [hsplit] at hnodup hord
  exact ⟨pre, post, hsplit, (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1,
    (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1⟩

theorem componentRunR_active_reservation_bounds {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {o : Options} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hparams : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult) (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      0 < regionInsetOf P ∧
      (∀ g < rm.clusters.length, stages.placement.minimum.origins.getD g 0 = regionInsetOf P) ∧
      (∀ g, (stages.placement.children.getD g []).Nodup) ∧
      (∀ g, 0 ≤ (reserveWidths stages.placement P).getD g 0) ∧
      (∀ g, 0 ≤ stages.placement.buckets.widths.getD g 0) ∧
      (∀ g, 0 ≤ stages.placement.buckets.loopWidth.getD g 0) ∧
      ∀ g < rm.clusters.length, let pl := stages.placement
        let w := reserveWidths pl P
        2 * regionInsetOf P + pl.buckets.widths.getD g 0 +
          ((pl.children.getD g []).map fun c => w.getD c 0).sum ≤
          w.getD g 0 - pl.buckets.loopWidth.getD g 0 := by
  obtain ⟨_, _, _, p, minimum, ord, reserved, _, _, _, _, _, hmin, _, ⟨stages⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hparents := activeRegion_parent_count hactive
  have hinset : 0 < regionInsetOf P := by
    have hpad := (checkedParams_sizing_nonneg hparams).2.1
    have hb := checkedParams_clusterBorderW_ge_one hparams
    unfold regionInsetOf
    omega
  obtain ⟨hown, hlane, hloop⟩ := componentRunR_active_bucket_signs hrun stages
  obtain ⟨hchild, horder⟩ := stages.reservation_order hparents hmin
  have hw := reserveWidths_nonnegative (pl := stages.placement) (Int.le_of_lt hinset) hown hlane hloop
  refine ⟨p, minimum, ord, reserved, stages, hinset, ?_, hchild, hw, hown, hloop, ?_⟩
  · intro g hg
    rw [stages.hPlacement]
    change minimum.origins.getD g 0 = regionInsetOf P
    rw [constrainR_origins hmin, hparents, List.getD_eq_getElem?_getD,
      List.getElem?_replicate_of_lt hg, Option.getD_some]
  · intro g hg
    obtain ⟨_, _, hsplit, htail, hread⟩ := horder g (Nat.le_of_lt hg)
    have hgPl : g < stages.placement.rm.clusters.length := by simpa only [stages.hPlacement] using hg
    exact Int.le_trans (Int.le_add_of_nonneg_right (hlane g))
      (reserveWidths_room_from_last_writes (pl := stages.placement) (P := P) hsplit hgPl htail hread)

private abbrev ChildOriginAllocationState := List Int × List Int × List (Option Int)

private theorem allocateGroup_lefts_inv {pl : RegionPlacement} {P : Params}
    {widths : List Int} {g : Nat} {before after : ChildOriginAllocationState}
    {I : List Int → Prop} (h : allocateGroup pl P widths g before = .ok after)
    (hi : I before.2.1)
    (hs : ∀ lefts c x, I lefts → c ∈ pl.children.getD g [] → I (setAt lefts c x)) :
    I after.2.1 := by
  rcases before with ⟨xs, lefts, lanes⟩
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨placed, hplaced, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  have hlefts : after.2.1 = placed.2 :=
    (congrArg (fun out : ChildOriginAllocationState => out.2.1) (Except.ok.inj h)).symm
  rw [hlefts]
  refine foldOkInv (I := fun a : Int × List Int => I a.2) hi ?_ hplaced
  intro a c b ha hc hb
  have he : (a.1 + widths.getD c 0, setAt a.2 c a.1) = b := Except.ok.inj hb
  rw [← he]
  exact hs a.2 c a.1 ha hc

private theorem allocateGroups_lefts_inv {pl : RegionPlacement} {P : Params}
    {widths : List Int} {groups : List Nat} {before after : ChildOriginAllocationState}
    {I : List Int → Prop}
    (h : groups.foldlM (fun a g => allocateGroup pl P widths g a) before = .ok after)
    (hi : I before.2.1)
    (hs : ∀ g ∈ groups, ∀ lefts c x, I lefts → c ∈ pl.children.getD g [] →
      I (setAt lefts c x)) :
    I after.2.1 :=
  foldOkInv (I := fun a : ChildOriginAllocationState => I a.2.1) hi
    (fun _ g _ ha hg hstep => allocateGroup_lefts_inv hstep ha (hs g hg)) h

private theorem allocateGroups_left_lookup {pl : RegionPlacement} {P : Params}
    {widths : List Int} {groups : List Nat} {before after : ChildOriginAllocationState}
    {target : Nat} (haway : ∀ g ∈ groups, target ∉ pl.children.getD g [])
    (h : groups.foldlM (fun a g => allocateGroup pl P widths g a) before = .ok after) :
    after.2.1.getD target 0 = before.2.1.getD target 0 := by
  refine allocateGroups_lefts_inv (I := fun a => a.getD target 0 = before.2.1.getD target 0)
    h rfl ?_
  intro g hg a c x ha hc
  have hne : ¬ (target = c ∧ c < a.length) := fun he => haway g hg (he.1.symm ▸ hc)
  rw [setAt_getD, ite_eq_right hne]
  exact ha

theorem RegionCrossAllocationStages.childBudget_visit_stability {P : Params}
    {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    {s : RegionSpec} {inp : Input} {candidate : Graph}
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hmin : constrainR rm P p = .ok minimum)
    {owner child k : Nat} (howner : owner ≤ rm.clusters.length)
    (hchild : (stages.placement.children.getD owner [])[k]? = some child) :
    ∃ (pre post : List Nat) (before after : List Int × List Int × List (Option Int)),
      stages.placement.order = pre ++ owner :: post ∧
      pre.foldlM (fun a g => allocateGroup stages.placement P (reserveWidths stages.placement P) g a)
        (stages.before, List.replicate (stages.placement.rm.clusters.length + 1) 0,
          List.replicate stages.placement.p.chains.length none) = .ok before ∧
      allocateGroup stages.placement P (reserveWidths stages.placement P) owner before =
        .ok after ∧
      child < before.2.1.length ∧
      before.2.1.getD owner 0 = stages.allocation.lefts.getD owner 0 ∧
      after.2.1.getD child 0 = stages.allocation.lefts.getD child 0 := by
  have hparents := activeRegion_parent_count hactive
  have hrows : ChildRowsShape rm stages.children :=
    regionChildren_rows_shape hparents hmin stages.hChildren
  have hrowsPl : ChildRowsShape rm stages.placement.children := by
    rw [stages.hPlacement]
    exact hrows
  have hinit : VisitFrontier rm stages.children [] [rm.clusters.length] :=
    ⟨by simp, fun c hc => Or.inl (by simpa using hc), by simp, fun c hc => (List.not_mem_nil hc).elim⟩
  have hwalk : VisitFrontier rm stages.placement.children stages.placement.order [] := by
    rw [stages.hPlacement]
    exact childPreorder_frontier hrows _ hinit
  obtain ⟨revPre, revPost, hrev, _, _⟩ := (stages.reservation_order hparents hmin).2 owner howner
  have hmember : owner ∈ stages.placement.order :=
    List.mem_reverse.mp (List.mem_iff_append.mpr ⟨revPre, revPost, hrev⟩)
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hmember
  have hownerNotPost : owner ∉ post := by
    have hn : stages.placement.order.Nodup := by
      simpa only [List.append_nil] using hwalk.unique
    rw [hsplit] at hn
    exact (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  have hownerAvoid : ∀ g ∈ owner :: post, owner ∉ stages.placement.children.getD g [] := by
    have hord := hwalk.ordered
    rw [hsplit] at hord
    have htail := (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1
    intro g hg
    rcases List.mem_cons.mp hg with he | ht
    · rw [he]
      exact hwalk.noSelf owner hmember
    · exact htail g ht
  obtain ⟨hcBound, hcOwner⟩ := (hrowsPl.2 owner).2 child (List.mem_of_getElem? hchild)
  have hchildAvoid : ∀ g ∈ post, child ∉ stages.placement.children.getD g [] := by
    intro g hg hc
    have he : g = owner := ((hrowsPl.2 g).2 child hc).2.symm.trans hcOwner
    exact hownerNotPost (he ▸ hg)
  let init : ChildOriginAllocationState :=
    (stages.before, List.replicate (stages.placement.rm.clusters.length + 1) 0,
      List.replicate stages.placement.p.chains.length none)
  let step (a : ChildOriginAllocationState) (g : Nat) :=
    allocateGroup stages.placement P (reserveWidths stages.placement P) g a
  have halloc := stages.hAllocation
  unfold allocatePl at halloc
  obtain ⟨final, hfold, hfinish⟩ := bindOk halloc
  change stages.placement.order.foldlM step init = .ok final at hfold
  have hfinal : final.2.1 = stages.allocation.lefts :=
    congrArg (fun out : RegionAllocation × List Int => out.1.lefts) (Except.ok.inj hfinish)
  rw [hsplit, List.foldlM_append] at hfold
  obtain ⟨before, hpre, hrest⟩ := bindOk hfold
  have hvisitAndTail := hrest
  rw [List.foldlM_cons] at hvisitAndTail
  obtain ⟨after, hvisit, hpost⟩ := bindOk hvisitAndTail
  have hlen : before.2.1.length = stages.placement.rm.clusters.length + 1 := by
    refine allocateGroups_lefts_inv
      (I := fun a => a.length = stages.placement.rm.clusters.length + 1) hpre ?_ ?_
    · exact List.length_replicate
    · intro _ _ a c x ha _
      rw [setAt_length]
      exact ha
  have hbound : child < before.2.1.length := by
    rw [hlen, stages.hPlacement]
    exact Nat.lt_succ_of_lt hcBound
  have hownerStable := allocateGroups_left_lookup hownerAvoid hrest
  have hchildStable := allocateGroups_left_lookup hchildAvoid hpost
  rw [hfinal] at hownerStable hchildStable
  exact ⟨pre, post, before, after, hsplit, hpre, hvisit, hbound,
    hownerStable.symm, hchildStable.symm⟩

theorem RegionCrossAllocationStages.childBudget_left_from_allocation {P : Params}
    {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    {s : RegionSpec} {inp : Input} {candidate : Graph}
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hmin : constrainR rm P p = .ok minimum)
    {owner child k : Nat} (howner : owner ≤ rm.clusters.length)
    (hchild : (stages.placement.children.getD owner [])[k]? = some child) :
    stages.allocation.lefts.getD child 0 = stages.allocation.lefts.getD owner 0 +
      (if owner = rm.clusters.length then 0 else regionInsetOf P) +
      stages.placement.buckets.widths.getD owner 0 +
      (((stages.placement.children.getD owner []).take k).map fun c =>
        (reserveWidths stages.placement P).getD c 0).sum := by
  obtain ⟨_, _, _, _, _, _, hvisit, hbound, hownerRead, hchildWrite⟩ :=
    stages.childBudget_visit_stability hactive hmin howner hchild
  have hparents := activeRegion_parent_count hactive
  have hinset : (if owner != stages.placement.rm.clusters.length then
        stages.placement.minimum.origins.getD owner 0 else 0) =
      (if owner = rm.clusters.length then 0 else regionInsetOf P) := by
    rw [stages.hPlacement]
    change (if owner != rm.clusters.length then minimum.origins.getD owner 0 else 0) = _
    by_cases heq : owner = rm.clusters.length
    · simp [heq]
    · have hlt := Nat.lt_of_le_of_ne howner heq
      rw [ite_eq_left (bne_iff_ne.mpr heq), ite_eq_right heq]
      rw [constrainR_origins hmin, hparents, List.getD_eq_getElem?_getD,
        List.getElem?_replicate_of_lt hlt, Option.getD_some]
  have hleft := allocateGroup_child_left hvisit ((stages.reservation_order hparents hmin).1 owner)
    hchild hbound
  simpa only [hchildWrite, hownerRead, hinset] using hleft

theorem componentRunR_active_child_budget_lefts {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp candidate labels orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult) (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      constrainR rm P p = .ok minimum ∧
      ∀ {owner child k : Nat}, owner ≤ rm.clusters.length →
        (stages.placement.children.getD owner [])[k]? = some child →
        stages.allocation.lefts.getD child 0 = stages.allocation.lefts.getD owner 0 +
          (if owner = rm.clusters.length then 0 else regionInsetOf P) +
            stages.placement.buckets.widths.getD owner 0 +
            (((stages.placement.children.getD owner []).take k).map fun c =>
              (reserveWidths stages.placement P).getD c 0).sum := by
  obtain ⟨_, _, _, p, minimum, ord, reserved, _, _, _, _, _, hmin, _, ⟨stages⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  exact ⟨p, minimum, ord, reserved, stages, hmin,
    fun howner hchild => stages.childBudget_left_from_allocation hactive hmin howner hchild⟩

inductive RegionGroupBranch (rows : List (List Nat)) : Nat → Nat → Prop
  | here {a : Nat} : RegionGroupBranch rows a a
  | down {a b c : Nat} (h : b ∈ rows.getD a []) (tail : RegionGroupBranch rows b c) :
      RegionGroupBranch rows a c

private theorem RegionGroupBranch.snoc {rows : List (List Nat)} {a b c : Nat}
    (h : RegionGroupBranch rows a b) (he : c ∈ rows.getD b []) :
    RegionGroupBranch rows a c := by
  induction h with
  | here => exact .down he .here
  | down hed _ ih => exact .down hed (ih he)

private theorem childPreorder_paths (rows : List (List Nat)) (root : Nat)
    (fuel : Nat) (pending visited : List Nat)
    (hpath : ∀ g ∈ visited ++ pending, RegionGroupBranch rows root g) :
    ∀ g ∈ childPreorderGo rows fuel pending visited, RegionGroupBranch rows root g := by
  induction fuel generalizing pending visited with
  | zero => exact fun g hg => hpath g (List.mem_append_left _ hg)
  | succ fuel ih =>
    cases htop : pending.getLast? with
    | none =>
      rw [childPreorderGo, htop]
      exact fun g hg => hpath g (List.mem_append_left _ hg)
    | some head =>
      obtain ⟨pendingRest, rfl⟩ := List.getLast?_eq_some_iff.mp htop
      rw [childPreorderGo, htop, List.dropLast_concat]
      refine ih _ _ ?_
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · rcases List.mem_append.mp hg with hg | hg
        · exact hpath g (List.mem_append_left _ hg)
        · exact hpath g (List.mem_append_right _ (List.mem_append_right _ hg))
      · rcases List.mem_append.mp hg with hg | hg
        · exact hpath g (List.mem_append_right _ (List.mem_append_left _ hg))
        · have hh : RegionGroupBranch rows root head :=
            hpath head (by simp)
          exact hh.snoc (List.mem_reverse.mp hg)

theorem RegionCrossAllocationStages.group_paths {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) :
    (∀ a b, b ∈ stages.placement.children.getD a [] →
      b < rm.clusters.length ∧ parentGroup rm b = a) ∧
    ∀ g ≤ rm.clusters.length,
      RegionGroupBranch stages.placement.children rm.clusters.length g := by
  have hrows := regionChildren_rows_shape hparents hmin stages.hChildren
  refine ⟨?_, ?_⟩
  · intro a b hb
    rw [stages.hPlacement] at hb
    exact (hrows.2 a).2 b hb
  · intro g hg
    obtain ⟨pre, post, hsplit, _, _⟩ := (stages.reservation_order hparents hmin).2 g hg
    have hmem : g ∈ stages.placement.order :=
      List.mem_reverse.mp (List.mem_iff_append.mpr ⟨pre, post, hsplit⟩)
    rw [stages.hPlacement] at hmem ⊢
    refine childPreorder_paths _ _ _ _ _ ?_ g hmem
    intro k hk
    have he : k = rm.clusters.length := by simpa using hk
    rw [he]
    exact .here

theorem RegionCrossAllocationStages.root_left {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) :
    stages.allocation.lefts.getD rm.clusters.length 0 = 0 := by
  have he := (stages.group_paths hparents hmin).1
  have ha := stages.hAllocation
  unfold allocatePl at ha
  obtain ⟨final, hfold, hfin⟩ := bindOk ha
  have hout : final.2.1 = stages.allocation.lefts :=
    congrArg (fun res : RegionAllocation × List Int => res.1.lefts) (Except.ok.inj hfin)
  rw [← hout]
  have hstable := allocateGroups_left_lookup (target := rm.clusters.length)
    (fun g _ hg => (Nat.lt_irrefl _) (he g _ hg).1) hfold
  rw [hstable]
  exact replicate_getD_same _ _ _

theorem RegionCrossAllocationStages.allocation_topology {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) :
    stages.placement.order.Nodup ∧
    stages.placement.order.Pairwise (fun a b => a ∉ stages.placement.children.getD b []) ∧
    (∀ g, g ∉ stages.placement.children.getD g []) ∧
    ∀ g ≤ rm.clusters.length, g ∈ stages.placement.order := by
  have hrows := regionChildren_rows_shape hparents hmin stages.hChildren
  have hinit : VisitFrontier rm stages.children [] [rm.clusters.length] :=
    ⟨by simp, fun c hc => Or.inl (by simpa using hc), by simp, fun c hc => (List.not_mem_nil hc).elim⟩
  have hwalk : VisitFrontier rm stages.placement.children stages.placement.order [] := by
    rw [stages.hPlacement]
    exact childPreorder_frontier hrows _ hinit
  have hmem : ∀ g ≤ rm.clusters.length, g ∈ stages.placement.order := by
    intro g hg
    obtain ⟨pre, post, hsplit, _, _⟩ := (stages.reservation_order hparents hmin).2 g hg
    exact List.mem_reverse.mp (List.mem_iff_append.mpr ⟨pre, post, hsplit⟩)
  refine ⟨by simpa only [List.append_nil] using hwalk.unique, hwalk.ordered, ?_, hmem⟩
  intro g hself
  have hb : g < rm.clusters.length := by
    rw [stages.hPlacement] at hself
    exact ((hrows.2 g).2 g hself).1
  exact hwalk.noSelf g (hmem g (Nat.le_of_lt hb)) hself







private theorem setAtLength {α : Type} (xs : List α) (i : Nat) (value : α) :
    (setAt xs i value).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem setAtOther {α : Type} (xs : List α) (i j : Nat) (value fallback : α)
    (hne : i ≠ j) : (setAt xs i value).getD j fallback = xs.getD j fallback := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => cases j with
      | zero => exact (hne rfl).elim
      | succ j => rfl
    | succ i => cases j with
      | zero => rfl
      | succ j => exact ih i j (fun h => hne (congrArg Nat.succ h))

private theorem setAtSelf {α : Type} (xs : List α) (i : Nat) (value fallback : α)
    (hin : i < xs.length) : (setAt xs i value).getD i fallback = value := by
  induction xs generalizing i with
  | nil => simp at hin
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hin)

private theorem setAtOutside {α : Type} (xs : List α) (i : Nat) (value : α)
    (hout : xs.length ≤ i) : setAt xs i value = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => simp at hout
    | succ i => exact congrArg (List.cons x) (ih i (by simpa using hout))

private def bucketMember (ngs : List Nat) (g : Nat) (q : ProperNode × Nat) : Bool :=
  q.1.node.border == 0 && ngs.getD q.2 0 == g

private theorem bucketMember_iff {ngs : List Nat} {g : Nat} {q : ProperNode × Nat} :
    bucketMember ngs g q ↔ q.1.node.border = 0 ∧ ngs.getD q.2 0 = g := by
  simp only [bucketMember, Bool.and_eq_true_iff, beq_iff_eq]

private def gatherMembers (ngs : List Nat) (members : List (List Nat))
    (q : ProperNode × Nat) : List (List Nat) :=
  if q.1.node.border != 0 then members else
    let owner := ngs.getD q.2 0
    setAt members owner (members.getD owner [] ++ [q.2])

private theorem gatherMembers_getD (ngs : List Nat) (entries : List (ProperNode × Nat))
    (members : List (List Nat)) (g : Nat) :
    (entries.foldl (gatherMembers ngs) members).getD g [] = members.getD g [] ++
      (if g < members.length then (entries.filter (bucketMember ngs g)).map Prod.snd else []) := by
  induction entries generalizing members with
  | nil => simp
  | cons q rest ih =>
    rw [List.foldl_cons, ih]
    by_cases hp : q.1.node.border = 0
    · have hstep : gatherMembers ngs members q =
          setAt members (ngs.getD q.2 0) (members.getD (ngs.getD q.2 0) [] ++ [q.2]) := by
        unfold gatherMembers
        exact ite_eq_right (fun h => (bne_iff_ne.mp h) hp)
      rw [hstep, setAtLength]
      by_cases ho : ngs.getD q.2 0 = g
      · rw [ho]
        by_cases hin : g < members.length
        · have hm : bucketMember ngs g q := bucketMember_iff.mpr ⟨hp, ho⟩
          rw [setAtSelf _ _ _ _ hin, List.filter_cons_of_pos hm]
          simp only [ite_eq_left hin, List.map_cons, List.append_assoc, List.singleton_append]
        · rw [setAtOutside _ _ _ (Nat.le_of_not_gt hin)]
          simp only [ite_eq_right hin]
      · have hm : ¬ bucketMember ngs g q := fun h => ho (bucketMember_iff.mp h).2
        rw [setAtOther _ _ _ _ _ ho, List.filter_cons_of_neg hm]
    · have hstep : gatherMembers ngs members q = members := by
        unfold gatherMembers
        exact ite_eq_left (bne_iff_ne.mpr hp)
      have hm : ¬ bucketMember ngs g q := fun h => hp (bucketMember_iff.mp h).1
      rw [hstep, List.filter_cons_of_neg hm]

private theorem newRegionBuckets_members (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (ngs : List Nat) (labelWidths x : List Int) (g : Nat) :
    (newRegionBuckets rm cg p ngs labelWidths x).members.getD g [] =
      if g < rm.clusters.length + 1 then
        (p.nodes.zipIdx.filter (bucketMember ngs g)).map Prod.snd else [] := by
  let empty : RegionBuckets :=
    ⟨List.replicate (rm.clusters.length + 1) [], List.replicate (rm.clusters.length + 1) 0,
      List.replicate (rm.clusters.length + 1) 2147483647,
      List.replicate (rm.clusters.length + 1) (-2147483648),
      List.replicate (rm.clusters.length + 1) [], List.replicate (rm.clusters.length + 1) 0,
      List.replicate (rm.clusters.length + 1) 0⟩
  let gather (acc : RegionBuckets) (q : ProperNode × Nat) : RegionBuckets :=
    if q.1.node.border != 0 then acc else
      let owner := ngs.getD q.2 0
      let width := q.1.node.w + 2 * (q.1.node.loopExtent : Int)
      let left := RouteImpl.xAt x q.2 - Int.tdiv width 2
      let right := left + width
      { acc with
        low := setAt acc.low owner (min (acc.low.getD owner 2147483647) left)
        high := setAt acc.high owner (max (acc.high.getD owner (-2147483648)) right)
        members := setAt acc.members owner (acc.members.getD owner [] ++ [q.2]) }
  let addLane (acc : RegionBuckets) (q : Edge × Nat) : RegionBuckets :=
    if !q.1.reversed || q.1.tail == q.1.head then acc else
      let root := rm.clusters.length
      let owner := edgeOwnerOf rm ngs root q.1.tail q.1.head
      if owner == root then acc else
        { acc with
          lanes := setAt acc.lanes owner (acc.lanes.getD owner [] ++ [q.2])
          laneWidth := setAt acc.laneWidth owner
            (max (acc.laneWidth.getD owner 0) (labelWidths.getD q.2 0)) }
  change ((cg.edges.zipIdx.foldl addLane (p.nodes.zipIdx.foldl gather empty)).members).getD g [] = _
  have laneMembers (entries : List (Edge × Nat)) (acc : RegionBuckets) :
      (entries.foldl addLane acc).members = acc.members := by
    induction entries generalizing acc with
    | nil => rfl
    | cons q rest ih =>
      rw [List.foldl_cons, ih]
      dsimp only [addLane]
      split
      · rfl
      · split <;> rfl
  have gatheredMembers (entries : List (ProperNode × Nat)) (acc : RegionBuckets) :
      (entries.foldl gather acc).members = entries.foldl (gatherMembers ngs) acc.members := by
    induction entries generalizing acc with
    | nil => rfl
    | cons q rest ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      have heq : (gather acc q).members = gatherMembers ngs acc.members q := by
        dsimp only [gather, gatherMembers]
        split <;> rfl
      rw [heq]
  rw [laneMembers, gatheredMembers, gatherMembers_getD]
  have hnil : (List.replicate (rm.clusters.length + 1) ([] : List Nat)).getD g [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  simp only [empty, hnil, List.length_replicate, List.nil_append]

private theorem newRegionBuckets_count (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (ngs : List Nat) (labelWidths x : List Int) (g v : Nat) {n : ProperNode}
    (hv : p.nodes[v]? = some n) (hp : n.node.border = 0) :
    ((newRegionBuckets rm cg p ngs labelWidths x).members.getD g []).count v =
      if g < rm.clusters.length + 1 ∧ ngs.getD v 0 = g then 1 else 0 := by
  rw [newRegionBuckets_members]
  by_cases hg : g < rm.clusters.length + 1
  · rw [ite_eq_left hg]
    have hmem : v ∈ (p.nodes.zipIdx.filter (bucketMember ngs g)).map Prod.snd ↔
        ngs.getD v 0 = g := by
      constructor
      · intro h
        obtain ⟨⟨m, k⟩, hq, rfl⟩ := List.mem_map.mp h
        obtain ⟨hm, howner⟩ := List.mem_filter.mp hq
        have hlookup := List.mem_zipIdx_iff_getElem?.mp hm
        have heq : m = n := Option.some.inj (hlookup.symm.trans hv)
        subst m
        exact (bucketMember_iff.mp howner).2
      · intro h
        exact List.mem_map.mpr ⟨(n, v), List.mem_filter.mpr
          ⟨List.mem_zipIdx_iff_getElem?.mpr hv, bucketMember_iff.mpr ⟨hp, h⟩⟩, rfl⟩
    by_cases ho : ngs.getD v 0 = g
    · rw [ite_eq_left ⟨hg, ho⟩]
      have hnd : (p.nodes.zipIdx.map Prod.snd).Nodup := by
        rw [List.zipIdx_map_snd]
        exact List.nodup_range'
      have hsub := (List.filter_sublist (p := bucketMember ngs g)
        (l := p.nodes.zipIdx)).map Prod.snd
      exact (hsub.nodup hnd).count_of_mem (hmem.mpr ho)
    · rw [ite_eq_right (fun h => ho h.2)]
      exact List.count_eq_zero_of_not_mem (fun h => ho (hmem.mp h))
  · simp [hg]

private def NotClusterAnchor (rm : ComponentRegions) (v : Nat) : Prop :=
  ∀ c ∈ rm.clusters, c.top ≠ v ∧ c.bottom ≠ v

private def regionFrameStep (pl : RegionPlacement) (P : Params) (alloc : RegionAllocation)
    (x : List Int) (q : RegionCluster × Nat) : List Int :=
  let c := q.1
  let left := alloc.lefts.getD q.2 0
  let frameRight := left + alloc.widths.getD q.2 0 - pl.buckets.loopWidth.getD q.2 0
  let center := left + Int.tdiv (frameRight - left) 2
  let x := pl.p.nodes.zipIdx.foldl (fun x nq =>
    if nq.1.node.clusterPath.getLast? != some c.decl then x
    else
      match nq.1.node.border with
      | -1 => setAt x nq.2 (left + Int.tdiv P.clusterBorderW 2)
      | 1 => setAt x nq.2 (frameRight - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
      | 3 => setAt x nq.2 center
      | _ => x) x
  setAt (setAt x c.top center) c.bottom center

private theorem regionFrames_plain {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {xs : List Int} {v : Nat} {n : ProperNode}
    (hv : pl.p.nodes[v]? = some n) (hplain : n.node.border = 0)
    (hanchor : NotClusterAnchor pl.rm v) :
    (regionFrames pl P alloc xs).getD v 0 = xs.getD v 0 := by
  have markers (ns : List (ProperNode × Nat)) (x : List Int) (decl : Nat)
      (left right center : Int)
      (hns : ∀ q ∈ ns, pl.p.nodes[q.2]? = some q.1) :
      (ns.foldl (fun x q =>
        if q.1.node.clusterPath.getLast? != some decl then x else
          match q.1.node.border with
          | -1 => setAt x q.2 (left + Int.tdiv P.clusterBorderW 2)
          | 1 => setAt x q.2 (right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
          | 3 => setAt x q.2 center
          | _ => x) x).getD v 0 = x.getD v 0 := by
    induction ns generalizing x with
    | nil => rfl
    | cons q qs ih =>
      rw [List.foldl_cons, ih _ (fun e he => hns e (List.mem_cons_of_mem _ he))]
      by_cases heq : q.2 = v
      · have hq := hns q List.mem_cons_self
        rw [heq, hv] at hq
        have hborder : q.1.node.border = 0 :=
          (congrArg (fun m : ProperNode => m.node.border) (Option.some.inj hq)).symm.trans hplain
        simp [hborder]
      · split
        · rfl
        · split <;> first | rfl | exact setAtOther _ _ _ _ _ heq
  have step_plain (q : RegionCluster × Nat) (x : List Int)
      (hq : q.1 ∈ pl.rm.clusters) :
      (regionFrameStep pl P alloc x q).getD v 0 = x.getD v 0 := by
    obtain ⟨ht, hb⟩ := hanchor q.1 hq
    unfold regionFrameStep
    dsimp only
    rw [setAtOther _ _ _ _ _ hb, setAtOther _ _ _ _ _ ht]
    exact markers pl.p.nodes.zipIdx x _ _ _ _
      (fun e he => List.mem_zipIdx_iff_getElem?.mp he)
  have fold_plain (entries : List (RegionCluster × Nat)) (x : List Int)
      (hentries : ∀ q ∈ entries, q.1 ∈ pl.rm.clusters) :
      (entries.foldl (regionFrameStep pl P alloc) x).getD v 0 = x.getD v 0 := by
    induction entries generalizing x with
    | nil => rfl
    | cons q qs ih =>
      rw [List.foldl_cons, ih _ (fun e he => hentries e (List.mem_cons_of_mem _ he))]
      exact step_plain q x (hentries q List.mem_cons_self)
  have hframe : regionFrames pl P alloc xs =
      pl.rm.clusters.zipIdx.foldl (regionFrameStep pl P alloc) xs := rfl
  rw [hframe]
  exact fold_plain pl.rm.clusters.zipIdx xs (fun q hq =>
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq))

private theorem clusterPortR_other {pl : RegionPlacement} {g k v : Nat} {xs out : List Int}
    (h : clusterPortR pl g k xs = .ok out) (hne : k ≠ v) :
    out.getD v 0 = xs.getD v 0 := by
  unfold clusterPortR at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have he := (Except.ok.inj h).symm
      rw [he, setAtOther _ _ _ _ _ hne]
  · cases h

private theorem reservedPortsR_other {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs out : List Int} {outP : Proper} {v : Nat}
    (h : reservedPortsR pl cg labels xs = .ok (out, outP))
    (hanchor : NotClusterAnchor pl.rm v) :
    out.getD v 0 = xs.getD v 0 ∧ outP.nodes[v]? = pl.p.nodes[v]? := by
  let step (acc : List Int × Array ProperNode) (q : RegionCluster × Nat) :
      Except LayoutError (List Int × Array ProperNode) := do
    let c := q.1
    let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      pure (x, acc.2.set! c.top { top with node := { top.node with
        h := max (RouteImpl.nodeH pl.p c.top) footprint } })
  have foldOther (entries : List (RegionCluster × Nat)) (initial fin : List Int × Array ProperNode)
      (hentries : ∀ q ∈ entries, q.1 ∈ pl.rm.clusters)
      (hf : entries.foldlM step initial = .ok fin) :
      fin.1.getD v 0 = initial.1.getD v 0 ∧ fin.2[v]? = initial.2[v]? := by
    induction entries generalizing initial with
    | nil =>
      change Except.ok initial = Except.ok fin at hf
      cases hf
      exact ⟨rfl, rfl⟩
    | cons q qs ih =>
      rw [List.foldlM_cons] at hf
      obtain ⟨mid, hmid, htail⟩ := bindOk hf
      have hrest := ih mid (fun e he => hentries e (List.mem_cons_of_mem _ he)) htail
      obtain ⟨ht, hb⟩ := hanchor q.1 (hentries q List.mem_cons_self)
      dsimp only [step] at hmid
      split at hmid
      · cases hmid
      · obtain ⟨x1, hx1, hmid⟩ := bindOk hmid
        obtain ⟨x2, hx2, hmid⟩ := bindOk hmid
        rw [← Except.ok.inj hmid] at hrest
        refine ⟨hrest.1.trans ((clusterPortR_other hx2 hb).trans (clusterPortR_other hx1 ht)), ?_⟩
        exact hrest.2.trans (by
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne ht])
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = .ok (out, outP) at h
  obtain ⟨fin, hf, h⟩ := bindOk h
  have hother := foldOther _ _ _ (fun _ he =>
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)) hf
  have hout := Except.ok.inj h
  have hx : out = fin.1 := (congrArg Prod.fst hout).symm
  have hp : outP.nodes = fin.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) hout).symm
  rw [hx, hp, Array.getElem?_toList, ← List.getElem?_toArray]
  exact hother

private theorem regionFrames_reservedPorts_plain {pl : RegionPlacement} {P : Params}
    {cg : Graph} {labels : List MeasuredLabel} {alloc : RegionAllocation}
    {xs out : List Int} {outP : Proper} {v : Nat} {n : ProperNode}
    (h : reservedPortsR pl cg labels (regionFrames pl P alloc xs) = .ok (out, outP))
    (hv : pl.p.nodes[v]? = some n) (hplain : n.node.border = 0)
    (hanchor : NotClusterAnchor pl.rm v) :
    out.getD v 0 = xs.getD v 0 ∧ outP.nodes[v]? = pl.p.nodes[v]? := by
  obtain ⟨hx, hp⟩ := reservedPortsR_other h hanchor
  exact ⟨hx.trans (regionFrames_plain (pl := pl) (P := P) (alloc := alloc) (xs := xs)
    hv hplain hanchor), hp⟩

private theorem resolved_cluster_anchor_source {P : Params} {s : RegionSpec}
    {inp : Input} {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm))
    {c : RegionCluster} (hc : c ∈ rm.clusters) :
    (∃ n, cg.nodes[c.top]? = some n ∧ n.border ≠ 0) ∧
    (∃ n, cg.nodes[c.bottom]? = some n ∧ n.border ≠ 0) := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bindOk h
    split at h
    · cases h
    · have hcluster : rm.clusters = clusterRows inp s cg := by
        have he := Option.some.inj (Except.ok.inj h)
        exact (congrArg ComponentRegions.clusters he).symm
      rw [hcluster] at hc
      unfold clusterRows at hc
      obtain ⟨q, hq, hc⟩ := List.mem_filterMap.mp hc
      dsimp only at hc
      split at hc
      · cases hc
      · rename_i hborder
        have ht : ∃ n, cg.nodes[q.2]? = some n ∧ n.border ≠ 0 := by
          refine ⟨q.1, List.mem_zipIdx_iff_getElem?.mp hq, ?_⟩
          intro hh
          simp [hh] at hborder
        have he := Option.some.inj hc
        rw [← he]
        refine ⟨ht, ?_⟩
        dsimp only
        split
        · rename_i b hb
          have hmem := List.mem_of_find?_eq_some hb
          have htest := List.find?_some hb
          refine ⟨b.1, List.mem_zipIdx_iff_getElem?.mp hmem, ?_⟩
          intro hh
          simp [hh] at htest
        · exact ht

private theorem source_coordinate_record (P : Params) (exact : List Nat) (s : RegionSpec)
    {labeled : Proper} {v : Nat} {n : Node}
    (h : labeled.nodes[v]? = some ⟨n, false, none, false⟩) :
    ∃ m, (coordinateGraphR P exact (some s) labeled).nodes[v]? = some m ∧
      m.node.border = n.border ∧ m.node.clusterPath = n.clusterPath := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  have hkeys := sizeProperPortsX_key P exact labeled v
  change (sized.nodes[v]?).map _ = _ at hkeys
  rw [h] at hkeys
  cases hs : sized.nodes[v]? with
  | none => simp [hs] at hkeys
  | some sz =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkeys
    let t : ProperNode := if sz.node.border == -2 || sz.node.border == 2 then
      { sz with node := { sz.node with w := 0, h := 0 } } else sz
    have hlookupT : titled.nodes[v]? = some t := by
      unfold titled titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by
        simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hs).1)]
      simp only [List.getElem?_map, hs, Option.map_some] <;> rfl
    have htkeys : t.node.border = sz.node.border ∧ t.node.clusterPath = sz.node.clusterPath := by
      dsimp only [t]
      split <;> exact ⟨rfl, rfl⟩
    obtain ⟨extra, hbordered, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    have hlookupC : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? =
        some (clearF t) := by
      rw [clearProxyExtents_nodes, List.getElem?_map, hbordered,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp hlookupT).1, hlookupT] <;> rfl
    obtain ⟨m, hm, _⟩ := materialize_exists _ hlookupC
    have ⟨old, ho, _, hb, _, hsame⟩ := materialize_lookup _ hm
    have he : old = clearF t := Option.some.inj (ho.symm.trans hlookupC)
    subst old
    have htDummy : t.dummy = false := by
      dsimp only [t]
      split <;> exact hkeys.1
    have hcDummy : (clearF t).dummy = false := (clearF_keys t).1.trans htDummy
    refine ⟨m, hm, hb.trans ((clearF_keys t).2.1.trans (htkeys.1.trans hkeys.2.1)), ?_⟩
    rw [hsame hcDummy, (clearF_keys t).2.2.1, htkeys.2, hkeys.2.2]

/-- In a component run, region ports target original frame markers, not
plain proper nodes. Ranking preserves the graph records that identify them. -/
private theorem resolved_anchors_not_plain {P : Params} {s : RegionSpec}
    {inp : Input} {cg cg' : Graph} {rm : ComponentRegions} {exact : List Nat}
    {ranks : List Int} {rankBudget : Bool} {p0 labeled : Proper}
    {labels : List MeasuredLabel}
    (hresolved : newComponentRegions (some s) P inp cg = .ok (some rm))
    (hrank : rankEquivalentR rm cg = .ok (ranks, cg', rankBudget))
    (hnorm : normalize cg' ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg' p0 (componentLabels cg' labels) = .ok labeled)
    {v : Nat} {n : ProperNode}
    (hv : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some n)
    (hp : n.node.border = 0) : NotClusterAnchor rm v := by
  have hnodes := rankEquivalentR_nodes_eq hrank
  have away {i : Nat} (hi : ∃ nd, cg.nodes[i]? = some nd ∧ nd.border ≠ 0) : i ≠ v := by
    obtain ⟨nd, hnd, hborder⟩ := hi
    intro heq
    subst i
    rw [← hnodes] at hnd
    obtain ⟨m, hm, hb, _⟩ := source_coordinate_record P exact s
      (addLabelNodes_untouched_node hlab (normalize_node_record hnorm hnd) rfl)
    have he : m = n := Option.some.inj (hm.symm.trans hv)
    rw [he, hp] at hb
    exact hborder hb.symm
  intro c hc
  obtain ⟨ht, hb⟩ := resolved_cluster_anchor_source hresolved hc
  exact ⟨away ht, away hb⟩

private theorem plain_frame_cross_rect {P : Params} {cg : Graph} {run : Run}
    {i : Nat} {source : Node} {n : ProperNode} (hs : cg.nodes[i]? = some source)
    (hb : source.border = 0) (hn : run.proper.nodes[i]? = some n)
    (hx : run.xs.getD i 0 = run.coordinateXs.getD i 0) :
    frameRect P cg run i =
      ⟨run.coordinateXs.getD i 0 - Int.fdiv n.node.w 2, run.ys.getD i 0, n.node.w, n.node.h⟩ := by
  have hget : cg.nodes.getD i default = source := by
    simp only [List.getD_eq_getElem?_getD, hs, Option.getD_some]
  have hframe : frameRect P cg run i = nodeRect cg run i := by
    unfold frameRect
    simp only []
    rw [hget, hb]
    rfl
  rw [hframe, ← hx]
  simp [nodeRect, hn]

private theorem dcpBind {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private inductive DcpWalk (kids : Nat → List Nat) : List Nat → List Nat → Prop where
  | stop (todo : List Nat) : DcpWalk kids todo []
  | visit {g : Nat} {todo visits : List Nat} :
      DcpWalk kids (kids g ++ todo) visits → DcpWalk kids (g :: todo) (g :: visits)

private theorem dcpWalkOfPreorder (cs : List (List Nat)) (fuel : Nat)
    (todo seen : List Nat) :
    ∃ visits, childPreorderGo cs fuel todo.reverse seen = seen ++ visits ∧
      DcpWalk (fun g => cs.getD g []) todo visits := by
  induction fuel generalizing todo seen with
  | zero =>
    exact ⟨[], by simp [childPreorderGo], .stop todo⟩
  | succ fuel ih =>
    cases todo with
    | nil => exact ⟨[], by simp [childPreorderGo], .stop []⟩
    | cons g todo =>
      obtain ⟨visits, he, hwalk⟩ := ih (cs.getD g [] ++ todo) (seen ++ [g])
      have hscan : childPreorderGo cs (fuel + 1) (g :: todo).reverse seen =
          childPreorderGo cs fuel (cs.getD g [] ++ todo).reverse (seen ++ [g]) := by
        simp [childPreorderGo]
      exact ⟨g :: visits, by rw [hscan, he, List.append_assoc, List.singleton_append], .visit hwalk⟩

private theorem dcpWalkGap {kids : Nat → List Nat} {left right first last : Nat → Int}
    (self : ∀ g, left g ≤ first g ∧ last g ≤ right g)
    (children : ∀ g, (kids g).Pairwise (fun a b => right a ≤ left b) ∧
      ∀ c ∈ kids g, left g ≤ left c ∧ last g ≤ left c ∧ right c ≤ right g)
    {todo visits : List Nat} (walk : DcpWalk kids todo visits)
    (pending : todo.Pairwise (fun a b => right a ≤ left b)) :
    visits.Pairwise (fun a b => last a ≤ first b) ∧
      ∀ g ∈ visits, ∃ host ∈ todo, left host ≤ first g ∧ last g ≤ right host := by
  induction walk with
  | stop => simp
  | @visit g todo visits _ ih =>
    obtain ⟨hfront, htail⟩ := List.pairwise_cons.mp pending
    obtain ⟨hchildPair, hchild⟩ := children g
    have hnext : (kids g ++ todo).Pairwise (fun a b => right a ≤ left b) :=
      List.pairwise_append.mpr ⟨hchildPair, htail, fun c hc v hv =>
        Int.le_trans (hchild c hc).2.2 (hfront v hv)⟩
    obtain ⟨hpair, hcover⟩ := ih hnext
    refine ⟨List.pairwise_cons.mpr ⟨?_, hpair⟩, ?_⟩
    · intro v hv
      obtain ⟨host, hm, hl, _⟩ := hcover v hv
      rcases List.mem_append.mp hm with hm | hm
      · exact Int.le_trans (hchild host hm).2.1 hl
      · exact Int.le_trans (self g).2 (Int.le_trans (hfront host hm) hl)
    · intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v
        exact ⟨g, List.mem_cons_self, self g⟩
      · obtain ⟨host, hm, hl, hr⟩ := hcover v hv
        rcases List.mem_append.mp hm with hm | hm
        · exact ⟨g, List.mem_cons_self, Int.le_trans (hchild host hm).1 hl,
            Int.le_trans hr (hchild host hm).2.2⟩
        · exact ⟨host, List.mem_cons_of_mem _ hm, hl, hr⟩

private theorem dcpPrefixNonneg (f : Nat → Int) (hf : ∀ g, 0 ≤ f g)
    (xs : List Nat) (i : Nat) :
    0 ≤ ((xs.take i).map f).sum := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simpa only [List.take_succ_cons, List.map_cons, List.sum_cons] using
        Int.add_nonneg (hf x) (ih i)

private theorem dcpPrefixMono (f : Nat → Int) (hf : ∀ g, 0 ≤ f g)
    (xs : List Nat) (i j : Nat) (hij : i ≤ j) :
    ((xs.take i).map f).sum ≤ ((xs.take j).map f).sum := by
  induction xs generalizing i j with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simpa only [List.take_zero, List.map_nil, List.sum_nil] using dcpPrefixNonneg f hf (x :: xs) j
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        exact Int.add_le_add_left (ih i j (by omega)) _

private theorem dcpSumLookup (f : Nat → Int) (hf : ∀ g, 0 ≤ f g)
    {xs : List Nat} {i j c : Nat} (hc : xs[i]? = some c) (hij : i < j) :
    ((xs.take i).map f).sum + f c ≤ ((xs.take j).map f).sum := by
  have hsum := dcpPrefixMono f hf xs (i + 1) j (by omega)
  simpa only [List.take_add_one, hc, Option.toList_some, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero] using hsum

private abbrev DcpState := List Int × List Int × List (Option Int)

private abbrev dcpInit (pl : RegionPlacement) (xs : List Int) : DcpState :=
  (xs, List.replicate (pl.rm.clusters.length + 1) 0,
    List.replicate pl.p.chains.length none)

private abbrev dcpFold (pl : RegionPlacement) (P : Params) (gs : List Nat) (st : DcpState) :
    Except LayoutError DcpState :=
  gs.foldlM (fun a g => allocateGroup pl P (reserveWidths pl P) g a) st

private theorem dcpAllocationFinal {pl : RegionPlacement} {P : Params}
    {xs shifted : List Int} {alloc : RegionAllocation}
    (h : allocatePl pl P xs = .ok (alloc, shifted)) :
    ∃ final, dcpFold pl P pl.order (dcpInit pl xs) = .ok final ∧ final.2.1 = alloc.lefts := by
  unfold allocatePl at h
  obtain ⟨final, hf, hout⟩ := dcpBind h
  exact ⟨final, hf, congrArg (fun a : RegionAllocation × List Int => a.1.lefts)
    (Except.ok.inj hout)⟩

private theorem dcpTraceLeft {pl : RegionPlacement} {P : Params}
    {pre post : List Nat} {g : Nat} {xs shifted : List Int}
    {alloc : RegionAllocation} {before : DcpState}
    (h : allocatePl pl P xs = .ok (alloc, shifted))
    (horder : pl.order = pre ++ g :: post)
    (hpre : dcpFold pl P pre (dcpInit pl xs) = .ok before)
    (havoid : ∀ k ∈ g :: post, g ∉ pl.children.getD k []) :
    before.2.1.getD g 0 = alloc.lefts.getD g 0 := by
  obtain ⟨final, hf, hout⟩ := dcpAllocationFinal h
  unfold dcpFold at hpre hf
  simp only [horder, List.foldlM_append, hpre, bind, Except.bind] at hf
  change dcpFold pl P (g :: post) before = .ok final at hf
  have he := allocateGroups_left_lookup (pl := pl) (P := P) havoid hf
  rw [hout] at he
  exact he.symm

private theorem dcpStageTopology {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) :
    let pl := stages.placement
    let root := rm.clusters.length
    pl.children.length = root + 1 ∧
    (∀ g, (pl.children.getD g []).Nodup ∧
      ∀ c ∈ pl.children.getD g [], c < root ∧ parentGroup rm c = g) ∧
    pl.order.Nodup ∧
    pl.order.Pairwise (fun a b => a ∉ pl.children.getD b []) ∧
    (∀ g ∈ pl.order, g ∉ pl.children.getD g []) ∧
    (∀ g ≤ root, g ∈ pl.order) ∧
    ∃ tail, pl.order = root :: tail := by
  have hrows := regionChildren_rows_shape hparents hmin stages.hChildren
  have hinit : VisitFrontier rm stages.children [] [rm.clusters.length] :=
    ⟨by simp, fun c hc => Or.inl (by simpa using hc), by simp,
      fun c hc => (List.not_mem_nil hc).elim⟩
  have hw := childPreorder_frontier hrows (stages.children.length + 1) hinit
  have ht : ∃ tail, stages.placement.order = rm.clusters.length :: tail := by
    rw [stages.hPlacement]
    obtain ⟨tail, htail, _⟩ := dcpWalkOfPreorder stages.children stages.children.length
      (stages.children.getD rm.clusters.length []) [rm.clusters.length]
    exact ⟨tail, by
      simpa only [childPreorderGo, List.getLast?_singleton, List.dropLast_singleton,
        List.nil_append, List.singleton_append] using htail⟩
  refine ⟨by rw [stages.hPlacement]; exact hrows.1,
    by rw [stages.hPlacement]; exact hrows.2, ?_, ?_, ?_, ?_, ht⟩
  · rw [stages.hPlacement]
    simpa only [List.append_nil] using hw.unique
  · rw [stages.hPlacement]
    exact hw.ordered
  · rw [stages.hPlacement]
    exact hw.noSelf
  · intro g hg
    rcases Nat.eq_or_lt_of_le hg with rfl | hg
    · obtain ⟨tail, ht⟩ := ht
      rw [ht]
      exact List.mem_cons_self
    · obtain ⟨pre, post, he, _, _⟩ :=
        (stages.reservation_order hparents hmin).2 g (Nat.le_of_lt hg)
      exact List.mem_reverse.mp (List.mem_iff_append.mpr ⟨pre, post, he⟩)

private theorem dcpRootChildLeft {pl : RegionPlacement} {P : Params}
    {xs shifted : List Int} {alloc : RegionAllocation} {tail : List Nat}
    (ha : allocatePl pl P xs = .ok (alloc, shifted))
    (horder : pl.order = pl.rm.clusters.length :: tail) (hnd : pl.order.Nodup)
    (hrows : ∀ g, (pl.children.getD g []).Nodup ∧
      ∀ c ∈ pl.children.getD g [], c < pl.rm.clusters.length ∧ parentGroup pl.rm c = g)
    {c k : Nat} (hc : (pl.children.getD pl.rm.clusters.length [])[k]? = some c) :
    alloc.lefts.getD pl.rm.clusters.length 0 = 0 ∧
    alloc.lefts.getD c 0 = pl.buckets.widths.getD pl.rm.clusters.length 0 +
      (((pl.children.getD pl.rm.clusters.length []).take k).map fun c' =>
        (reserveWidths pl P).getD c' 0).sum := by
  let root := pl.rm.clusters.length
  let initial := dcpInit pl xs
  obtain ⟨final, hf, hfinal⟩ := dcpAllocationFinal ha
  have hnoRoot : ∀ g ∈ pl.order, root ∉ pl.children.getD g [] := by
    intro g _ hc
    have hfalse := ((hrows g).2 root hc).1
    exact (Nat.lt_irrefl root) hfalse
  have hzero := allocateGroups_left_lookup (pl := pl) (P := P) hnoRoot hf
  rw [hfinal] at hzero
  change alloc.lefts.getD root 0 = (List.replicate (root + 1) (0 : Int)).getD root 0 at hzero
  have hzero' : alloc.lefts.getD root 0 = 0 := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt (Nat.lt_succ_self root),
      Option.getD_some] using hzero
  unfold dcpFold at hf
  rw [horder, List.foldlM_cons] at hf
  obtain ⟨after, hstep, hpost⟩ := dcpBind hf
  obtain ⟨hcBound, hcParent⟩ := (hrows root).2 c (List.mem_of_getElem? hc)
  have htNot : root ∉ tail := by rw [horder] at hnd; exact (List.nodup_cons.mp hnd).1
  have havoid : ∀ g ∈ tail, c ∉ pl.children.getD g [] := by
    intro g hg hgC
    have he := ((hrows g).2 c hgC).2.symm.trans hcParent
    exact htNot (he ▸ hg)
  have hstable := allocateGroups_left_lookup (pl := pl) (P := P) havoid hpost
  rw [hfinal] at hstable
  have hbound : c < initial.2.1.length := by
    change c < (List.replicate (root + 1) (0 : Int)).length
    simp only [List.length_replicate]
    exact Nat.lt_succ_of_lt hcBound
  have hcLeft := allocateGroup_child_left hstep (hrows root).1 hc hbound
  change after.2.1.getD c 0 =
    (List.replicate (root + 1) (0 : Int)).getD root 0 +
    (if root != root then pl.minimum.origins.getD root 0 else 0) +
    pl.buckets.widths.getD root 0 + _ at hcLeft
  exact ⟨hzero', hstable.trans (by
    rw [show (List.replicate (root + 1) (0 : Int)).getD root 0 = 0 from by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt (Nat.lt_succ_self root),
        Option.getD_some]] at hcLeft
    simpa using hcLeft)⟩

private def dcpStart (pl : RegionPlacement) (alloc : RegionAllocation) (g : Nat) : Int :=
  alloc.lefts.getD g 0 +
    (if g != pl.rm.clusters.length then pl.minimum.origins.getD g 0 else 0)

private theorem dcpStagesGap {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    {s : RegionSpec} {inp : Input} {candidate : Graph}
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hmin : constrainR rm P p = .ok minimum)
    (hinset : 0 ≤ regionInsetOf P) (hslot : 0 ≤ P.slot) :
    let pl := stages.placement
    pl.order.Pairwise (fun a b =>
      dcpStart pl stages.allocation a + pl.buckets.widths.getD a 0 ≤
        dcpStart pl stages.allocation b) := by
  let pl := stages.placement
  let alloc := stages.allocation
  let root := rm.clusters.length
  let kids (g : Nat) := pl.children.getD g []
  let left (g : Nat) := alloc.lefts.getD g 0
  let first (g : Nat) := dcpStart pl alloc g
  let own (g : Nat) := pl.buckets.widths.getD g 0
  let last (g : Nat) := first g + own g
  let w (g : Nat) := (reserveWidths pl P).getD g 0
  let right (g : Nat) := if g < root then left g + w g else last g + ((kids g).map w).sum
  have hparents := activeRegion_parent_count hactive
  have hrm : pl.rm = rm := by change stages.placement.rm = rm; rw [stages.hPlacement]
  have hminPl : pl.minimum = minimum := by
    change stages.placement.minimum = minimum
    rw [stages.hPlacement]
  obtain ⟨hclen, hrows, hnd, _, _, _, tail, hroot⟩ := dcpStageTopology stages hparents hmin
  obtain ⟨hown, hlane, hloop⟩ := stages.bucket_signs hslot
  have hw : ∀ g, 0 ≤ w g := reserveWidths_nonnegative hinset hown hlane hloop
  have hstart (g : Nat) : first g = left g + (if g < root then regionInsetOf P else 0) := by
    change alloc.lefts.getD g 0 +
      (if g != pl.rm.clusters.length then pl.minimum.origins.getD g 0 else 0) =
      alloc.lefts.getD g 0 + (if g < root then regionInsetOf P else 0)
    rw [hrm, hminPl, constrainR_origins hmin, hparents]
    by_cases hg : g < root
    · have hne : (g != rm.clusters.length) = true := bne_iff_ne.mpr (Nat.ne_of_lt hg)
      have horigin : (List.replicate rm.clusters.length (regionInsetOf P)).getD g 0 =
          regionInsetOf P := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hg, Option.getD_some]
      rw [ite_eq_left hne, ite_eq_left hg, horigin]
    · have hnone : (List.replicate rm.clusters.length (regionInsetOf P))[g]? = none :=
        List.getElem?_eq_none_iff.mpr (by
          simpa only [List.length_replicate] using Nat.le_of_not_gt hg)
      have horigin : (List.replicate rm.clusters.length (regionInsetOf P)).getD g 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
      rw [ite_eq_right hg, horigin, ite_self]
  have hroom (g : Nat) (hg : g < root) :
      2 * regionInsetOf P + own g + ((kids g).map w).sum ≤ w g := by
    obtain ⟨_, _, horder, hnot, hread⟩ :=
      (stages.reservation_order hparents hmin).2 g (Nat.le_of_lt hg)
    have hgPl : g < pl.rm.clusters.length := by rw [hrm]; exact hg
    have hraw := reserveWidths_room_from_last_writes (pl := pl) (P := P) horder hgPl hnot hread
    have hln : 0 ≤ laneExtentOf pl.buckets P.slot g := hlane g
    have hlp : 0 ≤ pl.buckets.loopWidth.getD g 0 := hloop g
    change 2 * regionInsetOf P + own g + ((kids g).map w).sum +
      laneExtentOf pl.buckets P.slot g ≤ w g - pl.buckets.loopWidth.getD g 0 at hraw
    omega
  have hLeft (g : Nat) : left g ≤ first g := by
    rw [hstart]
    split <;> omega
  have hRight (g : Nat) : last g ≤ right g := by
    have hsum : 0 ≤ ((kids g).map w).sum := by
      simpa only [List.take_length] using dcpPrefixNonneg w hw (kids g) (kids g).length
    by_cases hg : g < root
    · have hr := hroom g hg
      change first g + own g ≤ if g < root then left g + w g else _
      rw [ite_eq_left hg, hstart g, ite_eq_left hg]
      omega
    · change last g ≤ if g < root then _ else last g + ((kids g).map w).sum
      rw [ite_eq_right hg]
      exact Int.le_add_of_nonneg_right hsum
  have hChild (g i c : Nat) (hc : (kids g)[i]? = some c) :
      left c = last g + (((kids g).take i).map w).sum := by
    by_cases hg : g < root
    · change left c = first g + own g + (((kids g).take i).map w).sum
      rw [hstart g, ite_eq_left hg]
      have hne : g ≠ rm.clusters.length := Nat.ne_of_lt hg
      simpa only [ite_eq_right hne] using
        stages.childBudget_left_from_allocation (owner := g) (child := c) (k := i)
          hactive hmin (Nat.le_of_lt hg) hc
    · have hbound : g < pl.children.length := by
        apply Classical.byContradiction
        intro h
        have hn : pl.children[g]? = none := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt h)
        have he : kids g = [] := by
          change pl.children.getD g [] = []
          rw [List.getD_eq_getElem?_getD, hn, Option.getD_none]
        rw [he] at hc
        cases hc
      change pl.children.length = root + 1 at hclen
      have hg' : g = root := by omega
      subst g
      have ho : pl.order = pl.rm.clusters.length :: tail := by rw [hrm]; exact hroot
      have hr : ∀ i, (pl.children.getD i []).Nodup ∧ ∀ j ∈ pl.children.getD i [],
          j < pl.rm.clusters.length ∧ parentGroup pl.rm j = i := by rw [hrm]; exact hrows
      have hslot' : (pl.children.getD pl.rm.clusters.length [])[i]? = some c := by
        rw [hrm]
        exact hc
      obtain ⟨hzero, hleft⟩ := dcpRootChildLeft (pl := pl) (P := P)
        stages.hAllocation ho hnd hr hslot'
      rw [hrm] at hzero hleft
      change left root = 0 at hzero
      change left c = first root + own root + (((kids root).take i).map w).sum
      rw [hstart root, ite_eq_right (Nat.lt_irrefl root), hzero, Int.add_zero, Int.zero_add]
      exact hleft
  have hChildren (g : Nat) : (kids g).Pairwise (fun a b => right a ≤ left b) ∧
      ∀ c ∈ kids g, left g ≤ left c ∧ last g ≤ left c ∧ right c ≤ right g := by
    constructor
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have ha : (kids g)[i]? = some (kids g)[i] := List.getElem?_eq_getElem hi
      have hb : (kids g)[j]? = some (kids g)[j] := List.getElem?_eq_getElem hj
      have hlt := ((hrows g).2 _ (List.mem_of_getElem? ha)).1
      have ha' := hChild g i _ ha
      have hb' := hChild g j _ hb
      have hpre := dcpSumLookup w hw ha hij
      rw [show right (kids g)[i] = left (kids g)[i] + w (kids g)[i] from ite_eq_left hlt,
        ha', hb', Int.add_assoc]
      exact Int.add_le_add_left hpre (last g)
    · intro c hc
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
      have hsum := dcpPrefixNonneg w hw (kids g) i
      have hz := hChild g i c hi
      have hlast : left g ≤ last g :=
        Int.le_trans (hLeft g) (Int.le_add_of_nonneg_right (hown g))
      have hchildStart : last g ≤ left c := by
        rw [hz]
        exact Int.le_add_of_nonneg_right hsum
      refine ⟨Int.le_trans hlast hchildStart, hchildStart, ?_⟩
      have hcLt := ((hrows g).2 c hc).1
      have hlimit := (List.getElem?_eq_some_iff.mp hi).1
      have hpre := dcpSumLookup w hw hi hlimit
      rw [List.take_length] at hpre
      rw [show right c = left c + w c from ite_eq_left (show c < root from hcLt), hz]
      by_cases hg : g < root
      · have hr := hroom g hg
        change last g + (((kids g).take i).map w).sum + w c ≤
          if g < root then left g + w g else _
        unfold last
        rw [ite_eq_left hg, hstart g, ite_eq_left hg]
        omega
      · change _ ≤ if g < root then _ else last g + ((kids g).map w).sum
        rw [ite_eq_right hg, Int.add_assoc]
        exact Int.add_le_add_left hpre (last g)
  have hwalk : DcpWalk kids [root] pl.order := by
    obtain ⟨visits, he, hwalk⟩ := dcpWalkOfPreorder stages.children (stages.children.length + 1)
      [root] []
    have hout : pl.order = visits := by
      change stages.placement.order = visits
      rw [stages.hPlacement]
      simpa only [List.reverse_singleton, List.nil_append] using he
    rw [hout]
    change DcpWalk (fun g => pl.children.getD g []) [root] visits
    have hcs : pl.children = stages.children := by
      change stages.placement.children = stages.children
      rw [stages.hPlacement]
    rwa [hcs]
  exact (dcpWalkGap (fun g => ⟨hLeft g, hRight g⟩) hChildren hwalk
    (List.pairwise_singleton _ _)).1

theorem activeDifferentBuckets_gap {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    {s : RegionSpec} {inp : Input} {candidate : Graph}
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hmin : constrainR rm P p = .ok minimum)
    (hinset : 0 ≤ regionInsetOf P) (hslot : 0 ≤ P.slot)
    {a b : Nat} (ha : a ≤ rm.clusters.length) (hb : b ≤ rm.clusters.length) (hne : a ≠ b) :
    let first (g : Nat) := stages.allocation.lefts.getD g 0 +
      (if g = rm.clusters.length then 0 else regionInsetOf P)
    let last (g : Nat) := first g + stages.placement.buckets.widths.getD g 0
    last a ≤ first b ∨ last b ≤ first a := by
  have hparents := activeRegion_parent_count hactive
  obtain ⟨_, _, _, _, _, hmembers, _⟩ := dcpStageTopology stages hparents hmin
  have hpair := dcpStagesGap stages hactive hmin hinset hslot
  have hrm : stages.placement.rm = rm := by rw [stages.hPlacement]
  have hminimum : stages.placement.minimum = minimum := by rw [stages.hPlacement]
  have hfirst {g : Nat} (hg : g ≤ rm.clusters.length) :
      dcpStart stages.placement stages.allocation g =
        stages.allocation.lefts.getD g 0 + (if g = rm.clusters.length then 0 else regionInsetOf P) := by
    unfold dcpStart
    rw [hrm, hminimum]
    by_cases he : g = rm.clusters.length
    · simp [he]
    · have hlt := Nat.lt_of_le_of_ne hg he
      have horigin : (List.replicate rm.clusters.length (regionInsetOf P)).getD g 0 =
          regionInsetOf P := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hlt, Option.getD_some]
      rw [ite_eq_left (bne_iff_ne.mpr he), ite_eq_right he, constrainR_origins hmin,
        hparents, horigin]
  rcases OrderImpl.pairwise_ne_cases hpair (hmembers a ha) (hmembers b hb) hne with hab | hba
  · exact Or.inl (by simpa only [hfirst ha, hfirst hb] using hab)
  · exact Or.inr (by simpa only [hfirst ha, hfirst hb] using hba)

private theorem dcpNodeOwnerBound {rm : ComponentRegions} {p : Proper} {owners : List Nat}
    (ho : nodeGroupsOf rm p = .ok owners) {v : Nat} {n : ProperNode}
    (hn : p.nodes[v]? = some n) :
    owners.getD v 0 ≤ rm.clusters.length := by
  let owner (q : ProperNode × Nat) : Except LayoutError Nat :=
    match q.1.node.clusterPath.getLast? with
    | none => pure rm.clusters.length
    | some decl =>
      match clusterOfDecl rm decl with
      | some k => pure k
      | none => throw .domain
  have hmap : p.nodes.zipIdx.mapM owner = .ok owners := ho
  have hzip : p.nodes.zipIdx[v]? = some (n, v) := by
    simp only [List.getElem?_zipIdx, hn, Option.map_some, Nat.zero_add]
  obtain ⟨g, hcall, hget⟩ :=
    (mapM_getElem? owner p.nodes.zipIdx owners hmap).2 v (n, v) hzip
  rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  dsimp only [owner] at hcall
  cases hp : n.node.clusterPath.getLast? with
  | none =>
    have he : (Except.ok rm.clusters.length : Except LayoutError Nat) = .ok g := by
      simpa only [hp, Pure.pure, Except.pure] using hcall
    exact (Except.ok.inj he) ▸ Nat.le_refl rm.clusters.length
  | some d =>
    cases hd : clusterOfDecl rm d with
    | none =>
      simp only [hp, hd, throw, throwThe, MonadExceptOf.throw] at hcall
      cases hcall
    | some k =>
      have he : (Except.ok k : Except LayoutError Nat) = .ok g := by
        simpa only [hp, hd, Pure.pure, Except.pure] using hcall
      unfold clusterOfDecl at hd
      obtain ⟨hk, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hd
      rw [← Except.ok.inj he]
      exact Nat.le_of_lt hk

private theorem dcpShiftSum (visits : List (Nat × Int)) (g : Nat) (dx : Int)
    (hnd : (visits.map Prod.fst).Nodup) (hmem : (g, dx) ∈ visits) :
    (visits.map fun q => if q.1 = g then q.2 else 0).sum = dx := by
  have hnone (rs : List (Nat × Int)) (hout : g ∉ rs.map Prod.fst) :
      (rs.map fun q => if q.1 = g then q.2 else 0).sum = 0 := by
    induction rs with
    | nil => rfl
    | cons q qs ih =>
      have hne : q.1 ≠ g := fun he =>
        hout (List.mem_map.mpr ⟨q, List.mem_cons_self, he⟩)
      have htail : g ∉ qs.map Prod.fst := fun hg =>
        hout (List.mem_cons_of_mem _ hg)
      simp only [List.map_cons, List.sum_cons, ite_eq_right hne, ih htail, Int.zero_add]
  induction visits with
  | nil => simp at hmem
  | cons q qs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hmem with rfl | hm
    · change (if g = g then dx else 0) +
        (qs.map fun q => if q.1 = g then q.2 else 0).sum = dx
      rw [ite_eq_left (Eq.refl g), hnone qs hnot, Int.add_zero]
    · have hne : q.1 ≠ g := by
        intro he
        apply hnot
        exact List.mem_map.mpr ⟨(g, dx), hm, he.symm⟩
      simp only [List.map_cons, List.sum_cons, ite_eq_right hne, ih htail hm, Int.zero_add]

private theorem dcpAllocatedCenter {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum)
    {v : Nat} {n : ProperNode} (hn : p.nodes[v]? = some n) (hpn : n.node.border = 0) :
    let pl := stages.placement
    let g := stages.groups.getD v 0
    g ∈ pl.order ∧ v ∈ pl.buckets.members.getD g [] ∧
    stages.shifted.getD v 0 =
      stages.before.getD v 0 + dcpStart pl stages.allocation g - pl.buckets.low.getD g 0 := by
  let pl := stages.placement
  let g := stages.groups.getD v 0
  have hg := dcpNodeOwnerBound stages.hGroups hn
  obtain ⟨_, _, hnd, hEarlier, hSelf, hMembers, _⟩ := dcpStageTopology stages hparents hmin
  have hm : g ∈ pl.order := hMembers g hg
  have hcount (k : Nat) : (pl.buckets.members.getD k []).count v = if k = g then 1 else 0 := by
    change (stages.placement.buckets.members.getD k []).count v = _
    rw [stages.hPlacement]
    have hc := newRegionBuckets_count
      rm cg p stages.groups
      (cg.edges.map fun e => (stackSize cg.slot (routeLabels labels e.decl)).width)
      stages.before k v hn hpn
    rw [hc]
    by_cases he : k = g
    · subst k
      have hyes : g < rm.clusters.length + 1 ∧ stages.groups.getD v 0 = g :=
        ⟨Nat.lt_succ_of_le hg, rfl⟩
      rw [ite_eq_left hyes, ite_eq_left (Eq.refl g)]
    · have hno : ¬ (k < rm.clusters.length + 1 ∧ stages.groups.getD v 0 = k) :=
        fun hk => he hk.2.symm
      rw [ite_eq_right hno, ite_eq_right he]
  have hmem : v ∈ pl.buckets.members.getD g [] := by
    have hc : (pl.buckets.members.getD g []).count v = 1 :=
      (hcount g).trans (ite_eq_left (Eq.refl g))
    exact List.count_pos_iff.mp (by simpa only [hc] using Nat.zero_lt_succ 0)
  obtain ⟨visits, hvOrder, hVisit, _, hTrace⟩ := allocatePl_translation_trace stages.hAllocation
  have hIn : g ∈ visits.map Prod.fst := by rwa [hvOrder]
  obtain ⟨q, hq, hqg⟩ := List.mem_map.mp hIn
  obtain ⟨qg, dx⟩ := q
  change qg = g at hqg
  subst qg
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hq
  obtain ⟨before, hBefore, hShift⟩ := hVisit k g dx hk
  have hget : pl.order[k]? = some g := by
    rw [← hvOrder, List.getElem?_map, hk, Option.map_some]
  obtain ⟨pre, post, hSplit, hkLen⟩ : ∃ pre post, pl.order = pre ++ g :: post ∧ pre.length = k := by
    refine ⟨pl.order.take k, pl.order.drop (k + 1), ?_, ?_⟩
    · have htail := List.take_append_drop (k + 1) pl.order
      rw [List.take_add_one, hget, Option.toList_some, List.append_assoc, List.singleton_append] at htail
      exact htail.symm
    · have hbound := (List.getElem?_eq_some_iff.mp hget).1
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hbound)]
  have hpreTake : pl.order.take k = pre := by
    rw [hSplit, ← hkLen, List.take_left]
  rw [hpreTake] at hBefore
  have hAvoid : ∀ j ∈ g :: post, g ∉ pl.children.getD j [] := by
    rw [hSplit] at hEarlier
    have hPost := (List.pairwise_cons.mp (List.pairwise_append.mp hEarlier).2.1).1
    intro j hj
    rcases List.mem_cons.mp hj with hj | hj
    · rw [hj]
      exact hSelf g hm
    · exact hPost j hj
  have hRead := dcpTraceLeft stages.hAllocation hSplit hBefore hAvoid
  have hvBound : v < stages.before.length := by
    rw [CoordsImpl.crossCoordsClusterWith_length stages.hCross]
    exact (List.getElem?_eq_some_iff.mp hn).1
  have hTrace' := hTrace v hvBound
  have hdisp :
      (visits.map fun q => ((pl.buckets.members.getD q.1 []).count v : Int) * q.2).sum = dx := by
    rw [show (visits.map fun q => ((pl.buckets.members.getD q.1 []).count v : Int) * q.2) =
      visits.map (fun q => if q.1 = g then q.2 else 0) from by
        apply List.map_congr_left
        intro q _
        rw [hcount]
        split <;> simp]
    exact dcpShiftSum visits g dx (by rwa [hvOrder]) hq
  rw [hdisp, hShift] at hTrace'
  unfold regionBucketShift at hTrace'
  rw [hRead] at hTrace'
  change stages.shifted.getD v 0 = stages.before.getD v 0 +
    (dcpStart pl stages.allocation g - pl.buckets.low.getD g 0) at hTrace'
  refine ⟨hm, hmem, ?_⟩
  change stages.shifted.getD v 0 =
    stages.before.getD v 0 + dcpStart pl stages.allocation g - pl.buckets.low.getD g 0
  omega

theorem componentRunR_active_plain_same_rank_gap {P : Params} {exactIds : List String} {s : RegionSpec}
    {inp : Input} {candidate cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {o : Options}
    (hParams : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp candidate labels orderOptions =
      .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    {a b : Nat} {an bn : Node} (ha : cg.nodes[a]? = some an) (hb : cg.nodes[b]? = some bn)
    (hpa : an.border = 0) (hpb : bn.border = 0) (hab : a ≠ b)
    (hr : (rk run.proper.rank a).toNat = (rk run.proper.rank b).toNat) :
    R8a_OverlapRowsXGap (frameRect P cg run a) (frameRect P cg run b) := by
  obtain ⟨_, _, labeled, p, minimum, _, _, _, hRank, hNorm, hLabels, hCoord, hMin, _, ⟨stages⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  let pl := stages.placement
  let g (v : Nat) := stages.groups.getD v 0
  let w (v : Nat) := CoordsImpl.nodeW p v
  let first (owner : Nat) := dcpStart pl stages.allocation owner
  let bw (owner : Nat) := pl.buckets.widths.getD owner 0
  let x (v : Nat) := stages.before.getD v 0
  let low (owner : Nat) := pl.buckets.low.getD owner 0
  let r (v : Nat) := frameRect P cg run v
  have hpPl : pl.p = p := by change stages.placement.p = p; rw [stages.hPlacement]
  have hrmPl : pl.rm = rm := by change stages.placement.rm = rm; rw [stages.hPlacement]
  have hparents := activeRegion_parent_count hactive
  obtain ⟨hgap, hrecords⟩ := componentRunR_region_plain_cross_geometry hrun
  obtain ⟨la, hla, hamem, _⟩ :=
    (componentRunR_plain_rank_bands (exactIds := exactIds) hrun).1 (v := a) (source := an) ha hpa
  obtain ⟨lb, hlb, hbmem, _⟩ :=
    (componentRunR_plain_rank_bands (exactIds := exactIds) hrun).1 (v := b) (source := bn) hb hpb
  rw [← hr] at hlb
  have hlEq := Option.some.inj (hla.symm.trans hlb)
  have hLayer : la ∈ run.layers := List.mem_of_getElem? hla
  have hbLayer : b ∈ la := hlEq.symm ▸ hbmem
  have hframeNode {v : Nat} {src : Node} (hsrc : cg.nodes[v]? = some src) (hplain : src.border = 0) :
      ∃ n : ProperNode, p.nodes[v]? = some n ∧ n.node.border = 0 ∧
        (r v).x = run.xs.getD v 0 - n.node.w / 2 ∧ (r v).w = n.node.w ∧
        g v ∈ pl.order ∧ run.xs.getD v 0 = x v + first (g v) - low (g v) ∧
        first (g v) ≤ (r v).x ∧ (r v).x + (r v).w ≤ first (g v) + bw (g v) := by
    obtain ⟨n, hnc, hbdr, _⟩ :=
      source_coordinate_record P (exactDecls exactIds inp) s
        (addLabelNodes_untouched_node hLabels (normalize_node_record hNorm hsrc) rfl)
    have hbdr' := hbdr.trans hplain
    have haAway := resolved_anchors_not_plain (exact := exactDecls exactIds inp)
      (labels := labels) hactive hRank hNorm hLabels hnc hbdr'
    rw [hCoord] at hnc
    have hnPl : pl.p.nodes[v]? = some n := by rw [hpPl]; exact hnc
    have haAwayPl : NotClusterAnchor pl.rm v := by rw [hrmPl]; exact haAway
    obtain ⟨hxCoord, hnCoord⟩ :=
      regionFrames_reservedPorts_plain (pl := pl) (P := P) (alloc := stages.allocation)
        stages.hFramesAndPorts hnPl hbdr' haAwayPl
    obtain ⟨m, hmCoord, hmProper, _, hxRun⟩ := hrecords hsrc hplain
    rw [hnPl, hmCoord] at hnCoord
    have he : m = n := Option.some.inj hnCoord
    subst m
    obtain ⟨horder, hmem, hxShift⟩ := dcpAllocatedCenter stages hparents hMin hnc hbdr'
    have hRunX := hxRun.trans (hxCoord.trans hxShift)
    have hrect := plain_frame_cross_rect (P := P) hsrc hplain hmProper hxRun
    have hxRect : (r v).x = run.xs.getD v 0 - n.node.w / 2 := by
      change (frameRect P cg run v).x = _
      simp only [hrect, hxRun, Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))]
    have hwRect : (r v).w = n.node.w := congrArg Rect.w hrect
    have hHull := stages.bucket_width_and_hull.2 (g v) v hmem
    rw [hpPl] at hHull
    have hWidth : n.node.w ≤ w v := by simpa only [hnc] using CoordsImpl.nodeW_ge_width p v
    have hSize := (CoordsImpl.crossCoordsClusterWith_spec stages.hCross).2.2.2.1
    have hwNonneg : 0 ≤ w v := CoordsImpl.nodeW_nonneg hSize v
    have hwe := Int.tdiv_eq_ediv_of_nonneg (b := 2) hwNonneg
    change low (g v) ≤ x v - Int.tdiv (w v) 2 ∧
      x v - Int.tdiv (w v) 2 + w v ≤ low (g v) + bw (g v) at hHull
    rw [hwe] at hHull
    obtain ⟨hLower, hUpper⟩ := hHull
    have hHalf : n.node.w / 2 ≤ w v / 2 := Int.ediv_le_ediv (by decide) hWidth
    have hOtherHalf : n.node.w - n.node.w / 2 ≤ w v - w v / 2 := by omega
    change run.xs.getD v 0 = x v + first (g v) - low (g v) at hRunX
    refine ⟨n, hnc, hbdr', hxRect, hwRect, horder, hRunX, ?_, ?_⟩
    · rw [hxRect, hRunX]
      omega
    · rw [hxRect, hwRect, hRunX]
      omega
  obtain ⟨ma, hma, hba, hxa, hwa, hga, hxa', hla', hra⟩ := hframeNode ha hpa
  obtain ⟨mb, hmb, hbb, hxb, hwb, hgb, hxb', hlb', hrb⟩ := hframeNode hb hpb
  unfold R8a_OverlapRowsXGap
  intro _ _ _
  change (r a).x + (r a).w ≤ (r b).x ∨ (r b).x + (r b).w ≤ (r a).x
  by_cases hOwner : g a = g b
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hamem
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hbLayer
    have hne : i ≠ j := by
      intro he
      rw [he] at hi
      exact hab (Option.some.inj (hi.symm.trans hj))
    rw [hOwner] at hxa'
    have hwa' : ma.node.w ≤ w a := by simpa only [hma] using CoordsImpl.nodeW_ge_width p a
    have hwb' : mb.node.w ≤ w b := by simpa only [hmb] using CoordsImpl.nodeW_ge_width p b
    have hHalfA : ma.node.w / 2 ≤ w a / 2 := Int.ediv_le_ediv (by decide) hwa'
    have hHalfB : mb.node.w / 2 ≤ w b / 2 := Int.ediv_le_ediv (by decide) hwb'
    have hOtherHalfA : ma.node.w - ma.node.w / 2 ≤ w a / 2 + 1 := by omega
    have hOtherHalfB : mb.node.w - mb.node.w / 2 ≤ w b / 2 + 1 := by omega
    rcases Nat.lt_or_gt_of_ne hne with hij | hji
    · left
      have hs := crossCoordsClusterWith_plain_order stages.hCross hLayer hij hi hj hma hba
      change Int.fdiv (w a) 2 + Int.fdiv (w b) 2 + min P.nodeGap P.clusterPad ≤ x b - x a at hs
      simp only [Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))] at hs
      rw [hxa, hwa, hxb, hxa', hxb']
      omega
    · right
      have hs := crossCoordsClusterWith_plain_order stages.hCross hLayer hji hj hi hmb hbb
      change Int.fdiv (w b) 2 + Int.fdiv (w a) 2 + min P.nodeGap P.clusterPad ≤ x a - x b at hs
      simp only [Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))] at hs
      rw [hxb, hwb, hxa, hxa', hxb']
      omega
  · have hinset : 0 ≤ regionInsetOf P := by
      have hp := (checkedParams_sizing_nonneg hParams).2.1
      have hw := checkedParams_clusterBorderW_ge_one hParams
      unfold regionInsetOf
      omega
    have hslot : 0 ≤ P.slot :=
      Int.le_trans (by decide : (0 : Int) ≤ 1) (componentRunR_slot_pos hrun)
    have hsep := dcpStagesGap stages hactive hMin hinset hslot
    rcases OrderImpl.pairwise_ne_cases hsep hga hgb hOwner with habGap | hbaGap
    · exact Or.inl (Int.le_trans hra (Int.le_trans habGap hlb'))
    · exact Or.inr (Int.le_trans hrb (Int.le_trans hbaGap hla'))

theorem r8a_selected_demoted_cross_parent {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    {g b : Box} (pair : R8a_SelectedPair execution g b)
    (hg : pair.uNode.border = 0) (hb : pair.wNode.border = 0)
    (_hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == pair.sourceGroup.id) = true)
    (hrank : (rk pair.selected.run.proper.rank pair.u).toNat =
      (rk pair.selected.run.proper.rank pair.w).toNat)
    (_hparent : pair.sourceGroup.parent ≠ pair.sourcePeer.parent) :
    R8a_OverlapRowsXGap
      (frameRect execution.params pair.selected.cg pair.selected.run pair.u)
      (frameRect execution.params pair.selected.cg pair.selected.run pair.w) := by
  have hrun := pair.selected.run_eq
  rw [pair.active] at hrun
  have hregions : newComponentRegions pair.selected.spec execution.params inp
      (componentCandidateR pair.selected.spec execution.graph pair.part.1
        pair.selected.candidate) = .ok pair.selected.regions := by
    rw [pair.selected.effective_eq]
    exact componentTrialR_selected_regions _ pair.selected.regions_eq
  rw [pair.active] at hregions
  have hsome : ∃ rm, pair.selected.regions = some rm := by
    cases hreg : pair.selected.regions with
    | none =>
      have heff := pair.selected.effective_eq
      rw [pair.active, hreg] at heff
      simp at heff
    | some rm => exact ⟨rm, rfl⟩
  obtain ⟨rm, hrm⟩ := hsome
  rw [hrm] at hregions
  have hne : pair.u ≠ pair.w := by
    intro he
    have hu := pair.group_pos
    rw [he] at hu
    exact pair.decl_ne (Option.some.inj (hu.symm.trans pair.peer_pos))
  exact componentRunR_active_plain_same_rank_gap execution.checked hrun hregions
    pair.group_node pair.peer_node hg hb hne hrank



end Elegant.Layered.PipelineImpl
