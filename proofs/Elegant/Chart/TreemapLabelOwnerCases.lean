import Elegant.Chart.TreemapC8bKernelFacts
import Elegant.Chart.TreemapLabelFacts
import Elegant.Chart.TreemapLabelFacts3
import Elegant.Kinds.Treemap

namespace Elegant.Treemap.C8b

open Elegant.Treemap
open Elegant.Treemap.C8a
open Elegant.Treemap.CanvasC1
open Elegant.Treemap.LabelFacts
open Elegant.Treemap.LabelFacts3

variable {m : Model}

set_option autoImplicit false

/-! ### String suffix helpers -/

/-- `".value"` and `".name"` cannot be the suffixes of equal strings. -/
private theorem suffix_ne_value_name (a b : String) :
    a ++ ".value" ≠ b ++ ".name" := by
  intro h
  have h6 : ".value".length = 6 := rfl
  have h5 : ".name".length = 5 := rfl
  have hlen : a.length + 6 = b.length + 5 := by
    have h2 := congrArg String.length h
    simp only [String.length_append, h6, h5] at h2
    exact h2
  have hto := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at hto
  have hhd := congrArg (fun l : List Char => List.drop b.length l) hto
  rw [List.drop_append, List.drop_append] at hhd
  have hb : b.toList.length = b.length := String.length_toList
  have ha : a.toList.length = a.length := String.length_toList
  rw [hb, ha] at hhd
  have hsub1 : b.length - a.length = 1 := by omega
  rw [hsub1] at hhd
  have hdropa : List.drop b.length a.toList = [] := by
    apply List.drop_of_length_le
    rw [ha]; omega
  have hdropb : List.drop b.length b.toList = [] := by
    apply List.drop_of_length_le
    rw [hb]
    exact Nat.le_refl _
  rw [hdropa, List.nil_append, hdropb, List.nil_append, Nat.sub_self,
    List.drop_zero] at hhd
  revert hhd
  decide

/-- Cancelling a common `".name"` suffix. -/
private theorem append_name_cancel {a b : String} (h : a ++ ".name" = b ++ ".name") :
    a = b := by
  have h2 := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_right h2)

/-- Cancelling a common `".value"` suffix. -/
private theorem append_value_cancel {a b : String} (h : a ++ ".value" = b ++ ".value") :
    a = b := by
  have h2 := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_right h2)

/-- `"title"` is not a `".name"`-suffixed string. -/
private theorem title_ne_name (a : String) : a ++ ".name" ≠ "title" := by
  intro h
  have h5 : ".name".length = 5 := rfl
  have h6 : "title".length = 5 := rfl
  have h2 := congrArg String.length h
  simp only [String.length_append, h5, h6] at h2
  have ha : a.length = 0 := by omega
  have ha' : a = "" := String.length_eq_zero_iff.mp ha
  rw [ha', String.empty_append] at h
  revert h
  decide

/-- `"title"` is not a `".value"`-suffixed string. -/
private theorem title_ne_value (a : String) : a ++ ".value" ≠ "title" := by
  intro h
  have h6 : ".value".length = 6 := rfl
  have h5 : "title".length = 5 := rfl
  have h2 := congrArg String.length h
  simp only [String.length_append, h6, h5] at h2
  omega

/-- A checked `width` call is nonnegative. -/
private theorem width_nonneg {cell : Bool} {text : String} {role : Measure.Role}
    {size x : Int} {fontFamily : Bool} (h : width cell text role size fontFamily = .ok x) : 0 ≤ x := by
  unfold width at h
  obtain ⟨metric, _, hw⟩ := CanvasC1.except_bind_ok h
  exact Measure.textWidth_nonneg hw

/-! ### Constants bridges -/

/-- The profile header constant in `if` form. -/
private theorem constants_header_eq (m : Model) :
    (constants m).header = if (m.profile == .cell) then 2 else 1600 := by
  unfold constants
  cases m.profile <;> simp [LayoutConst.treemap_section_header, LayoutConst.Pair.get]

/-- The header label inset is positive in both profiles. -/
private theorem header_ni_pos (m : Model) :
    0 < LayoutConst.treemap_header_label_inset.get m.profile := by
  cases m.profile <;> decide

/-- The header value inset is positive in both profiles. -/
private theorem header_vi_pos (m : Model) :
    0 < LayoutConst.treemap_header_value_inset.get m.profile := by
  cases m.profile <;> decide

/-- The header gap is nonnegative in both profiles. -/
private theorem header_gap_nonneg (m : Model) :
    0 ≤ LayoutConst.treemap_header_gap.get m.profile := by
  cases m.profile <;> decide

/-- The header top offset is positive in both profiles. -/
private theorem header_top_pos (m : Model) (c : Consts) (lh top : Int)
    (hlh : lh = if (m.profile == .cell) then 1 else 1280)
    (hch : c.header = if (m.profile == .cell) then 2 else 1600)
    (htop : top = LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile - lh) 2) :
    0 < top := by
  cases hmp : m.profile with
  | vector =>
    have hcpf : (m.profile == .cell) = false := by rw [hmp]; rfl
    have hl2 : lh = 1280 := by rw [hlh, hcpf]; rfl
    have hh2 : c.header = 1600 := by rw [hch, hcpf]; rfl
    have hb : LayoutConst.treemap_header_border.get m.profile = 0 := by
      rw [hmp]; rfl
    have hf : Int.fdiv ((1600 : Int) - 0 - 1280) 2 = 160 := by decide
    rw [htop, hb, hh2, hl2, hf]
    decide
  | cell =>
    have hcp : (m.profile == .cell) = true := by rw [hmp]; rfl
    have hl2 : lh = 1 := by rw [hlh, hcp]; rfl
    have hh2 : c.header = 2 := by rw [hch, hcp]; rfl
    have hb : LayoutConst.treemap_header_border.get m.profile = 1 := by
      rw [hmp]; rfl
    have hf : Int.fdiv ((2 : Int) - 1 - 1) 2 = 0 := by decide
    rw [htop, hb, hh2, hl2, hf]
    decide

/-- The written name rectangle of a header step keeps a positive distance from
every side of the node's tile. -/
private theorem header_name_rect_strict (m : Model) (c : Consts) (n : Node)
    (text shown : String) (ns w vw lh top ni vi reserve avail : Int)
    (showValue : Bool)
    (hfit : fit (m.profile == .cell) text avail .label ns m.options.fontFamily = .ok (some (shown, w)))
    (hlh : lh = if (m.profile == .cell) then 1 else 1280)
    (hch : c.header = if (m.profile == .cell) then 2 else 1600)
    (htop : top = LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile - lh) 2)
    (hhgt : ¬((tileRect n.rect).h ≤ top + lh))
    (havail : avail = if showValue then (tileRect n.rect).w - ni - reserve
      else (tileRect n.rect).w - 2 * ni)
    (hreserve : reserve = vi + vw + LayoutConst.treemap_header_gap.get m.profile)
    (hni : ni = LayoutConst.treemap_header_label_inset.get m.profile)
    (hvi : vi = LayoutConst.treemap_header_value_inset.get m.profile)
    (hvw0 : 0 ≤ vw) :
    Rect.StrictInside (tileRect n.rect)
      ⟨(tileRect n.rect).x + ni, (tileRect n.rect).y + top, w, lh⟩ := by
  have hw : w ≤ avail := fit_width_le_avail (m.profile == .cell) _ _ _ _ _ _ hfit
  have hnipos : 0 < ni := by rw [hni]; exact header_ni_pos m
  have hvipos : 0 < vi := by rw [hvi]; exact header_vi_pos m
  have hgap := header_gap_nonneg m
  have htoppos := header_top_pos m c lh top hlh hch htop
  unfold Rect.StrictInside
  dsimp only
  by_cases hsv : showValue = true
  · simp only [hsv, ↓reduceIte] at havail
    omega
  · have hsvf : showValue = false := by
      cases hb : showValue with
      | true => exact absurd hb hsv
      | false => rfl
    simp only [hsvf] at havail
    omega

/-- The written value rectangle of a header step keeps a positive distance
from every side of the node's tile; no successful name fit is needed. -/
private theorem header_value_rect_strict (m : Model) (c : Consts) (n : Node)
    (vw lh top ni vi : Int)
    (hlh : lh = if (m.profile == .cell) then 1 else 1280)
    (hch : c.header = if (m.profile == .cell) then 2 else 1600)
    (htop : top = LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile - lh) 2)
    (hhgt : ¬((tileRect n.rect).h ≤ top + lh))
    (hni : ni = LayoutConst.treemap_header_label_inset.get m.profile)
    (hvi : vi = LayoutConst.treemap_header_value_inset.get m.profile)
    (hvwle : vw + vi + ni ≤ (tileRect n.rect).w) :
    Rect.StrictInside (tileRect n.rect)
      ⟨(tileRect n.rect).x + (tileRect n.rect).w - vi - vw,
        (tileRect n.rect).y + top, vw, lh⟩ := by
  have hnipos : 0 < ni := by rw [hni]; exact header_ni_pos m
  have hvipos : 0 < vi := by rw [hvi]; exact header_vi_pos m
  have htoppos := header_top_pos m c lh top hlh hch htop
  unfold Rect.StrictInside
  dsimp only
  omega

/-! ### List and lookup helpers -/

/-- A `findIdx?` hit carries its element and predicate. -/
private theorem findIdx?_lookup {α : Type} (l : List α) (p : α → Bool) (j : Nat)
    (h : l.findIdx? p = some j) : ∃ x, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none => rw [hv] at h; simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩

/-- Generic form of the modify-at-index equation. -/
private theorem getElem?_modify' {α : Type} (l : List α) (j : Nat) (f : α → α) (i : Nat) :
    (l.modify j f)[i]? = (l[i]?).map (fun l => if j = i then f l else l) :=
  List.getElem?_modify f j l i

/-- The changed index of a single modify is the modified index, and the new
value is the written one. -/
private theorem modify_changed_eq {α : Type} (l : List α) (j i : Nat) (f : α → α)
    (h : (l.modify j f)[i]? ≠ l[i]?) :
    j = i ∧ ∃ x, l[i]? = some x ∧ (l.modify j f)[i]? = some (f x) := by
  have hb : ∃ x, l[i]? = some x := by
    cases hx : l[i]? with
    | none => rw [getElem?_modify' l j f i, hx] at h; simp at h
    | some x => exact ⟨x, rfl⟩
  obtain ⟨x, hx⟩ := hb
  by_cases hij : j = i
  · refine ⟨hij, x, hx, ?_⟩
    rw [getElem?_modify' l j f i, hx, hij]
    have hfun : (fun l => if i = i then f l else l) = f := by
      funext l; simp
    rw [hfun]
    rfl
  · exfalso
    rw [getElem?_modify' l j f i, hx] at h
    simp only [hij] at h
    exact h rfl

/-- A name-then-value double modify changes exactly the name or the value
index; the written label is the corresponding one. -/
private theorem two_modify_index {α : Type} (before middle after : List α)
    (j k i : Nat) (fN fV : α → α)
    (hM : middle = before.modify j fN)
    (hA : after = middle.modify k fV)
    (hjk : j ≠ k)
    (hchange : after[i]? ≠ before[i]?) :
    (i = j ∧ ∃ x, before[i]? = some x ∧ after[i]? = some (fN x)) ∨
    (k = i ∧ ∃ x, before[i]? = some x ∧ after[i]? = some (fV x)) := by
  by_cases hki : k = i
  · have hji : j ≠ i := fun h => hjk (h.trans hki.symm)
    have hmidI : middle[i]? = before[i]? := by
      rw [hM, getElem?_modify' before j fN i]
      cases hb2 : before[i]? with
      | none => rfl
      | some x => simp [hji]
    refine Or.inr ⟨hki, ?_⟩
    cases hb : before[i]? with
    | none =>
      exfalso
      have h1 : middle[i]? = none := by rw [hmidI, hb]
      rw [hA, getElem?_modify' middle k fV i, h1, hb] at hchange
      simp at hchange
    | some x =>
      have hxm : middle[i]? = some x := by rw [hmidI]; exact hb
      refine ⟨x, rfl, ?_⟩
      rw [hA, ← hmidI] at hchange
      obtain ⟨_, x', hx', hpl⟩ := modify_changed_eq middle k i fV hchange
      have hxx : x' = x := Option.some.inj (hx'.symm.trans hxm)
      subst hxx
      rw [hA]
      exact hpl
  · have hAfterMid : after[i]? = middle[i]? := by
      rw [hA, getElem?_modify' middle k fV i]
      cases hm2 : middle[i]? with
      | none => rfl
      | some x => simp [fun h => hki h]
    have hch2 : middle[i]? ≠ before[i]? := by
      rw [hAfterMid] at hchange
      exact hchange
    rw [hM] at hch2
    obtain ⟨hij, x, hx, hpl2⟩ := modify_changed_eq before j i fN hch2
    refine Or.inl ⟨hij.symm, x, hx, ?_⟩
    rw [hAfterMid, hM]
    exact hpl2

/-- The label id at a `findIdx?` name hit. -/
private theorem label_id_of_name {before : List PlacedLabel} {n : Node} {j : Nat}
    (hj : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") = some j) :
    ∃ x, before[j]? = some x ∧ x.source.id = n.source.id ++ ".name" := by
  obtain ⟨x, hx, hp⟩ := findIdx?_lookup _ _ j hj
  exact ⟨x, hx, beq_iff_eq.mp hp⟩

/-- The label id at a `findIdx?` value hit. -/
private theorem label_id_of_value {before : List PlacedLabel} {n : Node} {k : Nat}
    (hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") = some k) :
    ∃ x, before[k]? = some x ∧ x.source.id = n.source.id ++ ".value" := by
  obtain ⟨x, hx, hp⟩ := findIdx?_lookup _ _ k hv
  exact ⟨x, hx, beq_iff_eq.mp hp⟩

/-- The name and value indices of one node are distinct. -/
private theorem name_index_ne_value_index {before : List PlacedLabel} {n : Node} {j k : Nat}
    (hj : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") = some j)
    (hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") = some k) :
    j ≠ k := by
  intro h
  obtain ⟨x1, hx1, hp1⟩ := label_id_of_name hj
  obtain ⟨x2, hx2, hp2⟩ := label_id_of_value hv
  rw [h] at hx1
  have hx : x1 = x2 := Option.some.inj (hx1.symm.trans hx2)
  refine suffix_ne_value_name n.source.id n.source.id ?_
  rw [← hp2, ← hp1]
  exact (congrArg (fun x : PlacedLabel => x.source.id) hx).symm

/-! ### Model label hygiene -/

/-- `eraseDups` never lengthens a string list. -/
private theorem eraseDups_length_le_aux : ∀ l : List String, l.eraseDups.length ≤ l.length
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    have h1 := eraseDups_length_le_aux (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons]
    omega
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A string list whose `eraseDups` keeps the length has no duplicates. -/
private theorem nodup_of_eraseDups_length :
    ∀ l : List String, l.eraseDups.length = l.length → l.Nodup
  | [] => fun _ => List.nodup_nil
  | a :: as => by
    intro h
    rw [List.eraseDups_cons] at h
    simp only [List.length_cons] at h
    have h1 := eraseDups_length_le_aux (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    have hf : (as.filter fun b => !b == a).length = as.length := by omega
    have hall : ∀ b ∈ as, (!b == a) = true := List.length_filter_eq_length_iff.mp hf
    have hfe : (as.filter fun b => !b == a) = as := List.filter_eq_self.mpr hall
    have hn := nodup_of_eraseDups_length (as.filter fun b => !b == a) (by omega)
    rw [hfe] at hn
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, hn⟩
    have := hall a hmem
    simp at this
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Model labels in a well-formed model have distinct ids. -/
private theorem labels_ids_nodup (hwf : WellFormed m) :
    (m.labels.map (·.id)).Nodup := by
  unfold WellFormed modelWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hl⟩, _⟩, _⟩, _⟩, _⟩ := hwf
  have hl' : ((m.labels.map (·.id)).eraseDups.length == (m.labels.map (·.id)).length) = true := hl
  exact nodup_of_eraseDups_length _ (beq_iff_eq.mp hl')

/-- The `"title"` model label is unique, so `find?` locates it. -/
private theorem labels_find_title (hwf : WellFormed m) {lt : ModelLabel}
    (hmem : lt ∈ m.labels) (hid : lt.id = "title") :
    m.labels.find? (fun x => x.id == "title") = some lt := by
  have hnodup := labels_ids_nodup hwf
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hlen, hval⟩ := List.getElem?_eq_some_iff.mp hidx
  have hmapidx : (m.labels.map (·.id))[idx]? = some "title" := by
    simp only [List.getElem?_map, hidx, Option.map_some, hid]
  have hfindIdx : m.labels.findIdx? (fun x => x.id == "title") = some idx := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hlen, ?_, ?_⟩
    · simp [hval, hid]
    · intro j hjk hpx
      exfalso
      have hjlen : j < m.labels.length := Nat.lt_trans hjk hlen
      have hxid : (m.labels[j]'hjlen).id = "title" := beq_iff_eq.mp hpx
      have hjeq : m.labels[j]? = some (m.labels[j]'hjlen) :=
        List.getElem?_eq_getElem hjlen
      have hmapj : (m.labels.map (·.id))[j]? = some "title" := by
        simp only [List.getElem?_map, hjeq, Option.map_some, hxid]
      have hji : j = idx :=
        (List.Nodup.getElem?_inj (i := j) (j := idx)
          (by rw [List.length_map]; exact hjlen) hnodup).mp
          (hmapj.trans hmapidx.symm)
      omega
  rw [List.find?_eq_bind_findIdx?_getElem?, hfindIdx]
  simp [hidx]

/-- A nonempty title label text puts the reserved band at `titleBand`. -/
private theorem bandOf_titleBand (hwf : WellFormed m) {lt : ModelLabel}
    (hmem : lt ∈ m.labels) (hid : lt.id = "title") (htext : ¬ lt.text.isEmpty) :
    bandOf m = (constants m).titleBand := by
  have hfind := labels_find_title hwf hmem hid
  unfold bandOf labelText
  rw [hfind]
  simp only [Option.map_some, Option.getD_some]
  have hne : (lt.text).isEmpty = false := by
    cases h : lt.text.isEmpty with
    | true => exact absurd h htext
    | false => rfl
  simp [hne]

/-! ### Context and dump bridges -/

/-- The seeded list of a context is `seededNodes`. -/
private theorem ctx_seed_eq (ctx : Ctx m) : ctx.seed = seededNodes m := by
  rw [ctx.hseedEq]
  rfl

/-- The tiled list of any context of a successful layout is the executed node
list. -/
private theorem ctx_final_of_execution (ctx : Ctx m) {nodes : List Node}
    (hnodes : tileNodes (constants m) (seededNodes m) = .ok nodes) :
    ctx.final = nodes := by
  have hf := ctx.hfinal
  rw [ctx_seed_eq] at hf
  exact Except.ok.inj (hf.symm.trans hnodes)

/-- Untouched labels keep the initial zero rectangle. -/
private theorem initialLabels_rect_zero (m : Model) (i : Nat) (pl : PlacedLabel)
    (h : (initialLabels m)[i]? = some pl) : pl.rect = ⟨0, 0, 0, 0⟩ := by
  unfold initialLabels at h
  rw [List.getElem?_map] at h
  obtain ⟨l0, _, heq⟩ := Option.map_eq_some_iff.mp h
  rw [← heq]
  split
  · rfl
  · split <;> rfl

/-- A dump label's id, owner and rect come from the placed label's source. -/
private theorem dumpLabel_fields (l : PlacedLabel) :
    (dumpLabel l).id = l.source.id ∧
    (dumpLabel l).owner = l.source.owner ∧
    (dumpLabel l).rect = l.rect :=
  ⟨rfl, rfl, rfl⟩


/-! ### Geometry of one changing leaf step -/

/-- Everything the kernel needs from a changing leaf step at a non-root,
childless node: the changed label belongs to the step's node and is strictly
inside the tile (a childless group) or contained in it (a non-group leaf). -/
private theorem leaf_write_geometry (m : Model) (nodes : List Node) (n : Node)
    (before after : List PlacedLabel) (i : Nat)
    (hguard : leafGroupLabelVerticalStrict m nodes = true)
    (hroot : (n.source.id == "root") = false)
    (hmem : n ∈ nodes)
    (hsrc : sources before = m.labels)
    (hchild : (children nodes n.source.id).isEmpty = true)
    (hstep : placeLeaf m (denseConstants m nodes) n before = .ok after)
    (hne : after ≠ before)
    (hchange : after[i]? ≠ before[i]?) :
    ∃ pl : PlacedLabel, after[i]? = some pl ∧
      (pl.source.id = n.source.id ++ ".name" ∨ pl.source.id = n.source.id ++ ".value") ∧
      (Rect.StrictInside (tileRect n.rect) pl.rect ∨
        (n.source.role ≠ .group ∧ Rect.Contained (tileRect n.rect) pl.rect)) := by
  by_cases hg : n.source.role = .group
  · have hs : sources before = sources (initialLabels m) := by
      rw [hsrc, initialLabels_sources]
    obtain ⟨pl, hplI, hidI, hstrict⟩ | ⟨pl, hplI, hidI, hstrict⟩ :=
      leaf_group_write_strict_rects m nodes n before after i hguard hmem hroot hg
      hchild hs hstep hne hchange
    · exact ⟨pl, hplI, Or.inl hidI, Or.inl hstrict⟩
    · exact ⟨pl, hplI, Or.inr hidI, Or.inl hstrict⟩
  · have hrun := changed_leaf_write_run m (denseConstants m nodes) n before after hstep hne
    simp only [LeafWriteRun] at hrun
    obtain ⟨j, ns, shown, nw, vw, middle, hj, _hns, hfit, _hW, hM, hA⟩ := hrun
    obtain ⟨hmin, hvec⟩ := leaf_place_side_conditions m nodes n before after hstep hne
    obtain ⟨lh, hlh⟩ : ∃ lh : Int, lh = if (m.profile == .cell) then 1 else 1280 :=
      ⟨_, rfl⟩
    obtain ⟨pair, hpair⟩ : ∃ pair : Int,
        pair = 2 * lh + (denseConstants m nodes).spacing := ⟨_, rfl⟩
    obtain ⟨room, hroom⟩ : ∃ room : Bool,
        room = decide (pair ≤ (if (m.profile == .cell) then
          (tileRect n.rect).h - 2 * (denseConstants m nodes).pad
          else (tileRect n.rect).h)) := ⟨_, rfl⟩
    obtain ⟨sv, hsv⟩ : ∃ sv : Bool,
        sv = (((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
          room) && decide (vw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad)) :=
      ⟨_, rfl⟩
    obtain ⟨rows, hrows⟩ : ∃ rows : Int, rows = if sv then pair else lh := ⟨_, rfl⟩
    obtain ⟨top, htop⟩ : ∃ top : Int,
        top = if (m.profile == .cell) then
          (tileRect n.rect).y + (denseConstants m nodes).pad +
            Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad - rows) 2
        else (tileRect n.rect).y + Int.fdiv ((tileRect n.rect).h - rows) 2 := ⟨_, rfl⟩
    rw [← hlh, ← hpair, ← hroom, ← hsv, ← hrows, ← htop] at hM hA
    have hgeo := leaf_body_rects_contained m nodes n before j ns shown nw vw lh pair rows
      top room sv hfit hlh hpair hroom hsv hrows htop hmin hvec
    rcases hk : (before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")) with _ | k
    · have hsvf : sv = false := by
        rw [hsv, hk]
        rfl
      have hAm : after = middle := by rw [hA]; simp [hsvf]
      rw [hAm, hM] at hchange
      obtain ⟨hji, x, hx, hplw⟩ := modify_changed_eq before j i _ hchange
      obtain ⟨x1, hx1, hp1⟩ := label_id_of_name hj
      rw [hji] at hx1
      have hxx : x = x1 := Option.some.inj (hx.symm.trans hx1)
      rw [hxx] at hplw
      refine ⟨_, by rw [hAm, hM]; exact hplw, Or.inl ?_, Or.inr ⟨hg, ?_⟩⟩
      · simpa using hp1
      · exact hgeo.1
    · have hjk : j ≠ k := name_index_ne_value_index hj hk
      simp only [hk] at hA
      by_cases hsvT : sv = true
      · simp only [hsvT, ↓reduceIte] at hA
        obtain ⟨hij, x, hx, hplw⟩ | ⟨hik, x, hx, hplw⟩ :=
          two_modify_index before middle after j k i _ _ hM hA hjk hchange
        · obtain ⟨x1, hx1, hp1⟩ := label_id_of_name hj
          rw [← hij] at hx1
          have hxx : x = x1 := Option.some.inj (hx.symm.trans hx1)
          rw [hxx] at hplw
          refine ⟨_, hplw, Or.inl ?_, Or.inr ⟨hg, ?_⟩⟩
          · simpa using hp1
          · exact hgeo.1
        · obtain ⟨x2, hx2, hp2⟩ := label_id_of_value hk
          rw [hik] at hx2
          have hxx : x = x2 := Option.some.inj (hx.symm.trans hx2)
          rw [hxx] at hplw
          refine ⟨_, hplw, Or.inr ?_, Or.inr ⟨hg, ?_⟩⟩
          · simpa using hp2
          · exact hgeo.2 hsvT
      · have hsvf : sv = false := by
          cases hb : sv with
          | true => exact absurd hb hsvT
          | false => rfl
        have hAm : after = middle := by rw [hA]; simp [hsvf]
        rw [hAm, hM] at hchange
        obtain ⟨hji, x, hx, hplw⟩ := modify_changed_eq before j i _ hchange
        obtain ⟨x1, hx1, hp1⟩ := label_id_of_name hj
        rw [hji] at hx1
        have hxx : x = x1 := Option.some.inj (hx.symm.trans hx1)
        rw [hxx] at hplw
        refine ⟨_, by rw [hAm, hM]; exact hplw, Or.inl ?_, Or.inr ⟨hg, ?_⟩⟩
        · simpa using hp1
        · exact hgeo.1

/-! ### Geometry of one changing header step -/

/-- The height guard of a changing header step, recovered from the skip lemma. -/
private theorem header_height_of_change (m : Model) (c : Consts) (n : Node)
    (before after : List PlacedLabel)
    (hplace : placeHeader m c n before = .ok after)
    (hchange : after ≠ before) :
    ¬((tileRect n.rect).h ≤ LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
        (if m.profile == .cell then 1 else 1280)) 2 +
      (if m.profile == .cell then 1 else 1280)) := by
  intro hh
  have hskip := placeHeader_skip_height m c n before hh
  have he : after = before := Except.ok.inj (hplace.symm.trans hskip)
  exact hchange he

/-- Everything the kernel needs from a changing header step: the changed label
belongs to the step's node and its rectangle is strictly inside the tile. The
value-only write (absent `.name`) is covered: the value rectangle needs no
successful name fit. -/
private theorem header_write_geometry (m : Model) (c : Consts) (n : Node)
    (before after : List PlacedLabel) (i : Nat)
    (hplace : placeHeader m c n before = .ok after)
    (hheight : ¬((tileRect n.rect).h ≤ LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
        (if m.profile == .cell then 1 else 1280)) 2 +
      (if m.profile == .cell then 1 else 1280)))
    (hch : c.header = if (m.profile == .cell) then 2 else 1600)
    (hchange : after[i]? ≠ before[i]?) :
    ∃ pl : PlacedLabel, after[i]? = some pl ∧
      (pl.source.id = n.source.id ++ ".name" ∨ pl.source.id = n.source.id ++ ".value") ∧
      Rect.StrictInside (tileRect n.rect) pl.rect := by
  have hheight' : ∀ (lh top : Int),
      lh = (if (m.profile == .cell) then 1 else 1280) →
      top = LayoutConst.treemap_header_border.get m.profile +
        Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile - lh) 2 →
      ¬((tileRect n.rect).h ≤ top + lh) := by
    intro lh top hlh htop
    have hsame : top + lh = LayoutConst.treemap_header_border.get m.profile +
        Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
          (if m.profile == .cell then 1 else 1280)) 2 +
        (if m.profile == .cell then 1 else 1280) := by
      rw [htop, hlh]
    rw [hsame]
    exact hheight
  cases hn : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") with
  | none =>
    obtain ⟨vw, hw, ho⟩ := placeHeader_absent_name_cases m c n before after hn hheight hplace
    cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
    | none =>
      have hvs : (before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome = false := by
        rw [hv]; rfl
      simp only [hvs, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at ho
      rw [ho] at hchange
      exact absurd rfl hchange
    | some k =>
      rw [hv] at ho
      dsimp only at ho
      cases hP : decide (vw + LayoutConst.treemap_header_value_inset.get m.profile +
          LayoutConst.treemap_header_label_inset.get m.profile ≤ (tileRect n.rect).w) with
      | false =>
        simp only [hP] at ho
        rw [ho] at hchange
        exact absurd rfl hchange
      | true =>
        simp only [hP] at ho
        obtain ⟨hki, x, hx, hplx⟩ := modify_changed_eq before k i _ (by rwa [ho] at hchange)
        obtain ⟨x1, hx1, hp1⟩ := label_id_of_value hv
        rw [hki] at hx1
        have hxx : x = x1 := Option.some.inj (hx.symm.trans hx1)
        have hrect : ((fun l : PlacedLabel => { putLabel l l.source.text
            ⟨(tileRect n.rect).x + (tileRect n.rect).w -
              LayoutConst.treemap_header_value_inset.get m.profile - vw,
              (tileRect n.rect).y +
                (LayoutConst.treemap_header_border.get m.profile +
                  Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                    (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
              vw, if (m.profile == Profile.cell) = true then 1 else 1280⟩
              (Int.fdiv (LayoutConst.treemap_header_value_size.get m.profile) 64)
              with align := .«end», italic := true }) x).rect =
            ⟨(tileRect n.rect).x + (tileRect n.rect).w -
              LayoutConst.treemap_header_value_inset.get m.profile - vw,
              (tileRect n.rect).y +
                (LayoutConst.treemap_header_border.get m.profile +
                  Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                    (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
              vw, if (m.profile == Profile.cell) = true then 1 else 1280⟩ := rfl
        refine ⟨_, by rw [ho]; exact hplx, Or.inr ?_, ?_⟩
        · simpa [hxx, putLabel] using hp1
        · rw [hrect]
          exact header_value_rect_strict m c n vw _ _ _ _ rfl hch rfl
            (hheight' _ _ rfl rfl) rfl rfl (of_decide_eq_true hP)
  | some j =>
    obtain ⟨vw, fitted, middle, hw, hfit, hm, ho⟩ :=
      placeHeader_fit_cases m c n before after j hn hheight hplace
    have hvw0 : 0 ≤ vw := by
      cases hvs : (before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome with
      | true =>
        simp only [hvs, ↓reduceIte] at hw
        exact width_nonneg hw
      | false =>
        simp only [hvs] at hw
        have e : (0 : Int) = vw := Except.ok.inj hw
        omega
    cases hf : fitted with
    | none =>
      simp only [hf] at hm
      cases hsv : ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
          decide (vw + LayoutConst.treemap_header_value_inset.get m.profile +
            LayoutConst.treemap_header_label_inset.get m.profile ≤ (tileRect n.rect).w) &&
          decide ((tileRect n.rect).w - LayoutConst.treemap_header_label_inset.get m.profile -
            (LayoutConst.treemap_header_value_inset.get m.profile + vw +
              LayoutConst.treemap_header_gap.get m.profile) ≥
            LayoutConst.treemap_header_label_min.get m.profile)) with
      | false =>
        simp only [hsv] at ho
        rw [ho, hm] at hchange
        exact absurd rfl hchange
      | true =>
        simp only [hsv, ↓reduceIte] at ho
        cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
        | none =>
          rw [hv] at ho
          dsimp only at ho
          rw [ho, hm] at hchange
          exact absurd rfl hchange
        | some k =>
          rw [hv] at hsv
          simp only [Option.isSome_some, Bool.true_and] at hsv
          have hP : decide (vw + LayoutConst.treemap_header_value_inset.get m.profile +
              LayoutConst.treemap_header_label_inset.get m.profile ≤
              (tileRect n.rect).w) = true := by
            cases hX : decide (vw + LayoutConst.treemap_header_value_inset.get m.profile +
                LayoutConst.treemap_header_label_inset.get m.profile ≤
                (tileRect n.rect).w) with
            | true => rfl
            | false => simp only [hX, Bool.false_and, Bool.false_eq_true] at hsv
          have hQ : decide ((tileRect n.rect).w - LayoutConst.treemap_header_label_inset.get m.profile -
              (LayoutConst.treemap_header_value_inset.get m.profile + vw +
                LayoutConst.treemap_header_gap.get m.profile) ≥
              LayoutConst.treemap_header_label_min.get m.profile) = true := by
            cases hX : decide ((tileRect n.rect).w - LayoutConst.treemap_header_label_inset.get m.profile -
                (LayoutConst.treemap_header_value_inset.get m.profile + vw +
                  LayoutConst.treemap_header_gap.get m.profile) ≥
                LayoutConst.treemap_header_label_min.get m.profile) with
            | true => rfl
            | false => simp only [hP, hX, Bool.true_and, Bool.false_eq_true] at hsv
          have hle : vw + LayoutConst.treemap_header_value_inset.get m.profile +
              LayoutConst.treemap_header_label_inset.get m.profile ≤ (tileRect n.rect).w :=
            of_decide_eq_true hP
          rw [hv] at ho
          dsimp only at ho
          obtain ⟨hki, x, hx, hplx⟩ :=
            modify_changed_eq middle k i _ (by rw [ho, ←hm] at hchange; exact hchange)
          obtain ⟨x1, hx1, hp1⟩ := label_id_of_value hv
          rw [hki] at hx1
          have hmb : middle[i]? = before[i]? := by rw [hm]
          have hxx : x = x1 := Option.some.inj (hx.symm.trans (hmb.trans hx1))
          have hrect : ((fun l : PlacedLabel => { putLabel l l.source.text
              ⟨(tileRect n.rect).x + (tileRect n.rect).w -
                LayoutConst.treemap_header_value_inset.get m.profile - vw,
                (tileRect n.rect).y +
                  (LayoutConst.treemap_header_border.get m.profile +
                    Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                      (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
                vw, if (m.profile == Profile.cell) = true then 1 else 1280⟩
                (Int.fdiv (LayoutConst.treemap_header_value_size.get m.profile) 64)
                with align := .«end», italic := true }) x).rect =
              ⟨(tileRect n.rect).x + (tileRect n.rect).w -
                LayoutConst.treemap_header_value_inset.get m.profile - vw,
                (tileRect n.rect).y +
                  (LayoutConst.treemap_header_border.get m.profile +
                    Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                      (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
                vw, if (m.profile == Profile.cell) = true then 1 else 1280⟩ := rfl
          refine ⟨_, by rw [ho]; exact hplx, Or.inr ?_, ?_⟩
          · simpa [hxx, putLabel] using hp1
          · rw [hrect]
            exact header_value_rect_strict m c n vw _ _ _ _ rfl hch rfl
              (hheight' _ _ rfl rfl) rfl rfl hle
    | some pair =>
      obtain ⟨shown, w⟩ := pair
      simp only [hf] at hm hfit
      cases hsv : ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
          decide (vw + LayoutConst.treemap_header_value_inset.get m.profile +
            LayoutConst.treemap_header_label_inset.get m.profile ≤ (tileRect n.rect).w) &&
          decide ((tileRect n.rect).w - LayoutConst.treemap_header_label_inset.get m.profile -
            (LayoutConst.treemap_header_value_inset.get m.profile + vw +
              LayoutConst.treemap_header_gap.get m.profile) ≥
            LayoutConst.treemap_header_label_min.get m.profile)) with
      | false =>
        simp only [hsv] at ho
        rw [ho] at hchange
        obtain ⟨hji, x, hx, hplw⟩ := modify_changed_eq before j i _ (by rw [hm] at hchange; exact hchange)
        obtain ⟨x1, hx1, hp1⟩ := label_id_of_name hn
        rw [hji] at hx1
        have hxx : x = x1 := Option.some.inj (hx.symm.trans hx1)
        have hrect : ((fun l : PlacedLabel => { putLabel l shown
            ⟨(tileRect n.rect).x + LayoutConst.treemap_header_label_inset.get m.profile,
              (tileRect n.rect).y +
                (LayoutConst.treemap_header_border.get m.profile +
                  Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                    (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
              w, if (m.profile == Profile.cell) = true then 1 else 1280⟩
              (Int.fdiv (LayoutConst.treemap_header_label_size.get m.profile) 64)
              with align := .start }) x).rect =
            ⟨(tileRect n.rect).x + LayoutConst.treemap_header_label_inset.get m.profile,
              (tileRect n.rect).y +
                (LayoutConst.treemap_header_border.get m.profile +
                  Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                    (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
              w, if (m.profile == Profile.cell) = true then 1 else 1280⟩ := rfl
        refine ⟨_, by rw [ho, hm]; exact hplw, Or.inl ?_, ?_⟩
        · simpa [hxx, putLabel] using hp1
        · rw [hrect]
          exact header_name_rect_strict m c n _ _ _ _ _ _ _ _ _ _ _ _ hfit rfl hch rfl
            (hheight' _ _ rfl rfl) rfl rfl rfl rfl hvw0
      | true =>
        simp only [hsv, ↓reduceIte] at ho
        have hA : (before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome = true := by
          cases hA : (before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome with
          | true => rfl
          | false => simp only [hA, Bool.false_and, Bool.false_eq_true] at hsv
        have hle : vw + LayoutConst.treemap_header_value_inset.get m.profile +
            LayoutConst.treemap_header_label_inset.get m.profile ≤ (tileRect n.rect).w := by
          have hB : decide (vw + LayoutConst.treemap_header_value_inset.get m.profile +
              LayoutConst.treemap_header_label_inset.get m.profile ≤
              (tileRect n.rect).w) = true := by
            cases hB : decide (vw + LayoutConst.treemap_header_value_inset.get m.profile +
              LayoutConst.treemap_header_label_inset.get m.profile ≤
              (tileRect n.rect).w) with
            | true => rfl
            | false => simp only [hA, hB, Bool.true_and, Bool.false_and, Bool.false_eq_true] at hsv
          exact of_decide_eq_true hB
        cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
        | none =>
          simp only [hv, Option.isSome_none] at hA
          exact absurd hA (by decide)
        | some k =>
          simp only [hv] at ho
          have hjk : j ≠ k := name_index_ne_value_index hn hv
          obtain ⟨hji, x, hx, hplw⟩ | ⟨hki, x, hx, hplw⟩ :=
            two_modify_index before middle after j k i _ _ hm ho hjk hchange
          · obtain ⟨x1, hx1, hp1⟩ := label_id_of_name hn
            rw [← hji] at hx1
            have hxx : x = x1 := Option.some.inj (hx.symm.trans hx1)
            have hrect : ((fun l : PlacedLabel => { putLabel l shown
                ⟨(tileRect n.rect).x + LayoutConst.treemap_header_label_inset.get m.profile,
                  (tileRect n.rect).y +
                    (LayoutConst.treemap_header_border.get m.profile +
                      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                        (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
                  w, if (m.profile == Profile.cell) = true then 1 else 1280⟩
                  (Int.fdiv (LayoutConst.treemap_header_label_size.get m.profile) 64)
                  with align := .start }) x).rect =
                ⟨(tileRect n.rect).x + LayoutConst.treemap_header_label_inset.get m.profile,
                  (tileRect n.rect).y +
                    (LayoutConst.treemap_header_border.get m.profile +
                      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                        (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
                  w, if (m.profile == Profile.cell) = true then 1 else 1280⟩ := rfl
            refine ⟨_, hplw, Or.inl ?_, ?_⟩
            · simpa [hxx, putLabel] using hp1
            · rw [hrect]
              exact header_name_rect_strict m c n _ _ _ _ _ _ _ _ _ _ _ _ hfit rfl hch rfl
                (hheight' _ _ rfl rfl) rfl rfl rfl rfl hvw0
          · obtain ⟨x2, hx2, hp2⟩ := label_id_of_value hv
            have hxv : before[i]? = some x := hx
            rw [hki] at hx2
            have hxx : x = x2 := Option.some.inj (hxv.symm.trans hx2)
            have hrect : ((fun l : PlacedLabel => { putLabel l l.source.text
                ⟨(tileRect n.rect).x + (tileRect n.rect).w -
                  LayoutConst.treemap_header_value_inset.get m.profile - vw,
                  (tileRect n.rect).y +
                    (LayoutConst.treemap_header_border.get m.profile +
                      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                        (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
                  vw, if (m.profile == Profile.cell) = true then 1 else 1280⟩
                  (Int.fdiv (LayoutConst.treemap_header_value_size.get m.profile) 64)
                  with align := .«end», italic := true }) x).rect =
                ⟨(tileRect n.rect).x + (tileRect n.rect).w -
                  LayoutConst.treemap_header_value_inset.get m.profile - vw,
                  (tileRect n.rect).y +
                    (LayoutConst.treemap_header_border.get m.profile +
                      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
                        (if (m.profile == Profile.cell) = true then 1 else 1280)) 2),
                  vw, if (m.profile == Profile.cell) = true then 1 else 1280⟩ := rfl
            refine ⟨_, hplw, Or.inr ?_, ?_⟩
            · simpa [hxx, putLabel] using hp2
            · rw [hrect]
              exact header_value_rect_strict m c n vw _ _ _ _ rfl hch rfl
                (hheight' _ _ rfl rfl) rfl rfl hle


/-! ### Owner equation and main theorem -/

/-- The step node's id is the written label's owner. -/
private theorem owner_of_write (m : Model) (result : Layered.FamilyResult)
    (hlay : Kinds.Treemap.layout m = .ok result) (n : Node) (pl : PlacedLabel)
    (hs : pl.source ∈ m.labels)
    (hid : pl.source.id = n.source.id ++ ".name" ∨ pl.source.id = n.source.id ++ ".value") :
    n.source.id = pl.source.owner := by
  have hlab := Kinds.Treemap.layout_label_ids_name_owner m result hlay pl.source hs
  rcases hlab with hname | hvalue | ⟨htitle, _⟩
  · rcases hid with hid | hid
    · exact append_name_cancel (hid.symm.trans hname)
    · exact absurd (hid.symm.trans hname) (suffix_ne_value_name _ _)
  · rcases hid with hid | hid
    · exact absurd (hid.symm.trans hvalue) (suffix_ne_value_name _ _).symm
    · exact append_value_cancel (hid.symm.trans hvalue)
  · rcases hid with hid | hid
    · exact absurd (hid.symm.trans htitle) (title_ne_name _)
    · exact absurd (hid.symm.trans htitle) (title_ne_value _)

/-- Every dump label is accounted for: the untouched zero rectangle, the title
label inside the title band, or a label written at its owner node's step. -/
theorem label_owner_cases' (m : Model) :
    ∀ (ctx : Ctx m) (result : Layered.FamilyResult),
      WellFormed m → Kinds.Treemap.layout m = .ok result →
      ∀ (l : Label), l ∈ result.scene.layoutDump.labels →
      l.rect = ⟨0, 0, 0, 0⟩ ∨
      (l.id = "title" ∧ bandOf m = (constants m).titleBand ∧
        Rect.Contained ⟨0, 0, (constants m).width, (constants m).titleBand⟩ l.rect) ∨
      ∃ n : Node, n ∈ ctx.final ∧ n.source.id = l.owner ∧
        (Rect.StrictInside (tileRect n.rect) l.rect ∨
          (n.source.role ≠ .group ∧ Rect.Contained (tileRect n.rect) l.rect)) := by
  intro ctx result hwf hlay l hl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨_, nodes, titleLabels, finalLabels, hnodes, hscene_eq, hcases⟩ :=
    public_label_placement_cases m result hlay i
  have hmap : result.scene.layoutDump.labels =
      finalLabels.map (fun pl => (dumpLabel pl).toLabel) := by
    have hfun : (SceneLabel.toLabel ∘ dumpLabel) =
      (fun pl => (dumpLabel pl).toLabel) := rfl
    show result.scene.labels.map SceneLabel.toLabel = _
    rw [hscene_eq, List.map_map, hfun]
  rw [hmap, List.getElem?_map] at hi
  obtain ⟨pl, hfin_dump, hEq⟩ := Option.map_eq_some_iff.mp hi
  have hfields := dumpLabel_fields pl
  have hid : l.id = pl.source.id := by
    have := congrArg Label.id hEq
    rw [hfields.1] at this
    exact this.symm
  have hown : l.owner = pl.source.owner := by
    have := congrArg Label.owner hEq
    rw [hfields.2.1] at this
    exact this.symm
  have hrect : l.rect = pl.rect := by
    have := congrArg Label.rect hEq
    rw [hfields.2.2] at this
    exact this.symm
  rcases hcases with ⟨hidx, _, horig⟩ | ⟨prior, n, suffix, lb, la, heq, _, hs, hc, hbs, has, hfin, _, hroot, hor⟩
  · rcases horig with htitle_eq | ⟨l0, shown, w, hj, hl0, hfit, htitle⟩
    · have hinit : (initialLabels m)[i]? = some pl := by
        rw [← htitle_eq]
        exact hidx.symm.trans hfin_dump
      have hzero := initialLabels_rect_zero m i pl hinit
      exact Or.inl (hrect.trans hzero)
    · have hplsome : titleLabels[i]? = some pl := hidx.symm.trans hfin_dump
      rw [htitle] at hplsome
      have hpl_eq := Option.some.inj hplsome
      subst hpl_eq
      simp only [putLabel_source] at hid hrect
      have htitle_id : l0.source.id = "title" := by
        obtain ⟨x, hx, hpred⟩ := findIdx?_lookup _ _ i hj
        have hxx : x = l0 := Option.some.inj (hx.symm.trans hl0)
        rw [← hxx]
        exact beq_iff_eq.mp hpred
      rw [htitle_id] at hid
      have hsi := source_at_index m (initialLabels m) (initialLabels_sources m) i
      rw [hl0] at hsi
      simp only [Option.map_some] at hsi
      have hmem0 : l0.source ∈ m.labels := List.mem_of_getElem? hsi.symm
      have hne : l0.source.text.isEmpty = false := by
        cases he : l0.source.text.isEmpty with
        | true =>
          unfold fit at hfit
          rw [he] at hfit
          simp only [↓reduceIte, pure, Except.pure] at hfit
          cases hfit
        | false => rfl
      have hband : bandOf m = (constants m).titleBand :=
        bandOf_titleBand hwf hmem0 htitle_id (by intro he; rw [he] at hne; exact (by decide : (true : Bool) ≠ false) hne)
      have hcont : Rect.Contained ⟨0, 0, (constants m).width, (constants m).titleBand⟩ l.rect := by
        rw [hrect]
        exact title_rect_in_band m _ _ _ hfit
      exact Or.inr (Or.inl ⟨hid, hband, hcont⟩)
  · have hfe : ctx.final = nodes := ctx_final_of_execution ctx hnodes
    have hmem_nodes : n ∈ nodes := by
      rw [heq]
      exact List.mem_append.mpr (Or.inr (by simp))
    have hfin_ctx : n ∈ ctx.final := hfe ▸ hmem_nodes
    have hne : la ≠ lb := fun he => hc (congrArg (fun ls => ls[i]?) he)
    rcases hor with ⟨hchild, _⟩ | ⟨hchild2, _⟩
    · have hplace : placeLeaf m (denseConstants m nodes) n lb = .ok la := by
        rcases step_cases m nodes (denseConstants m nodes) n lb la hs with
          ⟨_, heq0⟩ | ⟨_, _, hpl⟩ | ⟨_, hcon, _⟩
        · exact absurd heq0 hne
        · exact hpl
        · exact absurd (hchild.symm.trans hcon) (by decide)
      have hscene : Elegant.Treemap.layout m = .ok result.scene :=
        Kinds.Treemap.layout_adapter_success m result hlay
      obtain ⟨gnodes, hgn, hguard⟩ := layout_guard_holds m result.scene hscene
      have hgn_eq : gnodes = nodes := Except.ok.inj (hgn.symm.trans hnodes)
      rw [hgn_eq] at hguard
      obtain ⟨pl2, hla, hid2, hgeo⟩ :=
        leaf_write_geometry m nodes n lb la i hguard hroot hmem_nodes hbs hchild hplace hne hc
      have hsi := source_at_index m la has i
      rw [hla] at hsi
      simp only [Option.map_some] at hsi
      have hmem2 : pl2.source ∈ m.labels := List.mem_of_getElem? hsi.symm
      have hpleq : pl = pl2 := Option.some.inj (hfin_dump.symm.trans (hfin.trans hla))
      subst hpleq
      have hown2 := owner_of_write m result hlay n pl hmem2 hid2
      exact Or.inr (Or.inr ⟨n, hfin_ctx, hown2.trans hown.symm, by rw [hrect]; exact hgeo⟩)
    · have hplace : placeHeader m (constants m) n lb = .ok la := by
        rcases step_cases m nodes (denseConstants m nodes) n lb la hs with
          ⟨_, heq0⟩ | ⟨_, hcon, _⟩ | ⟨_, _, hph⟩
        · exact absurd heq0 hne
        · exact absurd (hchild2.symm.trans hcon) (by decide)
        · exact hph
      have hheight := header_height_of_change m (constants m) n lb la hplace hne
      obtain ⟨pl2, hla, hid2, hstrict⟩ :=
        header_write_geometry m (constants m) n lb la i hplace hheight
          (constants_header_eq m) hc
      have hsi := source_at_index m la has i
      rw [hla] at hsi
      simp only [Option.map_some] at hsi
      have hmem2 : pl2.source ∈ m.labels := List.mem_of_getElem? hsi.symm
      have hpleq : pl = pl2 := Option.some.inj (hfin_dump.symm.trans (hfin.trans hla))
      subst hpleq
      have hown2 := owner_of_write m result hlay n pl hmem2 hid2
      exact Or.inr (Or.inr ⟨n, hfin_ctx, hown2.trans hown.symm, Or.inl (by rw [hrect]; exact hstrict)⟩)

