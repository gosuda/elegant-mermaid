import Elegant.Chart.TreemapC8bKernelFacts
import Elegant.Chart.TreemapC8bLabelKernels

/-!
### The two treemap label kernels

This module closes the two open label kernels of the C8b bundle:
`label_owner_cases'` (every dump label is the untouched zero rectangle, the
title inside the title band, or a label written at its owner node's step,
strictly inside the owner tile or merely contained for a non-group leaf) and
`internal_label_header_band'` (a label owned by an internal node ends at or
above the header band bottom and is strictly inside the tile, the zero
rectangle, or the title).  `treemap_kernels` assembles the bundle.
-/

namespace Elegant.Treemap.C8b

open Elegant.Treemap.C8a
open Elegant.Treemap.CanvasC1
open Elegant.Treemap.Clearance
open Elegant.Treemap.TileForest
open Elegant.Treemap.Containment
open Elegant.Treemap.LabelFacts
open Elegant.Treemap.LabelFacts3

variable {m : Model}

set_option autoImplicit false

/-! ### List and lookup helpers -/

/-- A `findIdx?` hit carries its element and predicate. -/
private theorem findIdx?_lookup {α : Type} {l : List α} (p : α → Bool) (j : Nat)
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

/-- The element at the first `findIdx?` hit is what `find?` returns. -/
private theorem find?_of_findIdx? {α : Type} {l : List α} (p : α → Bool) (i : Nat) (x : α)
    (hi : l.findIdx? p = some i) (hx : l[i]? = some x) : l.find? p = some x := by
  induction l generalizing i with
  | nil => rw [List.findIdx?_nil] at hi; exact absurd hi (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at hi
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at hi
      cases i with
      | zero =>
        have hxy : y = x := by simpa using hx
        subst hxy
        show (match p y with | true => some y | false => List.find? p ys) = some y
        rw [hp]
      | succ j' => exact absurd hi (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at hi
      cases i with
      | zero => exact absurd hi (by simp)
      | succ j' =>
        have hys : ys.findIdx? p = some j' := by simpa using hi
        have hxs : ys[j']? = some x := by simpa using hx
        simp only [List.find?_cons, hp]
        exact ih j' hys hxs

/-- `findIdx?` on sources matches `findIdx?` on ids of the source labels. -/
private theorem findIdx?_sources (ls : List PlacedLabel) (t : String) :
    (sources ls).findIdx? (fun l => l.id == t) =
      ls.findIdx? (fun x => x.source.id == t) := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [sources, List.map_cons, List.findIdx?_cons]
    by_cases h : x.source.id == t
    · simp only [h, ↓reduceIte]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (Option.map (fun i => i + 1)) ih

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
    {size x : Int} (h : width cell text role size = .ok x) : 0 ≤ x := by
  unfold width at h
  obtain ⟨metric, _, hw⟩ := CanvasC1.except_bind_ok h
  exact Measure.textWidth_nonneg hw

/-! ### Constants and tile bridges -/

/-- The title band never exceeds the header band plus padding in either
profile, so a title label inside the band clears every tile top edge. -/
private theorem treemap_titleBand_le (m : Model) :
    (constants m).titleBand ≤ (constants m).header + (constants m).padY := by
  unfold constants
  cases m.profile <;>
    simp [LayoutConst.treemap_title_band, LayoutConst.treemap_section_header,
      LayoutConst.treemap_section_padding_y, LayoutConst.Pair.get]

/-- The profile header constant in `if` form. -/
private theorem constants_header_eq (m : Model) :
    (constants m).header = if (m.profile == .cell) then 2 else 1600 := by
  unfold constants
  cases m.profile <;> simp [LayoutConst.treemap_section_header, LayoutConst.Pair.get]

/-- Every final tile has a nonnegative top coordinate: the tiling fold keeps
each node contained in the canvas tile. -/
private theorem tile_y_nonneg (ctx : Ctx m) (n : Node) (hn : n ∈ ctx.final) :
    0 ≤ (tileRect n.rect).y := by
  have hout := tileNodes_invariant (constants m) (bandOf m) ctx.seed ctx.final
    (ctx_seedinv (ctx := ctx)) ctx.hfinal
  have hcont := (hout n hn).2
  rw [tileRect_canvasTile] at hcont
  unfold Rect.Contained at hcont
  exact hcont.2.2.1

/-- The tiled node list of a context carries the model's box ids without
duplicates. -/
private theorem ctx_final_ids_nodup (ctx : Ctx m) :
    (ctx.final.map (fun n => n.source.id)).Nodup := by
  have heq : ctx.final.map (fun n => n.source.id) =
      (ctx.final.map Node.source).map (fun b : ModelBox => b.id) := by
    simp only [List.map_map, Function.comp_def]
  rw [heq, tiled_source ctx.hfinal, ctx.hsrc]
  exact Model.boxIds_nodup ctx.hwf

/-- Two final nodes with the same source id are equal. -/
private theorem ctx_final_eq_of_id (ctx : Ctx m) {p a : Node}
    (hp : p ∈ ctx.final) (ha : a ∈ ctx.final) (hid : p.source.id = a.source.id) :
    p = a := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
  have hids : (ctx.final.map (fun n => n.source.id))[i]? = some a.source.id := by
    rw [List.getElem?_map, hi]
    simp only [hid, Option.map_some]
  have hij : i = j :=
    C8a.getElem?_pos_eq (ctx_final_ids_nodup ctx) hids
      (by rw [List.getElem?_map, hj]; simp)
  have hvals : ctx.final[i]? = ctx.final[j]? := by rw [hij]
  rw [hi, hj] at hvals
  exact Option.some.inj hvals

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
    (hfit : fit (m.profile == .cell) text avail .label ns = .ok (some (shown, w)))
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

/-- The bottom edge of a written header label stays within the node's band
budget. -/
private theorem header_band_bottom (m : Model) (top lh : Int)
    (hlh : lh = if (m.profile == .cell) then 1 else 1280)
    (htop : top = LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv ((constants m).header -
        LayoutConst.treemap_header_border.get m.profile - lh) 2) :
    top + lh ≤ (constants m).header + (constants m).padY := by
  rw [htop, hlh]
  exact treemap_band_bottom_ge m


/-! ### Generic modify-index helpers -/

/-- Generic form of the modify-at-index equation. -/
private theorem getElem?_modify' {α : Type} (l : List α) (j : Nat) (f : α → α) (i : Nat) :
    (l.modify j f)[i]? = (l[i]?).map (fun l => if j = i then f l else l) :=
  List.getElem?_modify f j l i

/-- A modify that leaves index `i` alone. -/
private theorem modify_unchanged {α : Type} (l : List α) (j i : Nat) (f : α → α)
    (h : j ≠ i) : (l.modify j f)[i]? = l[i]? := by
  rw [getElem?_modify' l j f i]
  cases hx : l[i]? with
  | none => rfl
  | some x =>
    show some (if j = i then f x else x) = some x
    by_cases hj : j = i
    · exact absurd hj h
    · simp [hj]

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
  obtain ⟨x, hx, hp⟩ := findIdx?_lookup _ j hj
  exact ⟨x, hx, beq_iff_eq.mp hp⟩

/-- The label id at a `findIdx?` value hit. -/
private theorem label_id_of_value {before : List PlacedLabel} {n : Node} {k : Nat}
    (hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") = some k) :
    ∃ x, before[k]? = some x ∧ x.source.id = n.source.id ++ ".value" := by
  obtain ⟨x, hx, hp⟩ := findIdx?_lookup _ k hv
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

/-! ### Geometry of one changing leaf step -/

/-- Everything the two kernels need from a changing leaf step at a non-root,
childless node: the changed label belongs to the step's node and is strictly
inside the tile (a childless group) or contained in it (a non-group leaf). -/
private theorem leaf_write_geometry (m : Model) (nodes : List Node) (n : Node)
    (before after : List PlacedLabel) (i : Nat)
    (hguard : leafGroupLabelVerticalStrict m nodes = true)
    (hmem : n ∈ nodes)
    (hsrc : sources before = m.labels)
    (hchild : (children nodes n.source.id).isEmpty = true)
    (hstep : step m nodes (denseConstants m nodes) before n = .ok after)
    (hne : after ≠ before)
    (hchange : after[i]? ≠ before[i]?) :
    ∃ pl : PlacedLabel, after[i]? = some pl ∧
      (pl.source.id = n.source.id ++ ".name" ∨ pl.source.id = n.source.id ++ ".value") ∧
      (Rect.StrictInside (tileRect n.rect) pl.rect ∨
        (n.source.role ≠ .group ∧ Rect.Contained (tileRect n.rect) pl.rect)) := by
  have hpl : placeLeaf m (denseConstants m nodes) n before = .ok after := by
    rcases step_cases m nodes (denseConstants m nodes) n before after hstep with
      ⟨_, heq⟩ | ⟨_, _, hp⟩ | ⟨_, hchild', _⟩
    · exact absurd heq hne
    · exact hp
    · rw [hchild'] at hchild; exact absurd hchild (by simp)
  have hroot : (n.source.id == "root") = false := by
    rcases step_cases m nodes (denseConstants m nodes) n before after hstep with
      ⟨_, heq⟩ | ⟨hid, _, _⟩ | ⟨hid, hchild', _⟩
    · exact absurd heq hne
    · exact hid
    · rw [hchild'] at hchild; exact absurd hchild (by simp)
  by_cases hg : n.source.role = .group
  · have hs : sources before = sources (initialLabels m) := by
      rw [hsrc, initialLabels_sources]
    obtain ⟨pl, hplI, hidI, hstrict⟩ | ⟨pl, hplI, hidI, hstrict⟩ :=
      leaf_group_write_strict_rects m nodes n before after i hguard hmem hroot hg
      hchild hs hpl hne hchange
    · exact ⟨pl, hplI, Or.inl hidI, Or.inl hstrict⟩
    · exact ⟨pl, hplI, Or.inr hidI, Or.inl hstrict⟩
  · have hrun := changed_leaf_write_run m (denseConstants m nodes) n before after hpl hne
    simp only [LeafWriteRun] at hrun
    obtain ⟨j, ns, shown, nw, vw, middle, hj, _hns, hfit, _hW, hM, hA⟩ := hrun
    obtain ⟨hmin, hvec⟩ := leaf_place_side_conditions m nodes n before after hpl hne
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

/-! ### Label and dump identification -/

/-- Two final nodes whose sources share an id are equal. -/
private theorem ctx_final_eq_of_source {ctx : Ctx m} {p a : Node}
    (hp : p ∈ ctx.final) (ha : a ∈ ctx.final) (hid : p.source.id = a.source.id) :
    p = a := by
  have hnodup2 : (ctx.final.map fun x => x.source.id).Nodup := by
    have hseedMap : ctx.seed.map Node.source = m.boxes := by
      rw [ctx.hseedEq]
      exact seeded_source m
    have hmap : ctx.final.map Node.source = m.boxes :=
      (tiled_source ctx.hfinal).trans hseedMap
    have h2 : ctx.final.map (fun x => x.source.id) = m.boxes.map (·.id) := by
      rw [← hmap, List.map_map]
      rfl
    rw [h2]
    exact Model.boxIds_nodup ctx.hwf
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
  have hi' : (ctx.final.map fun x => x.source.id)[i]? = some a.source.id := by
    rw [List.getElem?_map, hi]
    exact congrArg some hid
  have hj' : (ctx.final.map fun x => x.source.id)[j]? = some a.source.id := by
    rw [List.getElem?_map, hj]; rfl
  have hij : i = j := C8a.getElem?_pos_eq hnodup2 hi' hj'
  have hpn : p = a := by
    have hi2 : ctx.final[i]? = some a := by rw [hij]; exact hj
    exact Option.some.inj (hi.symm.trans hi2)
  exact hpn

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

/-- A dump label's id, owner and rect come from the placed label's source. -/
private theorem dumpLabel_fields (l : PlacedLabel) :
    (dumpLabel l).id = l.source.id ∧
    (dumpLabel l).owner = l.source.owner ∧
    (dumpLabel l).rect = l.rect :=
  ⟨rfl, rfl, rfl⟩

/-- Membership of a dump label gives an index and the placed label producing it. -/
private theorem dump_label_index (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) (l : Label)
    (hl : l ∈ result.scene.layoutDump.labels) :
    ∃ pl : PlacedLabel,
      l.id = pl.source.id ∧ l.owner = pl.source.owner ∧ l.rect = pl.rect ∧
      pl.source ∈ m.labels := by
  obtain ⟨nodes, titleLabels, finalLabels, hnodes, ht, hf, hts, hfs, hd⟩ :=
    public_label_execution m result h
  have hmap : result.scene.layoutDump.labels =
      finalLabels.map (fun pl => (dumpLabel pl).toLabel) := by
    have hfun : (SceneLabel.toLabel ∘ dumpLabel) = (fun pl => (dumpLabel pl).toLabel) := rfl
    show result.scene.labels.map SceneLabel.toLabel = _
    rw [hd, List.map_map, hfun]
  rw [hmap] at hl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  rw [List.getElem?_map] at hi
  obtain ⟨pl, hpl, hEq⟩ := Option.map_eq_some_iff.mp hi
  have hfields := dumpLabel_fields pl
  have hto : (dumpLabel pl).toLabel = l := hEq
  have hid : l.id = pl.source.id := by
    have := congrArg Label.id hto
    rw [hfields.1] at this
    exact this.symm
  have hown : l.owner = pl.source.owner := by
    have := congrArg Label.owner hto
    rw [hfields.2.1] at this
    exact this.symm
  have hrect : l.rect = pl.rect := by
    have := congrArg Label.rect hto
    rw [hfields.2.2] at this
    exact this.symm
  have hsrc : pl.source ∈ m.labels := by
    have hsi : (sources finalLabels)[i]? = some pl.source := by
      show (finalLabels.map (·.source))[i]? = some pl.source
      simp [List.getElem?_map, hpl]
    have hmi : m.labels[i]? = some pl.source := by
      rw [hfs] at hsi
      exact hsi
    exact List.mem_of_getElem? hmi

  exact ⟨pl, hid, hown, hrect, hsrc⟩
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
end Elegant.Treemap.C8b
