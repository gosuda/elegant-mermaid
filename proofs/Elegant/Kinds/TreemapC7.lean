import Elegant.Chart.TreemapC8a
import Elegant.Chart.TreemapC8b
import Elegant.Chart.TreemapC8bKernelFacts
import Elegant.Chart.TreemapContainmentFacts
import Elegant.Chart.TreemapFacts
import Elegant.Chart.TreemapLabelFacts
import Elegant.Chart.TreemapLabelFacts2
import Elegant.Chart.TreemapLabelFacts3
import Elegant.Chart.TreemapRoutes
import Elegant.Kinds.Treemap
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Kinds.Treemap

open Elegant.Treemap
open Elegant.Treemap.C8a
open Elegant.Treemap.CanvasC1
open Elegant.Treemap.C8b
open Elegant.Treemap.LabelFacts
open Elegant.Treemap.LabelFacts3
open Elegant.Treemap.TileForest
/-! ### Small rectangle helpers -/

/-- A zero-size rectangle meets no interior (left variant). -/
theorem c7_meetsInterior_zero_left (r : Rect) :
    ¬ Rect.meetsInterior ⟨0, 0, 0, 0⟩ r := by
  show ¬ ((max 0 r.x < min (0 + 0) (r.x + r.w)) ∧
    (max 0 r.y < min (0 + 0) (r.y + r.h)))
  intro h
  obtain ⟨h1, h2⟩ := h
  omega

/-- Containment transports disjointness from the container to the contained. -/
theorem c7_disjoint_of_contained {l o b : Rect}
    (hlo : Rect.Contained o l) (hd : Disjoint o b) : Disjoint l b := by
  unfold Rect.Contained at hlo
  intro hm
  exact hd ⟨by omega, by omega⟩

/-! ### String suffix lemmas -/

/-- `".value"` and `".name"` cannot be the suffixes of equal strings. -/
theorem c7_suffix_ne_value_name (a b : String) :
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
theorem c7_append_name_cancel {a b : String} (h : a ++ ".name" = b ++ ".name") :
    a = b := by
  have h2 := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_right h2)

/-- Cancelling a common `".value"` suffix. -/
theorem c7_append_value_cancel {a b : String} (h : a ++ ".value" = b ++ ".value") :
    a = b := by
  have h2 := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_right h2)

/-- `"title"` is not a `".name"`-suffixed string. -/
theorem c7_title_ne_name (a : String) : a ++ ".name" ≠ "title" := by
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
theorem c7_title_ne_value (a : String) : a ++ ".value" ≠ "title" := by
  intro h
  have h6 : ".value".length = 6 := rfl
  have h5 : "title".length = 5 := rfl
  have h2 := congrArg String.length h
  simp only [String.length_append, h6, h5] at h2
  omega

/-- A checked `width` call is nonnegative. -/
theorem c7_width_nonneg {cell : Bool} {text : String} {role : Measure.Role}
    {size x : Int} (h : width cell text role size = .ok x) : 0 ≤ x := by
  unfold width at h
  obtain ⟨metric, _, hw⟩ := CanvasC1.except_bind_ok h
  exact Measure.textWidth_nonneg hw

/-! ### Clause C7 from the C8b kernels -/

/-- Clause C7 of the validator for the treemap adapter, from the geometric
kernels of `Elegant.Treemap.C8b.Kernels`.  The exclusive boxes of a dump are
exactly the tiles carrying `source.exclusive`, which need not be false for
non-group boxes (well-formedness only forces groups non-exclusive), so the
clause is a genuine label-versus-tile clearance statement. -/
theorem treemap_c7_of_kernels (m : Model) (result : Layered.FamilyResult)
    (K : Elegant.Treemap.C8b.Kernels m) :
    WellFormed m → WithinLimits m → Kinds.Treemap.layout m = .ok result →
    Validator.C7 result.scene.layoutDump := by
  intro hwf _hlimits h
  intro l hl b hb _hbexc hnotin
  obtain ⟨nodes, titleLabels, finalLabels, hnodes, ht, hf, hts, hfs, hd⟩ :=
    public_label_execution m result h
  obtain ⟨nodes2, hnodes2, hboxes, _, _⟩ :=
    layout_execution m result.scene (Kinds.Treemap.layout_adapter_success m result h)
  have hnodes_eq : nodes = nodes2 := by
    have h1 : tileNodes (constants m) (seededNodes m) = .ok nodes := hnodes
    have h2 : tileNodes (constants m) (seededNodes m) = .ok nodes2 := hnodes2
    exact Except.ok.inj (h1.symm.trans h2)
  let hctx : Ctx m := Ctx.forLayout m result hwf h nodes2 hnodes2
  have hdBoxes : result.scene.layoutDump.boxes = nodes2.map (fun n : Node =>
      ({ id := n.source.id, role := n.source.role.id, rect := tileRect n.rect,
         parent := n.source.parent, exclusive := n.source.exclusive } : Box)) := by
    show result.scene.boxes = _
    exact hboxes
  rw [hdBoxes] at hb
  obtain ⟨B, hBmem, hBeq⟩ := List.mem_map.mp hb
  have hBrect : b.rect = tileRect B.rect := by
    have := congrArg Box.rect hBeq
    simpa using this.symm
  have hBid : b.id = B.source.id := by
    have := congrArg Box.id hBeq
    simpa using this.symm
  have hroutes : result.scene.layoutDump.routes = [] := layout_routes_eq_nil m result h
  have hanc : result.scene.layoutDump.labelOwnerAnc l =
      l.owner :: result.scene.layoutDump.ancestors l.owner := by
    unfold LayoutDump.labelOwnerAnc
    rw [hroutes]
    rfl
  rw [hanc, List.mem_cons] at hnotin
  have hBowner : b.id ≠ l.owner := fun he => hnotin (Or.inl he)
  have hBanc : b.id ∉ result.scene.layoutDump.ancestors l.owner :=
    fun hm => hnotin (Or.inr hm)
  by_cases hdeg : (tileRect B.rect).w ≤ 0 ∨ (tileRect B.rect).h ≤ 0
  · rw [hBrect]
    exact (Disjoint.comm _ _).mp (disjoint_of_degenerate _ _ hdeg)
  · have hdegw : 0 < (tileRect B.rect).w := by omega
    have hdegh : 0 < (tileRect B.rect).h := by omega
    rcases K.label_owner_cases hctx result hwf h l hl with hzero | htitle | hown
    · rw [hzero]
      exact c7_meetsInterior_zero_left b.rect
    · obtain ⟨_, hband2, hcont⟩ := htitle
      rw [hBrect]
      rcases K.tile_below_band_or_degenerate hctx B hBmem with hy | hw | hh
      · unfold Rect.meetsInterior
        intro hm
        unfold Rect.Contained at hcont
        obtain ⟨_, _, _, hyb⟩ := hcont
        dsimp only at hyb
        rw [hband2] at hy
        have := hm.2
        omega
      · exact absurd hw (by omega)
      · exact absurd hh (by omega)
    · obtain ⟨n, hnmem, hnid, hrel⟩ := hown
      have hnmem2 : n ∈ nodes2 := hnmem
      let bN : Box :=
        { id := n.source.id, role := n.source.role.id,
          rect := tileRect n.rect, parent := n.source.parent,
          exclusive := n.source.exclusive }
      have hnBox : bN ∈ result.scene.layoutDump.boxes := by
        rw [hdBoxes]
        exact List.mem_map.mpr ⟨n, hnmem2, rfl⟩
      have hlen : result.scene.layoutDump.boxes.length = m.boxes.length := by
        rw [hdBoxes, List.length_map]
        have h1len : nodes2.length =
            ((assignSeries (aggregate (initialNodes m))).map
              (presetNode m (bandOf m))).length := by
          simpa using congrArg List.length (tiled_source hnodes2)
        have h2len : ((assignSeries (aggregate (initialNodes m))).map
            (presetNode m (bandOf m))).length = m.boxes.length := by
          simpa using congrArg List.length (seeded_source m)
        omega
      have hbb : ∀ b ∈ m.boxes, ∃ c ∈ result.scene.layoutDump.boxes,
          c.id = b.id ∧ c.parent = b.parent := by
        intro b hb
        obtain ⟨p, hp, hpsrc⟩ := ctx_final_node_of_box (ctx := hctx) b hb
        refine ⟨⟨p.source.id, p.source.role.id, tileRect p.rect, p.source.parent,
          p.source.exclusive⟩, ?_, ?_, ?_⟩
        · rw [hdBoxes]
          exact List.mem_map.mpr ⟨p, hp, rfl⟩
        · rw [hpsrc]
        · rw [hpsrc]
      have hfind : ∀ b ∈ m.boxes,
          m.boxes.find? (fun x : ModelBox => x.id == b.id) = some b :=
        fun b hb => ctx_find_box (ctx := hctx) b hb
      have hf : ∀ c ∈ result.scene.layoutDump.boxes,
          ∃ b ∈ m.boxes, b.id = c.id ∧ b.parent = c.parent := by
        intro c hc
        rw [hdBoxes] at hc
        obtain ⟨nn, hn, rfl⟩ := List.mem_map.mp hc
        exact ⟨nn.source, ctx_src_mem (ctx := hctx) nn hn, rfl, rfl⟩
      have hAncN : ∀ x : String, x ∈ result.scene.layoutDump.ancestors n.source.id ↔
          x ∈ boxAncestors m.boxes m.boxes.length n.source.id := by
        intro x
        have hgo : result.scene.layoutDump.ancestors n.source.id =
            LayoutDump.ancestors.go result.scene.layoutDump
              result.scene.layoutDump.boxes.length n.source.id := rfl
        have hA := dump_ancestors_eq result.scene.layoutDump m.boxes hfind hf hbb
          result.scene.layoutDump.boxes.length n.source.id
        rw [hgo, hA, hlen]
      have hAncB : ∀ x : String, x ∈ result.scene.layoutDump.ancestors b.id ↔
          x ∈ boxAncestors m.boxes m.boxes.length b.id := by
        intro x
        have hgo : result.scene.layoutDump.ancestors b.id =
            LayoutDump.ancestors.go result.scene.layoutDump
              result.scene.layoutDump.boxes.length b.id := rfl
        have hA := dump_ancestors_eq result.scene.layoutDump m.boxes hfind hf hbb
          result.scene.layoutDump.boxes.length b.id
        rw [hgo, hA, hlen]
      by_cases hBancN : B.source.id ∈
          boxAncestors m.boxes m.boxes.length n.source.id
      · exfalso
        rw [← hBid] at hBancN
        have hmem1 : b.id ∈ result.scene.layoutDump.ancestors n.source.id :=
          (hAncN b.id).mpr hBancN
        rw [hnid] at hmem1
        exact hBanc hmem1
      · by_cases hNancB : n.source.id ∈
            boxAncestors m.boxes m.boxes.length B.source.id
        · have hne : n.source.id ≠ B.source.id := by
            intro he
            exact boxAncestors_irrefl m hwf B.source.id (he ▸ hNancB)
          obtain ⟨hband, hstrict⟩ := K.internal_label_header_band hctx result hwf h
            n hnmem2 l hl hnid ⟨B, hBmem, hNancB⟩
          rcases hstrict with hinside | hzero2 | htitle2
          · have hdisj := K.descendant_tile_clear_of_header_label hctx n B l.rect
              hnmem2 hBmem hNancB hne hband hinside
            rw [hBrect]
            exact (Disjoint.comm _ _).mp hdisj
          · rw [hzero2]
            exact c7_meetsInterior_zero_left b.rect
          · obtain ⟨_, hband2, hcont⟩ := htitle2
            rw [hBrect]
            rcases K.tile_below_band_or_degenerate hctx B hBmem with hy | hw | hh
            · unfold Rect.meetsInterior
              intro hm
              unfold Rect.Contained at hcont
              obtain ⟨_, _, _, hyb⟩ := hcont
              dsimp only at hyb
              rw [hband2] at hy
              have := hm.2
              omega
            · exact absurd hw (by omega)
            · exact absurd hh (by omega)
        · have hdisj : Disjoint b.rect bN.rect :=
            treemap_tiles_laminar_disjoint m result hwf h b (hdBoxes ▸ hb) bN hnBox
              (by
                have hbNid : bN.id = n.source.id := rfl
                rw [hbNid, hnid]
                exact hBowner)
              (by
                have hbNid : bN.id = n.source.id := rfl
                rw [hbNid, hnid]
                exact hBanc)
              (by
                have hbNid : bN.id = n.source.id := rfl
                rw [hbNid]
                intro hx
                have hx2 := (hAncB n.source.id).mp hx
                rw [hBid] at hx2
                exact hNancB hx2)
          have hdisj' : Disjoint bN.rect b.rect := (Disjoint.comm _ _).mp hdisj
          exact c7_disjoint_of_contained (by
            rcases hrel with hls | ⟨_, hlc⟩
            · exact contained_of_strictInside hls
            · exact hlc) hdisj'

end Elegant.Kinds.Treemap
