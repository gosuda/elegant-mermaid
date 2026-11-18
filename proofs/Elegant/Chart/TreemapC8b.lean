import Elegant.Chart.TreemapC8a
import Elegant.Chart.TreemapAncestorsIrrefl
import Elegant.Chart.TreemapFacts
import Elegant.Chart.TreemapLabelFacts3
import Elegant.Chart.TreemapRoutes
import Elegant.Kinds.Treemap
import ElegantGeometry.Validator

namespace Elegant.Treemap.C8b

open Elegant.Treemap.C8a
open Elegant.Treemap.CanvasC1
open Elegant.Treemap.Clearance
open Elegant.Treemap.TileForest
open Elegant.Treemap.Containment
open Elegant.Treemap.LabelFacts
open Elegant.Treemap.LabelFacts3

variable {m : Model}

/-! ### Rectangle algebra -/

/-- `StrictInside` is transitive. -/
theorem strictInside_trans {a b c : Rect} (hab : Rect.StrictInside a b)
    (hbc : Rect.StrictInside b c) : Rect.StrictInside a c := by
  unfold Rect.StrictInside at *
  omega

/-- `l` strictly inside `o`, `o` contained in `g` gives `l` strictly inside `g`. -/
theorem strictInside_of_strictInside_contained {g o l : Rect}
    (hgo : Rect.Contained g o) (hol : Rect.StrictInside o l) :
    Rect.StrictInside g l := by
  unfold Rect.Contained at hgo
  unfold Rect.StrictInside at hol ⊢
  omega

/-- `l` contained in `n`, `n` strictly inside `g` gives `l` strictly inside `g`. -/
theorem strictInside_of_contained_strictInside {g n l : Rect}
    (hgn : Rect.StrictInside g n) (hnl : Rect.Contained n l) :
    Rect.StrictInside g l := by
  unfold Rect.StrictInside at hgn ⊢
  unfold Rect.Contained at hnl
  omega

/-- `StrictInside` implies `Contained`. -/
theorem contained_of_strictInside {o i : Rect} (h : Rect.StrictInside o i) :
    Rect.Contained o i := by
  unfold Rect.StrictInside at h
  unfold Rect.Contained
  omega

/-- Containment transports disjointness from the container to the contained. -/
theorem disjoint_of_contained {l o b : Rect}
    (hlo : Rect.Contained o l) (hd : Disjoint o b) : Disjoint l b := by
  unfold Rect.Contained at hlo
  intro hm
  exact hd ⟨by omega, by omega⟩

/-- A rectangle with a non-positive side meets no interior: it is disjoint
from every rectangle. -/
theorem disjoint_of_degenerate (r s : Rect) (hd : r.w ≤ 0 ∨ r.h ≤ 0) :
    Disjoint r s := by
  unfold Disjoint Rect.meetsInterior
  rcases hd with hw | hh <;> omega

/-- A zero-size rectangle at the origin is disjoint from every rectangle with
non-negative coordinates. -/
theorem disjoint_zero_origin (r : Rect) (hx : 0 ≤ r.x) (_hy : 0 ≤ r.y) :
    Disjoint ⟨0, 0, 0, 0⟩ r := by
  unfold Disjoint Rect.meetsInterior
  dsimp only
  omega

/-- A label contained in a degenerate tile is itself degenerate. -/
theorem degenerate_of_contained {l o : Rect} (hlo : Rect.Contained o l)
    (hdeg : o.w ≤ 0 ∨ o.h ≤ 0) : l.w ≤ 0 ∨ l.h ≤ 0 := by
  unfold Rect.Contained at hlo
  rcases hdeg with hw | hh <;> omega

/-- Treemap section padding keeps a positive horizontal margin. -/
theorem treemap_padX_ge (m : Model) : 1 ≤ (constants m).padX := by
  show 1 ≤ LayoutConst.treemap_section_padding_x.get m.profile
  cases m.profile <;> decide

/-- Treemap section padding keeps a positive vertical margin. -/
theorem treemap_padY_ge (m : Model) : 1 ≤ (constants m).padY := by
  show 1 ≤ LayoutConst.treemap_section_padding_y.get m.profile
  cases m.profile <;> decide

/-- Treemap header band plus padding keeps a positive body margin. -/
theorem treemap_band_ge (m : Model) :
    1 ≤ (constants m).header + (constants m).padY := by
  have h1 : 1 ≤ (constants m).header := by
    show 1 ≤ LayoutConst.treemap_section_header.get m.profile
    cases m.profile <;> decide
  have h2 := treemap_padY_ge m
  omega

/-! ### Geometric kernels

The six facts of `Kernels` are the geometric content of C8b over the executed
tiling.  Each is a statement about `ctx.final` node rectangles and the label
writes of `placeTitle`/`placeHeader`/`placeLeaf`.  They are OPEN: the intended
proofs use the `childArea`/`insetCell`/`squarify` margin structure and the
`LeafWriteRun`/`HeaderWriteRun` equations.  `treemap_c8b` is proved from them. -/

/-- The open geometric kernels of clause C8b for one model. -/
structure Kernels (m : Model) : Prop where
  /-- Every label of the dump is accounted for: either it is an untouched
  invisible label with the zero rectangle, the written title label inside the
  title band with `bandOf` equal to the title band, or a label written at its
  owner node's step whose rectangle is strictly inside the owner tile, or
  merely contained when the owner is a non-group leaf node (the vector leaf
  flush cases). -/
  label_owner_cases : ∀ (ctx : Ctx m) (result : Layered.FamilyResult),
    WellFormed m → Kinds.Treemap.layout m = .ok result →
    ∀ (l : Label), l ∈ result.scene.layoutDump.labels →
    l.rect = ⟨0, 0, 0, 0⟩ ∨
    (l.id = "title" ∧ bandOf m = (constants m).titleBand ∧
      Rect.Contained ⟨0, 0, (constants m).width, (constants m).titleBand⟩ l.rect) ∨
    ∃ n : Node, n ∈ ctx.final ∧ n.source.id = l.owner ∧
      (Rect.StrictInside (tileRect n.rect) l.rect ∨
        (n.source.role ≠ .group ∧ Rect.Contained (tileRect n.rect) l.rect))
  /-- A final node either has non-negative tile coordinates or a degenerate
  tile. -/
  tileRect_nonneg_or_degenerate : ∀ (ctx : Ctx m) (n : Node), n ∈ ctx.final →
    0 ≤ (tileRect n.rect).x ∧ 0 ≤ (tileRect n.rect).y ∨
      (tileRect n.rect).w ≤ 0 ∨ (tileRect n.rect).h ≤ 0
  /-- Every final tile lies at or below the title band, unless it is
  degenerate. -/
  tile_below_band_or_degenerate : ∀ (ctx : Ctx m) (n : Node), n ∈ ctx.final →
    bandOf m ≤ (tileRect n.rect).y ∨
      (tileRect n.rect).w ≤ 0 ∨ (tileRect n.rect).h ≤ 0
  /-- Proper descendants are strictly inside their ancestors, or degenerate:
  the per-step fact (a child tile produced by `tileStep` is strictly inside its
  parent's tile, or degenerate) transported along the parent chain. -/
  tile_strictInside_ancestor : ∀ (ctx : Ctx m) (a b : Node),
    a ∈ ctx.final → b ∈ ctx.final →
    a.source.id ∈ boxAncestors m.boxes m.boxes.length b.source.id →
    a.source.id ≠ b.source.id →
    Rect.StrictInside (tileRect a.rect) (tileRect b.rect) ∨
      (tileRect b.rect).w ≤ 0 ∨ (tileRect b.rect).h ≤ 0
  /-- A header-band label of an internal node is vertically clear of every
  proper descendant tile: the descendant's top edge lies at or below the
  label's bottom edge, so the rectangles are disjoint. -/
  descendant_tile_clear_of_header_label : ∀ (ctx : Ctx m) (n g : Node) (l : Rect),
    n ∈ ctx.final → g ∈ ctx.final →
    n.source.id ∈ boxAncestors m.boxes m.boxes.length g.source.id →
    n.source.id ≠ g.source.id →
    l.y + l.h ≤ (tileRect n.rect).y + (constants m).header + (constants m).padY →
    Rect.StrictInside (tileRect n.rect) l →
    Disjoint (tileRect g.rect) l
  /-- A label written for an internal node is a `placeHeader` band write: its
  rectangle sits strictly inside the node tile and its bottom edge lies at or
  below the header band bottom (`tileRect.y + header + padY` bounds the body
  area below the band). This covers both the `.name` and `.value` header
  writes; untouched labels owned by internal nodes keep the zero rectangle and
  are excluded by the strict containment. -/
  internal_label_header_band : ∀ (ctx : Ctx m) (result : Layered.FamilyResult),
    WellFormed m → Kinds.Treemap.layout m = .ok result →
    ∀ (n : Node), n ∈ ctx.final → ∀ (l : Label),
    l ∈ result.scene.layoutDump.labels → n.source.id = l.owner →
    (∃ g : Node, g ∈ ctx.final ∧
      n.source.id ∈ boxAncestors m.boxes m.boxes.length g.source.id) →
    l.rect.y + l.rect.h ≤ (tileRect n.rect).y +
        (constants m).header + (constants m).padY ∧
      Rect.StrictInside (tileRect n.rect) l.rect

/-! ### The dump-level bridge -/

/-- Clause C8b of the validator for the treemap adapter, from the open
geometric kernels. -/
theorem treemap_c8b (m : Model) (result : Layered.FamilyResult)
    (K : Kernels m)
    (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : Kinds.Treemap.layout m = .ok result) :
    Validator.C8b result.scene.layoutDump := by
  intro g hg hrole hl hlmem
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
  rw [hdBoxes] at hg
  obtain ⟨G, hGmem, hG⟩ := List.mem_map.mp hg
  have hGrect : g.rect = tileRect G.rect := by
    have := congrArg Box.rect hG
    simpa using this.symm
  have hGid : g.id = G.source.id := by
    have := congrArg Box.id hG
    simpa using this.symm
  -- Case analysis on the label.
  rcases K.label_owner_cases hctx result hwf h hl hlmem with hzero | htitle | hown
  · -- Untouched invisible label: the zero rectangle meets no interior.
    rw [hzero, hGrect]
    rcases K.tileRect_nonneg_or_degenerate hctx G hGmem with ⟨hx, hy⟩ | hw | hh
    · unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
    · exact Or.inl (disjoint_of_degenerate _ _ (Or.inl hw))
    · exact Or.inl (disjoint_of_degenerate _ _ (Or.inr hh))
  · -- The written title label sits in the title band; every non-degenerate
    -- tile lies at or below the band.
    obtain ⟨_, hband2, hcont⟩ := htitle
    rw [hGrect]
    rcases K.tile_below_band_or_degenerate hctx G hGmem with hy | hw | hh
    · left
      unfold Disjoint Rect.meetsInterior
      intro h
      unfold Rect.Contained at hcont
      obtain ⟨_, _, _, hyb⟩ := hcont
      dsimp only at hyb
      rw [hband2] at hy
      have := h.2
      omega
    · exact Or.inl (disjoint_of_degenerate _ _ (Or.inl hw))
    · exact Or.inl (disjoint_of_degenerate _ _ (Or.inr hh))
  · -- A written label owned by node `n`.
    obtain ⟨n, hnmem, hnid, hrel⟩ := hown
    have hnmem2 : n ∈ nodes2 := hnmem
    -- `n`'s dump box has the same id, parent, and tile rectangle as `n`.
    let bN : Box :=
      { id := n.source.id, role := n.source.role.id,
        rect := tileRect n.rect, parent := n.source.parent,
        exclusive := n.source.exclusive }
    have hnBox : bN ∈ result.scene.layoutDump.boxes := by
      rw [hdBoxes]
      exact List.mem_map.mpr ⟨n, hnmem2, rfl⟩
    -- Ancestor bookkeeping between `G` and `n` through `boxAncestors`.
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
    have hAncG : ∀ x : String, x ∈ result.scene.layoutDump.ancestors g.id ↔
        x ∈ boxAncestors m.boxes m.boxes.length g.id := by
      intro x
      have hgo : result.scene.layoutDump.ancestors g.id =
          LayoutDump.ancestors.go result.scene.layoutDump
            result.scene.layoutDump.boxes.length g.id := rfl
      have hA := dump_ancestors_eq result.scene.layoutDump m.boxes hfind hf hbb
        result.scene.layoutDump.boxes.length g.id
      rw [hgo, hA, hlen]
    have hAncN : ∀ x : String, x ∈ result.scene.layoutDump.ancestors n.source.id ↔
        x ∈ boxAncestors m.boxes m.boxes.length n.source.id := by
      intro x
      have hgo : result.scene.layoutDump.ancestors n.source.id =
          LayoutDump.ancestors.go result.scene.layoutDump
            result.scene.layoutDump.boxes.length n.source.id := rfl
      have hA := dump_ancestors_eq result.scene.layoutDump m.boxes hfind hf hbb
        result.scene.layoutDump.boxes.length n.source.id
      rw [hgo, hA, hlen]
    -- The three relations between `G` and `n`.
    by_cases hGancN : G.source.id ∈
        boxAncestors m.boxes m.boxes.length n.source.id
    · -- `G` is a proper ancestor of `n`.
      have hneGN : G.source.id ≠ n.source.id := by
        intro he
        exact boxAncestors_irrefl m hwf n.source.id (he ▸ hGancN)
      rcases K.tile_strictInside_ancestor hctx G n hGmem hnmem2 hGancN hneGN with
        hstrict | hw | hh
      · rcases hrel with hls | ⟨_, hlc⟩
        · exact Or.inr (by
            rw [hGrect]
            exact strictInside_of_strictInside_contained
              (contained_of_strictInside hstrict) hls)
        · exact Or.inr (by
            rw [hGrect]
            exact strictInside_of_contained_strictInside hstrict hlc)
      · have hdeg := degenerate_of_contained (by
            rcases hrel with h | ⟨_, hc⟩
            · exact contained_of_strictInside h
            · exact hc) (Or.inl hw)
        rw [hGrect]
        exact Or.inl ((Disjoint.comm _ _).mp (disjoint_of_degenerate _ _ hdeg))
      · have hdeg := degenerate_of_contained (by
            rcases hrel with h | ⟨_, hc⟩
            · exact contained_of_strictInside h
            · exact hc) (Or.inr hh)
        rw [hGrect]
        exact Or.inl ((Disjoint.comm _ _).mp (disjoint_of_degenerate _ _ hdeg))
    · by_cases hNancG : n.source.id ∈
          boxAncestors m.boxes m.boxes.length G.source.id
      · -- `n` is a proper ancestor of `G`: header-band clearance.
        have hneNG : n.source.id ≠ G.source.id := by
          intro he
          exact boxAncestors_irrefl m hwf G.source.id (he ▸ hNancG)
        obtain ⟨hband, hinside⟩ := K.internal_label_header_band hctx result hwf
          h n hnmem2 hl hlmem hnid ⟨G, hGmem, hNancG⟩
        have hdisjG := K.descendant_tile_clear_of_header_label hctx n G hl.rect
          hnmem2 hGmem hNancG hneNG hband hinside
        rw [hGrect]
        exact Or.inl hdisjG
      · -- Unrelated or identical: identical ids collapse to the same node
        -- (source ids are nodup), whereupon the label sits inside `g`.
        by_cases heq : G.source.id = n.source.id
        · have hnodup2 : (nodes2.map fun x => x.source.id).Nodup := by
            have hmap : nodes2.map Node.source = m.boxes :=
              (tiled_source hnodes2).trans (seeded_source m)
            have h2 : nodes2.map (fun x => x.source.id) = m.boxes.map (·.id) := by
              rw [← hmap, List.map_map]
              rfl
            rw [h2]
            exact Model.boxIds_nodup hwf
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hGmem
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hnmem2
          have hi' : (nodes2.map fun x => x.source.id)[i]? = some G.source.id := by
            rw [List.getElem?_map, hi]; rfl
          have hj' : (nodes2.map fun x => x.source.id)[j]? = some G.source.id := by
            rw [List.getElem?_map, hj]
            exact congrArg some heq.symm
          have hij : i = j := C8a.getElem?_pos_eq hnodup2 hi' hj'
          have hGn : G = n := by
            have hi2 : nodes2[i]? = some n := by rw [hij]; exact hj
            exact Option.some.inj (hi.symm.trans hi2)
          rw [hGn] at hG
          rw [← hG]
          rcases hrel with hls | ⟨hrole_ne, _hlc⟩
          · exact Or.inr hls
          · exfalso
            have hrole' : n.source.role.id = "group" := by
              have h2 := congrArg Box.role hG
              rw [hrole] at h2
              exact h2
            cases hrr : n.source.role with
            | node => simp [BoxRole.id, hrr] at hrole'
            | group => exact hrole_ne hrr
        · -- Genuinely unrelated: the tiles are disjoint, and the label is
          -- contained in `n`'s tile.
          have hdisj := treemap_tiles_laminar_disjoint m result hwf h g
            (hdBoxes ▸ hg) bN hnBox
            (by
              intro hbad
              apply heq
              rw [← hGid]
              exact hbad)
            (by
              intro hx
              have hbNid : bN.id = n.source.id := rfl
              rw [hbNid, hGid] at hx
              exact hGancN ((hAncN G.source.id).mp hx))
            (by
              intro hx
              have hbNid : bN.id = n.source.id := rfl
              rw [hbNid] at hx
              change n.source.id ∈ result.scene.layoutDump.ancestors g.id at hx
              have hx2 := (hAncG n.source.id).mp hx
              rw [hGid] at hx2
              exact hNancG hx2)
          have hdisj' : Disjoint (tileRect G.rect) (tileRect n.rect) := by
            rw [← hGrect]
            exact hdisj
          have hd : Disjoint (tileRect n.rect) (tileRect G.rect) :=
            (Disjoint.comm _ _).mp hdisj'
          rw [hGrect]
          rcases hrel with hls | ⟨_, hlc⟩
          · exact Or.inl ((Disjoint.comm _ _).mp
              (disjoint_of_contained (contained_of_strictInside hls) hd))
          · exact Or.inl ((Disjoint.comm _ _).mp
              (disjoint_of_contained hlc hd))

end Elegant.Treemap.C8b
