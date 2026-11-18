import Elegant.Kinds.Ishikawa
import Elegant.IshikawaOrthogonalityFacts
import Elegant.TreeNormalized
import Elegant.IshikawaLayoutProvenanceFacts
import Elegant.Kinds.IshikawaDecodeDepthFacts
import Elegant.Kinds.IshikawaValid

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaOrthogonalityFacts

theorem placed_route_depth_origin (ns : List Tree.Node)
    (p : Elegant.Ishikawa.Params) (spine : Int)
    (r placed : Elegant.Ishikawa.Rib)
    (hrun : Elegant.Ishikawa.place ns p spine r = .ok placed)
    (i : Nat) (rect : Rect) (pts : List Point)
    (hmem : (i, rect, pts) ∈ placed.pieces) :
    i = r.cause ∨ ∃ e ∈ r.entries, i = e.node ∧
      (e.depth % 2 = 0 → Polyline.isOrthogonal pts = true) := by
  rcases Elegant.Ishikawa.place_piece_depth_geometry ns p spine r placed hrun
      i rect pts hmem with hc | ⟨e, he, hi, a, b, hpts, hhorizontal⟩
  · exact Or.inl hc
  · refine Or.inr ⟨e, he, hi, ?_⟩
    intro heven
    rw [hpts]
    simp [Polyline.isOrthogonal, hhorizontal heven]

theorem normalized_route_orthogonality_origin (margin : Int)
    (raw placed : Tree.Layout) (canvas : Size)
    (hn : Tree.normalize margin raw = .ok (canvas, placed))
    (k : Nat) (pts : List Point) (hpts : placed.routes[k]? = some pts) :
    ∃ original : List Point, raw.routes[k]? = some original ∧
      Polyline.isOrthogonal pts = Polyline.isOrthogonal original := by
  obtain ⟨dx, dy, _, hroutes⟩ := Tree.normalize_records hn
  rw [hroutes, List.getElem?_map, Option.map_eq_some_iff] at hpts
  obtain ⟨original, horiginal, rfl⟩ := hpts
  exact ⟨original, horiginal, Tree.orthogonal_translate dx dy original⟩

theorem placed_flattened_rib_even_orthogonal (ns : List Tree.Node)
    (depths : List Nat) (hroot : depths[0]? = some 0)
    (hchildren : ∀ parent depth, depths[parent]? = some depth →
      ∀ i ∈ Elegant.Ishikawa.children ns parent, depths[i]? = some (depth + 1))
    (p : Elegant.Ishikawa.Params) (spine : Int)
    (r placed : Elegant.Ishikawa.Rib) (causeIndex : Nat)
    (hcause : r.cause ∈ Elegant.Ishikawa.children ns 0)
    (hentries : r.entries =
      (Elegant.Ishikawa.flatten ns (Elegant.Ishikawa.upper causeIndex) 64
        (Elegant.Ishikawa.children ns r.cause) (-1) 2 [] []).1)
    (hrun : Elegant.Ishikawa.place ns p spine r = .ok placed)
    (i depth : Nat) (rect : Rect) (pts : List Point)
    (hmem : (i, rect, pts) ∈ placed.pieces)
    (hdepth : depths[i]? = some depth) (heven : depth % 2 = 0) :
    Polyline.isOrthogonal pts = true := by
  obtain ⟨hc, he⟩ := Elegant.Ishikawa.cause_and_flatten_depth_lookup ns depths
    hroot hchildren r.cause causeIndex hcause
  rcases placed_route_depth_origin ns p spine r placed hrun i rect pts hmem with
    hi | ⟨e, hm, hi, horth⟩
  · rw [hi, hc] at hdepth
    have hd : depth = 1 := (Option.some.inj hdepth).symm
    omega
  · rw [hentries] at hm
    have hd := he e hm
    rw [hi, hd] at hdepth
    have heq : e.depth = depth := Option.some.inj hdepth
    exact horth (by omega)

theorem raw_even_depth_orthogonal (ns : List Tree.Node) (depths : List Nat)
    (hroot : depths[0]? = some 0)
    (hchildren : ∀ parent depth, depths[parent]? = some depth →
      ∀ i ∈ Elegant.Ishikawa.children ns parent, depths[i]? = some (depth + 1))
    (p : Elegant.Ishikawa.Params) (raw : Tree.Layout)
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (k depth : Nat) (pts : List Point)
    (hdepth : depths[k]? = some depth) (heven : depth % 2 = 0)
    (hpts : raw.routes[k]? = some pts) : Polyline.isOrthogonal pts = true := by
  rcases Elegant.Ishikawa.layout_origin ns p raw hrun with hempty | horigin
  · rw [hempty.2] at hpts
    simp at hpts
  · obtain ⟨ribs, length, spine, placedRibs, head, hg, _hlength, _hspine,
      hplaces, _hhead, hassemble⟩ := horigin
    have hroute := Elegant.Ishikawa.assemblePairs_route_origin spine
      placedRibs.length placedRibs _ _ _ raw (Nat.le_refl _) hassemble k pts hpts
    rcases hroute with hinitial | hspine | hpiece
    · have hempty : pts = [] := by
        have hm := List.mem_of_getElem? hinitial
        exact (List.mem_replicate.mp hm).2
      subst pts
      rfl
    · obtain ⟨_, x, rfl⟩ := hspine
      simp [Polyline.isOrthogonal]
    · obtain ⟨r, hr, rect, original, dx, hmem, rfl⟩ := hpiece
      obtain ⟨source, cause, index, _hsource, hcause, heq, hplace⟩ :=
        Elegant.Ishikawa.placed_rib_source ns p ribs placedRibs length spine
          hg hplaces r hr
      have hfields := Elegant.Ishikawa.generated_rib_fields ns cause index
      have hc : source.cause = cause :=
        (congrArg Elegant.Ishikawa.Rib.cause heq).trans hfields.1
      have he : source.entries =
          (Elegant.Ishikawa.flatten ns (Elegant.Ishikawa.upper index) 64
            (Elegant.Ishikawa.children ns source.cause) (-1) 2 [] []).1 := by
        have he0 := (congrArg Elegant.Ishikawa.Rib.entries heq).trans
          (congrArg Prod.fst hfields.2.2.1)
        simpa only [hc] using he0
      have hchild : source.cause ∈ Elegant.Ishikawa.children ns 0 := by
        rw [hc]
        exact List.fst_mem_of_mem_zipIdx hcause
      have ho := placed_flattened_rib_even_orthogonal ns depths
        hroot hchildren p spine
        (Elegant.Ishikawa.effectivePlacedInput ns length source)
        r index hchild he hplace k depth rect original hmem hdepth heven
      simpa only [Int.add_zero] using
        (Tree.orthogonal_translate dx 0 original).trans ho

theorem normalized_even_depth_orthogonal (ns : List Tree.Node) (depths : List Nat)
    (hroot : depths[0]? = some 0)
    (hchildren : ∀ parent depth, depths[parent]? = some depth →
      ∀ i ∈ Elegant.Ishikawa.children ns parent, depths[i]? = some (depth + 1))
    (p : Elegant.Ishikawa.Params) (raw placed : Tree.Layout)
    (margin : Int) (canvas : Size)
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (hn : Tree.normalize margin raw = .ok (canvas, placed))
    (k depth : Nat) (pts : List Point)
    (hdepth : depths[k]? = some depth) (heven : depth % 2 = 0)
    (hpts : placed.routes[k]? = some pts) : Polyline.isOrthogonal pts = true := by
  obtain ⟨original, horiginal, horth⟩ :=
    normalized_route_orthogonality_origin margin raw placed canvas hn k pts hpts
  rw [horth]
  exact raw_even_depth_orthogonal ns depths hroot hchildren p raw hrun
    k depth original hdepth heven horiginal

theorem normalized_empty_routes (p : Elegant.Ishikawa.Params)
    (raw placed : Tree.Layout) (margin : Int) (canvas : Size)
    (hrun : Elegant.Ishikawa.layout [] p = .ok raw)
    (hn : Tree.normalize margin raw = .ok (canvas, placed)) :
    placed.routes = [] := by
  have he : raw = (⟨[], []⟩ : Tree.Layout) := by
    simpa [Elegant.Ishikawa.layout, pure, Except.pure] using hrun.symm
  obtain ⟨dx, dy, _, hroutes⟩ := Tree.normalize_records hn
  simpa [he] using hroutes

theorem ishikawa_c4 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (hlayout : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    Validator.C4 result.scene.layoutDump := by
  apply Elegant.Kinds.IshikawaValid.ishikawa_c4_of_placed m result hwf hlimits
    ?_ hlayout
  intro input canvas placed hdecode hexecution k depth pts hdepth hpts heven
  obtain ⟨raw, hraw, hnormal⟩ := hexecution
  by_cases hempty : input.nodes = []
  · have he := normalized_empty_routes (Elegant.Kinds.Ishikawa.params m.profile)
      raw placed (LayoutConst.canvas_margin.get m.profile) canvas
      (by simpa only [hempty] using hraw) hnormal
    rw [he] at hpts
    simp at hpts
  · obtain ⟨path, hstate⟩ :=
      Elegant.Kinds.Ishikawa.successful_decode_depth_state hdecode
    have hroot := Elegant.Kinds.Ishikawa.decodeDepthState_nonempty_root
      input path hstate hempty
    exact normalized_even_depth_orthogonal input.nodes input.depths hroot
      (Elegant.Kinds.Ishikawa.decodeParentDepth_children input.nodes input.depths
        hstate.parentDepth)
      (Elegant.Kinds.Ishikawa.params m.profile) raw placed
      (LayoutConst.canvas_margin.get m.profile) canvas hraw hnormal
      k depth pts hdepth heven hpts

end Elegant.Kinds.IshikawaOrthogonalityFacts
