import Elegant.Kinds.MindmapFacts

set_option autoImplicit false

namespace Elegant
namespace Kinds
namespace Mindmap

open Common

private theorem build_route_origin {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {out : Tree.Layout} {r : Route}
    (hr : r ∈ (build m c measured canvas out).routes) :
    ∃ mr ∈ m.routes,
      r = ⟨mr.id, mr.fromId, mr.toId, mr.orthogonal,
        out.routes.getD (boxIndex m mr.toId) []⟩ := by
  obtain ⟨mr, hmr, he⟩ := List.mem_map.mp hr
  exact ⟨mr, hmr, he.symm⟩

private theorem built_boxes_disjoint {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {raw out : Tree.Layout}
    (hlen : measured.length = m.boxes.length) (hc : load m = .ok c)
    (h0 : 0 < m.boxes.length)
    (hl : Tree.mindmap (measuredNodes m measured) ⟨c.levelGap, c.siblingGap⟩ = .ok raw)
    (hn : Tree.normalize c.margin raw = .ok (canvas, out))
    {a b : Box} (ha : a ∈ (build m c measured canvas out).boxes)
    (hb : b ∈ (build m c measured canvas out).boxes) (hab : a.id ≠ b.id) :
    Disjoint a.rect b.rect := by
  have hns := measuredNodes_length hlen
  have hn0 : 0 < (measuredNodes m measured).length := by rw [hns]; exact h0
  obtain ⟨hv, hr⟩ := Tree.mindmap_nonempty hn0 hl
  obtain ⟨hL, hs, _⟩ := load_nonneg hc
  obtain ⟨i, ma, ra, hma, hra, rfl⟩ := build_box_origin ha
  obtain ⟨j, mb, rb, hmb, hrb, rfl⟩ := build_box_origin hb
  apply Tree.normalized_disjoint hL hs hv hn0 hr hn hra hrb
  intro hij
  subst j
  exact hab (congrArg ModelBox.id (Option.some.inj (hma.symm.trans hmb)))

private theorem built_route_geometry {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {raw out : Tree.Layout} (hwf : WellFormed m)
    (hlen : measured.length = m.boxes.length) (hc : load m = .ok c)
    (h0 : 0 < m.boxes.length) (hrel : treeRelations m = true)
    (hl : Tree.mindmap (measuredNodes m measured) ⟨c.levelGap, c.siblingGap⟩ = .ok raw)
    (hn : Tree.normalize c.margin raw = .ok (canvas, out))
    {r : Route} (hr : r ∈ (build m c measured canvas out).routes) :
    Polyline.isOrthogonal r.points = true ∧
      ∃ a b : Point, ∃ fb tb : Box,
        r.points.head? = some a ∧ r.points.getLast? = some b ∧
        (build m c measured canvas out).layoutDump.box? r.fromId = some fb ∧
        (build m c measured canvas out).layoutDump.box? r.toId = some tb ∧
        Validator.onBoundary a fb.rect ∧ Validator.onBoundary b tb.rect := by
  have hns := measuredNodes_length hlen
  have hn0 : 0 < (measuredNodes m measured).length := by rw [hns]; exact h0
  obtain ⟨hv, hraw⟩ := Tree.mindmap_nonempty hn0 hl
  obtain ⟨hL, hs, _⟩ := load_nonneg hc
  obtain ⟨mr, hmr, rfl⟩ := build_route_origin hr
  obtain ⟨fromBox, toBox, parent, hf, ht, hp, hfid, htid, he⟩ := treeRelations_spec hrel hmr
  subst parent
  have hi : boxIndex m mr.toId < (measuredNodes m measured).length := by
    rw [hns]
    exact (List.getElem?_eq_some_iff.mp ht).1
  have hparent := measuredNodes_parent hlen hp
  obtain ⟨pts, a, b, pr, cr, hpts, hpr, hcr, ha, hb, hpa, hpb, ho⟩ :=
    Tree.normalized_route_ports hL hs hv hn0 hraw hn hi hparent
  have hfb := build_box_lookup (c := c) (measured := measured) (canvas := canvas) hwf hf hpr
  have htb := build_box_lookup (c := c) (measured := measured) (canvas := canvas) hwf ht hcr
  simp only [hfid] at hfb
  simp only [htid] at htb
  simpa only [hpts, List.getD_eq_getElem?_getD, Option.getD_some] using
    (show Polyline.isOrthogonal pts = true ∧
      ∃ a b : Point, ∃ fb tb : Box,
        pts.head? = some a ∧ pts.getLast? = some b ∧
        (build m c measured canvas out).layoutDump.box? mr.fromId = some fb ∧
        (build m c measured canvas out).layoutDump.box? mr.toId = some tb ∧
        Validator.onBoundary a fb.rect ∧ Validator.onBoundary b tb.rect from
      ⟨ho, a, b, _, _, ha, hb, hfb, htb, hpa, hpb⟩)

private theorem built_route_clear {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {raw out : Tree.Layout}
    (hlen : measured.length = m.boxes.length) (hc : load m = .ok c)
    (h0 : 0 < m.boxes.length) (hrel : treeRelations m = true)
    (hl : Tree.mindmap (measuredNodes m measured) ⟨c.levelGap, c.siblingGap⟩ = .ok raw)
    (hn : Tree.normalize c.margin raw = .ok (canvas, out))
    {r : Route} (hr : r ∈ (build m c measured canvas out).routes)
    {b : Box} (hb : b ∈ (build m c measured canvas out).boxes)
    (hscope : b.id ∉ (build m c measured canvas out).layoutDump.routeScope r) :
    ¬ Polyline.hitsRect r.points b.rect := by
  have hns := measuredNodes_length hlen
  have hn0 : 0 < (measuredNodes m measured).length := by rw [hns]; exact h0
  obtain ⟨hv, hraw⟩ := Tree.mindmap_nonempty hn0 hl
  obtain ⟨hL, hs, _⟩ := load_nonneg hc
  obtain ⟨mr, hmr, rfl⟩ := build_route_origin hr
  obtain ⟨k, mb, br, hmb, hbr, rfl⟩ := build_box_origin hb
  obtain ⟨fromBox, toBox, parent, hf, ht, hp, hfid, htid, he⟩ := treeRelations_spec hrel hmr
  subst parent
  have hi : boxIndex m mr.toId < (measuredNodes m measured).length := by
    rw [hns]
    exact (List.getElem?_eq_some_iff.mp ht).1
  have hparent := measuredNodes_parent hlen hp
  obtain ⟨pts, a, b, pr, cr, hpts, _, _, _, _, _, _, _⟩ :=
    Tree.normalized_route_ports hL hs hv hn0 hraw hn hi hparent
  have hfrom : mb.id ≠ mr.fromId := by
    intro heq
    apply hscope
    simp [LayoutDump.routeScope, heq]
  have hto : mb.id ≠ mr.toId := by
    intro heq
    apply hscope
    simp [LayoutDump.routeScope, heq]
  have hkp : k ≠ boxIndex m mr.fromId := by
    intro heq
    rw [heq, hf] at hmb
    exact hfrom ((congrArg ModelBox.id (Option.some.inj hmb)).symm.trans hfid)
  have hki : k ≠ boxIndex m mr.toId := by
    intro heq
    rw [heq, ht] at hmb
    exact hto ((congrArg ModelBox.id (Option.some.inj hmb)).symm.trans htid)
  have hclear := Tree.normalized_route_clear hL hs hv hn0 hraw hn hi hparent hpts hbr hkp hki
  simpa only [List.getD_eq_getElem?_getD, hpts, Option.getD_some] using hclear

/-- Every successful nonempty mindmap scene satisfies all eight hard constraints. The
relation premise is established by the kind's model decoder, not by inspecting the scene. -/
theorem build_valid_nonempty {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {raw out : Tree.Layout} (hwf : WellFormed m)
    (hlen : measured.length = m.boxes.length) (hc : load m = .ok c)
    (h0 : 0 < m.boxes.length) (hrel : treeRelations m = true)
    (hl : Tree.mindmap (measuredNodes m measured) ⟨c.levelGap, c.siblingGap⟩ = .ok raw)
    (hn : Tree.normalize c.margin raw = .ok (canvas, out)) :
    HardConstraints (build m c measured canvas out).layoutDump := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, mb, r, _, hr, rfl⟩ :=
      build_box_origin (c := c) (measured := measured) (canvas := canvas) hb
    exact Tree.normalized_box_inside (load_nonneg hc).2.2 hn (List.mem_of_getElem? hr)
  · intro b hb d hd hbd _ _ _
    exact built_boxes_disjoint hlen hc h0 hl hn hb hd hbd
  · intro b hb hp
    obtain ⟨i, mb, r, _, _, rfl⟩ :=
      build_box_origin (c := c) (measured := measured) (canvas := canvas) hb
    exact False.elim (hp rfl)
  · intro r hr _
    exact (built_route_geometry hwf hlen hc h0 hrel hl hn hr).1
  · intro r hr
    exact (built_route_geometry hwf hlen hc h0 hrel hl hn hr).2
  · intro r hr b hb _ hscope
    exact built_route_clear hlen hc h0 hrel hl hn hr hb hscope
  · intro l hl
    cases hl
  · intro g hg _ b hb hbg _ _
    exact built_boxes_disjoint hlen hc h0 hl hn hg hb hbg.symm
  · intro g hg hrole l hlabel
    cases hlabel

theorem build_valid_empty {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {out : Tree.Layout} (hboxes : m.boxes = []) (hroutes : m.routes = []) :
    HardConstraints (build m c measured canvas out).layoutDump := by
  simp only [build, Scene.layoutDump, hboxes, hroutes]
  simp [HardConstraints, Validator.C1, Validator.C2, Validator.C3, Validator.C4,
    Validator.C5, Validator.C6, Validator.C7, Validator.C8, Validator.C8a, Validator.C8b]

theorem relations_empty {m : Model} (hboxes : m.boxes = []) (hrel : treeRelations m = true) :
    m.routes = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r hr
  obtain ⟨fromBox, _, _, hf, _, _, _, _, _⟩ := treeRelations_spec hrel hr
  rw [hboxes] at hf
  simp at hf

theorem layout_decompose {m : Model} {result : Layered.FamilyResult}
    (hrel : treeRelations m = true) (h : layout m = .ok result) :
    ∃ c metric measured raw canvas out,
      load m = .ok c ∧
      m.boxes.mapM (measureBox m c metric) = .ok measured ∧
      Tree.mindmap (measuredNodes m measured) ⟨c.levelGap, c.siblingGap⟩ = .ok raw ∧
      Tree.normalize c.margin raw = .ok (canvas, out) ∧
      result.scene = (build m c measured canvas out).projectCellAttachments (routeMarkers m) := by
  unfold layout at h
  simp only [hrel, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hlimit : limitFailure m with
  | some failure => simp [hlimit] at h
  | none =>
    rw [hlimit] at h
    cases hc : load m with
    | error e => simp [hc, liftGeometry, bind, Except.bind] at h
    | ok c =>
      cases hmetric : labelMetric m.options.profile m.options.fontFamily with
      | error e => simp [hc, hmetric, liftGeometry, bind, Except.bind] at h
      | ok metric =>
        cases hmeasured : m.boxes.mapM (measureBox m c metric) with
        | error e => simp [hc, hmetric, hmeasured, liftGeometry, bind, Except.bind] at h
        | ok measured =>
          cases hraw : Tree.mindmap (measuredNodes m measured) ⟨c.levelGap, c.siblingGap⟩ with
          | error e =>
            simp [hc, hmetric, hmeasured, hraw, liftGeometry, bind, Except.bind] at h
          | ok raw =>
            cases hnorm : Tree.normalize c.margin raw with
            | error e =>
              simp [hc, hmetric, hmeasured, hraw, hnorm,
                liftGeometry, bind, Except.bind] at h
            | ok pair =>
              obtain ⟨canvas, out⟩ := pair
              simp only [hc, hmetric, hmeasured, liftGeometry, bind, Except.bind,
                hraw, hnorm, pure, Except.pure] at h
              have he := Except.ok.inj h
              refine ⟨c, metric, measured, raw, canvas, out,
                by first | exact hc | rfl,
                by first | exact hmeasured | rfl,
                hraw, hnorm, ?_⟩
              rw [← he]

theorem layout_valid_of_relations {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hrel : treeRelations m = true) (h : layout m = .ok result) :
    HardConstraints result.scene.layoutDump := by
  obtain ⟨c, metric, measured, raw, canvas, out, hc, hmeasured, hraw, hnorm, hscene⟩ :=
    layout_decompose hrel h
  rw [hscene, Scene.projectCellAttachments_layoutDump]
  by_cases hempty : m.boxes = []
  · exact build_valid_empty hempty (relations_empty hempty hrel)
  · have h0 : 0 < m.boxes.length := List.length_pos_iff.mpr hempty
    have hlen := (measured_record _ _ _ hmeasured).1.symm
    exact build_valid_nonempty hwf hlen hc h0 hrel hraw hnorm

theorem layout_relations {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : treeRelations m = true := by
  unfold layout at h
  cases hlimit : limitFailure m with
  | some failure => simp [hlimit] at h
  | none =>
    rw [hlimit] at h
    cases hr : treeRelations m with
    | false => simp [hr, bind, Except.bind] at h
    | true => rfl

/-- Every successful mindmap layout satisfies the hard constraints; malformed developer
models are rejected by the relation decoder before measurement or placement. -/
theorem layout_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result) :
    HardConstraints result.scene.layoutDump :=
  layout_valid_of_relations hwf (layout_relations h) h

end Mindmap
end Kinds
end Elegant
