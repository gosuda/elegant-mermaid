import Elegant.Layered.RegionFoundation

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-!
# Actual parts of the region base.

This module is the actual-part family of the region tower: the layer between the
tracked execution record `SceneExecutionR` (`RegionFoundation.lean`) and the flat
clause proofs at `layoutRIds`. It replays the exact-pipeline family
(`ActualPartX` / `actual_components_parts_geometryX` in `ExactFlatFacts.lean`)
with `layoutComponentR` in place of `layoutComponentX`.

Replay map (X name -> R name in this file):
* `ActualPartX` -> `ActualPartR` (additionally carries the resolved region spec;
  the run record keeps the rewritten graph `componentRunR` returns).
* `ActualPartGeometryX` -> `ActualPartGeometryR`.
* `placePartX_parts`, `placePartX_parts_geometry` are shared and reused directly.
* `layoutComponentX_parts*`, `foldlM_layout_components_partsX`,
  `actual_components_partsX`(+ geometry) -> R versions below.
* Per-step covers `layoutComponentX_rects/routes/labels_cover`,
  `layoutComponentX_parts_mono` -> R versions below.
* `sceneExecutionX_parts_entry`, `SceneExecutionX.parts_coverage`,
  `key_part_positionX` -> R versions below.
* `actual_components_packed_rect_valueX`,
  `actual_components_packed_frame_sourceX` -> R versions below
  (`packAcc` is shared; only the parts family changes).
* `component_node_lookupX` -> `component_node_lookupR`
  (via `componentCandidateR`).
* Part-keys uniqueness from `actual_components_partsR` and
  `components_entries_nodup`.
* `placeComponentExact` route sources by unfolding (`placeComponentExact_routes_sourceR`).
* `componentRunX_routes_length`, `componentRunX_route_of_index` ->
  `componentRunR_routes_lengthR`, `componentRunR_route_of_indexR`
  (via `componentRunR_routes_eqR`).
* Seven run-level geometry facts as `*_factR` defs; the two pure-unfolding
  ones (routes length, route of index) are proved.

Private helpers of `ExactFlatFacts.lean` do not resolve across modules; this file
carries prefixed copies (`rap*`) with the same proofs.
-/

/-! ## Probe support: a two-region state model through the real pipeline. -/

/-- Two-region probe input: groups `G1`/`G2` each with two member groups; every
kept condensed node touches an edge, as in a real connected component. -/
private def rapProbeInp : Input :=
  { kind := "state"
    boxes := [{ id := "G1", role := .group, parent := "", exclusive := false },
      { id := "A", role := .group, parent := "G1", exclusive := false },
      { id := "B", role := .group, parent := "G1", exclusive := false },
      { id := "G2", role := .group, parent := "", exclusive := false },
      { id := "C", role := .group, parent := "G2", exclusive := false },
      { id := "D", role := .group, parent := "G2", exclusive := false },
      { id := "a1", parent := "A", exclusive := false },
      { id := "b1", parent := "B", exclusive := false },
      { id := "c1", parent := "C", exclusive := false },
      { id := "d1", parent := "D", exclusive := false }]
    routes := [{ id := "e1", fromId := "a1", toId := "c1" },
      { id := "e2", fromId := "b1", toId := "d1" },
      { id := "e3", fromId := "c1", toId := "b1" }]
    texts := ["G1", "A", "B", "G2", "C", "D", "a1", "b1", "c1", "d1"]
    edges := [.plain, .plain, .plain]
    labels := [] }

/-- The two region sets of the probe: `G1` over `{A,B}`, `G2` over `{C,D}`. -/
private def rapProbeSets : List ModelRegionSet :=
  [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]

/-- Real prefix of `layoutRIds` on the probe input. -/
private def rapPrepTwoRegion :
    Except LayoutError (Params × List (List Measure.Line) × Graph × Graph × List (List Nat)) := do
  let P ← checkedParams .vector rapProbeInp.kind
  let m ← metricOf .vector
  let target := Measure.wrapTarget m.profile P.wrapWidth 0
  let lines ← boxLines m target rapProbeInp
  let measured ← measureLabels P m target rapProbeInp .TB
  let g0 ← measuredGraph P rapProbeInp {} lines
  let g ← exactGraph P [] rapProbeInp {} measured g0
  pure (P, lines, g0, g, components g)

/-- The resolved region spec of the probe, as `layoutRIds` builds it. -/
private def rapSpecOfTwoRegion (P : Params) (lines : List (List Measure.Line)) :
    Except LayoutError RegionSpec := do
  let idSets ← graphRegions rapProbeInp rapProbeSets
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    (width, height)
  pure (RegionSpec.mk idSets titles)

/-- The full region run on the probe's first component. -/
private def rapRunTwoRegion (P : Params) (lines : List (List Measure.Line)) (g : Graph)
    (comp : List Nat) : Except LayoutError (Graph × Run) := do
  let spec ← rapSpecOfTwoRegion P lines
  componentRunR P [] (some spec) rapProbeInp (componentGraph g comp) [] {}

def ActualPartR (P : Params) (exactIds : List String) (spec : Option RegionSpec)
    (inp : Input) (o : Options) (g : Graph) (labels : List MeasuredLabel)
    (q : List Nat × Part) : Prop :=
  ∃ index chosen cg run loops spec',
    index < 5 ∧
    Portfolio.portfolio o.thoroughness
      (componentTrialR P exactIds spec inp o g q.1 labels) = .ok chosen ∧
    chosen.value = (cg, run) ∧
    (∃ rs, newComponentRegions spec P inp (componentGraph g q.1) = .ok rs ∧
      spec' = if rs.isSome then spec else none) ∧
    componentRunR P (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' g q.1 index) labels (candidateOrder index) = .ok (cg, run) ∧
    componentLoops P cg run labels = .ok loops ∧
    q.2.routes = (placeComponentExact P cg run 0 labels loops).routes

/-- The region component geometry record: chosen portfolio trial with the
exact-placed part up to its area. -/
def ActualPartGeometryR (P : Params) (exactIds : List String) (spec : Option RegionSpec)
    (inp : Input) (o : Options) (g : Graph) (labels : List MeasuredLabel)
    (q : List Nat × Part) : Prop :=
  ∃ index chosen cg run loops area spec',
    index < 5 ∧
    Portfolio.portfolio o.thoroughness
      (componentTrialR P exactIds spec inp o g q.1 labels) = .ok chosen ∧
    chosen.value = (cg, run) ∧
    (∃ rs, newComponentRegions spec P inp (componentGraph g q.1) = .ok rs ∧
      spec' = if rs.isSome then spec else none) ∧
    componentRunR P (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' g q.1 index) labels (candidateOrder index) = .ok (cg, run) ∧
    componentLoops P cg run labels = .ok loops ∧
    q.2 = { placeComponentExact P cg run 0 labels loops with area := area }

/-! ## Item 2. Chosen-trial lemma and scene decomposition (parts). -/

theorem layoutComponentR_parts {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {acc out : Acc} {comp : List Nat} {labels : List MeasuredLabel}
    (h : layoutComponentR P exactIds spec inp o g acc comp labels = .ok out) :
    ∃ part, out.parts = acc.parts ++ [(comp, part)] ∧
      ActualPartR P exactIds spec inp o g labels (comp, part) := by
  unfold layoutComponentR at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨metric, _, h⟩ := bind_ok h
  obtain ⟨areas, _, h⟩ := bind_ok h
  obtain ⟨loops, part, hl, hparts, hroutes⟩ := placePartX_parts hp
  obtain ⟨index, trial, hi, ht, hv, _⟩ := Portfolio.portfolio_selected hc
  unfold componentTrialR at ht
  obtain ⟨rs, hrs, ht⟩ := bind_ok ht
  obtain ⟨pair, hpair, ht⟩ := bind_ok ht
  obtain ⟨scene, _, ht⟩ := bind_ok ht
  have htrial := Except.ok.inj ht
  subst trial
  dsimp only at hv
  obtain ⟨cg, run⟩ := pair
  have he := Except.ok.inj h
  subst out
  let childArea := inp.fixedAreas.foldl (fun total child =>
    if chosen.scene.boxes.any (fun box => box.id == child.1) then total + child.2 else total) 0
  let augmented := { part with area := part.area + childArea + areas.sum }
  refine ⟨augmented, ?_, ?_⟩
  · simp [hparts, augmented, childArea]
  · unfold ActualPartR
    refine ⟨index, chosen, cg, run, loops, _, hi, hc, hv, ⟨rs, hrs, rfl⟩, hpair, ?_, ?_⟩
    · simpa only [hv] using hl
    · simpa only [hv] using hroutes
theorem foldlM_layout_components_partsR (P : Params) (exactIds : List String)
    (spec : Option RegionSpec) (inp : Input) (o : Options) (g : Graph)
    (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp labels)
        start = .ok out →
      ∃ parts, out.parts = start.parts ++ parts ∧ parts.map (·.1) = comps ∧
        ∀ q ∈ parts, ActualPartR P exactIds spec inp o g labels q := by
  intro comps
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil] at h
    have hout : start = out := Except.ok.inj h
    subst out
    exact ⟨[], by simp, rfl, by simp⟩
  | cons comp comps ih =>
    intro start out h
    rw [List.foldlM_cons] at h
    obtain ⟨next, hn, hrest⟩ := bind_ok h
    obtain ⟨part, hp, hprod⟩ := layoutComponentR_parts hn
    obtain ⟨parts, hout, hmap, hall⟩ := ih next out hrest
    refine ⟨(comp, part) :: parts, ?_, ?_, ?_⟩
    · rw [hout, hp]
      simp only [List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, hmap]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hprod
      · exact hall q hq

theorem actual_components_partsR {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {start out : Acc}
    (hempty : start.parts = [])
    (h : (components g).foldlM
      (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp labels) start = .ok out) :
    out.parts.map (·.1) = components g ∧
      ∀ q ∈ out.parts, ActualPartR P exactIds spec inp o g labels q := by
  obtain ⟨parts, hp, hm, hall⟩ :=
    foldlM_layout_components_partsR P exactIds spec inp o g labels _ _ _ h
  simp only [hempty, List.nil_append] at hp
  subst parts
  exact ⟨hm, hall⟩

theorem layoutComponentR_parts_geometry {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {acc out : Acc} {comp : List Nat} {labels : List MeasuredLabel}
    (h : layoutComponentR P exactIds spec inp o g acc comp labels = .ok out) :
    ∃ part, out.parts = acc.parts ++ [(comp, part)] ∧
      ActualPartGeometryR P exactIds spec inp o g labels (comp, part) := by
  unfold layoutComponentR at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨metric, _, h⟩ := bind_ok h
  obtain ⟨areas, _, h⟩ := bind_ok h
  obtain ⟨loops, area, hl, hparts⟩ := placePartX_parts_geometry hp
  obtain ⟨index, trial, hi, ht, hv, _⟩ := Portfolio.portfolio_selected hc
  unfold componentTrialR at ht
  obtain ⟨rs, hrs, ht⟩ := bind_ok ht
  obtain ⟨pair, hpair, ht⟩ := bind_ok ht
  obtain ⟨scene, _, ht⟩ := bind_ok ht
  have htrial := Except.ok.inj ht
  subst trial
  dsimp only at hv
  obtain ⟨cg, run⟩ := pair
  have he := Except.ok.inj h
  subst out
  let childArea := inp.fixedAreas.foldl (fun total child =>
    if chosen.scene.boxes.any (fun box => box.id == child.1) then total + child.2 else total) 0
  let base := placeComponentExact P chosen.value.1 chosen.value.2 0 labels loops
  let augmented := { base with area := area + childArea + areas.sum }
  refine ⟨augmented, ?_, ?_⟩
  · simp [hparts, augmented, base, childArea]
  · unfold ActualPartGeometryR
    refine ⟨index, chosen, cg, run, loops, area + childArea + areas.sum, _,
      hi, hc, hv, ⟨rs, hrs, rfl⟩, hpair, ?_, ?_⟩
    · simpa only [hv] using hl
    · simp only [augmented, base, hv]

theorem foldlM_layout_components_parts_geometryR (P : Params) (exactIds : List String)
    (spec : Option RegionSpec) (inp : Input) (o : Options) (g : Graph)
    (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp labels)
        start = .ok out →
      ∃ parts, out.parts = start.parts ++ parts ∧ parts.map (·.1) = comps ∧
        ∀ q ∈ parts, ActualPartGeometryR P exactIds spec inp o g labels q := by
  intro comps
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil] at h
    have hout : start = out := Except.ok.inj h
    subst out
    exact ⟨[], by simp, rfl, by simp⟩
  | cons comp comps ih =>
    intro start out h
    rw [List.foldlM_cons] at h
    obtain ⟨next, hn, hrest⟩ := bind_ok h
    obtain ⟨part, hp, hprod⟩ := layoutComponentR_parts_geometry hn
    obtain ⟨parts, hout, hmap, hall⟩ := ih next out hrest
    refine ⟨(comp, part) :: parts, ?_, ?_, ?_⟩
    · rw [hout, hp]
      simp only [List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, hmap]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hprod
      · exact hall q hq

/-- The geometry-parts theorem: the region fold covers every component and every
part is an actual geometry part. Its proof uses only the shared `placePart` /
portfolio / trial structure, which coincides with the X instantiation. -/
theorem actual_components_parts_geometryR {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {start out : Acc}
    (hempty : start.parts = [])
    (h : (components g).foldlM
      (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp labels) start = .ok out) :
    out.parts.map (·.1) = components g ∧
      ∀ q ∈ out.parts, ActualPartGeometryR P exactIds spec inp o g labels q := by
  obtain ⟨parts, hp, hm, hall⟩ :=
    foldlM_layout_components_parts_geometryR P exactIds spec inp o g labels _ _ _ h
  simp only [hempty, List.nil_append] at hp
  subst parts
  exact ⟨hm, hall⟩

theorem layoutComponentR_parts_mono {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {labels : List MeasuredLabel}
    (h : layoutComponentR P exactIds spec inp o g acc comp labels = .ok acc') :
    ∀ q ∈ acc.parts, q ∈ acc'.parts := by
  unfold layoutComponentR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hp := congrArg Acc.parts he
  intro q hq
  rw [← hp]
  exact List.mem_append.mpr (Or.inl hq)


/-! ## Item 3. Per-step covers, entry decomposition, and route sources. -/

theorem layoutComponentR_rects_cover {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponentR P exactIds spec inp o g acc comp measured = .ok acc') :
    ∀ i (r : Rect), acc'.rects[i]? = some r →
      (∃ part ∈ acc'.parts, RectCovered part.1 part.2.rects.length i ∧ i < acc.rects.size) ∨
      acc.rects[i]? = some r := by
  unfold layoutComponentR at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i r hi
  rw [← congrArg Acc.rects he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hrects0⟩ :
        ∃ p : Part, result.parts = acc.parts ++ [(comp, p)] ∧
          p.rects = (placeComponentExact P chosen.value.1 chosen.value.2 0 measured
            loops).rects := by
      apply Exists.intro
      refine ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases zipCover_rects id _ comp acc.rects i r hi with hz | h
    · obtain ⟨k, hk, hkl, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.rects = part0.rects := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hrects0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hrects0]
        exact ⟨k, hk, hkl⟩
    · exact Or.inr h

theorem layoutComponentR_routes_cover {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponentR P exactIds spec inp o g acc comp measured = .ok acc') :
    ∀ i (pts : List Point), acc'.routes[i]? = some pts →
      (∃ part ∈ acc'.parts, RouteCovered part.2.routes i ∧ i < acc.routes.size) ∨
      acc.routes[i]? = some pts := by
  unfold layoutComponentR at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i pts hi
  rw [← congrArg Acc.routes he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hroutes0⟩ : ∃ p : Part,
        result.parts = acc.parts ++ [(comp, p)] ∧
          p.routes = (placeComponentExact P chosen.value.1 chosen.value.2 0 measured
            loops).routes := by
      apply Exists.intro
      exact ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases keyCover_pts id _ acc.routes i pts hi with hz | h
    · obtain ⟨r, hr, hke, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.routes = part0.routes := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hroutes0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hroutes0]
        exact ⟨r, hr, hke⟩
    · exact Or.inr h

theorem layoutComponentR_labels_cover {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponentR P exactIds spec inp o g acc comp measured = .ok acc') :
    ∀ i (r : Rect), acc'.labels[i]? = some r →
      (∃ part ∈ acc'.parts, LabelCovered part.2.labels i ∧ i < acc.labels.size) ∨
      acc.labels[i]? = some r := by
  unfold layoutComponentR at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i r hi
  rw [← congrArg Acc.labels he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hlabels0⟩ : ∃ p : Part,
        result.parts = acc.parts ++ [(comp, p)] ∧
          p.labels = (placeComponentExact P chosen.value.1 chosen.value.2 0 measured
            loops).labels := by
      apply Exists.intro
      exact ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases keyCover_rects id _ acc.labels i r hi with hz | h
    · obtain ⟨q, hq, hke, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.labels = part0.labels := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hlabels0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hlabels0]
        exact ⟨q, hq, hke⟩
    · exact Or.inr h

/-- Region fold preserves the rect array size (prefixed copy of the X proof). -/
private theorem rapComponentsFold_rects_sizeR (P : Params) (exactIds : List String)
    (spec : Option RegionSpec) (inp : Input) (o : Options) (g : Graph)
    (measured : List MeasuredLabel) (comps : List (List Nat)) :
    ∀ start out : Acc,
      comps.foldlM (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp measured)
        start = .ok out → out.rects.size = start.rects.size := by
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
  | cons comp rest ih =>
    intro start out h
    simp only [List.foldlM_cons] at h
    cases hc : layoutComponentR P exactIds spec inp o g start comp measured with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      exact (ih next out h).trans (layoutComponentR_sizes hc).1.symm

theorem SceneExecutionR.components_rects_sizeR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.componentsAcc.rects.size = inp.boxes.length := by
  have h := rapComponentsFold_rects_sizeR execution.params exactIds _ inp o execution.graph
    execution.measured (components execution.graph) _ _ execution.components_eq
  simpa only [Array.size_replicate] using h

/-- The execution lines cover every input box (prefixed copy). -/
private theorem rapMapMOkLenR {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    simp only [List.mapM_nil] at h
    have := Except.ok.inj h
    subst this
    rfl
  | cons x xs ih =>
    intro out h
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he := Except.ok.inj h
    subst he
    simp only [List.length_cons, ih _ hrest]

private theorem rapSceneExecutionR_lines_lenR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length := rapMapMOkLenR _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx
theorem sceneExecutionR_edges_boundedR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
      e.tail < execution.graph.nodes.length ∧
        e.head < execution.graph.nodes.length := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · rw [exactGraph_edges execution.graph_eq] at he
    have hlines : execution.lines.length = inp.boxes.length :=
      rapSceneExecutionR_lines_lenR execution
    have hbd := measuredGraph_edges_bounded execution.graph0_eq hlines e he
    have hlen := exactGraph_length execution.graph_eq
    omega
  · exact constraints_bounded _ e he

/-- The region candidate keeps the component nodes (prefixed copy). -/
private theorem rapCandidateR_nodes (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec g comp index).nodes = (componentGraph g comp).nodes := by
  cases spec with
  | none =>
    show (componentCandidate g comp index).nodes = _
    exact componentCandidate_nodes g comp index
  | some _ =>
    unfold componentCandidateR componentGraph
    dsimp only

private theorem rapCandidateR_nodes_lengthR (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec g comp index).nodes.length = comp.length := by
  rw [rapCandidateR_nodes]
  show (comp.map fun v => g.nodes.getD v default).length = comp.length
  exact List.length_map ..

theorem component_node_lookupR {graph : Graph} {comp : List Nat} {spec : Option RegionSpec}
    {cand : Nat} {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidateR spec graph comp cand).nodes[pos]? = some node := by
  rw [rapCandidateR_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

/-- Membership in a zipped list (prefixed copy of the X proof). -/
private theorem rapMem_zip_introR {α β : Type} {l : List α} {l' : List β} {i : Nat}
    {a : α} {b : β} (h1 : l[i]? = some a) (h2 : l'[i]? = some b) : (a, b) ∈ l.zip l' := by
  induction l generalizing l' i with
  | nil => rw [List.getElem?_nil] at h1; exact absurd h1 (by simp)
  | cons x xs ih =>
    cases l' with
    | nil => rw [List.getElem?_nil] at h2; exact absurd h2 (by simp)
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at h1 h2
        simp only [Option.some.injEq] at h1 h2
        subst h1
        subst h2
        exact Or.inl ⟨rfl, rfl⟩
      | succ i' =>
        rw [List.getElem?_cons_succ] at h1 h2
        exact Or.inr (ih h1 h2)

/-- The exact placement writes one rectangle per component-graph node
(prefixed copy of the X proof). -/
private theorem rapPlacedRects_lengthR (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  simp [List.length_map, List.length_range]


theorem sceneExecutionR_graph_lenR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {i : Nat} (hi : i < inp.boxes.length) : i < execution.graph.nodes.length := by
  have h1 := measuredGraph_nodes_length_ge execution.graph0_eq
    (rapSceneExecutionR_lines_lenR execution)
  have h2 := exactGraph_length execution.graph_eq
  omega
/-- Rank rewriting preserves the node list (edge orientations only). -/
theorem rankEquivalentR_nodes_eq {rm : ComponentRegions} {cg cg' : Graph}
    {ranks : List Int} {budget : Bool}
    (h : rankEquivalentR rm cg = .ok (ranks, cg', budget)) :
    cg'.nodes = cg.nodes := by
  unfold rankEquivalentR at h
  dsimp only at h
  split at h
  · have hF : False := by
      simp only [bind, Except.bind] at h
      exact absurd h (by simp)
    exact hF.elim
  · obtain ⟨conds, _, h⟩ := bind_ok h
    obtain ⟨out1, _, h⟩ := bind_ok h
    obtain ⟨flagsAndOut, _, h⟩ := bind_ok h
    obtain ⟨ranked, _, h⟩ := bind_ok h
    have he := Except.ok.inj h
    have hcon := congrArg (fun q : List Int × Graph × Bool => q.2.1.nodes) he
    simpa only using hcon.symm

/-- The region run keeps the candidate nodes (only edges are rewritten). -/
theorem componentRunR_nodes_eq {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    cg'.nodes.length = cg.nodes.length := by
  unfold componentRunR at h
  obtain ⟨rs, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨rr, _, h⟩ := bind_ok h
    obtain ⟨ranked, hranked, h⟩ := bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := bind_ok h
        obtain ⟨p, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨ord, _, h⟩ := bind_ok h
        obtain ⟨xs, _, h⟩ := bind_ok h
        obtain ⟨placed, _, h⟩ := bind_ok h
        obtain ⟨routed, _, h⟩ := bind_ok h
        split at h
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          have he := Except.ok.inj h
          have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
          have h1 : cg = cg1 :=
            congrArg (fun q : List Int × Graph × Bool => q.2.1) (Except.ok.inj hranked)
          rw [hfst, ← h1]
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          have he := Except.ok.inj h
          have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
          have h1 : cg = cg1 :=
            congrArg (fun q : List Int × Graph × Bool => q.2.1) (Except.ok.inj hranked)
          rw [hfst, ← h1]
  · obtain ⟨ranked, hranked, h⟩ := bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := bind_ok h
        obtain ⟨p, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨ord, _, h⟩ := bind_ok h
        split at h
        · simp only [bind, Except.bind] at h
          exact absurd h (by simp)
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨placed, _, h⟩ := bind_ok h
          obtain ⟨routed, _, h⟩ := bind_ok h
          split at h
          · obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            have he := Except.ok.inj h
            have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
            have hnodes := rankEquivalentR_nodes_eq hranked
            rw [hfst, hnodes]
          · obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            have he := Except.ok.inj h
            have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
            have hnodes := rankEquivalentR_nodes_eq hranked
            rw [hfst, hnodes]

theorem sceneExecutionR_parts_entryR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {i : Nat}
    (hi : i < inp.boxes.length) :
    ∃ part ∈ execution.componentsAcc.parts,
      ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hm, hall⟩ := actual_components_parts_geometryR hempty execution.components_eq
  have hin := sceneExecutionR_graph_lenR execution hi
  obtain ⟨comp, hcomp, hiv⟩ := components_cover hin (sceneExecutionR_edges_boundedR execution)
  have hmem : comp ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hm]
    exact hcomp
  obtain ⟨part, hpart, hpc⟩ := List.mem_map.mp hmem
  obtain ⟨index, chosen, cg, run, loops, area, spec', _, _, _, _, hrun, hloops, hpartdef⟩ :=
    hall part hpart
  have hrectlen : part.2.rects.length = comp.length := by
    rw [hpartdef]
    have hcg : cg.nodes.length = comp.length := by
      have hnodes := componentRunR_nodes_eq hrun
      have hcand := rapCandidateR_nodes_lengthR spec' execution.graph part.1 index
      simp_all
    show (placeComponentExact execution.params cg run 0
      execution.measured loops).rects.length = comp.length
    rw [rapPlacedRects_lengthR]
    exact hcg
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hiv
  have hjlt : j < comp.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjrect : j < part.2.rects.length := by rw [hrectlen]; exact hjlt
  refine ⟨part, hpart, (i, part.2.rects[j]'hjrect), ?_, rfl⟩
  · exact rapMem_zip_introR (by simpa only [hpc] using hj)
      (List.getElem?_eq_some_iff.mpr ⟨hjrect, rfl⟩)

/-! ## Item 3 continued. Coverage, positions, uniqueness, route sources, pack transport. -/

theorem SceneExecutionR.parts_coverageR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      ∃ part ∈ execution.componentsAcc.parts,
        ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i := by
  intro i rect hrect
  have hi := (Array.getElem?_eq_some_iff.mp hrect).1
  rw [execution.components_rects_sizeR] at hi
  exact sceneExecutionR_parts_entryR execution hi

theorem key_part_positionR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {key : Nat}
    (hkey : key < inp.boxes.length) :
    ∃ (part : List Nat × Part) (pos k : Nat),
      part ∈ execution.componentsAcc.parts ∧
      execution.componentsAcc.parts[k]? = some part ∧
      part.1[pos]? = some key := by
  have hsizeC : execution.componentsAcc.rects.size = inp.boxes.length :=
    execution.components_rects_sizeR
  have hrect : execution.componentsAcc.rects[key]? =
      some execution.componentsAcc.rects[key] :=
    Array.getElem?_eq_some_iff.mpr ⟨by rw [hsizeC]; exact hkey, rfl⟩
  obtain ⟨part, hpart, entry, hentry, hentryKey⟩ := execution.parts_coverageR _ _ hrect
  have hkeyIn : key ∈ part.1 := by
    rw [← hentryKey]
    exact (List.of_mem_zip hentry).1
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hkeyIn
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hpart
  exact ⟨part, pos, k, hpart, hk, hpos⟩

/-- Component keys of the region fold are unique. -/
theorem actual_components_parts_keys_nodupR {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {start out : Acc}
    (hempty : start.parts = [])
    (h : (components g).foldlM
      (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp labels) start = .ok out) :
    (out.parts.map (·.1)).Nodup := by
  obtain ⟨hm, _⟩ := actual_components_partsR hempty h
  rw [hm]
  exact components_entries_nodup g

/-- Routes of exact placement are declaration-tagged shifted loop-or-edge points
(pure unfolding of `placeComponentExact`; no run internals). -/
theorem placeComponentExact_routes_sourceR {P : Params} {cg : Graph} {run : Run}
    {cursor : Int} {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} :
    ∃ dx dy : Int, (placeComponentExact P cg run cursor labels loops).routes =
      cg.edges.zipIdx.map fun q =>
        (q.1.decl, (((loops.find? (fun l => l.1 == q.1.decl)).map
          (fun l => l.2.points)).getD (edgePoints run q.2 q.1)).map (shiftPoint dx dy)) := by
  unfold placeComponentExact
  exact ⟨_, _, rfl⟩

/-- Exact-placement rect lookup (prefixed copy of the X proof). -/
private theorem rapPlacedRects_getR {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} {cursor : Int}
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Guarded rect write (prefixed copy of the X proof). -/
private theorem rapGuarded_rect_writeR (a : Array Rect) (key : Nat) (rect : Rect) :
    (if key < a.size then a.set! key rect else a) = a.set! key rect := by
  by_cases h : key < a.size
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, Array.set!_eq_setIfInBounds]
    simp only [Array.setIfInBounds, h, ↓reduceDIte]

/-- Guarded rect fold (prefixed copy of the X proof). -/
private theorem rapGuarded_rect_foldR (entries : List (Nat × Rect)) (a : Array Rect)
    (transform : Rect → Rect) :
    entries.foldl (fun out entry =>
      if entry.1 < out.size then out.set! entry.1 (transform entry.2) else out) a =
      entries.foldl (fun out entry => out.set! entry.1 (transform entry.2)) a := by
  have hstep : (fun (out : Array Rect) (entry : Nat × Rect) =>
      if entry.1 < out.size then out.set! entry.1 (transform entry.2) else out) =
      (fun out entry => out.set! entry.1 (transform entry.2)) := by
    funext out entry
    exact rapGuarded_rect_writeR out entry.1 (transform entry.2)
  rw [hstep]

/-- Untouched keys survive the pack fold (prefixed copy of the X proof). -/
private theorem rapPack_rects_fold_untouchedR (pairs : List ((List Nat × Part) × Rect))
    (a : Array Rect) (key : Nat) (fallback : Rect)
    (hnot : ∀ q ∈ pairs, key ∉ q.1.1) :
    (pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
      (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) a).getD
      key fallback =
      a.getD key fallback := by
  induction pairs generalizing a with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q' hq' => hnot q' (List.mem_cons_of_mem _ hq'))]
    apply routes_foldl_getD_ne
    intro hm
    obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hm
    exact hnot q List.mem_cons_self (hkey ▸ (List.of_mem_zip hentry).1)

/-- Zip keys stay unique over nodup keys (prefixed copy of the X proof). -/
private theorem rapZip_rect_keys_nodupR (keys : List Nat) (rects : List Rect)
    (hn : keys.Nodup) : ((keys.zip rects).map (·.1)).Nodup := by
  induction keys generalizing rects with
  | nil => simp
  | cons key keys ih =>
    cases rects with
    | nil => simp
    | cons rect rects =>
      obtain ⟨hkey, hkeys⟩ := List.nodup_cons.mp hn
      simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih rects hkeys⟩
      intro hm
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hm
      exact hkey (heq ▸ (List.of_mem_zip hentry).1)

/-- Pack fold equals the rect-entry fold (prefixed copy of the X proof). -/
private theorem rapPack_rects_eq_foldR (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) :
    (pairs.foldl packStep start).rects =
      pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
        (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) start.rects := by
  induction pairs generalizing start with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    unfold packStep
    dsimp only
    rw [rapGuarded_rect_foldR]

/-- Selected packed entry reads back the shifted rect (prefixed copy of the X proof). -/
private theorem rapPack_rects_fold_selectedR
    (pairs : List ((List Nat × Part) × Rect)) (a : Array Rect)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : pairs[c]? = some q)
    (i key : Nat) (rect fallback : Rect)
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    (hnodup : q.1.1.Nodup) (hsize : key < a.size)
    (hnot : ∀ q' ∈ pairs.drop (c + 1), key ∉ q'.1.1) :
    (pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
      (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) a).getD
      key fallback =
      shiftRect q.2.x q.2.y rect := by
  induction pairs generalizing a c with
  | nil => simp at hselected
  | cons current rest ih =>
    simp only [List.foldl_cons]
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hselected
      subst current
      simp only [List.drop_succ_cons, List.drop_zero] at hnot
      rw [rapPack_rects_fold_untouchedR rest _ key fallback hnot]
      exact routes_foldl_getD_mem (shiftRect q.2.x q.2.y) _ a i key rect fallback
        hentry (rapZip_rect_keys_nodupR _ _ hnodup) hsize
    | succ c =>
      simp only [List.getElem?_cons_succ] at hselected
      simp only [List.drop_succ_cons] at hnot
      apply ih _ c hselected
      · rw [routes_foldl_size]
        exact hsize
      · exact hnot

theorem actual_components_packed_rect_valueR
    {P : Params} {exactIds : List String} {inp : Input} {o : Options} {graph : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    {spec : Option RegionSpec}
    (hempty : start.parts = [])
    (hfold : (components graph).foldlM
      (fun acc comp => layoutComponentR P exactIds spec inp o graph acc comp labels) start = .ok mid)
    (hpack : packAcc P o mid = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (mid.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} {rect : Rect}
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    (hsize : key < mid.rects.size) (fallback : Rect) :
    out.rects.getD key fallback = shiftRect q.2.x q.2.y rect := by
  obtain ⟨hparts, _⟩ := actual_components_partsR hempty hfold
  have hpart : mid.parts[c]? = some q.1 := zip_getElem?_left hselected
  have hmember : q.1 ∈ mid.parts := List.mem_of_getElem? hpart
  have hcomponent : q.1.1 ∈ components graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hmember
  have hnodup : q.1.1.Nodup := components_nodup graph q.1.1 hcomponent
  have hkey : key ∈ q.1.1 := (List.of_mem_zip (List.mem_of_getElem? hentry)).1
  have hnot : ∀ later ∈ (mid.parts.zip packed.boxes).drop (c + 1), key ∉ later.1.1 := by
    intro later hlater
    obtain ⟨j, hcj, hj⟩ := zip_drop_mem_later_getElem? hlater
    have hpartsNodup : (mid.parts.map (·.1)).Nodup := by
      rw [hparts]
      exact components_entries_nodup graph
    obtain ⟨hc, hqc⟩ := List.getElem?_eq_some_iff.mp hpart
    obtain ⟨hjbound, hqj⟩ := List.getElem?_eq_some_iff.mp hj
    have hne : q.1.1 ≠ later.1.1 := by
      have hp := List.pairwise_iff_getElem.mp hpartsNodup
      have hneq := hp c j (by simpa using hc) (by simpa using hjbound) hcj
      simpa only [List.getElem_map, hqc, hqj] using hneq
    have hlaterComponent : later.1.1 ∈ components graph := by
      rw [← hparts]
      exact List.mem_map_of_mem (List.mem_of_getElem? hj)
    exact components_disjoint hcomponent hlaterComponent hne hkey
  unfold packAcc at hpack
  obtain ⟨actualPacked, hactualPacked, hpack⟩ := bind_ok hpack
  have heq : actualPacked = packed := by
    rw [hpacked] at hactualPacked
    exact (Except.ok.inj hactualPacked).symm
  subst actualPacked
  have hout := Except.ok.inj hpack
  subst out
  change ((mid.parts.zip packed.boxes).foldl packStep
    { mid with canvasW := packed.width, canvasH := packed.height, titles := [] }).rects.getD
      key fallback = _
  rw [rapPack_rects_eq_foldR]
  exact rapPack_rects_fold_selectedR _ _ c q hselected i key rect fallback hentry hnodup hsize hnot

theorem actual_components_packed_frame_sourceR
    {P : Params} {exactIds : List String} {inp : Input} {o : Options} {graph : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    {spec : Option RegionSpec}
    (hempty : start.parts = [])
    (hfold : (components graph).foldlM
      (fun acc comp => layoutComponentR P exactIds spec inp o graph acc comp labels) start = .ok mid)
    (hpack : packAcc P o mid = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (mid.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} (hkey : q.1.1[i]? = some key)
    (hsize : key < mid.rects.size) (fallback : Rect) :
    ∃ index cg run loops area spec',
      componentRunR P (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' graph q.1.1 index) labels (candidateOrder index) = .ok (cg, run) ∧
      componentLoops P cg run labels = .ok loops ∧
      q.1.2 = { placeComponentExact P cg run 0 labels loops with area := area } ∧
      let bounds := placeBoundsX P cg run labels loops
      out.rects.getD key fallback =
        shiftRect q.2.x q.2.y
          (shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect P cg run i)) := by
  obtain ⟨_, hall⟩ := actual_components_parts_geometryR hempty hfold
  have hpart : q.1 ∈ mid.parts := List.mem_of_getElem? (zip_getElem?_left hselected)
  obtain ⟨index, chosen, cg, run, loops, area, spec', _, _, _, _, hrun, hloops, hpartdef⟩ :=
    hall q.1 hpart
  let bounds := placeBoundsX P cg run labels loops
  let rect := shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect P cg run i)
  have hi : i < cg.nodes.length := by
    have hk := (List.getElem?_eq_some_iff.mp hkey).1
    rw [componentRunR_nodes_eq hrun, rapCandidateR_nodes_lengthR]
    exact hk
  have hrect : q.1.2.rects[i]? = some rect := by
    rw [hpartdef]
    exact rapPlacedRects_getR hi
  have hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect) :=
    List.getElem?_zip_eq_some.mpr ⟨hkey, hrect⟩
  refine ⟨index, cg, run, loops, area, spec', hrun, hloops, hpartdef, ?_⟩
  exact actual_components_packed_rect_valueR hempty hfold hpack packed hpacked
    hselected hentry hsize fallback

/-! ## Item 4. Run-level geometry facts. -/

/-- Rank chains cover the rewritten edges. -/
def componentRunR_proper_chains_length_factR : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    run.proper.chains.length = cg'.edges.length

/-- Region-run routes cover the proper chains. -/
def componentRunR_routes_length_factR : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    run.routes.length = run.proper.chains.length

/-- Every proper chain index resolves to a region-run route. -/
def componentRunR_route_of_index_factR : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    ∀ {i : Nat}, componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    i < run.proper.chains.length →
    ∃ rt : EdgeRoute, run.routes[i]? = some rt ∧ rt.original = i ∧
      RouteImpl.laneRouteOf P.slot run.proper run.ys run.top
        (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes i = .ok rt

/-- Rank rewriting preserves edge declarations. -/
def componentRunR_edges_decls_factR : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    cg'.edges.map (·.decl) = cg.edges.map (·.decl)

/-- Coordinate chains match the routed chains. -/
def componentRunR_coordinate_chains_factR : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    run.coordinateProper.chains.length = run.proper.chains.length

/-- Title reservation zeroes title node widths. -/
def componentRunR_title_zeroing_factR : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    ∀ {n : ProperNode}, componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    n ∈ run.coordinateProper.nodes →
    n.node.border = -2 ∨ n.node.border = 2 → n.node.w = 0

/-- Placed xs read the coordinate xs. -/
def componentRunR_placement_xs_factR : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    ∀ (i : Nat), componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    run.xs.getD i 0 = run.coordinateXs.getD i 0

/-- The region run routes are the lane-routed points of the final proper graph. -/
theorem componentRunR_routes_eqR {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    RouteImpl.routePointsWithLanes P.slot run.proper run.layers run.xs run.ys run.top
      run.lanes = .ok run.routes := by
  unfold componentRunR at h
  obtain ⟨rs, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨rr, _, h⟩ := bind_ok h
    obtain ⟨ranked, _, h⟩ := bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := bind_ok h
        obtain ⟨p, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨ord, _, h⟩ := bind_ok h
        obtain ⟨xs, _, h⟩ := bind_ok h
        obtain ⟨placed, _, h⟩ := bind_ok h
        obtain ⟨routed, _, h⟩ := bind_ok h
        split at h
        · obtain ⟨lanes_1, _, h⟩ := bind_ok h
          obtain ⟨yt, _, h⟩ := bind_ok h
          obtain ⟨resv, _, h⟩ := bind_ok h
          obtain ⟨routes, hroutes, h⟩ := bind_ok h
          have he := Except.ok.inj h
          have hP : run.proper = OrderImpl.dropSynthetic routed.fst :=
            (congrArg (fun q : Graph × Run => q.2.proper) he).symm
          have hL : run.layers = placed.2.fst :=
            (congrArg (fun q : Graph × Run => q.2.layers) he).symm
          have hX : run.xs = routed.snd :=
            (congrArg (fun q : Graph × Run => q.2.xs) he).symm
          have hY : run.ys = resv.fst :=
            (congrArg (fun q : Graph × Run => q.2.ys) he).symm
          have hT : run.top = resv.snd :=
            (congrArg (fun q : Graph × Run => q.2.top) he).symm
          have hN : run.lanes = lanes_1 :=
            (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
          have hR : run.routes = routes :=
            (congrArg (fun q : Graph × Run => q.2.routes) he).symm
          rw [hP, hL, hX, hY, hT, hN, hR]
          exact hroutes
        · obtain ⟨lanes_1, _, h⟩ := bind_ok h
          obtain ⟨yt, _, h⟩ := bind_ok h
          obtain ⟨resv, _, h⟩ := bind_ok h
          obtain ⟨routes, hroutes, h⟩ := bind_ok h
          have he := Except.ok.inj h
          have hP : run.proper = OrderImpl.dropSynthetic routed.fst :=
            (congrArg (fun q : Graph × Run => q.2.proper) he).symm
          have hL : run.layers = placed.2.fst :=
            (congrArg (fun q : Graph × Run => q.2.layers) he).symm
          have hX : run.xs = routed.snd :=
            (congrArg (fun q : Graph × Run => q.2.xs) he).symm
          have hY : run.ys = resv.fst :=
            (congrArg (fun q : Graph × Run => q.2.ys) he).symm
          have hT : run.top = resv.snd :=
            (congrArg (fun q : Graph × Run => q.2.top) he).symm
          have hN : run.lanes = lanes_1 :=
            (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
          have hR : run.routes = routes :=
            (congrArg (fun q : Graph × Run => q.2.routes) he).symm
          rw [hP, hL, hX, hY, hT, hN, hR]
          exact hroutes
  · obtain ⟨ranked, _, h⟩ := bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := bind_ok h
        obtain ⟨p, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨ord, _, h⟩ := bind_ok h
        split at h
        · simp only [bind, Except.bind] at h
          exact absurd h (by simp)
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨placed, _, h⟩ := bind_ok h
          obtain ⟨routed, _, h⟩ := bind_ok h
          split at h
          · obtain ⟨lanes_1, _, h⟩ := bind_ok h
            obtain ⟨yt, _, h⟩ := bind_ok h
            obtain ⟨resv, _, h⟩ := bind_ok h
            obtain ⟨routes, hroutes, h⟩ := bind_ok h
            have he := Except.ok.inj h
            have hP : run.proper = OrderImpl.dropSynthetic routed.fst :=
              (congrArg (fun q : Graph × Run => q.2.proper) he).symm
            have hL : run.layers = placed.2.fst :=
              (congrArg (fun q : Graph × Run => q.2.layers) he).symm
            have hX : run.xs = routed.snd :=
              (congrArg (fun q : Graph × Run => q.2.xs) he).symm
            have hY : run.ys = resv.fst :=
              (congrArg (fun q : Graph × Run => q.2.ys) he).symm
            have hT : run.top = resv.snd :=
              (congrArg (fun q : Graph × Run => q.2.top) he).symm
            have hN : run.lanes = lanes_1 :=
              (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
            have hR : run.routes = routes :=
              (congrArg (fun q : Graph × Run => q.2.routes) he).symm
            rw [hP, hL, hX, hY, hT, hN, hR]
            exact hroutes
          · obtain ⟨lanes_1, _, h⟩ := bind_ok h
            obtain ⟨yt, _, h⟩ := bind_ok h
            obtain ⟨resv, _, h⟩ := bind_ok h
            obtain ⟨routes, hroutes, h⟩ := bind_ok h
            have he := Except.ok.inj h
            have hP : run.proper = OrderImpl.dropSynthetic routed.fst :=
              (congrArg (fun q : Graph × Run => q.2.proper) he).symm
            have hL : run.layers = placed.2.fst :=
              (congrArg (fun q : Graph × Run => q.2.layers) he).symm
            have hX : run.xs = routed.snd :=
              (congrArg (fun q : Graph × Run => q.2.xs) he).symm
            have hY : run.ys = resv.fst :=
              (congrArg (fun q : Graph × Run => q.2.ys) he).symm
            have hT : run.top = resv.snd :=
              (congrArg (fun q : Graph × Run => q.2.top) he).symm
            have hN : run.lanes = lanes_1 :=
              (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
            have hR : run.routes = routes :=
              (congrArg (fun q : Graph × Run => q.2.routes) he).symm
            rw [hP, hL, hX, hY, hT, hN, hR]
            exact hroutes

/-- Region-run routes cover the proper chains (proved from the run equation). -/
theorem componentRunR_routes_lengthR : componentRunR_routes_length_factR := by
  unfold componentRunR_routes_length_factR
  intro P exact spec inp cg cg' run labels orderOptions h
  have hroutes := componentRunR_routes_eqR h
  unfold RouteImpl.routePointsWithLanes at hroutes
  split at hroutes
  · simp at hroutes
  · simpa using RouteImpl.mapOk_length _ _ _ hroutes

/-- Every proper chain index resolves to a region-run route (proved from the run equation). -/
theorem componentRunR_route_of_indexR : componentRunR_route_of_index_factR := by
  unfold componentRunR_route_of_index_factR
  intro P exact spec inp cg cg' run labels orderOptions i h hi
  have hroutes := componentRunR_routes_eqR h
  unfold RouteImpl.routePointsWithLanes at hroutes
  split at hroutes
  · simp at hroutes
  · have hrange : i < (List.range run.proper.chains.length).length := by
      simpa only [List.length_range] using hi
    obtain ⟨rt, hget, hok⟩ := RouteImpl.mapOk_getElem _ _ _ hroutes i hrange
    have hri : (List.range run.proper.chains.length)[i] = i := by simp
    rw [hri] at hok
    exact ⟨rt, hget, RouteImpl.laneRouteOf_original hok, hok⟩

end PipelineImpl
end Layered
end Elegant
