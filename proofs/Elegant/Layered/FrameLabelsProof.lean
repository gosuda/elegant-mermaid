import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.CgShape

set_option autoImplicit false

 /-! # Frame-label clearance: transport repair and partial discharge

 `PipelineImpl.LabelFramePackedClear` and `PipelineImpl.FallbackCaptionClear`
 (`Layered/LabelsC8b.lean`) are the two executed facts that lift `Validator.C8b`
 to the flat layered pipeline. `Layered/LabelsC8bFacts.lean` derives them from
 the named cores `ExecutedPartFrameCores`, `PackedPartTransport`, and
 `SceneOwnedTextFrameCore`.

 This file discharges the structural part of that bundle and repairs a defect
 in it:

 * `packedShelfExistence_of_execution` — the pack-existence half of the
   transport holds outright: `packAcc` exposes the packed shelf state and its
   box count matches the executed part count.
 * `packed_titles_mem_source` — the title-membership half holds outright: every
   packed title entry comes from one executed part entry with its packed shelf
   box and packed shift.
 * `packedTransport_hrects_false` — `PackedPartTransport` as stated is FALSE:
   its rect clause quantifies over every `k : Nat` with no size bound, but
   component indices only cover `k < inp.boxes.length`, while
   `packedAcc.rects.getD k default = default` for `k` past the array size.
   The witness index `packedAcc.rects.size + graph.nodes.length` reads `default`
   yet belongs to no component, so no source part exists. The nearest true
   statement is `PackedPartTransportBounded`, which guards the rect clause by
   `k < packedAcc.rects.size` (the only way the transport is ever used).
 * `PackedLabelsTransport` — the one remaining unproved residual, about packed
   label provenance, strictly simpler than the seam goal, every constrained
   variable pinned by an executed accumulator equation.

 The packed-frame `ownedTextRect` fallback clause (D3) and its transport
 premise `PackedOwnedCaptionContained` are deleted, not repaired: D3 evaluates
 `ownedTextRect` before `orientRect`, so it is FALSE on executed vector LR/RL
 layouts, and `layout_c8b` never uses it (fallback captions are covered at
 scene level by `FallbackCaptionClear`). The component-local geometric cores
 (`ExecutedPartFrameCores`, `SceneOwnedTextFrameCore`) stay as the named
 hypotheses of `LabelsC8bFacts.lean`; neither `WellFormed` nor `framedParents`
 is needed by anything proved here.
 -/

namespace Elegant.Layered

namespace PipelineImpl

/-- The pack-existence half of the packed transport holds outright: `packAcc`
exposes the packed shelf state, and its box count matches the executed part
count. This is the structural skeleton of `PackedPartTransport`. -/
theorem packedShelfExistence_of_execution {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∃ packed : Pack.State,
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed ∧
      packed.boxes.length = execution.componentsAcc.parts.length := by
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, _⟩ := bind_ok hpack
  refine ⟨packed, hpacked, ?_⟩
  rw [Pack.pack_count hpacked, List.length_map]

/-- The packing fold appends each part's mapped titles after the titles
accumulated so far. -/
private theorem pack_titles_fold (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).titles =
      start.titles ++
        pairs.flatMap (fun pair => pair.1.2.titles.map
          (fun title => (pair.1.1.getD title.1 0,
            shiftRect pair.2.x pair.2.y title.2))) := by
  induction pairs generalizing start with
  | nil => simp
  | cons pair rest ih =>
    simp [List.foldl_cons, ih, packStep, List.append_assoc]

/-- The title-membership half of the packed transport holds outright: every
packed title entry comes from one executed part entry, with its packed shelf
box and packed shift. Title keys are in range because `componentTitles`
records component node positions (`componentTitles_dimension_source`) and the
candidate graph has exactly the component's node count. -/
theorem packed_titles_mem_source {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    {key : Nat} {stored : Rect}
    (hmem : (key, stored) ∈ execution.packedAcc.titles) :
    ∃ (pl : Nat) (part : List Nat × Part) (i : Nat) (stored0 box : Rect),
      execution.componentsAcc.parts[pl]? = some part ∧
      part.1[i]? = some key ∧
      (i, stored0) ∈ part.2.titles ∧
      packed.boxes[pl]? = some box ∧
      stored = shiftRect box.x box.y stored0 := by
  have hpackeq := execution.packed_eq
  unfold packAcc at hpackeq
  obtain ⟨packed', hpacked', hfold⟩ := bind_ok hpackeq
  have heqpacked : packed = packed' := Except.ok.inj (hpacked.symm.trans hpacked')
  subst heqpacked
  have hout : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
        { execution.componentsAcc with
          canvasW := packed.width, canvasH := packed.height, titles := [] } :=
    (Except.ok.inj hfold).symm
  rw [hout, pack_titles_fold] at hmem
  have hstart : ({ execution.componentsAcc with
      canvasW := packed.width, canvasH := packed.height, titles := [] } : Acc).titles
      = [] := rfl
  rw [hstart, List.nil_append] at hmem
  obtain ⟨pair, hpair, htitle⟩ := List.mem_flatMap.mp hmem
  obtain ⟨⟨i, stored0⟩, ht, hteq⟩ := List.mem_map.mp htitle
  have hlen : execution.componentsAcc.parts.length = packed.boxes.length := by
    rw [Pack.pack_count hpacked, List.length_map]
  obtain ⟨pl, hplpart, hplbox⟩ := mem_zip_pairing hlen pair hpair
  have hkeyeq : pair.1.1.getD i 0 = key := congrArg Prod.fst hteq
  have hstoreq : shiftRect pair.2.x pair.2.y stored0 = stored := congrArg Prod.snd hteq
  have hpartmem : pair.1 ∈ execution.componentsAcc.parts := List.mem_of_getElem? hplpart
  obtain ⟨index, run, loops, area, _, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpartmem
  have hrange : i < pair.1.1.length := by
    have htmap : (i, stored0) ∈ (componentTitles execution.params
        (componentCandidate execution.graph pair.1.1 index) run).map
        (fun q => (q.1, shiftRect (0 - (placeBounds execution.params
          (componentCandidate execution.graph pair.1.1 index) run
          execution.measured loops).minX)
          (0 - (placeBounds execution.params
          (componentCandidate execution.graph pair.1.1 index) run
          execution.measured loops).minY) q.2)) := by
      rw [hplace] at ht
      exact ht
    obtain ⟨raw, hraw, hreq⟩ := List.mem_map.mp htmap
    obtain ⟨top, htop, _, hindex, _, _⟩ := componentTitles_dimension_source
      execution.params (componentCandidate execution.graph pair.1.1 index) run hraw
    have hi := (List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp htop)).1
    have hlen2 : (componentCandidate execution.graph pair.1.1 index).nodes.length =
        pair.1.1.length := by
      rw [componentCandidate_nodes]
      show (componentGraph execution.graph pair.1.1).nodes.length = _
      unfold componentGraph
      dsimp only
      rw [List.length_map]
    have hkey : raw.1 = i := congrArg Prod.fst hreq
    have hi2 : i = top.2 := hkey.symm.trans hindex
    rw [hi2, ← hlen2]
    exact hi
  have hgetElem : pair.1.1[i]? = some pair.1.1[i] :=
    List.getElem?_eq_getElem hrange
  have hgetD : pair.1.1.getD i 0 = pair.1.1[i] := by
    rw [List.getD_eq_getElem?_getD, hgetElem, Option.getD_some]
  have hget : pair.1.1[i]? = some key := by
    rw [← hkeyeq, hgetD]
    exact List.getElem?_eq_getElem hrange
  exact ⟨pl, pair.1, i, stored0, pair.2, hplpart, hget, ht, hplbox, hstoreq.symm⟩
private theorem components_mem_bound {g : Graph} {comp : List Nat}
    (hmem : comp ∈ components g) {v : Nat} (hv : v ∈ comp) :
    v < g.nodes.length := by
  unfold components at hmem
  dsimp only at hmem
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hmem
  rw [← hr] at hv
  exact List.mem_range.mp (List.mem_filter.mp hv).1

/-- `PackedPartTransport` (`LabelsC8bFacts.lean`) is FALSE as stated: its rect
clause demands a source part for every `k : Nat`, but component indices only
cover `k < inp.boxes.length`, while `packedAcc.rects.getD k default = default`
past the array size. The witness `packedAcc.rects.size + graph.nodes.length`
reads `default` and belongs to no component, so the required source cannot
exist. The transport's only consumer applies it at valid box indices, so the
nearest true statement guards the rect clause by
`k < packedAcc.rects.size` (`PackedPartTransportBounded` below). -/
theorem packedTransport_hrects_false {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ¬ PackedPartTransport execution := by
  intro h
  obtain ⟨packed, _, hrects, _, _, _⟩ := h
  have hge : execution.packedAcc.rects.size ≤
      execution.packedAcc.rects.size + execution.graph.nodes.length := by omega
  have hget : execution.packedAcc.rects.getD
      (execution.packedAcc.rects.size + execution.graph.nodes.length) default = default :=
    array_getD_of_size_le hge
  obtain ⟨pk, part, pos, r0, box, hparts, hpos, _, _, _, _⟩ :=
    hrects (execution.packedAcc.rects.size + execution.graph.nodes.length) default hget
  have hpartmem : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hparts
  have hmapmem : part.1 ∈ execution.componentsAcc.parts.map (·.1) :=
    List.mem_map_of_mem hpartmem
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hmap, _⟩ := actual_components_parts hempty execution.components_eq
  rw [hmap] at hmapmem
  have hkc : execution.packedAcc.rects.size + execution.graph.nodes.length ∈ part.1 :=
    List.mem_of_getElem? hpos
  have hlt := components_mem_bound hmapmem hkc
  omega

 /-- The repaired packed transport: `PackedPartTransport` with the rect clause
 guarded by `k < packedAcc.rects.size` and the false packed-frame fallback
 clause (D3) removed. Every other clause is unchanged. The
 guard matches every use: the transport's consumer applies the rect clause at
 valid box indices (`inp.boxes[k]? = some _`), which satisfy the guard by
 `packed_rects_size`. -/
def PackedPartTransportBounded {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : Prop :=
  ∃ packed : Pack.State,
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
    (∀ (k : Nat), k < execution.packedAcc.rects.size → ∀ (r : Rect),
      execution.packedAcc.rects.getD k default = r →
      ∃ (pk : Nat) (part : List Nat × Part) (pos : Nat) (r0 box : Rect),
        execution.componentsAcc.parts[pk]? = some part ∧ part.1[pos]? = some k ∧
        part.2.rects[pos]? = some r0 ∧
        packed.boxes[pk]? = some box ∧
        r = shiftRect box.x box.y r0 ∧
        box.Contained r) ∧
    (∀ (index : Nat) (r : Rect), execution.packedAcc.labels.getD index default = r →
      (∃ (pl : Nat) (part : List Nat × Part) (r0 box : Rect),
        execution.componentsAcc.parts[pl]? = some part ∧
        (index, r0) ∈ part.2.labels ∧
        packed.boxes[pl]? = some box ∧
        r = shiftRect box.x box.y r0 ∧
        box.Contained r) ∨
      r = default) ∧
    (∀ (key : Nat) (stored : Rect), (key, stored) ∈ execution.packedAcc.titles →
      ∃ (pl : Nat) (part : List Nat × Part) (i : Nat) (stored0 box : Rect),
        execution.componentsAcc.parts[pl]? = some part ∧ part.1[i]? = some key ∧
        (i, stored0) ∈ part.2.titles ∧
        packed.boxes[pl]? = some box ∧
        stored = shiftRect box.x box.y stored0 ∧
        box.Contained
          (shiftRect box.x box.y
            { stored0 with
              w := (titleCaptionSize execution.params o
                (execution.lines.getD key [])).w
              h := (titleCaptionSize execution.params o
                (execution.lines.getD key [])).h })) ∧
    (∀ (k : Nat) (r : Rect), execution.packedAcc.rects.getD k default = r → 0 ≤ r.x)

/-- Residual: packed label provenance. Every packed label read comes from the
label list of one executed part (with its packed shelf box and packed shift),
or reads `default`. This is the array-provenance half of the transport's label
clause, about the `packAcc` fold over the `components` fold; it carries no
geometry. Every constrained index is pinned by a `packedAcc.labels.getD`
equation, every part by `componentsAcc.parts` membership. -/
def PackedLabelsTransport {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : Prop :=
  ∃ packed : Pack.State,
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
    ∀ (index : Nat) (r : Rect), execution.packedAcc.labels.getD index default = r →
      (∃ (pl : Nat) (part : List Nat × Part) (r0 box : Rect),
        execution.componentsAcc.parts[pl]? = some part ∧
        (index, r0) ∈ part.2.labels ∧
        packed.boxes[pl]? = some box ∧
        r = shiftRect box.x box.y r0) ∨
      r = default

 /-- Shelf dimensions match the part dimensions at every packed position. -/
 private theorem shelfDims_of_mem {inp : Input} {o : Options} {res : FamilyResult}
     {execution : SceneExecution inp o res} {packed : Pack.State}
     (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
       execution.params.nodeGap 0
       (LayoutConst.component_aspect_num.get o.profile)
       (LayoutConst.component_aspect_den.get o.profile)
       (execution.componentsAcc.parts.map fun q =>
         ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
     {pl : Nat} {part : List Nat × Part} {box : Rect}
     (hparts : execution.componentsAcc.parts[pl]? = some part)
     (hboxes : packed.boxes[pl]? = some box) :
     box.w = part.2.width ∧ box.h = part.2.height := by
   have hdim' := Pack.pack_dimensions hpacked
   simp only [Pack.dimensions, List.map_map, Function.comp_def] at hdim'
   have hdim := congrArg (fun l : List (Int × Int) => l[pl]?) hdim'
   rw [List.getElem?_map, hboxes, List.getElem?_map, hparts] at hdim
   simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdim
   exact hdim

 /-- Rect-value source: every packed box read at a valid index comes from the
 covering executed part, with its packed shelf box and packed shift. The
 covering part comes from `parts_coverage`; the shifted value comes from
 `actual_components_packed_rect_value`. This is the provable core of the
 repaired rect clause; the shelf containment follows from part boundedness. -/
 theorem packed_rect_value_source {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     {packed : Pack.State}
     (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
       execution.params.nodeGap 0
       (LayoutConst.component_aspect_num.get o.profile)
       (LayoutConst.component_aspect_den.get o.profile)
       (execution.componentsAcc.parts.map fun q =>
         ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
     {k : Nat} (hk : k < execution.packedAcc.rects.size) {r : Rect}
     (hget : execution.packedAcc.rects.getD k default = r) :
     ∃ (pk : Nat) (part : List Nat × Part) (pos : Nat) (r0 box : Rect),
       execution.componentsAcc.parts[pk]? = some part ∧ part.1[pos]? = some k ∧
       part.2.rects[pos]? = some r0 ∧
       packed.boxes[pk]? = some box ∧
       r = shiftRect box.x box.y r0 := by
   have hsz : execution.componentsAcc.rects.size = inp.boxes.length :=
     execution.components_rects_size
   have hpsz : execution.packedAcc.rects.size = inp.boxes.length :=
     execution.packed_rects_size
   have hilt : k < execution.componentsAcc.rects.size := by omega
   have hrC : ∃ rC : Rect, execution.componentsAcc.rects[k]? = some rC :=
     ⟨_, Array.getElem?_eq_some_iff.mpr ⟨hilt, rfl⟩⟩
   obtain ⟨rC, hrC⟩ := hrC
   obtain ⟨part, hpartmem, entry, hentrymem, hentryfst⟩ :=
     execution.parts_coverage k rC hrC
   obtain ⟨index, run, loops, area, _, _, heq, _, _, _, _⟩ :=
     execution.actual_component_sizing hpartmem
   have hrectlen : part.2.rects.length = part.1.length := by
     rw [heq]
     simp [placeComponent, componentCandidate_nodes, componentGraph]
   obtain ⟨pos, hpos1, hpos2⟩ := mem_zip_pairing hrectlen.symm entry hentrymem
   rw [hentryfst] at hpos1
   have hentry : (part.1.zip part.2.rects)[pos]? = some (k, entry.2) :=
     List.getElem?_zip_eq_some.mpr ⟨hpos1, hpos2⟩
   obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpartmem
   have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
     rw [Pack.pack_count hpacked, List.length_map]
   have hclen : c < execution.componentsAcc.parts.length :=
     (List.getElem?_eq_some_iff.mp hc).1
   have hcbox : c < packed.boxes.length := by
     rw [hlen]
     exact hclen
   have hboxget : packed.boxes[c]? = some packed.boxes[c] :=
     List.getElem?_eq_getElem hcbox
   have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
       some (part, packed.boxes[c]) :=
     List.getElem?_zip_eq_some.mpr ⟨hc, hboxget⟩
   have hsize : k < execution.componentsAcc.rects.size := by
     rw [hsz, ← execution.packed_rects_size]
     exact hk
   have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
       Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
       false, [], []⟩ : Acc).parts = [] := rfl
   have hval := actual_components_packed_rect_value hempty execution.components_eq
     execution.packed_eq packed hpacked hselected hentry hsize default
   rw [hval] at hget
   exact ⟨c, part, pos, entry.2, packed.boxes[c], hc, hpos1, hpos2, hboxget, hget.symm⟩

 /-- The repaired transport assembles from the proved structural halves
 (existence, titles, valid-index rect values), the named residual, part
 boundedness, shelf dimensions, and caption fit. -/
 theorem packedTransportBounded_of_residuals {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
    (hlab : PackedLabelsTransport execution) :
     PackedPartTransportBounded execution := by
   obtain ⟨packed, hpackE, hlenE⟩ := packedShelfExistence_of_execution execution
   obtain ⟨packedL, hpackL, hlabcl⟩ := hlab
   have heqL : packedL = packed := Except.ok.inj (hpackL.symm.trans hpackE)
   rw [heqL] at hlabcl
   refine ⟨packed, hpackE, ?_, ?_, ?_, ?_⟩
   · intro k hk r hget
     obtain ⟨pk, part, pos, r0, box, hparts, hpos1, hpos2, hboxes, hreq⟩ :=
       packed_rect_value_source execution hpackE hk hget
     refine ⟨pk, part, pos, r0, box, hparts, hpos1, hpos2, hboxes, hreq, ?_⟩
     have hbnd := execution.components_parts_bounded part (List.mem_of_getElem? hparts)
     have hr0 := hbnd.2.2.1 r0 (List.mem_of_getElem? hpos2)
     have hdim := shelfDims_of_mem hpackE hparts hboxes
     unfold Rect.Contained
     rw [hreq]
     dsimp only [shiftRect]
     omega
   · intro index r hget
     rcases hlabcl index r hget with
       ⟨pl, part, r0, box, hparts, hmem, hboxes, hreq⟩ | hdef
     · refine Or.inl ⟨pl, part, r0, box, hparts, hmem, hboxes, hreq, ?_⟩
       have hbnd := execution.components_parts_bounded part (List.mem_of_getElem? hparts)
       have hr0 := hbnd.2.2.2.2.2 (index, r0) hmem
       have hr0' : 0 ≤ r0.x ∧ r0.x + r0.w ≤ part.2.width ∧
           0 ≤ r0.y ∧ r0.y + r0.h ≤ part.2.height :=
         ⟨hr0.1, hr0.2.1, hr0.2.2.1, hr0.2.2.2.1⟩
       have hdim := shelfDims_of_mem hpackE hparts hboxes
       unfold Rect.Contained
       rw [hreq]
       dsimp only [shiftRect]
       omega
     · exact Or.inr hdef
   · intro key stored hmem
     obtain ⟨pl, part, i, stored0, box, hparts, hkey, htmem, hboxes, hstored⟩ :=
       packed_titles_mem_source execution hpackE hmem
     refine ⟨pl, part, i, stored0, box, hparts, hkey, htmem, hboxes, hstored, ?_⟩
     have hpartmem := List.mem_of_getElem? hparts
     have hbnd := execution.components_parts_bounded part hpartmem
     have htB := hbnd.2.2.2.1 (i, stored0) htmem
     have htB' : 0 ≤ stored0.x ∧ stored0.x + stored0.w ≤ part.2.width ∧
         0 ≤ stored0.y ∧ stored0.y + stored0.h ≤ part.2.height :=
       ⟨htB.1, htB.2.1, htB.2.2.1, htB.2.2.2.1⟩
     have hfit := execution.component_title_caption_fit hpartmem htmem
     have hgetD : part.1.getD i 0 = key := by
       rw [List.getD_eq_getElem?_getD, hkey, Option.getD_some]
     dsimp only at hfit
     rw [hgetD] at hfit
     have hdim := shelfDims_of_mem hpackE hparts hboxes
     have hfitW : (titleCaptionSize execution.params o
         (execution.lines.getD key [])).w ≤ stored0.w := hfit.2.2.1
     have hfitH : (titleCaptionSize execution.params o
         (execution.lines.getD key [])).h ≤ stored0.h := hfit.2.2.2
     have hfitW0 : 0 ≤ (titleCaptionSize execution.params o
         (execution.lines.getD key [])).w := hfit.1
     have hfitH0 : 0 ≤ (titleCaptionSize execution.params o
         (execution.lines.getD key [])).h := hfit.2.1
     unfold Rect.Contained
     dsimp only [shiftRect]
     omega
   · intro k r hget
     by_cases hk : k < execution.packedAcc.rects.size
     · obtain ⟨pk, part, pos, r0, box, hparts, _, hpos2, hboxes, hreq⟩ :=
         packed_rect_value_source execution hpackE hk hget
       have hb := Pack.pack_bounds hpackE
       have hbx := (hb.2 box (List.mem_of_getElem? hboxes)).1
       have hbnd := execution.components_parts_bounded part (List.mem_of_getElem? hparts)
       have hr0 := hbnd.2.2.1 r0 (List.mem_of_getElem? hpos2)
       rw [hreq]
       dsimp only [shiftRect]
       omega
     · have hle : execution.packedAcc.rects.size ≤ k := by omega
       have h0 : r = default := by
         rw [← hget]
         exact array_getD_of_size_le hle
       have hdx : (default : Rect).x = 0 := rfl
       rw [h0]
       omega
 /-- The caption resize commutes with the shelf translation. -/
 private theorem caption_shift_comm {stored : Rect} {dx dy w h : Int} :
     ({ shiftRect dx dy stored with w := w, h := h } : Rect) =
       shiftRect dx dy { stored with w := w, h := h } := rfl

 set_option maxHeartbeats 800000 in
 /-- The packed-coordinate C8b core of a successful flat `PipelineImpl.layout`
 from the repaired transport: the executed component-local geometric cores plus
 the bounded packed shelf transport give `LabelFramePackedClear` over the
 actual accumulator arrays. This is the `LabelsC8bFacts.labelFramePackedClear`
 proof replayed against `PackedPartTransportBounded`; the size guard holds at
 every use site by `packed_rects_size`. -/
 theorem labelFramePackedClear_of_bounded {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     (hcores : ExecutedPartFrameCores execution)
     (htransport : PackedPartTransportBounded execution) :
     LabelFramePackedClear execution.params inp o execution.lines execution.packedAcc := by
   obtain ⟨packed, hpack, hrects, hlabels, htitles, hnonneg⟩ := htransport
   refine ⟨?_, ?_⟩
   · intro index k gBox hbox hrole
     dsimp only
     have hksize : k < execution.packedAcc.rects.size := by
       rw [execution.packed_rects_size]
       exact (List.getElem?_eq_some_iff.mp hbox).1
     obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
       hrects k hksize (execution.packedAcc.rects.getD k default) rfl
     rw [hreq] at hboxk
     rcases hlabels index (execution.packedAcc.labels.getD index default) rfl with
       ⟨pl, partl, r0l, bl, hpartl, hmeml, hbl, hreql, hboxl⟩ | hdef
     · rw [hreql] at hboxl
       by_cases hpk : pk = pl
       · subst hpk
         obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
         obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
         obtain ⟨hcore, -, -⟩ := hcores partk (List.mem_of_getElem? hpartk)
         have hclr := hcore index r0l posk k gBox r0 hmeml hkeyk hbox hrole hr0
         rw [hreq, hreql]
         rcases hclr with h | h
         · exact Or.inl (disjoint_shiftRect h)
         · exact Or.inr (strictInside_shiftRect h)
       · have hpkL : pk < execution.componentsAcc.parts.length :=
           (List.getElem?_eq_some_iff.mp hpartk).1
         have hplL : pl < execution.componentsAcc.parts.length :=
           (List.getElem?_eq_some_iff.mp hpartl).1
         have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
           rw [Pack.pack_count hpack, List.length_map]
         have hpkBox : pk < packed.boxes.length := by omega
         have hplBox : pl < packed.boxes.length := by omega
         have hd : Disjoint bk bl := by
           have hd0 : Disjoint packed.boxes[pk] packed.boxes[pl] :=
             Pack.pack_boxes_disjoint hpack pk pl hpkBox hplBox hpk
           have hbk' : packed.boxes[pk] = bk := (List.getElem?_eq_some_iff.mp hbk).2
           have hbl' : packed.boxes[pl] = bl := (List.getElem?_eq_some_iff.mp hbl).2
           rw [hbk', hbl'] at hd0
           exact hd0
         rw [hreq, hreql]
         exact Or.inl (disjoint_of_contained_disjoint hboxk hboxl hd)
     · rw [hreq, hdef]
       exact Or.inl (disjoint_default_of_nonneg (by
         rw [← hreq]
         exact hnonneg k (execution.packedAcc.rects.getD k default) rfl))
   · intro key stored htitle k gBox hbox hrole
     dsimp only
     have hksize : k < execution.packedAcc.rects.size := by
       rw [execution.packed_rects_size]
       exact (List.getElem?_eq_some_iff.mp hbox).1
     obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
       hrects k hksize (execution.packedAcc.rects.getD k default) rfl
     rw [hreq] at hboxk
     obtain ⟨pl, partl, i, stored0, bl, hpartl, hkeyi, hmeml, hbl, hstored, hboxCap⟩ :=
       htitles key stored htitle
     by_cases hpk : pk = pl
     · subst hpk
       obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
       obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
       obtain ⟨-, hcore, -⟩ := hcores partk (List.mem_of_getElem? hpartk)
       have hgetD : partk.1.getD i 0 = key := by
         simp only [List.getD, hkeyi, Option.getD_some]
       have hclr := hcore i stored0 posk k gBox r0 hmeml hkeyk hbox hrole hr0
       simp only [hgetD] at hclr
       rw [hreq, hstored, caption_shift_comm]
       rcases hclr with h | h
       · exact Or.inl (disjoint_shiftRect h)
       · exact Or.inr (strictInside_shiftRect h)
     · have hpkL : pk < execution.componentsAcc.parts.length :=
         (List.getElem?_eq_some_iff.mp hpartk).1
       have hplL : pl < execution.componentsAcc.parts.length :=
         (List.getElem?_eq_some_iff.mp hpartl).1
       have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
         rw [Pack.pack_count hpack, List.length_map]
       have hpkBox : pk < packed.boxes.length := by omega
       have hplBox : pl < packed.boxes.length := by omega
       have hd : Disjoint bk bl := by
         have hd0 : Disjoint packed.boxes[pk] packed.boxes[pl] :=
           Pack.pack_boxes_disjoint hpack pk pl hpkBox hplBox hpk
         have hbk' : packed.boxes[pk] = bk := (List.getElem?_eq_some_iff.mp hbk).2
         have hbl' : packed.boxes[pl] = bl := (List.getElem?_eq_some_iff.mp hbl).2
         rw [hbk', hbl'] at hd0
         exact hd0
       rw [hreq, hstored, caption_shift_comm]
       exact Or.inl (disjoint_of_contained_disjoint hboxk hboxCap hd)

 /-- The seam-shaped frame-label clearance: the packed C8b core and the
 fallback-caption branch for one executed flat layout, from the repaired
 transport and the two geometric residuals. This is the `frameLabels` field of
 `LayeredSeams` with the false transport replaced by its bounded repair. -/
 theorem frameLabels_of_bounded {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     (hcores : ExecutedPartFrameCores execution)
     (htransport : PackedPartTransportBounded execution)
     (hscene : SceneOwnedTextFrameCore execution) :
     LabelFramePackedClear execution.params inp o execution.lines execution.packedAcc ∧
       FallbackCaptionClear execution :=
   ⟨labelFramePackedClear_of_bounded execution hcores htransport,
     by
       intro source index ownerIndex g _ _ _ hgMem hgRole
       exact hscene ownerIndex g hgMem hgRole⟩
 /-- The packing fold preserves the label array size across shelves. -/
 private theorem packFold_labels_size_hold
     (qs : List ((List Nat × Part) × Rect)) (arr : Array Rect) :
     (qs.foldl (fun a q => q.1.2.labels.foldl
       (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) a) arr).size =
       arr.size := by
   revert arr
   induction qs with
   | nil => intro arr; rfl
   | cons q rest ih =>
     intro arr
     rw [List.foldl_cons, ih]
     exact size_keyFold_rects_eq _ _ _

 /-- Residual R1 discharged: packed label provenance follows from the landed
 label-bridge lemmas. `packFold_labels_provenance` splits a packed label read
 into a part-source case and a no-carry case; the no-carry case resolves to
 `default` through `fold_labels_getD_of_no_carry` and the replicate start
 array, using `components_fold_labels_size` and the shelf-count equality. -/
 theorem packedLabelsTransport_of_bridge {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res) :
     PackedLabelsTransport execution := by
   obtain ⟨packed, hpackE, hlenE⟩ := packedShelfExistence_of_execution execution
   refine ⟨packed, hpackE, ?_⟩
   intro index r hget
   have hpackeq := execution.packed_eq
   unfold packAcc at hpackeq
   obtain ⟨packed', hpacked', hfold⟩ := bind_ok hpackeq
   have heq : packed = packed' := Except.ok.inj (hpackE.symm.trans hpacked')
   subst heq
   have hout : execution.packedAcc =
       (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
         { execution.componentsAcc with
           canvasW := packed.width, canvasH := packed.height, titles := [] } := by
     have he := Except.ok.inj hfold
     rw [inlineFold_eq_packStep] at he
     exact he.symm
   have hlen : execution.componentsAcc.parts.length = packed.boxes.length := by
     rw [Pack.pack_count hpackE, List.length_map]
   have hcomplabelssize : execution.componentsAcc.labels.size = inp.labels.length := by
     have h := components_fold_labels_size (components execution.graph) _ _
       execution.components_eq
     rw [h]
     show (Array.replicate inp.labels.length (default : Rect)).size = inp.labels.length
     simp
   by_cases hi : index < execution.componentsAcc.labels.size
   · have hprov := packFold_labels_provenance
       (execution.componentsAcc.parts.zip packed.boxes)
       { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] }
       index r (by simpa using hi) (by rwa [← hout])
     rcases hprov with ⟨q, hqzip, r0, hmem, hr⟩ | ⟨hno, hst⟩
     · obtain ⟨pl, hplpart, hplbox⟩ := mem_zip_pairing hlen q hqzip
       exact Or.inl ⟨pl, q.1, r0, q.2, hplpart, hmem, hplbox, hr⟩
     · have hnoparts : ∀ p ∈ execution.componentsAcc.parts, ∀ r0 : Rect,
           (index, r0) ∉ p.2.labels := by
         intro p hpmem r0 hmem
         obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpmem
         have hcbox : c < packed.boxes.length := by
           rw [← hlen]
           exact (List.getElem?_eq_some_iff.mp hc).1
         have hboxget : packed.boxes[c]? = some packed.boxes[c] :=
           List.getElem?_eq_getElem hcbox
         have hqzip : (p, packed.boxes[c]) ∈
             execution.componentsAcc.parts.zip packed.boxes :=
           zip_mem_of_getElem? hc hboxget
         exact hno (p, packed.boxes[c]) hqzip r0 hmem
       have hcomp := fold_labels_getD_of_no_carry (components execution.graph) _ _
         index execution.components_eq hnoparts
       have hst2 : execution.componentsAcc.labels.getD index default = r := hst
       rw [hcomp] at hst2
       dsimp only at hst2
       have hrep : (Array.replicate inp.labels.length (default : Rect)).getD index
           default = default := by
         rw [Array.getD_eq_getD_getElem?]
         cases h : (Array.replicate inp.labels.length (default : Rect))[index]? with
         | none => rfl
         | some x =>
           have hx : x = default := (layout_startAcc_defaults inp).2.2 index x h
           simp [hx]
       rw [hrep] at hst2
       exact Or.inr hst2.symm
   · have hle : execution.componentsAcc.labels.size ≤ index := by omega
     have hpacksize : execution.packedAcc.labels.size =
         execution.componentsAcc.labels.size := by
       rw [hout, pack_labels_eq_fold, packFold_labels_size_hold]
     have hle' : execution.packedAcc.labels.size ≤ index := by
       rw [hpacksize]; exact hle
     have hdef : execution.packedAcc.labels.getD index default = default :=
       array_getD_of_size_le hle'
     exact Or.inr (hget.symm.trans hdef)

 /-- The seam-shaped frame-label clearance with fewer open facts: the packed
 transport is discharged outright (`packedShelfExistence_of_execution`,
 `packed_titles_mem_source`, `packed_rect_value_source`, and the R1 bridge
 `packedLabelsTransport_of_bridge`), leaving the component-local geometric
 cores (`ExecutedPartFrameCores`) and the scene-level caption core
 (`SceneOwnedTextFrameCore`) as the only hypotheses. -/
 theorem frameLabels_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hcores : ExecutedPartFrameCores execution)
    (hscene : SceneOwnedTextFrameCore execution) :
    LabelFramePackedClear execution.params inp o execution.lines execution.packedAcc ∧
      FallbackCaptionClear execution := by
  have htransport := packedTransportBounded_of_residuals execution
    (packedLabelsTransport_of_bridge execution)
  exact ⟨labelFramePackedClear_of_bounded execution hcores htransport,
    by
      intro source index ownerIndex g _ _ _ hgMem hgRole
      exact hscene ownerIndex g hgMem hgRole⟩

 end PipelineImpl

end Elegant.Layered
