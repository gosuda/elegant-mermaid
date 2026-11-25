import Elegant.Layered.ExactFlatC8b
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.SceneBounds
import Elegant.Layered.PipelineFacts
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.Pack

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact packed-part transport (`X_PackedPartTransportBoundedB8`).

Replays `packedTransportBounded_of_residuals` (`FrameLabelsProof.lean`) over
`SceneExecutionX`. The plain proof assembles the transport from pack
existence, rect-value source, label provenance, title-membership source,
part boundedness, shelf dimensions, and caption fit. The exact replay keeps
the same assembly:

* Pack existence and the rect-value source are proved here. The rect source
  replays `packed_rect_value_source` with the tracked exact mirrors
  (`SceneExecutionX.parts_coverage`,
  `actual_components_packed_rect_valueX`, `ActualPartGeometryX` part shape,
  `placeComponentExact` rect length). The placement differs from the plain
  one only for runs with a nonempty `run.exact` (exact-width envelopes), and
  none of the transport steps inspect that branch.
* Part boundedness is the tracked `exactPartsBounded` (needs the tracked
  per-execution `ExactBorder2Unchanged` hypothesis, kept as `hX`).
* Shelf dimensions and `Pack.pack_bounds` are base-independent.
* Three single facts stay open as named residuals: exact label provenance
  (`X_PackedLabelsTransport`, mirror of the plain open residual
  `PackedLabelsTransport`), exact packed-title membership
  (`X_PackedTitlesMemSource`, mirror of `packed_titles_mem_source`),
  and exact stored-title caption fit (`X_ExactTitleCaptionFit`, mirror of
  `SceneExecution.component_title_caption_fit`).

Probe evidence (`wip/Probe/ExactPackedTransportTProbe.lean`): a Bool mirror
of every transport clause plus the title-fit and border facts evaluates to
`true` on a titled flat input, on the same input with a zero fixed size on
the exact id, and on the zero-fixed-size input without exact ids. -/

/-- Exact packed-label provenance residual: mirror of
`PackedLabelsTransport` over `SceneExecutionX`. Every packed label read
comes from the label list of one executed part (with its packed shelf box
and packed shift), or reads `default`. -/
def X_PackedLabelsTransport (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res),
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

/-- Exact packed-title membership residual: mirror of
`packed_titles_mem_source` over `SceneExecutionX`. Every packed title entry
comes from one executed part entry, with its packed shelf box and packed
shift. Title keys are in range for the same reason as in the plain proof;
the exact title-list construction is the one long step kept open here. -/
def X_PackedTitlesMemSource (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {packed : Pack.State}
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {key : Nat} {stored : Rect}
    (_hmem : (key, stored) ∈ execution.packedAcc.titles),
    ∃ (pl : Nat) (part : List Nat × Part) (i : Nat) (stored0 box : Rect),
      execution.componentsAcc.parts[pl]? = some part ∧
      part.1[i]? = some key ∧
      (i, stored0) ∈ part.2.titles ∧
      packed.boxes[pl]? = some box ∧
      stored = shiftRect box.x box.y stored0

/-- Exact stored-title caption-fit residual: mirror of
`SceneExecution.component_title_caption_fit` over `SceneExecutionX`. Every
stored title of an executed part covers its measured caption size. -/
def X_ExactTitleCaptionFit (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {part : List Nat × Part} (_hpart : part ∈ execution.componentsAcc.parts)
    {title : Nat × Rect} (_htitle : title ∈ part.2.titles),
    let lines := execution.lines.getD (part.1.getD title.1 0) []
    let width := lines.foldl (fun value line => max value line.width) 0
    let height := (max 1 lines.length : Int) * execution.params.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ title.2.w ∧ size.h ≤ title.2.h

/-- The packing fold preserves the rect array size (prefixed copy of the
private `X_packFold_rects_size` in `ExactFitClosure.lean`). -/
private theorem xpptb_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- Exact packed rect array size (prefixed copy of the private
`X_packed_rects_size` in `ExactFitClosure.lean`). -/
private theorem xpptb_packedAcc_rects_size {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width
      canvasH := packed.height
      titles := [] }).rects.size = inp.boxes.length
  rw [xpptb_packFold_rects_size]
  exact execution.components_rects_size

/-- Exact placed-component rect length (prefixed copy of the private
`placeComponentExact_rects_length` in `ExactFlatFacts.lean`). -/
private theorem xpptb_placeComponentExact_rects_length (P : Params) (cg : Graph)
    (run : Run) (cursor : Int) (labels : List MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run cursor labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  simp [List.length_map, List.length_range]

/-- Exact candidate node length (prefixed copy of the private
`componentCandidate_nodes_lengthX` in `ExactFlatFacts.lean`). -/
private theorem xpptb_componentCandidate_nodes_lengthX (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  show (comp.map fun v => g.nodes.getD v default).length = comp.length
  exact List.length_map ..

/-- Shelf dimensions match the part dimensions at every packed position
(prefixed copy of the private `shelfDims_of_mem` in
`FrameLabelsProof.lean`). -/
private theorem xpptb_shelfDims_of_mem {inp : Input} {o : Options} {res : FamilyResult}
    {exactIds : List String} {execution : SceneExecutionX exactIds inp o res}
    {packed : Pack.State}
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

/-- The pack-existence half of the exact packed transport holds outright:
`packAcc` exposes the packed shelf state, and its box count matches the
executed part count (replay of `packedShelfExistence_of_execution`). -/
private theorem xpptb_packedShelfExistence_of_execution {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
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

/-- Rect-value source over the exact execution: every packed box read at a
valid index comes from the covering executed part, with its packed shelf
box and packed shift (replay of `packed_rect_value_source` with
`SceneExecutionX.parts_coverage`, `actual_components_packed_rect_valueX`,
and the exact-placed part shape). -/
private theorem xpptb_rect_value_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
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
    xpptb_packedAcc_rects_size execution
  have hilt : k < execution.componentsAcc.rects.size := by omega
  have hrC : ∃ rC : Rect, execution.componentsAcc.rects[k]? = some rC :=
    ⟨_, Array.getElem?_eq_some_iff.mpr ⟨hilt, rfl⟩⟩
  obtain ⟨rC, hrC⟩ := hrC
  obtain ⟨part, hpartmem, entry, hentrymem, hentryfst⟩ :=
    execution.parts_coverage k rC hrC
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨index, _, run, loops, area, _, _, _, _, _, hpartdef⟩ :=
    (actual_components_parts_geometryX hempty execution.components_eq).2 part hpartmem
  have hrectlen : part.2.rects.length = part.1.length := by
    rw [hpartdef]
    change (placeComponentExact execution.params
      (componentCandidate execution.graph part.1 index) run 0
      execution.measured loops).rects.length = part.1.length
    rw [xpptb_placeComponentExact_rects_length,
      xpptb_componentCandidate_nodes_lengthX]
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
    rw [hsz, ← hpsz]
    exact hk
  have hval := actual_components_packed_rect_valueX hempty execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hsize default
  rw [hval] at hget
  exact ⟨c, part, pos, entry.2, packed.boxes[c], hc, hpos1, hpos2, hboxget, hget.symm⟩

/-- The exact packed-part transport holds modulo the three single-fact
residuals and the tracked border hypothesis: replay of
`packedTransportBounded_of_residuals` over `SceneExecutionX`. Shelf
containment in every clause comes from the tracked `exactPartsBounded`
plus the base-independent shelf dimensions; the title clause additionally
consumes the exact title-membership and caption-fit residuals, and the
label clause consumes the exact label-provenance residual. -/
theorem X_packedPartTransportBounded_holds (exactIds : List String)
    (hlabels : X_PackedLabelsTransport exactIds)
    (htitles : X_PackedTitlesMemSource exactIds)
    (hfit : X_ExactTitleCaptionFit exactIds)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hX : ExactBorder2Unchanged execution) :
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
      (∀ (k : Nat) (r : Rect), execution.packedAcc.rects.getD k default = r → 0 ≤ r.x) := by
  obtain ⟨packed, hpackE, hlenE⟩ := xpptb_packedShelfExistence_of_execution execution
  obtain ⟨packedL, hpackL, hlabcl⟩ := hlabels execution
  have heqL : packedL = packed := Except.ok.inj (hpackL.symm.trans hpackE)
  rw [heqL] at hlabcl
  refine ⟨packed, hpackE, ?_, ?_, ?_, ?_⟩
  · intro k hk r hget
    obtain ⟨pk, part, pos, r0, box, hparts, hpos1, hpos2, hboxes, hreq⟩ :=
      xpptb_rect_value_source execution hpackE hk hget
    refine ⟨pk, part, pos, r0, box, hparts, hpos1, hpos2, hboxes, hreq, ?_⟩
    have hbnd := exactPartsBounded execution hX part (List.mem_of_getElem? hparts)
    have hr0 := hbnd.2.2.1 r0 (List.mem_of_getElem? hpos2)
    have hdim := xpptb_shelfDims_of_mem hpackE hparts hboxes
    unfold Rect.Contained
    rw [hreq]
    dsimp only [shiftRect]
    omega
  · intro index r hget
    rcases hlabcl index r hget with
      ⟨pl, part, r0, box, hparts, hmem, hboxes, hreq⟩ | hdef
    · refine Or.inl ⟨pl, part, r0, box, hparts, hmem, hboxes, hreq, ?_⟩
      have hbnd := exactPartsBounded execution hX part (List.mem_of_getElem? hparts)
      have hr0 := hbnd.2.2.2.2.2 (index, r0) hmem
      have hr0' : 0 ≤ r0.x ∧ r0.x + r0.w ≤ part.2.width ∧
          0 ≤ r0.y ∧ r0.y + r0.h ≤ part.2.height :=
        ⟨hr0.1, hr0.2.1, hr0.2.2.1, hr0.2.2.2.1⟩
      have hdim := xpptb_shelfDims_of_mem hpackE hparts hboxes
      unfold Rect.Contained
      rw [hreq]
      dsimp only [shiftRect]
      omega
    · exact Or.inr hdef
  · intro key stored hmem
    obtain ⟨pl, part, i, stored0, box, hparts, hkey, htmem, hboxes, hstored⟩ :=
      htitles execution hpackE hmem
    refine ⟨pl, part, i, stored0, box, hparts, hkey, htmem, hboxes, hstored, ?_⟩
    have hpartmem := List.mem_of_getElem? hparts
    have hbnd := exactPartsBounded execution hX part hpartmem
    have htB := hbnd.2.2.2.1 (i, stored0) htmem
    have htB' : 0 ≤ stored0.x ∧ stored0.x + stored0.w ≤ part.2.width ∧
        0 ≤ stored0.y ∧ stored0.y + stored0.h ≤ part.2.height :=
      ⟨htB.1, htB.2.1, htB.2.2.1, htB.2.2.2.1⟩
    have hfitX := hfit execution hpartmem htmem
    have hgetD : part.1.getD i 0 = key := by
      rw [List.getD_eq_getElem?_getD, hkey, Option.getD_some]
    dsimp only at hfitX
    rw [hgetD] at hfitX
    have hdim := xpptb_shelfDims_of_mem hpackE hparts hboxes
    have hfitW : (titleCaptionSize execution.params o
        (execution.lines.getD key [])).w ≤ stored0.w := hfitX.2.2.1
    have hfitH : (titleCaptionSize execution.params o
        (execution.lines.getD key [])).h ≤ stored0.h := hfitX.2.2.2
    have hfitW0 : 0 ≤ (titleCaptionSize execution.params o
        (execution.lines.getD key [])).w := hfitX.1
    have hfitH0 : 0 ≤ (titleCaptionSize execution.params o
        (execution.lines.getD key [])).h := hfitX.2.1
    unfold Rect.Contained
    dsimp only [shiftRect]
    omega
  · intro k r hget
    by_cases hk : k < execution.packedAcc.rects.size
    · obtain ⟨pk, part, pos, r0, box, hparts, _, hpos2, hboxes, hreq⟩ :=
        xpptb_rect_value_source execution hpackE hk hget
      have hb := Pack.pack_bounds hpackE
      have hbx := (hb.2 box (List.mem_of_getElem? hboxes)).1
      have hbnd := exactPartsBounded execution hX part (List.mem_of_getElem? hparts)
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

end PipelineImpl
end Layered
end Elegant
