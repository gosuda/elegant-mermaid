import Elegant.Layered.CaptionsSeamFacts
import Elegant.Layered.CaptionSizingGroupFacts
import Elegant.Layered.CaptionDescendantFacts
import Elegant.Layered.CaptionOwnerScopeFacts
import Elegant.Layered.CaptionTitleBranchFacts
import Elegant.Layered.CaptionDescendantCore
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.GroupFrameSizingFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Caption inputs from the executed group floors and the caption contract. -/
theorem captionInputs_of_premises {inp : Input} {o : Options} {res : FamilyResult}
    (hcap : ∃ captions : String → String, CaptionInputs captions inp o)
    (hfloor : Elegant.Layered.CaptionGroupFrameWidthFloor inp o res)
    (htitle : Elegant.Layered.CaptionGroupTitleWidthFloor inp o res) :
    Elegant.Layered.CaptionInputs inp o res :=
  Elegant.Layered.captionInputs_of_group_facts hcap hfloor htitle

/-- Executed group-owner half of `OwnerScopeSamePartClear`: when the
non-exclusive caption owner at `ownerIndex` is a group-role box, its run-level
`frameRect` is disjoint from the run-level `frameRect` of the foreign exclusive
box at `bi` in the same executed part. This is the missing executed fact for
unrelated group-versus-plain layouts (the node-owner half follows from
`componentRun_positions_disjoint` via `WellFormed`); it is pinned by the same
executed-part membership and successful `componentRun` as the goal and covers
strictly fewer pairs. -/
def OwnerScopeGroupOwnerDisjoint (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (Elegant.Layered.captionLabel inp o res execution ownerIndex source lines) →
    source.owner ∉ res.scene.layoutDump.ancestors b.id →
    ∀ (ownerBox : ModelBox), inp.boxes[ownerIndex]? = some ownerBox →
      ownerBox.role = .group →
      ∀ (bi k posOwner posB : Nat) (part : List Nat × Part),
        res.scene.boxes[bi]? = some b →
        execution.componentsAcc.parts[k]? = some part →
        part.1[posOwner]? = some ownerIndex →
        part.1[posB]? = some bi →
        posOwner ≠ posB →
        ∀ (candidate : Nat) (run : Run),
          componentRun execution.params
            (componentCandidate execution.graph part.1 candidate)
            execution.measured (candidateOrder candidate) = .ok run →
          Disjoint
            (frameRect execution.params
              (componentCandidate execution.graph part.1 candidate) run
              posOwner)
            (frameRect execution.params
              (componentCandidate execution.graph part.1 candidate) run
              posB)

/-- A `findIdx?` hit exposes the box at that index (local copy of the private
`CaptionOwnerScopeFacts` helper). -/
private theorem ownerRes_findIdx_lookup {α : Type} {p : α → Bool}
    {l : List α} {n : Nat} (h : l.findIdx? p = some n) :
    n < l.length ∧ ∃ a, l[n]? = some a ∧ p a = true := by
  induction l generalizing n with
  | nil =>
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons a as ih =>
    rw [List.findIdx?_cons] at h
    by_cases hp : p a = true
    · rw [ite_eq_left hp] at h
      have hn : n = 0 := (Option.some.inj h).symm
      subst hn
      exact ⟨Nat.zero_lt_succ _, a, rfl, hp⟩
    · rw [ite_eq_right hp] at h
      obtain ⟨m, hmfind, hmn⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hmlen, x, hxget, hpx⟩ := ih hmfind
      rw [← hmn]
      exact ⟨Nat.succ_lt_succ hmlen, x, (List.getElem?_cons_succ).trans hxget, hpx⟩

/-- A component position key is the measured-graph node at that key (local copy
of the private `FlatC2` helper). -/
private theorem ownerRes_component_node_lookup {graph : Graph} {comp : List Nat}
    {cand : Nat} {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

/-- A node-role source box of a successful execution is a border-0 measured
node, whether or not its size is fixed. -/
private theorem ownerRes_node_border_zero {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {key : Nat} {box : ModelBox} (hbox : inp.boxes[key]? = some box)
    (hrole : box.role = .node) (hlen : key < execution.lines.length) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0 := by
  have hline : execution.lines[key]? = some execution.lines[key] :=
    List.getElem?_eq_some_iff.mpr ⟨hlen, rfl⟩
  cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
  | none =>
    have hfalse : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
      List.any_eq_false.mpr (List.find?_eq_none.mp hf)
    obtain ⟨node, hnode, _, hborder⟩ :=
      measuredGraph_node_border_zero execution.checked execution.graph_eq
        hline hbox hrole hfalse
    exact ⟨node, hnode, hborder⟩
  | some entry =>
    obtain ⟨_, _, node, _, _, hnode, hborder, _⟩ :=
      measuredGraph_fixed_loop_reservation execution.graph_eq
        (List.getElem?_eq_some_iff.mp hline).1 hbox hf
    exact ⟨node, hnode, hborder⟩

/-- `OwnerScopeSamePartClear` from `WellFormed` and the group-owner half: a
node-role owner and the foreign exclusive box are both border-0 measured
nodes, so `componentRun_positions_disjoint` applies; a group-role owner uses
the residual. -/
theorem ownerScopeSamePartClear_of_group_disjoint {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (Elegant.Layered.inputModel inp o))
    (hgroup : OwnerScopeGroupOwnerDisjoint inp o res) :
    Elegant.Layered.OwnerScopeSamePartClear inp o res := by
  intro execution index ownerIndex source lines b hsrc hmeas hfindIdx hmem hex
    hscope hd _hnone bi k posOwner posB part hbi hk hposO hposB hne candidate run hrun
  obtain ⟨_, obox, hobox, hpobox⟩ := ownerRes_findIdx_lookup hfindIdx
  have hpred : (obox.id == source.owner && !obox.exclusive) = true := hpobox
  simp only [Bool.and_eq_true] at hpred
  by_cases hrole : obox.role = .group
  · exact hgroup execution index ownerIndex source lines b hsrc hmeas hfindIdx
      hmem hex hscope hd obox hobox hrole bi k posOwner posB part hbi hk hposO
      hposB hne candidate run hrun
  · have hroleNode : obox.role = .node := by
      cases h : obox.role with
      | node => rfl
      | group => exact absurd h hrole
    have hlinesLen : execution.lines.length = inp.boxes.length := by
      have hl := execution.lines_eq
      unfold boxLines at hl
      calc execution.lines.length = (inp.boxes.zipIdx).length :=
          (mapM_getElem? _ _ _ hl).1
        _ = inp.boxes.length := List.length_zipIdx
    have hOILen : ownerIndex < execution.lines.length := by
      rw [hlinesLen]
      exact (List.getElem?_eq_some_iff.mp hobox).1
    obtain ⟨sb, hsb, _, _, hsbex, _⟩ := sceneBox_source_rect execution hbi
    have hsbexTrue : sb.exclusive = true := by rw [← hsbex]; exact hex
    have hBILen : bi < execution.lines.length := by
      rw [hlinesLen]
      exact (List.getElem?_eq_some_iff.mp hsb).1
    obtain ⟨nodeO, hnodeO, hbO⟩ :=
      ownerRes_node_border_zero execution hobox hroleNode hOILen
    have hngB : sb.role ≠ .group :=
      wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsb) hsbexTrue
    have hroleB : sb.role = .node := by
      cases h : sb.role with
      | node => rfl
      | group => exact absurd h hngB
    obtain ⟨nodeB, hnodeB, hbB⟩ :=
      ownerRes_node_border_zero execution hsb hroleB hBILen
    have hmap := (actual_components_parts_geometry (P := execution.params)
      (by rfl : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ : Acc).parts = []) execution.components_eq).1
    have hpartMem : part ∈ execution.componentsAcc.parts :=
      List.mem_of_getElem? hk
    have hcomp : part.1 ∈ components execution.graph := by
      rw [← hmap]
      exact List.mem_map.mpr ⟨part, hpartMem, rfl⟩
    have hnodeOlookup :
        (componentCandidate execution.graph part.1 candidate).nodes[posOwner]? =
        some nodeO := ownerRes_component_node_lookup hposO hnodeO
    have hnodeBlookup :
        (componentCandidate execution.graph part.1 candidate).nodes[posB]? =
        some nodeB := ownerRes_component_node_lookup hposB hnodeB
    exact componentRun_positions_disjoint execution.graph_eq hcomp hrun
      hnodeOlookup hnodeBlookup hbO hbB hne

/-- Same-part half of `TitleExclusiveFrameDisjoint`: the packed title caption of
`key` is disjoint from the packed rect of the exclusive box `k` when the title
fold location `cT` and the exclusive part index `cB` coincide. This covers
strictly fewer pairs than the goal (the cross-part half is separate); it is
pinned by the same packed-title membership and executed-part membership as the
goal. -/
def TitleExclusiveSamePart (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (_hwf : WellFormed (Elegant.Layered.inputModel inp o))
    (execution : SceneExecution inp o res) (key : Nat) (stored : Rect),
    (key, stored) ∈ execution.packedAcc.titles →
    ∀ (k : Nat) (fBox : ModelBox), inp.boxes[k]? = some fBox →
      fBox.exclusive = true →
      ∀ (packed : Pack.State),
        Pack.pack (if o.profile == .cell then o.maxWidth else 0)
          execution.params.nodeGap 0
          (LayoutConst.component_aspect_num.get o.profile)
          (LayoutConst.component_aspect_den.get o.profile)
          (execution.componentsAcc.parts.map fun q =>
            Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed →
        ∀ (cT : Nat) (partT : List Nat × Part) (boxT : Rect) (title : Nat × Rect),
          (execution.componentsAcc.parts.zip packed.boxes)[cT]? =
            some (partT, boxT) →
          title ∈ partT.2.titles →
          key = partT.1.getD title.1 0 →
          stored = shiftRect boxT.x boxT.y title.2 →
          ∀ (cB : Nat) (partB : List Nat × Part) (posB : Nat),
            execution.componentsAcc.parts[cB]? = some partB →
            partB.1[posB]? = some k →
            cT = cB →
            Disjoint (execution.packedAcc.rects.getD k default)
              { stored with
                w := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).w
                h := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).h }

/-- Cross-part half of `TitleExclusiveFrameDisjoint`: the packed title caption
of `key` (located via the title fold in part `cT`) is disjoint from the packed
rect of the exclusive box `k` (located in part `cB`) when the part indices
differ. This covers strictly fewer pairs than the goal (the same-part half is
separate); it is pinned by the same packed-title membership and executed-part
membership as the goal. -/
def TitleExclusiveCrossPart (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (_hwf : WellFormed (Elegant.Layered.inputModel inp o))
    (execution : SceneExecution inp o res) (key : Nat) (stored : Rect),
    (key, stored) ∈ execution.packedAcc.titles →
    ∀ (k : Nat) (fBox : ModelBox), inp.boxes[k]? = some fBox →
      fBox.exclusive = true →
      ∀ (packed : Pack.State),
        Pack.pack (if o.profile == .cell then o.maxWidth else 0)
          execution.params.nodeGap 0
          (LayoutConst.component_aspect_num.get o.profile)
          (LayoutConst.component_aspect_den.get o.profile)
          (execution.componentsAcc.parts.map fun q =>
            Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed →
        ∀ (cT : Nat) (partT : List Nat × Part) (boxT : Rect) (title : Nat × Rect),
          (execution.componentsAcc.parts.zip packed.boxes)[cT]? =
            some (partT, boxT) →
          title ∈ partT.2.titles →
          key = partT.1.getD title.1 0 →
          stored = shiftRect boxT.x boxT.y title.2 →
          ∀ (cB : Nat) (partB : List Nat × Part) (posB : Nat),
            execution.componentsAcc.parts[cB]? = some partB →
            partB.1[posB]? = some k →
            cT ≠ cB →
            Disjoint (execution.packedAcc.rects.getD k default)
              { stored with
                w := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).w
                h := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).h }

/-- The title fold deposits shifted part titles into the packed accumulator
(local copy of the private `CaptionWidthFacts` helper). -/
private theorem titleRes_pack_titles_fold
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).titles = start.titles ++
      pairs.flatMap (fun pair => pair.1.2.titles.map
        (fun title => (pair.1.1.getD title.1 0,
          shiftRect pair.2.x pair.2.y title.2))) := by
  induction pairs generalizing start with
  | nil => simp
  | cons pair rest ih =>
    simp [List.foldl_cons, ih, packStep, List.append_assoc]

/-- Every packed title comes from a part title shifted by its shelf origin. -/
private theorem titleRes_packed_title_part {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (packed : Pack.State) (hpack : Pack.pack
      (if o.profile == .cell then o.maxWidth else 0) execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    {key : Nat} {stored : Rect}
    (hmem : (key, stored) ∈ execution.packedAcc.titles) :
    ∃ (cT : Nat) (partT : List Nat × Part) (boxT : Rect) (title : Nat × Rect),
      (execution.componentsAcc.parts.zip packed.boxes)[cT]? =
        some (partT, boxT) ∧
      title ∈ partT.2.titles ∧
      key = partT.1.getD title.1 0 ∧
      stored = shiftRect boxT.x boxT.y title.2 := by
  have hpackEq := execution.packed_eq
  unfold packAcc at hpackEq
  obtain ⟨packed0, hpack0, hfold0⟩ := bind_ok hpackEq
  have h0 : packed0 = packed := Except.ok.inj (hpack0.symm.trans hpack)
  rw [h0] at hfold0
  have hpackedAcc : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
        { execution.componentsAcc with
          canvasW := packed.width, canvasH := packed.height,
          titles := [] } := (Except.ok.inj hfold0).symm
  rw [hpackedAcc, titleRes_pack_titles_fold] at hmem
  simp only [List.nil_append] at hmem
  obtain ⟨pair, hpairMem, hmemMap⟩ := List.mem_flatMap.mp hmem
  obtain ⟨title, htitleMem, heq⟩ := List.mem_map.mp hmemMap
  obtain ⟨cT, hzipT⟩ := List.mem_iff_getElem?.mp hpairMem
  exact ⟨cT, pair.1, pair.2, title, hzipT, htitleMem,
    (congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

/-- `TitleExclusiveFrameDisjoint` from `WellFormed` and the same/cross-part
halves. The title is located via the title fold and the exclusive index via
`ownerScope_part_position`; equal part indices use the same-part half,
distinct indices use the cross-part half. -/
theorem titleExclusiveFrameDisjoint_of_parts {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (Elegant.Layered.inputModel inp o))
    (hsame : TitleExclusiveSamePart inp o res)
    (hcross : TitleExclusiveCrossPart inp o res)
    (execution : SceneExecution inp o res) :
    TitleExclusiveFrameDisjoint execution := by
  intro key stored hmem k fBox hbox hex
  have hpackEq := execution.packed_eq
  unfold packAcc at hpackEq
  obtain ⟨packed, hpack, _⟩ := bind_ok hpackEq
  have hKLEN : k < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hbox).1
  obtain ⟨partB, posB, cB, hcB, hposB⟩ :=
    Elegant.Layered.ownerScope_part_position execution hKLEN
  obtain ⟨cT, partT, boxT, title, hzipT, htitleMem, hkeyEq, hstoredEq⟩ :=
    titleRes_packed_title_part execution packed hpack hmem
  by_cases heq : cT = cB
  · exact hsame hwf execution key stored hmem k fBox hbox hex packed hpack cT
      partT boxT title hzipT htitleMem hkeyEq hstoredEq cB partB posB hcB hposB
      heq
  · exact hcross hwf execution key stored hmem k fBox hbox hex packed hpack cT
      partT boxT title hzipT htitleMem hkeyEq hstoredEq cB partB posB hcB hposB
      heq

/-- Fallback half of `CaptionDescendantSamePartClear`: when the packed
accumulator carries no installed title for the owner, the fallback
`ownedTextRect` caption (the `sceneCaptionRect` branch for `find? = none`) misses
the interior of the exclusive descendant member. This covers strictly fewer
pairs than the goal (the installed-title branch is separate, discharged via
`TitleExclusiveFrameDisjoint`); it is pinned by the same executed-part
membership and successful `componentRun` as the goal. The `WellFormed` and
`framedParents` premises rule out the ill-formed node-owner descendant shape,
so the remaining obligation is the group caption-band reservation transported
through packing and the margin/orientation projection. -/
def DescendantFallbackClear (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (_hwf : WellFormed (Elegant.Layered.inputModel inp o))
    (_hfp : Elegant.Layered.framedParents inp = true)
    (execution : SceneExecution inp o res) (index ownerIndex bi : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (Elegant.Layered.captionLabel inp o res execution ownerIndex source lines) →
    source.owner ∈ res.scene.layoutDump.ancestors b.id →
    (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == source.owner) = none →
    ∀ (kO kB posO posB : Nat) (partO partB : List Nat × Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[kO]? = some partO →
      execution.componentsAcc.parts[kB]? = some partB →
      partO.1[posO]? = some ownerIndex →
      partB.1[posB]? = some bi →
      ¬ (sceneCaptionRect execution.params inp o execution.lines
          execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- `CaptionDescendantSamePartClear` from `WellFormed`, `framedParents`, the
installed-title clearance (`TitleExclusiveFrameDisjoint`), and the fallback
half. The `find?` on the packed titles decides the `sceneCaptionRect` branch:
`some` uses the packed title disjointness transported to the scene, `none`
uses the residual. -/
theorem captionDescendantSamePartClear_of_fallback {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (Elegant.Layered.inputModel inp o))
    (hfp : Elegant.Layered.framedParents inp = true)
    (htitle : ∀ (execution : SceneExecution inp o res),
      TitleExclusiveFrameDisjoint execution)
    (hfallback : DescendantFallbackClear inp o res) :
    Elegant.Layered.CaptionDescendantSamePartClear inp o res := by
  intro execution index ownerIndex bi source lines b hsrc hmeas hfindIdx hmem
    hex hscope hd kO kB posO posB partO partB hbi hkO hkB hposO hposB
  cases hfind : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == source.owner) with
  | none =>
    exact hfallback hwf hfp execution index ownerIndex bi source lines b hsrc
      hmeas hfindIdx hmem hex hscope hd hfind kO kB posO posB partO partB hbi
      hkO hkB hposO hposB
  | some tsel =>
    have hselMem := List.mem_of_find?_eq_some hfind
    obtain ⟨stored, hstoredMem, hfeq⟩ := List.mem_filterMap.mp hselMem
    cases hbx : inp.boxes[stored.1]? with
    | none => simp only [hbx] at hfeq; cases hfeq
    | some _box0 =>
      simp only [hbx] at hfeq
      have hpair := Option.some.inj hfeq
      have htrect : shiftRect execution.params.canvasMargin
          execution.params.canvasMargin (orientRect o.direction
            execution.packedAcc.canvasH
            { stored.2 with
              w := (titleCaptionSize execution.params o
                (execution.lines.getD stored.1 [])).w
              h := (titleCaptionSize execution.params o
                (execution.lines.getD stored.1 [])).h }) = tsel.2 :=
        congrArg Prod.snd hpair
      simp only [sceneCaptionRect]
      rw [hfind]
      simp only [Option.map_some, Option.getD_some]
      rw [← htrect]
      simp only [Scene.layoutDump] at hmem
      rw [execution.boxes_eq_map] at hmem
      obtain ⟨q, hq, hbeq⟩ := List.mem_map.mp hmem
      obtain ⟨fBox, hKey⟩ := q
      have hKeyBox : inp.boxes[hKey]? = some fBox :=
        List.mem_zipIdx_iff_getElem?.mp hq
      have hex' : fBox.exclusive = true := by
        rw [← hbeq] at hex
        exact hex
      rw [← hbeq]
      show ¬ (shiftRect execution.params.canvasMargin
          execution.params.canvasMargin (orientRect o.direction
            execution.packedAcc.canvasH
            { stored.2 with
              w := (titleCaptionSize execution.params o
                (execution.lines.getD stored.1 [])).w
              h := (titleCaptionSize execution.params o
                (execution.lines.getD stored.1 [])).h })).meetsInterior
        (shiftRect execution.params.canvasMargin
          execution.params.canvasMargin (orientRect o.direction
            execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD hKey default)))
      have hd := htitle execution stored.1 stored.2 hstoredMem hKey fBox
        hKeyBox hex'
      exact disjoint_sceneTransport (fun hm => hd (rect_meetsInterior_comm hm))


/-- The layered caption seam from the remaining residuals: `WellFormed` and
`framedParents` are the `LayeredSeams.captions` premises; the caption-input
existence plus the two group floors give `CaptionInputs`; the group-owner half
gives `OwnerScopeSamePartClear`; the title same/cross halves give
`TitleExclusiveFrameDisjoint`; the title clearance plus the fallback half give
`CaptionDescendantSamePartClear`; the tracked combiner
(`CaptionsSeamFacts.sceneCaptionBoxContainment_of_residuals`) plus the other
worker's `frameLabels` bundle (`LabelFramePackedClear` and
`FallbackCaptionClear`) conclude `SceneCaptionBoxContainment`. Its hypotheses
are exactly the residuals that remain plus the other worker's frame-label
bundle. -/
theorem sceneCaptionBoxContainment_of_residuals {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (Elegant.Layered.inputModel inp o))
    (hfp : Elegant.Layered.framedParents inp = true)
    (hcap_exists : ∃ captions : String → String, CaptionInputs captions inp o)
    (hfloorW : Elegant.Layered.CaptionGroupFrameWidthFloor inp o res)
    (hfloorT : Elegant.Layered.CaptionGroupTitleWidthFloor inp o res)
    (hgroup : OwnerScopeGroupOwnerDisjoint inp o res)
    (hsameT : TitleExclusiveSamePart inp o res)
    (hcrossT : TitleExclusiveCrossPart inp o res)
    (hfallback : DescendantFallbackClear inp o res)
    (hframes : ∀ (execution : SceneExecution inp o res),
      LabelFramePackedClear execution.params inp o execution.lines
        execution.packedAcc ∧ FallbackCaptionClear execution) :
    Elegant.Layered.SceneCaptionBoxContainment inp o res := by
  have hinputs := captionInputs_of_premises hcap_exists hfloorW hfloorT
  have hsameFull := ownerScopeSamePartClear_of_group_disjoint hwf hgroup
  have htitle : ∀ (execution : SceneExecution inp o res),
      TitleExclusiveFrameDisjoint execution :=
    fun execution => titleExclusiveFrameDisjoint_of_parts hwf hsameT hcrossT
      execution
  have hdesc :=
    captionDescendantSamePartClear_of_fallback hwf hfp htitle hfallback
  exact Elegant.Layered.sceneCaptionBoxContainment_of_residuals hwf hdesc
    hinputs hsameFull hframes htitle
end Elegant.Layered.PipelineImpl
