import Elegant.Layered.CaptionsSeamFacts
import Elegant.Layered.CaptionDescendantFacts
import Elegant.Layered.CaptionOwnerScopeFacts
import Elegant.Layered.CaptionTitleBranchFacts
import Elegant.Layered.CaptionDescendantCore
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.GroupFrameSizingFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

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

/-- A node-or-fixed owner box of a successful execution is a border-0 measured
node: a node-role box is border-0 with or without a fixed entry, and a fixed
group is laid out as a plain node with border 0. -/
theorem ownerRes_node_border_zero {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {key : Nat} {box : ModelBox} (hbox : inp.boxes[key]? = some box)
    (hrole : box.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true)
    (hlen : key < execution.lines.length) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0 := by
  have hline : execution.lines[key]? = some execution.lines[key] :=
    List.getElem?_eq_some_iff.mpr ⟨hlen, rfl⟩
  rcases hrole with hnode | hfixedTrue
  · cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
    | none =>
      have hfalse : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        List.any_eq_false.mpr (List.find?_eq_none.mp hf)
      obtain ⟨node, hnode, _, hborder⟩ :=
        measuredGraph_node_border_zero execution.checked execution.graph_eq
          hline hbox hnode hfalse
      exact ⟨node, hnode, hborder⟩
    | some entry =>
      obtain ⟨_, _, node, _, _, hnode, hborder, _⟩ :=
        measuredGraph_fixed_loop_reservation execution.graph_eq
          (List.getElem?_eq_some_iff.mp hline).1 hbox hf
      exact ⟨node, hnode, hborder⟩
  · cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
    | none =>
      obtain ⟨e, hmem, hid⟩ := List.any_eq_true.mp hfixedTrue
      exact absurd (List.find?_eq_none.mp hf e hmem) (by rw [hid]; decide)
    | some entry =>
      obtain ⟨_, _, node, _, _, hnode, hborder, _⟩ :=
        measuredGraph_fixed_loop_reservation execution.graph_eq
          (List.getElem?_eq_some_iff.mp hline).1 hbox hf
      exact ⟨node, hnode, hborder⟩

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


end Elegant.Layered.PipelineImpl
