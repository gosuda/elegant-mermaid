import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.LabelsC8bFacts

set_option autoImplicit false

/-! # The installed-title branch of the caption scope clearance

`CaptionTitleBranchClear` (`Layered/CaptionScopeGeometry.lean`) is the branch
of `CaptionScopeClearance` in which the packed accumulator carries an
installed title for the caption owner, so `sceneCaptionRect` is the
transported stored title rect.  This file discharges it.

`LabelFramePackedClear` (`Layered/LabelsC8bFacts.lean`) states the caption
clearance against group frames as a disjunction `Disjoint ∨ caption-inside`
(the C8b shape).  Its containment branch cannot yield the C7-style
conclusion "the caption misses the interior of a foreign exclusive box",
because a caption lying strictly inside a foreign box frame would satisfy
`meetsInterior`.  The title branch therefore needs the executed clearance in
disjoint form against the packed rect of every *exclusive* model box, which
is exactly what the caption band reservation (the owner is non-exclusive, so
the owner itself is not an exclusive box) and the foreign-frame facts give
for every exclusive box.  That single fact is `TitleExclusiveFrameDisjoint`;
it is a named executed-clearance fact in the `LabelsC8bFacts` conjunct
family, stated over the actual `packedAcc.titles` and `packedAcc.rects`
arrays.

With it, the proof is pure plumbing: the `find?` premise of the branch
rewrites `sceneCaptionRect` to the transported stored title (the same
`titleCaptionSize` substitution `sceneOf` performs), the scene-box membership
rewrites `b.rect` to the transported packed rect of the model box at the
same index (whose `exclusive` flag is the premise's `b.exclusive`), and
`not_meetsInterior_sceneTransport` moves the packed disjointness through the
common margin/orientation projection. -/

namespace Elegant.Layered

namespace PipelineImpl

/-- The executed disjoint-form caption clearance the installed-title branch
consumes: a packed title caption (the stored rect resized by
`titleCaptionSize`, exactly the term `sceneOf` substitutes) is disjoint from
the packed rect of every exclusive model box.  The owner of an installed
title is a non-exclusive box, so this says precisely that the caption misses
the frame of every exclusive box — the caption-band reservation inside its
own component and shelf disjointness across components. -/
def TitleExclusiveFrameDisjoint {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : Prop :=
  ∀ (key : Nat) (stored : Rect), (key, stored) ∈ execution.packedAcc.titles →
    ∀ (k : Nat) (fBox : ModelBox), inp.boxes[k]? = some fBox →
      fBox.exclusive = true →
      Disjoint (execution.packedAcc.rects.getD k default)
        { stored with
          w := (titleCaptionSize execution.params o
            (execution.lines.getD key [])).w
          h := (titleCaptionSize execution.params o
            (execution.lines.getD key [])).h }

/-- The installed-title branch of the caption scope clearance, from the
executed C8b seam bundle (`LayeredSeams.frameLabels` shape) and the
disjoint-form exclusive-frame clearance. -/
theorem captionTitleBranchClear_of_frames {inp : Input} {o : Options}
    {res : FamilyResult}
    (hframes : ∀ (execution : SceneExecution inp o res),
      LabelFramePackedClear execution.params inp o execution.lines
        execution.packedAcc ∧ FallbackCaptionClear execution)
    (hnode : ∀ (execution : SceneExecution inp o res),
      TitleExclusiveFrameDisjoint execution) :
    CaptionTitleBranchClear inp o res := by
  intro execution index ownerIndex source lines b _hsrc _hmeas _hfindIdx hmem hex
    _hscope htitle
  obtain ⟨_, _⟩ := hframes execution
  cases hfind : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == source.owner) with
  | none =>
    rw [hfind] at htitle
    simp at htitle
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
      simp only [PipelineImpl.sceneCaptionRect]
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
      have hd := hnode execution stored.1 stored.2 hstoredMem hKey fBox
        hKeyBox hex'
      exact disjoint_sceneTransport (fun hm => hd (rect_meetsInterior_comm hm))

end PipelineImpl

end Elegant.Layered
