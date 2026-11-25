import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.CaptionResidualsProof
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.LabelsC8b
import Elegant.Layered.Compound

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem fallback_findIdx_lookup {α : Type} {p : α → Bool}
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

private theorem fallback_ancestors_parent (d : LayoutDump) :
    ∀ (fuel : Nat) (s x : String), x ∈ LayoutDump.ancestors.go d fuel s →
      ∃ c ∈ d.boxes, c.parent = x ∧ x ≠ "" := by
  intro fuel
  induction fuel with
  | zero => intro s x hx; cases hx
  | succ fuel ih =>
    intro s x hx
    have hgo : LayoutDump.ancestors.go d (fuel + 1) s =
        match d.box? s with
        | none => []
        | some b => if b.parent = "" then []
                    else b.parent :: LayoutDump.ancestors.go d fuel b.parent := rfl
    rw [hgo] at hx
    cases hs : d.box? s with
    | none => rw [hs] at hx; cases hx
    | some b =>
      rw [hs] at hx
      simp only at hx
      split at hx
      · cases hx
      · rename_i hpar
        rcases List.mem_cons.mp hx with heq | hx
        · refine ⟨b, ?_, heq.symm, ?_⟩
          · unfold LayoutDump.box? at hs
            exact List.mem_of_find?_eq_some hs
          · rw [heq]
            exact hpar
        · obtain ⟨c, hcMem, hcParent, hxNe⟩ := ih b.parent x hx
          exact ⟨c, hcMem, hcParent, hxNe⟩

theorem SceneExecution.fallback_owner_cases
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {k : Nat} {obox : ModelBox} (hbox : inp.boxes[k]? = some obox)
    (hnone : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none) :
    obox.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true := by
  by_cases hfix : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true
  · exact Or.inr hfix
  · have hfixFalse : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false :=
      Bool.eq_false_iff.mpr hfix
    by_cases hrole : obox.role = .group
    · exfalso
      obtain ⟨nodes, edges, titles, hprepared, hlength, _⟩ :=
        measuredGraph_prepared_source execution.graph_eq
      have hlines : execution.lines.length = inp.boxes.length := by
        have h := execution.lines_eq
        simp only [boxLines] at h
        calc execution.lines.length = (inp.boxes.zipIdx).length :=
            (mapM_getElem? _ _ _ h).1
          _ = inp.boxes.length := List.length_zipIdx
      have hi : k < nodes.length := by
        rw [hlength, hlines]
        exact (List.getElem?_eq_some_iff.mp hbox).1
      have hpreparedSource :
          (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node } else box)[k]? = some obox := by
        simp [List.getElem?_map, hbox, hfixFalse]
      have hrecord := Compound.prepare_group_title_record
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)
        execution.params.clusterPad titles
        { nodes := nodes, edges := edges, slot := execution.params.slot }
        hi hpreparedSource hrole
      rw [← hprepared] at hrecord
      obtain ⟨_, caption, _, hsel, _⟩ :=
        execution.scene_caption_selector_containment hwf hbox hrecord rfl
      have hpredTrue := List.find?_some hsel
      have hmemThm := List.mem_of_find?_eq_some hsel
      obtain ⟨stored, hstoredMem, hfeq⟩ := List.mem_filterMap.mp hmemThm
      have hPoint : ∀ stored : Nat × Rect,
          ((do
            let owner ← inp.boxes[stored.1]?
            let textLines := execution.lines.getD stored.1 []
            let width := textLines.foldl (fun value line => max value line.width) 0
            let height := (max 1 textLines.length : Int) * execution.params.lineH
            let size := match o.direction with
              | .LR | .RL => Size.mk height width
              | .TB | .BT => Size.mk width height
            pure (owner.id, shiftRect execution.params.canvasMargin
              execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH
                { stored.2 with w := size.w, h := size.h }))) : Option (String × Rect))
          = ((do
            let owner ← inp.boxes[stored.1]?
            let size := titleCaptionSize execution.params o (execution.lines.getD stored.1 [])
            pure (owner.id, shiftRect execution.params.canvasMargin
              execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH
                { stored.2 with w := size.w, h := size.h }))) : Option (String × Rect)) := by
        intro stored
        cases hbx : inp.boxes[stored.1]? with
        | none => rfl
        | some _ => rfl
      have hfeqScene : ((do
            let owner ← inp.boxes[stored.1]?
            let size := titleCaptionSize execution.params o (execution.lines.getD stored.1 [])
            pure (owner.id, shiftRect execution.params.canvasMargin
              execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH
                { stored.2 with w := size.w, h := size.h }))) : Option (String × Rect))
          = some caption := by
        rw [← hPoint stored]
        exact hfeq
      have hmemScene : caption ∈ sceneTitlesExpr execution.params inp o execution.lines
          execution.packedAcc := by
        unfold sceneTitlesExpr
        exact List.mem_filterMap.mpr ⟨stored, hstoredMem, hfeqScene⟩
      have hpredFalse := List.find?_eq_none.mp hnone _ hmemScene
      exact absurd hpredTrue hpredFalse
    · have hroleNode : obox.role = .node := by
        cases h : obox.role with
        | node => rfl
        | group => exact absurd h hrole
      exact Or.inl hroleNode

theorem descendantFallbackClear_vacuous {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) :
    DescendantFallbackClear inp o res := by
  intro _ _ execution _index ownerIndex _bi source _lines b _hsrc _hmeas hfindIdx _hmem _hex _hscope hd hnone _kO _kB _posO _posB _partO _partB _hbi _hkO _hkB _hposO _hposB
  exfalso
  obtain ⟨_, obox, hobox, hpobox⟩ := fallback_findIdx_lookup hfindIdx
  have hpred : (obox.id == source.owner && !obox.exclusive) = true := hpobox
  simp only [Bool.and_eq_true] at hpred
  have hoboxId : obox.id = source.owner := beq_iff_eq.mp hpred.1
  have hnone' : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
    rw [hoboxId]
    exact hnone
  have hfall := execution.fallback_owner_cases hwf hobox hnone'
  have hmemAnc : source.owner ∈
      LayoutDump.ancestors.go res.scene.layoutDump
        res.scene.layoutDump.boxes.length b.id := hd
  obtain ⟨c, hcMem, hcParent, hxNe⟩ :=
    fallback_ancestors_parent res.scene.layoutDump
      res.scene.layoutDump.boxes.length b.id source.owner hmemAnc
  have hcScene : c ∈ res.scene.boxes := by
    simpa [Scene.layoutDump] using hcMem
  obtain ⟨jc, hjc⟩ := List.mem_iff_getElem?.mp hcScene
  obtain ⟨child, hchildGet, _, hparentEq, _, _⟩ :=
    sceneBox_source_rect execution hjc
  have hchildMem : child ∈ inp.boxes := List.mem_of_getElem? hchildGet
  have hchildParent : child.parent = source.owner := hparentEq.symm.trans hcParent
  have hchildNe : child.parent ≠ "" := by
    rw [hchildParent]
    exact hxNe
  obtain ⟨parentBox, hparentMem, hparentId, hparentRole, hparentFixed⟩ :=
    framedParents_parent hfp hchildMem hchildNe
  have hids := Model.boxIds_nodup hwf
  have ha : (inp.boxes.map (·.id))[ownerIndex]? = some obox.id := by
    simp [List.getElem?_map, hobox]
  obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hparentMem
  have hb : (inp.boxes.map (·.id))[pi]? = some parentBox.id := by
    simp [List.getElem?_map, hpi]
  have heq : obox.id = parentBox.id := hoboxId.trans (hparentId.trans hchildParent).symm
  have hlookups : (inp.boxes.map (·.id))[ownerIndex]? =
      (inp.boxes.map (·.id))[pi]? := by
    rw [ha, hb, heq]
  have hbound : ownerIndex < (inp.boxes.map (·.id)).length :=
    (List.getElem?_eq_some_iff.mp ha).1
  have hidxEq : ownerIndex = pi := (List.Nodup.getElem?_inj hbound hids).mp hlookups
  have hboxEq : obox = parentBox := by
    have hsame : inp.boxes[ownerIndex]? = inp.boxes[pi]? := by rw [hidxEq]
    rw [hobox, hpi] at hsame
    exact Option.some.inj hsame
  have hroleGroup : obox.role = .group := by
    rw [hboxEq]
    exact hparentRole
  have hfixFalse : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false := by
    rw [hboxEq]
    exact hparentFixed
  rcases hfall with hnode | hfixedTrue
  · rw [hroleGroup] at hnode
    contradiction
  · rw [hfixFalse] at hfixedTrue
    contradiction

end Elegant.Layered.PipelineImpl
