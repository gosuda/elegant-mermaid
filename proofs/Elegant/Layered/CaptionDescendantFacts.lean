import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.CaptionOwnerScopeFacts
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.PartSeparation

set_option autoImplicit false

/-! # Caption descendant clearance: the descendant half

`CaptionDescendantClear` (`Layered/CaptionScopeGeometry.lean`) is residual (c)
of the caption seam: an exclusive dump box that is a proper descendant of the
non-exclusive caption owner misses the interior of the owner's caption rect.
The owner key and a descendant key live in one executed component: the
descendant relation is the model parent chain, and parent and child
declarations of one component are placed by the same `componentRun`.  The
remaining geometric obligation is therefore the part-local caption-band /
descendant-member separation, transported through `Pack.pack` shelf origins,
the margin shift, and the direction projection.

`CaptionDescendantSamePartClear` states exactly that obligation: under the
same label/scope hypotheses as the residual, for every executed-part witness
tuple locating the owner key `ownerIndex` and the member key `bi`, the scene
caption rect of the owner misses the interior of `b`.  This mirrors
`OwnerScopeSamePartClear` (`Layered/CaptionOwnerScopeFacts.lean`); unlike that
residual there is no cross-part case, because a proper descendant of the owner
cannot be packed into a different shelf. -/

namespace Elegant.Layered

/-- A `findIdx?` hit exposes the box at that index and its predicate value
(local copy of the private `CaptionOwnerScopeFacts` helper). -/
private theorem captionDescendant_findIdx_lookup {α : Type} {p : α → Bool}
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

/-- The part-local clearance the descendant clause still owes: for every
executed-part witness tuple locating the non-exclusive owner key `ownerIndex`
and the exclusive descendant key `bi`, the transported caption rect of the
owner misses the interior of the member's scene box.  Discharge route: the
caption band reservation of `componentRun` (`component_group_caption_rank_fit`,
`componentRun_group_reservation`) puts the caption above every proper
descendant frame in packed coordinates; `Pack.pack` shelf transport, the
margin shift, and `orientRect` preserve the separation. -/
def CaptionDescendantSamePartClear (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (index ownerIndex bi : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (captionLabel inp o res execution ownerIndex source lines) →
    source.owner ∈ res.scene.layoutDump.ancestors b.id →
    ∀ (kO kB posO posB : Nat) (partO partB : List Nat × PipelineImpl.Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[kO]? = some partO →
      execution.componentsAcc.parts[kB]? = some partB →
      partO.1[posO]? = some ownerIndex →
      partB.1[posB]? = some bi →
      ¬ (PipelineImpl.sceneCaptionRect execution.params inp o execution.lines
          execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- Residual (c) of the caption seam: `CaptionDescendantClear` holds once the
same-part descendant clearance is available.  Every proper descendant of the
owner is packed into the owner's executed part, so the two
`ownerScope_part_position` lookups instantiate the premise directly; there is
no cross-part branch. -/
theorem captionDescendantClear_of_same_part {inp : Input} {o : Options}
    {res : FamilyResult} (hsame : CaptionDescendantSamePartClear inp o res) :
    CaptionDescendantClear inp o res := by
  intro execution index ownerIndex source lines b hsrc hmeas hfindIdx hmem hex
    hscope hd
  have hmem0 : b ∈ res.scene.layoutDump.boxes := hmem
  simp only [Scene.layoutDump, List.mem_iff_getElem?] at hmem
  obtain ⟨bi, hbi⟩ := hmem
  obtain ⟨sb, hsb, _hbid, _hsbpar, _hsbex, _hbrect⟩ :=
    PipelineImpl.sceneBox_source_rect execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨hOILen, _obox, _hobox, _hpobox⟩ :=
    captionDescendant_findIdx_lookup hfindIdx
  obtain ⟨partO, posO, kO, hkO, hposO⟩ :=
    ownerScope_part_position execution hOILen
  obtain ⟨partB, posB, kB, hkB, hposB⟩ :=
    ownerScope_part_position execution hbiLen
  exact hsame execution index ownerIndex bi source lines b hsrc hmeas hfindIdx
    hmem0 hex hscope hd kO kB posO posB partO partB hbi hkO hkB hposO hposB

#print axioms Elegant.Layered.captionDescendantClear_of_same_part

end Elegant.Layered
