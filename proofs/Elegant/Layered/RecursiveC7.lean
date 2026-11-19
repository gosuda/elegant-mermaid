import Elegant.Layered.RecursiveC6
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.LabelsC7

set_option autoImplicit false

/-!
# C7 through `layoutRecursive`: labels miss exclusive boxes outside their scope

`layoutRecursive_c7_of_flat` lifts clause 7 of the layout validator (a label
does not overlap an exclusive box outside its owner scope) through the
recursive layout dispatcher.  The proof recurses on the fuel: a
non-recursive leaf applies the flat clause, and an expanded child merges the
recursive child and parent scenes through `expandChild`, whose C7 case is
proved here from per-expansion facts.

Well-formedness and framed parents are carried through the recursion by
`SubInputsWellFormed`, so the flat clause applies at every `layout` leaf
the recursion performs.
-/

namespace Elegant.Layered.PipelineImpl

open Validator

/-! ### Shift transports -/


theorem shift_preserves_not_meets {a b : Rect} (dx dy : Int) (h : ¬ a.meetsInterior b) :
    ¬ (shiftRect dx dy a).meetsInterior (shiftRect dx dy b) := by
  intro hc
  refine h ?_
  simp only [shiftRect, Rect.meetsInterior] at hc ⊢
  omega


/-! ### Flat clause seams -/

/-! The route-label seams (`routeLabelRect`, `RunLocalLabelClearance`,
`RouteLabelDumpBridges`, `LabelRunsClearExclusiveBoxes`) and the caption
seam (`SceneCaptionBoxContainment`) are the shared constants of
`Elegant.Layered.LabelsC7`; they are not restated here, so the recursive
lift and `Elegant.Layered.layout_c7` speak the same seam constants.
`PartsSeparated` is LabelsC7's packing-separation premise for the
route-label bridge's other-part case. -/

/-! ### Flat clause -/

/-- The flat clause of the brief: a single non-recursive layout keeps every
label clear of exclusive boxes outside the label's owner scope.  Assumed
here, discharged at the family seam; the well-formedness, framed-parent,
packing-separation, and the two label-clearance seams are the ones the flat
clause proof consumes.  The seam constants are `Elegant.Layered.LabelsC7`'s,
so `Elegant.Layered.layout_c7` feeds this clause directly. -/
abbrev FlatC7 : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    PartsSeparated inp o res →
    LabelRunsClearExclusiveBoxes inp o res →
    SceneCaptionBoxContainment inp o res →
    layout inp o = .ok res → Validator.C7 res.scene.layoutDump

/-! ### Merge classification -/

/-- The caption rect `expandChild` installs for labels owned by the split
group. -/
def groupTitleRect (group : ModelBox) (P : Params) (titleLines : List Measure.Line)
    (titleHeight : Int) (frame : Box) : Rect :=
  childTitleRect group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0) titleHeight frame.rect

private theorem embed_excl (g : String) (dx dy : Int) (b : Box) :
    (embedBox g dx dy b).exclusive = b.exclusive := rfl

private theorem embed_id (g : String) (dx dy : Int) (b : Box) :
    (embedBox g dx dy b).id = b.id := rfl

/-- Every label of a merged scene is the group's own caption at the title
rect, a shifted child-scene label owned by another box, or a verbatim
parent-scene label owned by another box. -/
def ExpandChildLabelClasses (P : Params) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (frame : Box) (dx dy : Int)
    (parent child result : FamilyResult) : Prop :=
  ∀ rl ∈ result.scene.layoutDump.labels,
    rl.owner = group.id ∧
      rl.rect = groupTitleRect group P titleLines titleHeight frame ∨
    (∃ cl ∈ child.scene.labels, rl.owner ≠ group.id ∧ rl.id = cl.id ∧
        rl.owner = cl.owner ∧ rl.rect = shiftRect dx dy cl.rect) ∨
    (∃ pl ∈ parent.scene.labels, rl.owner ≠ group.id ∧ rl.id = pl.id ∧
        rl.owner = pl.owner ∧ rl.rect = pl.rect)

/-! ### C7: labels miss exclusive boxes outside their owner scope -/

/-- The per-expansion facts the C7 merge needs: box lookup transport for
both merged scenes, scene sizes, the label classification, owner-scope
transport for child and parent labels, the scope anchors
`{group.id} ++ ancestors group.id` of the expanded group inside the merged
dump, and the four cross-scene clearance facts. -/
def ExpandChildC7Step (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
        result.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
    (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
        result.scene.layoutDump.box? b.id = some b) ∧
    child.scene.boxes.length ≤ result.scene.boxes.length ∧
    parent.scene.boxes.length ≤ result.scene.boxes.length ∧
    ExpandChildLabelClasses P group titleLines titleHeight frame dx dy parent child result ∧
    (∀ cl ∈ child.scene.labels, ∀ rl ∈ result.scene.layoutDump.labels, rl.id = cl.id →
        ∀ x ∈ child.scene.layoutDump.labelOwnerAnc cl.toLabel,
          x ∈ result.scene.layoutDump.labelOwnerAnc rl) ∧
    (∀ pl ∈ parent.scene.labels, ∀ rl ∈ result.scene.layoutDump.labels, rl.id = pl.id →
        ∀ x ∈ parent.scene.layoutDump.labelOwnerAnc pl.toLabel,
          x ∈ result.scene.layoutDump.labelOwnerAnc rl) ∧
    (∀ rl ∈ result.scene.layoutDump.labels,
        ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
          x ∈ result.scene.layoutDump.labelOwnerAnc rl) ∧
    (∀ cl ∈ child.scene.labels, cl.owner ≠ group.id →
        ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
          pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
          ¬ (shiftRect dx dy cl.rect).meetsInterior pb.rect) ∧
    (∀ cb ∈ child.scene.boxes, cb.exclusive = true →
        ∀ rl ∈ result.scene.layoutDump.labels, rl.owner = group.id →
          ¬ rl.rect.meetsInterior (shiftRect dx dy cb.rect)) ∧
    (∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
        ∀ cb ∈ child.scene.boxes, cb.exclusive = true →
          ¬ pl.rect.meetsInterior (shiftRect dx dy cb.rect)) ∧
    (∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
        ∀ rl ∈ result.scene.layoutDump.labels, rl.owner = group.id →
          ¬ rl.rect.meetsInterior pb.rect)

/-- `expandChild` preserves C7.  A merged label is the group caption at the
title rect, a shifted child label, or a parent-scene label, and a merged
box is an embedded child box or a parent-scene box:

* child label vs child box: the child clause transports through the common
  shift, because the child owner scope is included in the merged scope;
* child label vs parent box: the group and its ancestors are scope anchors
  of every merged label, so a box outside them lies in a foreign frame and
  is missed by `hforeignLabel`;
* parent label vs parent box: the parent clause transports, because parent
  owner scopes are included in the merged scopes;
* parent label vs child box and caption vs any box: the dedicated
  cross-scene clearance facts. -/
theorem expandChild_c7 {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child result : FamilyResult}
    (hchildC7 : Validator.C7 child.scene.layoutDump)
    (hparentC7 : Validator.C7 parent.scene.layoutDump)
    (hstep : ExpandChildC7Step P inp o group titleHeight parent child result)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    Validator.C7 result.scene.layoutDump := by
  obtain ⟨frame, metric, titleLines, _lines, dx, dy, hframe, hmetric, htitle,
    _hlines, hdx, hdy, _hcanvas, hboxes⟩ := expandChild_sources h
  obtain ⟨hchildLk, hparentLk, hlenC, hlenP, hclassify, hscopeChild, hscopeParent,
      hanchor, hforeignLabel, hmissChildTitle, hmissParentLabel, hforeignTitle⟩ :=
    hstep frame titleLines dx dy hframe hdx hdy ⟨metric, hmetric, htitle⟩
  have hchildMono := ancestors_mono (child.scene.layoutDump) (result.scene.layoutDump)
    (embedBox group.id dx dy)
    (fun y yb hyb => by
      have hyid : yb.id = y := by simpa using List.find?_some hyb
      rw [← hyid] at hyb ⊢
      exact hchildLk yb hyb)
    (fun yb hne => by
      have hfalse : (yb.parent == "") = false := by
        cases hE : (yb.parent == "") with
        | true => exact absurd (beq_iff_eq.mp hE) hne
        | false => rfl
      simp [embedBox, hfalse])
    hlenC
  have hparentMono := ancestors_mono (parent.scene.layoutDump) (result.scene.layoutDump)
    id
    (fun y yb hyb => by
      have hyid : yb.id = y := by simpa using List.find?_some hyb
      rw [← hyid] at hyb ⊢
      exact hparentLk yb hyb)
    (fun _ _ => rfl)
    hlenP
  intro rl hrl b hb hex hscope
  obtain ⟨sl, hsl, hrlEq⟩ :=
    List.mem_map.mp (by simpa [Scene.layoutDump] using hrl :
      rl ∈ result.scene.labels.map (·.toLabel))
  subst rl
  have hbMem : b ∈ result.scene.layoutDump.boxes := hb
  change b ∈ result.scene.boxes at hbMem
  rw [hboxes] at hbMem
  obtain ⟨_, -, hbfind⟩ := List.mem_filterMap.mp hbMem
  have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hbfind
  have hrlDump : sl.toLabel ∈ result.scene.layoutDump.labels :=
    List.mem_map.mpr ⟨sl, hsl, rfl⟩
  rcases hclassify sl.toLabel hrlDump with ⟨hown, hrect⟩ |
    ⟨cl, hcl, hone, hid, hown, hrect⟩ | ⟨pl, hpl, hone, hid, hown, hrect⟩
  · -- the group's own caption at the title rect
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨cb, hcb, hbEq⟩ := List.mem_map.mp hbc
      have hex' : cb.exclusive = true := by
        rw [← hbEq] at hex
        exact (embed_excl group.id dx dy cb).symm.trans hex
      have hbrect : b.rect = shiftRect dx dy cb.rect := by
        rw [← hbEq]; rfl
      rw [hbrect]
      exact hmissChildTitle cb hcb hex' sl.toLabel hrlDump hown
    · -- parent-scene box: foreign to the group by the scope antecedent
      have hin : b.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id := by
        intro hmem
        exact hscope (hanchor sl.toLabel hrlDump b.id hmem)
      exact hforeignTitle b hbp hex hin sl.toLabel hrlDump hown
  · -- embedded child label
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨cb, hcb, hbEq⟩ := List.mem_map.mp hbc
      have hex' : cb.exclusive = true := by
        rw [← hbEq] at hex
        exact (embed_excl group.id dx dy cb).symm.trans hex
      have hbid : b.id = cb.id := by rw [← hbEq]; rfl
      have hbrect : b.rect = shiftRect dx dy cb.rect := by
        rw [← hbEq]; rfl
      have hcbScope : cb.id ∉ child.scene.layoutDump.labelOwnerAnc cl.toLabel := by
        intro hmem
        apply hscope
        rw [hbid]
        exact hscopeChild cl hcl sl.toLabel hrlDump hid cb.id hmem
      rw [hrect, hbrect]
      exact shift_preserves_not_meets dx dy
        (hchildC7 cl.toLabel (List.mem_map.mpr ⟨cl, hcl, rfl⟩) cb hcb hex' hcbScope)
    · -- parent-scene box: foreign to the group by the scope antecedent
      have hin : b.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id := by
        intro hmem
        exact hscope (hanchor sl.toLabel hrlDump b.id hmem)
      rw [hrect]
      exact hforeignLabel cl hcl (fun h => hone (hown.trans h)) b hbp hex hin
  · -- parent-scene label
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨cb, hcb, hbEq⟩ := List.mem_map.mp hbc
      have hex' : cb.exclusive = true := by
        rw [← hbEq] at hex
        exact (embed_excl group.id dx dy cb).symm.trans hex
      have hbrect : b.rect = shiftRect dx dy cb.rect := by
        rw [← hbEq]; rfl
      rw [hrect, hbrect]
      exact hmissParentLabel pl hpl (fun h => hone (hown.trans h)) cb hcb hex'
    · -- parent-scene box: the parent clause transports
      have hpbScope : b.id ∉ parent.scene.layoutDump.labelOwnerAnc pl.toLabel := by
        intro hmem
        refine hscope ?_
        exact hscopeParent pl hpl sl.toLabel hrlDump hid b.id hmem
      rw [hrect]
      exact hparentC7 pl.toLabel (List.mem_map.mpr ⟨pl, hpl, rfl⟩) b hbp hex hpbScope

/-! ### The lift through `layoutRecursive` -/

/-- `layoutRecursive` preserves C7 given the flat clause for leaf layouts,
the two `LabelsC7` seams as global facts about flat results, the sub-input
well-formedness seam, and, for every expansion the recursion performs, the
per-expansion facts of `ExpandChildC7Step`.  Well-formedness and framed
parents are carried through the recursion by `SubInputWellFormed`, so the
flat clause applies at every `layout` leaf the recursion performs. -/
theorem layoutRecursive_c7_of_flat (hflat7 : FlatC7)
    (hsep : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      PartsSeparated inp o res)
    (hseam1 : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LabelRunsClearExclusiveBoxes inp o res)
    (hseam2 : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      SceneCaptionBoxContainment inp o res)
    (hsub : SubInputWellFormed)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildC7Step P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursive fuel inp o = .ok res → Validator.C7 res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hwf hframed h
      exact hflat7 inp o res hwf hframed (hsep inp o res) (hseam1 inp o res hwf hframed)
        (hseam2 inp o res hwf hframed) h
  | succ fuel ih =>
      intro inp o res hwf hframed h
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := inputRoutesCovered hwf
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
      · exact hflat7 inp o res hwf hframed (hsep inp o res) (hseam1 inp o res hwf hframed)
          (hseam2 inp o res hwf hframed) hlayout
      · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
          hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
        obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
          hsub fuel inp o group P metric titleLines child parent hwf hframed hP hm hwrap
            hchild hparentAt
        have hchildC7 := ih _ _ _ hwfChild hframedChild hchild
        have hparentC7 := ih _ _ _ hwfParent hframedParent hparentAt
        have hstep := hgeo fuel P inp o group titleLines _ parent child res hexpandAt hframed
          ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
        exact expandChild_c7 hchildC7 hparentC7 hstep hexpandAt

end Elegant.Layered.PipelineImpl
