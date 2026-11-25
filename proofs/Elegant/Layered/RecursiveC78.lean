import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.InputFixedFit
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.SceneBounds

set_option autoImplicit false

/-!
# C8a, C8b through `layoutRecursive`

`layoutRecursive_c8a_of_flat` and `layoutRecursive_c8b_of_flat` lift the two
frame clearance clauses through the recursive subdivision. The leaf case is
the flat clause (`FlatC8a` / `FlatC8b`), conditioned on the well-formedness
and framed-parent premises the flat proofs consume. Well-formedness of the
sub-inputs travels through the recursion by the named seam
`SubInputsWellFormed`, so the flat clause applies at every `layout` leaf.

Every `expandChild` merge dispatches boxes into embedded child images
(shifted by `(dx, dy)`, child roots reparented to the group) and verbatim
parent-scene boxes, and labels into embedded child images, verbatim
parent-scene labels, and the group's own caption at the title rect. The
per-expansion facts this needs are packaged in `ExpandChildC8aStep` and
`ExpandChildC8bStep` and discharged at the family seam; the merge-local
reasoning (dispatch, ancestor transport, shift transports) is proved here.
-/

namespace Elegant.Layered.PipelineImpl

open Validator

/-! ### Shift transports -/

theorem shift_preserves_disjoint {a b : Rect} (dx dy : Int) (h : Disjoint a b) :
    Disjoint (shiftRect dx dy a) (shiftRect dx dy b) := by
  unfold Disjoint at h ⊢
  intro hc
  refine h ?_
  simp only [shiftRect, Rect.meetsInterior] at hc ⊢
  omega

theorem shift_preserves_strictInside {g l : Rect} (dx dy : Int) (h : g.StrictInside l) :
    (shiftRect dx dy g).StrictInside (shiftRect dx dy l) := by
  simp only [shiftRect, Rect.StrictInside] at h ⊢
  omega

/-- A rectangle contained in an `outer` one stays disjoint from everything
the outer one misses: `outer.Contained inner` reads "outer contains inner".
The contained inner's open interior is a subset of the outer's, so any
interior meeting with `other` would already meet `outer`. -/
theorem disjoint_contained_left {inner outer other : Rect}
    (hic : outer.Contained inner) (hd : Disjoint outer other) : Disjoint inner other := by
  unfold Disjoint Rect.meetsInterior Rect.Contained at *
  intro hc
  apply hd
  rcases hc with ⟨hx1, hy1⟩
  obtain ⟨hox, hoxr, hoy, hoyr⟩ := hic
  constructor <;> omega


/-! ### Ancestor monotonicity under a lookup transport -/


/-- The id of a located dump box is the lookup key. -/
theorem boxLookupIdC8 {d : LayoutDump} {y : String} {yb : Box}
    (hyb : d.box? y = some yb) : yb.id = y :=
  beq_iff_eq.mp (List.find?_some (p := fun (b : Box) => b.id == y) hyb)

/-- Ancestor walks are monotone under a lookup transport: if every box of
the source dump resolves in the target dump to an image that keeps the
parent pointer whenever it is nonempty, then every id on a source ancestor
chain also lies on the corresponding target ancestor chain (the target has
at least as much fuel). -/
theorem ancestors_sub (childD finD : LayoutDump) (E : Box → Box)
    (hres : ∀ (y : String) (yb : Box), childD.box? y = some yb →
      finD.box? y = some (E yb))
    (hpar : ∀ (yb : Box), yb.parent ≠ "" → (E yb).parent = yb.parent)
    (hlen : childD.boxes.length ≤ finD.boxes.length) :
    ∀ (x : String), childD.ancestors x ⊆ finD.ancestors x := by
  have key : ∀ (n m : Nat) (x : String), n ≤ m →
      List.Subset (LayoutDump.ancestors.go childD n x)
        (LayoutDump.ancestors.go finD m x) := by
    intro n
    induction n with
    | zero =>
        intro _ _ _ y hy
        simp [LayoutDump.ancestors.go] at hy
    | succ n ih =>
        intro m x hnm y hy
        cases hm : m with
        | zero => exact absurd hnm (by omega)
        | succ m' =>
          cases hpx : childD.box? x with
          | none => simp [LayoutDump.ancestors.go, hpx] at hy
          | some yb =>
            by_cases hpb : yb.parent = ""
            · simp [LayoutDump.ancestors.go, hpx, hpb] at hy
            · have hEp : (E yb).parent = yb.parent := hpar yb hpb
              simp [LayoutDump.ancestors.go, hpx, hres x yb hpx, hEp, hpb] at hy ⊢
              rcases hy with hyy | hy'
              · exact Or.inl hyy
              · exact Or.inr (ih m' yb.parent (by omega) hy')
  intro x
  show List.Subset (LayoutDump.ancestors.go childD childD.boxes.length x)
    (LayoutDump.ancestors.go finD finD.boxes.length x)
  exact key childD.boxes.length finD.boxes.length x hlen

/-! ### Sub-input seam -/


/-- The well-formedness seam of the recursive split: whenever the input the
recursion splits at `group` is well-formed and has framed parents, both
sub-inputs the recursion builds are well-formed and have framed parents as
well.  The parent sub-input is stated at the values `layoutRecursive`
actually constructs, so the family seam discharges this from
`selectInput` preservation alone. -/
def SubInputsWellFormed : Prop :=
  ∀ (fuel : Nat) (inp : Input) (o : Options) (group : ModelBox)
    (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line)
    (child parent : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    checkedParams o.profile inp.kind = .ok P →
    metricOf o.profile = .ok metric →
    StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
          .ok titleLines →
    layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child →
    layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent →
    WellFormed (inputModel (childSubInput inp group) (childSubOptions o group)) ∧
    framedParents (childSubInput inp group) = true ∧
    WellFormed (inputModel (parentSubInput inp group P titleLines child) o) ∧
    framedParents (parentSubInput inp group P titleLines child) = true

/-! ### Flat clauses -/


/-- The flat clause for foreign frame clearance: a single non-recursive
layout keeps every group frame disjoint from boxes that are neither its
ancestors nor its descendants. -/
abbrev FlatC8a : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    layout inp o = .ok res → Validator.C8a res.scene.layoutDump

/-- The flat clause for frame/label clearance: a single non-recursive
layout keeps every group frame disjoint from labels or strictly contains
them. -/
abbrev FlatC8b : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o →
    layout inp o = .ok res → Validator.C8b res.scene.layoutDump

/-- The caption rect `expandChild` installs for labels owned by the split
group. -/
def groupTitleRectC8 (group : ModelBox) (P : Params) (titleLines : List Measure.Line)
    (titleHeight : Int) (frame : Box) : Rect :=
  childTitleRect group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0) titleHeight frame.rect

/-- Every label of a merged scene is the group's own caption at the title
rect, a shifted child-scene label owned by another box, or a verbatim
parent-scene label owned by another box. -/
def ExpandChildLabelClassesC8 (P : Params) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (frame : Box) (dx dy : Int)
    (parent child result : FamilyResult) : Prop :=
  ∀ rl ∈ result.scene.layoutDump.labels,
    rl.owner = group.id ∧
      rl.rect = groupTitleRectC8 group P titleLines titleHeight frame ∨
    (∃ cl ∈ child.scene.labels, rl.owner ≠ group.id ∧ rl.id = cl.id ∧
        rl.owner = cl.owner ∧ rl.rect = shiftRect dx dy cl.rect) ∨
    (∃ pl ∈ parent.scene.labels, rl.owner ≠ group.id ∧ rl.id = pl.id ∧
        rl.owner = pl.owner ∧ rl.rect = pl.rect)

/-! ### C8a: group frames are disjoint from foreign boxes -/

/-- The per-expansion facts the C8a merge needs: box lookup transport for
both merged scenes, scene sizes, the frame's group role and isolation from
parent-scene ancestor chains, child boxes inside the frame, and the scope
anchors `{group.id} ++ ancestors group.id` of every embedded box inside the
merged dump. -/
def ExpandChildC8aStep (P : Params) (inp : Input) (o : Options) (group : ModelBox)
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
    frame.role = "group" ∧
    (∀ cb ∈ child.scene.boxes, cb.id ≠ group.id) ∧
    (∀ cb ∈ child.scene.boxes, frame.rect.Contained (shiftRect dx dy cb.rect)) ∧
    (∀ cb ∈ child.scene.boxes,
        ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
          x ∈ result.scene.layoutDump.ancestors cb.id) ∧
    (∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
        group.id ∉ parent.scene.layoutDump.ancestors pb.id)

/-- `expandChild` preserves C8a.  Two merged boxes are each an embedded
child box or a parent-scene box:

* both parent boxes: the parent clause transports, because parent ancestor
  chains resolve unchanged in the merged dump;
* both child boxes: the child clause transports through the common shift,
  because child ancestor chains are included in the merged chains;
* child group vs parent box: the frame's foreign clearance transports,
  because the embedded box lies inside the frame;
* parent group vs child box: the frame and the parent group are mutually
  foreign (frame ids never occur on parent-scene ancestor chains), and the
  embedded box lies inside the frame. -/
theorem expandChild_c8a {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child result : FamilyResult}
    (hchildC8a : Validator.C8a child.scene.layoutDump)
    (hparentC8a : Validator.C8a parent.scene.layoutDump)
    (hstep : ExpandChildC8aStep P inp o group titleHeight parent child result)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    Validator.C8a result.scene.layoutDump := by
  obtain ⟨frame, metric, titleLines, _lines, dx, dy, hframe, hmetric, htitle,
    _hlines, hdx, hdy, _hcanvas, hboxes⟩ := expandChild_sources h
  obtain ⟨hchildLk, hparentLk, hlenC, hlenP, hframeRole, hchildGroupId,
    hchildBoxesInFrame, hanchor, hframeChainIsolated⟩ :=
    hstep frame titleLines dx dy hframe hdx hdy ⟨metric, hmetric, htitle⟩
  have hchildMono := ancestors_sub (child.scene.layoutDump) (result.scene.layoutDump)
    (embedBox group.id dx dy)
    (fun y yb hyb => by
      have key := hchildLk yb (by rw [boxLookupIdC8 hyb]; exact hyb)
      rw [boxLookupIdC8 hyb] at key
      exact key)
    (fun yb hne => by
      have hfalse : (yb.parent == "") = false := by
        cases hE : (yb.parent == "") with
        | true => exact absurd (beq_iff_eq.mp hE) hne
        | false => rfl
      simp [embedBox, hfalse])
    hlenC
  have hparentMono := ancestors_sub (parent.scene.layoutDump) (result.scene.layoutDump)
    id
    (fun y yb hyb => by
      have key := hparentLk yb (by rw [boxLookupIdC8 hyb]; exact hyb)
      rw [boxLookupIdC8 hyb] at key
      exact key)
    (fun _ _ => rfl)
    hlenP
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hframeMem : frame ∈ parent.scene.boxes := List.mem_of_find?_eq_some hframe
  intro g hg hgRole b hb hne hgNotAnc bNotAnc
  change g ∈ result.scene.boxes at hg
  change b ∈ result.scene.boxes at hb
  rw [hboxes] at hg hb
  obtain ⟨_, -, hgfind⟩ := List.mem_filterMap.mp hg
  obtain ⟨_, -, hbfind⟩ := List.mem_filterMap.mp hb
  have hgItems : g ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hgfind
  have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hbfind
  rcases List.mem_append.mp hgItems with hgc | hgp
  · -- g is an embedded child box
    obtain ⟨cg, hcg, hgEq⟩ := List.mem_map.mp hgc
    have hgid : g.id = cg.id := by rw [← hgEq]; rfl
    have hgrect : g.rect = shiftRect dx dy cg.rect := by rw [← hgEq]; rfl
    have hgrole : cg.role = "group" := by rw [← hgEq] at hgRole; simpa [embedBox] using hgRole
    rcases List.mem_append.mp hbItems with hbc | hbp
    · -- both embedded: the child clause transports through the shift
      obtain ⟨cb, hcb, hbEq⟩ := List.mem_map.mp hbc
      have hbid : b.id = cb.id := by rw [← hbEq]; rfl
      have hbrect : b.rect = shiftRect dx dy cb.rect := by rw [← hbEq]; rfl
      have hcbNotAnc : cb.id ∉ child.scene.layoutDump.ancestors cg.id := by
        intro hmem
        refine bNotAnc ?_
        rw [hbid, hgid]
        exact hchildMono cg.id hmem
      have hcgNotAnc : cg.id ∉ child.scene.layoutDump.ancestors cb.id := by
        intro hmem
        refine hgNotAnc ?_
        rw [hbid, hgid]
        exact hchildMono cb.id hmem
      rw [hgrect, hbrect]
      exact shift_preserves_disjoint dx dy
        (hchildC8a cg hcg hgrole cb hcb (by rw [← hbid, ← hgid]; exact hne)
          hcgNotAnc hcbNotAnc)
    · -- child group vs parent box: frame clearance transports
      have hbidNeGroup : b.id ≠ group.id := by
        intro hEq
        apply bNotAnc
        rw [hEq]
        have h2 := hanchor cg hcg group.id (List.mem_cons.mpr (Or.inl rfl))
        rw [← hgid] at h2
        exact h2
      have hbNotAncFrame : b.id ∉ parent.scene.layoutDump.ancestors frame.id := by
        rw [hframeId]
        intro hmem
        refine bNotAnc ?_
        rw [hgid]
        exact hanchor cg hcg b.id (List.mem_cons_of_mem _ hmem)
      have hbidNeFrame : b.id ≠ frame.id := by rw [hframeId]; exact hbidNeGroup
      have hframeNotAncB : frame.id ∉ parent.scene.layoutDump.ancestors b.id := by
        rw [hframeId]
        exact hframeChainIsolated b hbp hbidNeGroup
      rw [hgrect]
      exact disjoint_contained_left (hchildBoxesInFrame cg hcg)
        (hparentC8a frame hframeMem hframeRole b hbp hbidNeFrame hframeNotAncB
          hbNotAncFrame)
  · -- g is a parent-scene box
    rcases List.mem_append.mp hbItems with hbc | hbp
    · -- parent group vs embedded box: frame clearance transports
      obtain ⟨cb, hcb, hbEq⟩ := List.mem_map.mp hbc
      have hbid : b.id = cb.id := by rw [← hbEq]; rfl
      have hbrect : b.rect = shiftRect dx dy cb.rect := by rw [← hbEq]; rfl
      have hbidNeGroup : b.id ≠ group.id := by
        rw [hbid]
        exact hchildGroupId cb hcb
      have hgidNeGroup : g.id ≠ group.id := by
        intro hEq
        apply hgNotAnc
        rw [hEq]
        have h2 := hanchor cb hcb group.id (List.mem_cons.mpr (Or.inl rfl))
        rw [← hbid] at h2
        exact h2
      have hgidNeFrame : g.id ≠ frame.id := by
        rw [hframeId]
        exact hgidNeGroup
      have hgNotAncFrame : g.id ∉ parent.scene.layoutDump.ancestors frame.id := by
        rw [hframeId]
        intro hmem
        refine hgNotAnc ?_
        rw [hbid]
        exact hanchor cb hcb g.id (List.mem_cons_of_mem _ hmem)
      have hbNotAncOfG : frame.id ∉ parent.scene.layoutDump.ancestors g.id := by
        rw [hframeId]
        exact hframeChainIsolated g hgp hgidNeGroup
      rw [hbrect]
      exact (Rect.disjoint_comm _ _).mpr (disjoint_contained_left
        (hchildBoxesInFrame cb hcb)
        ((Rect.disjoint_comm _ _).mp (hparentC8a g hgp hgRole frame hframeMem
          hgidNeFrame.symm hgNotAncFrame hbNotAncOfG)))
    · -- both parent boxes: the parent clause transports
      have hgNotAncPb : g.id ∉ parent.scene.layoutDump.ancestors b.id := by
        intro hmem
        exact hgNotAnc (hparentMono b.id hmem)
      have hbNotAncG : b.id ∉ parent.scene.layoutDump.ancestors g.id := by
        intro hmem
        exact bNotAnc (hparentMono g.id hmem)
      exact hparentC8a g hgp hgRole b hbp hne hgNotAncPb hbNotAncG

/-! ### C8b: group frames are disjoint from labels or strictly contain them -/

/-- The per-expansion facts the C8b merge needs: the label classification
and the four cross-scene clearance facts (parent groups vs child labels,
child groups vs parent labels, child groups vs the caption, and parent
groups vs the caption). -/
def ExpandChildC8bStep (P : Params) (inp : Input) (o : Options) (group : ModelBox)
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
    ExpandChildLabelClassesC8 P group titleLines titleHeight frame dx dy parent child result ∧
    (∀ g ∈ parent.scene.boxes, g.role = "group" → ∀ cl ∈ child.scene.labels,
        Disjoint g.rect (shiftRect dx dy cl.rect) ∨
          g.rect.StrictInside (shiftRect dx dy cl.rect)) ∧
    (∀ cg ∈ child.scene.boxes, cg.role = "group" → ∀ pl ∈ parent.scene.labels,
        pl.owner ≠ group.id →
        Disjoint (shiftRect dx dy cg.rect) pl.rect ∨
          (shiftRect dx dy cg.rect).StrictInside pl.rect) ∧
    (∀ cg ∈ child.scene.boxes, cg.role = "group" →
        Disjoint (shiftRect dx dy cg.rect)
          (groupTitleRectC8 group P titleLines titleHeight frame) ∨
        (shiftRect dx dy cg.rect).StrictInside
          (groupTitleRectC8 group P titleLines titleHeight frame)) ∧
    (∀ g ∈ parent.scene.boxes, g.role = "group" →
        Disjoint g.rect (groupTitleRectC8 group P titleLines titleHeight frame) ∨
        g.rect.StrictInside (groupTitleRectC8 group P titleLines titleHeight frame))

/-- `expandChild` preserves C8b.  A merged group is an embedded child group
or a parent-scene group, and a merged label is the group caption at the
title rect, a shifted child label, or a parent-scene label; same-scene
pairs transport through the clauses of their own scene and cross-scene
pairs are covered by the dedicated clearance facts. -/
theorem expandChild_c8b {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child result : FamilyResult}
    (hchildC8b : Validator.C8b child.scene.layoutDump)
    (hparentC8b : Validator.C8b parent.scene.layoutDump)
    (hstep : ExpandChildC8bStep P inp o group titleHeight parent child result)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    Validator.C8b result.scene.layoutDump := by
  obtain ⟨frame, metric, titleLines, _lines, dx, dy, hframe, hmetric, htitle,
    _hlines, hdx, hdy, _hcanvas, hboxes⟩ := expandChild_sources h
  obtain ⟨hclassify, hparentGroupVsChildLabel, hchildGroupVsParentLabel,
    hchildGroupVsTitle, htitleVsParentGroups⟩ :=
    hstep frame titleLines dx dy hframe hdx hdy ⟨metric, hmetric, htitle⟩
  intro g hg hgRole rl hrl
  change g ∈ result.scene.boxes at hg
  obtain ⟨sl, hsl, hrlEq⟩ :=
    List.mem_map.mp (by simpa [Scene.layoutDump] using hrl :
      rl ∈ result.scene.labels.map (·.toLabel))
  subst rl
  rw [hboxes] at hg
  obtain ⟨_, -, hgfind⟩ := List.mem_filterMap.mp hg
  have hgItems : g ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hgfind
  have hrlDump : sl.toLabel ∈ result.scene.layoutDump.labels :=
    List.mem_map.mpr ⟨sl, hsl, rfl⟩
  rcases hclassify sl.toLabel hrlDump with ⟨_hown, hrect⟩ |
    ⟨cl, hcl, _hone, _hid, _hown2, hrect⟩ | ⟨pl, hpl, hone, _hid, hownEq, hrect⟩
  · -- rl is the group caption at the title rect
    rcases List.mem_append.mp hgItems with hgc | hgp
    · obtain ⟨cg, hcg, hgEq⟩ := List.mem_map.mp hgc
      have hgrole : cg.role = "group" := by
        rw [← hgEq] at hgRole
        simpa [embedBox] using hgRole
      have hgrect : g.rect = shiftRect dx dy cg.rect := by rw [← hgEq]; rfl
      rw [hgrect, hrect]
      exact hchildGroupVsTitle cg hcg hgrole
    · rw [hrect]
      exact htitleVsParentGroups g hgp hgRole
  · -- rl is a shifted child-scene label
    rcases List.mem_append.mp hgItems with hgc | hgp
    · obtain ⟨cg, hcg, hgEq⟩ := List.mem_map.mp hgc
      have hgrole : cg.role = "group" := by
        rw [← hgEq] at hgRole
        simpa [embedBox] using hgRole
      have hgrect : g.rect = shiftRect dx dy cg.rect := by rw [← hgEq]; rfl
      rcases hchildC8b cg hcg hgrole cl.toLabel (List.mem_map.mpr ⟨cl, hcl, rfl⟩)
        with hd | hs
      · rw [hgrect, hrect]
        exact Or.inl (shift_preserves_disjoint dx dy hd)
      · rw [hgrect, hrect]
        exact Or.inr (shift_preserves_strictInside dx dy hs)
    · rw [hrect]
      exact hparentGroupVsChildLabel g hgp hgRole cl hcl
  · -- rl is a verbatim parent-scene label
    rcases List.mem_append.mp hgItems with hgc | hgp
    · obtain ⟨cg, hcg, hgEq⟩ := List.mem_map.mp hgc
      have hgrole : cg.role = "group" := by
        rw [← hgEq] at hgRole
        simpa [embedBox] using hgRole
      have hgrect : g.rect = shiftRect dx dy cg.rect := by rw [← hgEq]; rfl
      have hplOwn : pl.owner ≠ group.id := hownEq ▸ hone
      rw [hgrect, hrect]
      exact hchildGroupVsParentLabel cg hcg hgrole pl hpl hplOwn
    · rw [hrect]
      exact hparentC8b g hgp hgRole pl.toLabel (List.mem_map.mpr ⟨pl, hpl, rfl⟩)

/-! ### Route coverage of well-formed inputs -/

/-- Route endpoints name boxes of the model: the `RoutesCovered` fact for a
well-formed layered input. -/
theorem routesCovered_of_wellFormed {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) : RoutesCovered inp := by
  unfold WellFormed modelWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hroutes⟩, _⟩, _⟩ := hwf
  intro route hroute
  have hR := List.all_eq_true.mp hroutes route hroute
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at hR
  exact hR

/-! ### The lifts through `layoutRecursive` -/

/-- `layoutRecursive` preserves C8a given the flat clause for leaf layouts,
the sub-input well-formedness seam, and, for every expansion the recursion
performs, the per-expansion facts of `ExpandChildC8aStep`. -/
theorem layoutRecursive_c8a_of_flat (hflat8a : FlatC8a)
    (hsub : SubInputsWellFormed)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursive fuel inp o = .ok res → Validator.C8a res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hwf hframed h
      exact hflat8a inp o res hwf hframed h
  | succ fuel ih =>
      intro inp o res hwf hframed h
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
      · exact hflat8a inp o res hwf hframed hlayout
      · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
          hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
        obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
          hsub fuel inp o group P metric titleLines child parent hwf hframed hP hm hwrap
            hchild hparentAt
        have hchildC8a := ih _ _ _ hwfChild hframedChild hchild
        have hparentC8a := ih _ _ _ hwfParent hframedParent hparentAt
        have hstep := hgeo fuel P inp o group titleLines _ parent child res hexpandAt hframed
          ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
          ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
        exact expandChild_c8a hchildC8a hparentC8a hstep hexpandAt

/-- `layoutRecursive` preserves C8b given the flat clause for leaf layouts,
the sub-input well-formedness seam, and, for every expansion the recursion
performs, the per-expansion facts of `ExpandChildC8bStep`. -/
theorem layoutRecursive_c8b_of_flat (hflat8b : FlatC8b)
    (hsub : SubInputsWellFormed)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o →
      layoutRecursive fuel inp o = .ok res → Validator.C8b res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hwf hframed hfit h
      exact hflat8b inp o res hwf hframed hfit h
  | succ fuel ih =>
      intro inp o res hwf hframed hfit h
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
      · exact hflat8b inp o res hwf hframed hfit hlayout
      · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
          hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
        obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
          hsub fuel inp o group P metric titleLines child parent hwf hframed hP hm hwrap
            hchild hparentAt
        have hfitChild := hfit.childSubInput group
        have hcm := layoutRecursive_canvas_margins fuel hchild
        have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
          rw [checkedParams_canvasMargin hP]
          exact hcm.1
        have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
          rw [checkedParams_canvasMargin hP]
          exact hcm.2
        have hfitParent := InputFixedFit.parentSubInput hwf hfit hP hm hwrap hcw hch
        have hchildC8b := ih _ _ _ hwfChild hframedChild hfitChild hchild
        have hparentC8b := ih _ _ _ hwfParent hframedParent hfitParent hparentAt
        have hstep := hgeo fuel P inp o group titleLines _ parent child res hexpandAt hframed
          ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
          ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
        exact expandChild_c8b hchildC8b hparentC8b hstep hexpandAt

end Elegant.Layered.PipelineImpl
