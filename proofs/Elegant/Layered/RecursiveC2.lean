import Elegant.Layered.RecursiveFit
import Elegant.Layered.RecursiveCallContext

set_option autoImplicit false

/-!
# C2 through `layoutRecursive`: exclusive same-parent boxes stay disjoint

`layoutRecursive_c2_of_flat` lifts clause 2 of the layout validator through the
recursive `expandChild` merge. The flat base case is assumed (`hflat`, stated
as `FlatC2` with exactly `layout_c2`'s premises — well-formed input model and a
successful run — so the family seam can discharge it with `layout_c2`); the
recursive step combines the child and parent C2 facts under the shift
`embedBox` performs.  Well-formedness is taken for the top-level input only:
`hsub : SubInputWellFormedC2` carries it to both sub-inputs of every expansion
the recursion performs.

All remaining premises are packaged per expansion step in `ExpandChildC2Step`.
The input side needs only unique and nonempty box ids; exclusivity-versus-role
facts such as `framedParents` are not used. Both scenes must be parent-closed,
and every scene box must mirror a kept source box of the expansion input with
its parent pointer: child-scene boxes come from sources inside the expanded
group with the group-facing parent rewritten to `""`, parent-scene boxes from
sources outside the group. Those mirrors make the mixed cases impossible: two
embedded children share a result parent only when the child-scene parents
already match, and a parent-scene box whose parent is the group would have to
come from a source that lies both inside and outside the group.
-/

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound

/-- The flat clause of the corrective brief: a single non-recursive layout keeps
exclusive same-parent boxes disjoint under exactly `layout_c2`'s premises
(well-formed input model and a successful run), so the family seam discharges
this seam with `layout_c2`. -/
abbrev FlatC2 : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) →
    layout inp o = .ok res → Validator.C2 res.scene.layoutDump

/-- `modelWellFormed` reads only the boxes, routes, and labels of an input, so
an input with the same selected boxes, routes, and labels is equally
well-formed: the fixed-size, fixed-child, and fixed-area side tables the
expansion step attaches never affect it. -/
private theorem wellFormed_inputModel_of_fields {p q : Input} {o : Options}
    (hboxes : q.boxes = p.boxes) (hroutes : q.routes = p.routes)
    (hlabels : q.labels = p.labels) (h : WellFormed (inputModel p o)) :
    WellFormed (inputModel q o) := by
  show modelWellFormed (inputModel q o) = true
  have heq : modelWellFormed (inputModel q o) = modelWellFormed (inputModel p o) := by
    unfold modelWellFormed inputModel
    simp only
    rw [hboxes, hroutes, hlabels]
  rw [heq]
  exact h

/-- Well-formedness of the sub-inputs `layoutRecursive` recurses into: whenever
the input a call splits at `group` is well-formed, both inputs the recursion
performs next are well-formed again — the child input (`selectInput` of the
boxes inside the group, under the group-direction options) and the parent
input (`selectInput` of the boxes outside the group, under whatever
fixed-size, fixed-child, and fixed-area side tables the expansion step
attaches). `modelWellFormed` reads only the boxes, routes, and labels of an
input, and both sub-inputs keep those as selections of the caller's, so this
is a real fact about `selectInput` and the actual recursion; the family seam
discharges it from `selectInput` preservation alone. -/
def SubInputWellFormedC2 : Prop :=
  ∀ (inp : Input) (o : Options) (group : ModelBox),
    WellFormed (inputModel inp o) →
    WellFormed (inputModel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      { o with direction := directionOf group.direction }) ∧
    ∀ (a : List (String × Size)) (b : List (String × Scene)) (c : List (String × Int)),
      WellFormed (inputModel
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } o)

/-- Disjointness is preserved by a common translation of both rectangles. -/
theorem shiftRect_disjoint_of {a b : Rect} (dx dy : Int) (h : Disjoint a b) :
    Disjoint (shiftRect dx dy a) (shiftRect dx dy b) := by
  unfold Disjoint Rect.meetsInterior shiftRect at *
  dsimp only
  omega

/-- `embedBox` keeps the box id. -/
private theorem embedBox_id {g : String} {dx dy : Int} {box b : Box}
    (h : embedBox g dx dy box = b) : b.id = box.id := by
  have h' := congrArg Box.id h
  simp only [embedBox] at h'
  exact h'.symm

/-- `embedBox` keeps the exclusive flag. -/
private theorem embedBox_exclusive {g : String} {dx dy : Int} {box b : Box}
    (h : embedBox g dx dy box = b) : b.exclusive = box.exclusive := by
  have h' := congrArg Box.exclusive h
  simp only [embedBox] at h'
  exact h'.symm

/-- `embedBox` shifts the rectangle. -/
private theorem embedBox_rect {g : String} {dx dy : Int} {box b : Box}
    (h : embedBox g dx dy box = b) : b.rect = shiftRect dx dy box.rect := by
  have h' := congrArg Box.rect h
  simp only [embedBox] at h'
  exact h'.symm

/-- `embedBox` rewrites a root parent to the group id. -/
private theorem embedBox_parent {g : String} {dx dy : Int} {box b : Box}
    (h : embedBox g dx dy box = b) :
    b.parent = (if box.parent == "" then g else box.parent) := by
  have h' := congrArg Box.parent h
  simp only [embedBox] at h'
  exact h'.symm

/-- A `==` test that comes out false witnesses inequality. -/
private theorem ne_of_beq_false {a b : String} (h : (a == b) = false) : a ≠ b := by
  intro hc
  rw [hc, beq_self_eq_true] at h
  exact Bool.noConfusion h

/-- The converse: unequal strings fail their `==` test. -/
private theorem beq_false_of_ne {a b : String} (h : a ≠ b) : (a == b) = false := by
  cases hbeq : (a == b) with
  | true => exact absurd (beq_iff_eq.mp hbeq) h
  | false => rfl

/-- A box whose parent is the group lies inside the group: the group's own
index heads the box's parent chain. -/
theorem inside_of_parent {boxes : List ModelBox} (hnodup : (boxes.map (·.id)).Nodup)
    {g m : ModelBox} (hg : g ∈ boxes) (hm : m ∈ boxes) (hgid : g.id = m.parent)
    (hne : m.parent ≠ "") :
    Compound.inside boxes g.id m.id = true := by
  have hlenpos : 0 < boxes.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hg)
  cases hf : boxes.findIdx? (fun box : ModelBox => box.id == g.id) with
  | none =>
      exact absurd (beq_self_eq_true g.id)
        (fun hc => Bool.noConfusion ((List.findIdx?_eq_none_iff.mp hf g hg).symm.trans hc))
  | some gidx =>
      obtain ⟨hglt, -, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      refine inside_of_ancestors hnodup hm rfl hf ?_
      rw [← hgid]
      have hmem : gidx ∈ Compound.ancestors boxes boxes.length g.id := by
        have hsucc : boxes.length = (boxes.length - 1).succ :=
          (Nat.succ_pred_eq_of_pos hlenpos).symm
        rw [hsucc, Compound.ancestors.eq_3 boxes g.id (boxes.length - 1)
          (fun h' => hne (by rw [← hgid]; exact h'))]
        simp only [hf, List.getElem?_eq_getElem hglt]
        exact List.mem_append.mpr (Or.inr (List.Mem.head []))
      exact hmem

/-- The per-expansion facts the C2 merge needs: unique nonempty input ids, both
scenes parent-closed, and each scene box mirroring a kept source box of the
input with its parent pointer. -/
def ExpandChildC2Step (_P : Params) (inp : Input) (_o : Options) (group : ModelBox)
    (_titleHeight : Int) (parent child _result : FamilyResult) : Prop :=
  ((inp.boxes.map (·.id)).Nodup ∧ group ∈ inp.boxes ∧ ∀ m ∈ inp.boxes, m.id ≠ "") ∧
    SceneParentClosed parent.scene ∧ SceneParentClosed child.scene ∧
    (∀ cb ∈ child.scene.boxes, ∃ m ∈ inp.boxes,
        Compound.inside inp.boxes group.id m.id = true ∧ m.id = cb.id ∧
          cb.parent = (if m.parent == group.id then "" else m.parent)) ∧
    (∀ pb ∈ parent.scene.boxes, ∃ m ∈ inp.boxes,
        (!Compound.inside inp.boxes group.id m.id) = true ∧ m.id = pb.id ∧
          pb.parent = m.parent)

/-- `expandChild` preserves C2. Two merged boxes with the same parent are either
both child-scene images (child C2 plus the common shift), both parent-scene
boxes (parent C2 verbatim), or one of each — and the mirrors rule the last
case out: an embedded child root points at the group, while a parent-scene box
pointing at the group would have to come from a source lying both inside and
outside the group, and a non-group shared parent would name a box of both
scenes, again splitting one input id into two opposite keep verdicts. -/
theorem expandChild_c2 {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child result : FamilyResult}
    (hchildC2 : Validator.C2 child.scene.layoutDump)
    (hparentC2 : Validator.C2 parent.scene.layoutDump)
    (hstep : ExpandChildC2Step P inp o group titleHeight parent child result)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    Validator.C2 result.scene.layoutDump := by
  obtain ⟨frame, _metric, _titleLines, _lines, dx, dy, _hframe, _hmetric, _htitle,
    _hlines, _hdx, _hdy, _hcanvas, hboxes⟩ := expandChild_sources h
  rcases hstep with ⟨⟨hnodup, hgroupMem, hneEmpty⟩, hpclosed, hcclosed, hchildFid, hparentFid⟩
  have hgid : group.id ≠ "" := hneEmpty group hgroupMem
  intro b hb c hc hne hbex hcex hpar
  have hbMem : b ∈ result.scene.layoutDump.boxes := hb
  have hcMem : c ∈ result.scene.layoutDump.boxes := hc
  simp only [Scene.layoutDump] at hbMem hcMem
  change b ∈ result.scene.boxes at hbMem
  change c ∈ result.scene.boxes at hcMem
  rw [hboxes] at hbMem hcMem
  obtain ⟨_, -, hbfind⟩ := List.mem_filterMap.mp hbMem
  obtain ⟨_, -, hcfind⟩ := List.mem_filterMap.mp hcMem
  have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hbfind
  have hcItems : c ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hcfind
  rcases List.mem_append.mp hbItems with hbc | hbp
  · rcases List.mem_append.mp hcItems with hcc | hcp
    · -- both merged boxes are child-scene images
      obtain ⟨cb, hcbmem, hbEq⟩ := List.mem_map.mp hbc
      have hbpar : b.parent = (if cb.parent == "" then group.id else cb.parent) :=
        embedBox_parent hbEq
      obtain ⟨cc, hccmem, hcEq⟩ := List.mem_map.mp hcc
      have hcpar : c.parent = (if cc.parent == "" then group.id else cc.parent) :=
        embedBox_parent hcEq
      have hbrect : b.rect = shiftRect dx dy cb.rect := embedBox_rect hbEq
      have hcrect : c.rect = shiftRect dx dy cc.rect := embedBox_rect hcEq
      have hbid : b.id = cb.id := embedBox_id hbEq
      have hcid : c.id = cc.id := embedBox_id hcEq
      have hbproj : b.exclusive = cb.exclusive := embedBox_exclusive hbEq
      have hcproj : c.exclusive = cc.exclusive := embedBox_exclusive hcEq
      have hcbex : cb.exclusive = true := by rw [← hbproj]; exact hbex
      have hccex : cc.exclusive = true := by rw [← hcproj]; exact hcex
      by_cases hcb0 : cb.parent = ""
      · simp [hcb0] at hbpar
        by_cases hcc0 : cc.parent = ""
        · simp [hcc0] at hcpar
          have hdisj := hchildC2 cb hcbmem cc hccmem
            (by rw [← hbid, ← hcid]; exact hne) hcbex hccex (by rw [hcb0, hcc0])
          rw [hbrect, hcrect]
          exact shiftRect_disjoint_of dx dy hdisj
        · rw [beq_false_of_ne hcc0] at hcpar
          simp at hcpar
          have hccg : cc.parent = group.id := by rw [← hcpar, ← hpar, hbpar]
          obtain ⟨m, -, -, -, hmpar⟩ := hchildFid cc hccmem
          rw [hccg] at hmpar
          by_cases hcmp : m.parent = group.id
          · simp [hcmp] at hmpar
            exact absurd hmpar hgid
          · rw [beq_false_of_ne hcmp] at hmpar
            simp at hmpar
            exact absurd hmpar.symm hcmp
      · rw [beq_false_of_ne hcb0] at hbpar
        simp at hbpar
        by_cases hcc0 : cc.parent = ""
        · simp [hcc0] at hcpar
          have hcbg : cb.parent = group.id := (hbpar.symm.trans hpar).trans hcpar
          obtain ⟨m, -, -, -, hmpar⟩ := hchildFid cb hcbmem
          rw [hcbg] at hmpar
          by_cases hcmp : m.parent = group.id
          · simp [hcmp] at hmpar
            exact absurd hmpar hgid
          · rw [beq_false_of_ne hcmp] at hmpar
            simp at hmpar
            exact absurd hmpar.symm hcmp
        · rw [beq_false_of_ne hcc0] at hcpar
          simp at hcpar
          have hdisj := hchildC2 cb hcbmem cc hccmem
            (by rw [← hbid, ← hcid]; exact hne) hcbex hccex
            (by rw [← hbpar, ← hcpar, hpar])
          rw [hbrect, hcrect]
          exact shiftRect_disjoint_of dx dy hdisj
    · -- embedded child image against a parent-scene box
      obtain ⟨cb, hcbmem, hbEq⟩ := List.mem_map.mp hbc
      have hbpar : b.parent = (if cb.parent == "" then group.id else cb.parent) :=
        embedBox_parent hbEq
      by_cases hcb0 : cb.parent = ""
      · -- child root: its parent is the group, and no parent-scene box can have
        -- the group as parent (its source would lie inside the group)
        simp [hcb0] at hbpar
        have hcpg : c.parent = group.id := hpar.symm.trans hbpar
        obtain ⟨m, hmmem, hout, -, hmpar⟩ := hparentFid c hcp
        rw [hcpg] at hmpar
        have hin : Compound.inside inp.boxes group.id m.id = true :=
          inside_of_parent hnodup hgroupMem hmmem hmpar (by rw [← hmpar]; exact hgid)
        rw [hin] at hout
        simp at hout
      · -- non-root child image: the shared parent names a child-scene box and a
        -- parent-scene box, so one input id keeps both verdicts
        rw [beq_false_of_ne hcb0] at hbpar
        simp at hbpar
        have hcpeq : c.parent = cb.parent := hpar.symm.trans hbpar
        rcases hcclosed cb hcbmem with hc0 | ⟨x, hxmem, hxid⟩
        · exact absurd hc0 hcb0
        rcases hpclosed c hcp with hp0 | ⟨y, hypmem, hyid⟩
        · exact absurd (by rw [← hcpeq]; exact hp0) hcb0
        obtain ⟨mx, hxmem2, hxin, hxid2, -⟩ := hchildFid x hxmem
        obtain ⟨my, hymem2, hyout, hyid2, -⟩ := hparentFid y hypmem
        have hmxmy : mx.id = my.id := by rw [hxid2, hxid, ← hcpeq, ← hyid, hyid2]
        rw [← hmxmy] at hyout
        rw [hxin] at hyout
        simp at hyout
  · rcases List.mem_append.mp hcItems with hcc | hcp
    · -- parent-scene box against an embedded child image
      obtain ⟨cc, hccmem, hcEq⟩ := List.mem_map.mp hcc
      have hcpar : c.parent = (if cc.parent == "" then group.id else cc.parent) :=
        embedBox_parent hcEq
      by_cases hcc0 : cc.parent = ""
      · -- child root mirrored: b's source would have the group as parent
        simp [hcc0] at hcpar
        have hbpg : b.parent = group.id := hpar.trans hcpar
        obtain ⟨m, hmmem, hout, -, hmpar⟩ := hparentFid b hbp
        rw [hbpg] at hmpar
        have hin : Compound.inside inp.boxes group.id m.id = true :=
          inside_of_parent hnodup hgroupMem hmmem hmpar (by rw [← hmpar]; exact hgid)
        rw [hin] at hout
        simp at hout
      · -- non-root child image: the shared parent names boxes of both scenes
        rw [beq_false_of_ne hcc0] at hcpar
        simp at hcpar
        have hbpeq : b.parent = cc.parent := hpar.trans hcpar
        rcases hcclosed cc hccmem with hc0 | ⟨x, hxmem, hxid⟩
        · exact absurd hc0 hcc0
        rcases hpclosed b hbp with hp0 | ⟨y, hypmem, hyid⟩
        · exact absurd (by rw [← hbpeq]; exact hp0) hcc0
        obtain ⟨mx, hxmem2, hxin, hxid2, -⟩ := hchildFid x hxmem
        obtain ⟨my, hymem2, hyout, hyid2, -⟩ := hparentFid y hypmem
        have hmxmy : mx.id = my.id := by rw [hxid2, hxid, ← hbpeq, ← hyid, hyid2]
        rw [← hmxmy] at hyout
        rw [hxin] at hyout
        simp at hyout
    · -- both merged boxes are parent-scene boxes, unchanged by the merge
      exact hparentC2 b hbp c hcp hne hbex hcex hpar
/-- Route endpoints name boxes of the model: the `RoutesCovered` fact for
a well-formed layered input (the `RecursiveC6` version, restated locally so
this module does not depend on the C6 lane). -/
theorem inputRoutesCoveredC2 {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) : RoutesCovered inp := by
  unfold WellFormed modelWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hroutes⟩, _⟩, _⟩ := hwf
  intro route hroute
  have h := List.all_eq_true.mp hroutes route hroute
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at h
  exact h



/-- Selections keep the nonempty ids of the input they select from: a selected
box is an input box whose `parent` field alone may be rewritten. -/
theorem selectInput_ids_nonempty {inp : Input} (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (keep : ModelBox → Bool) (root : String) :
    ∀ m ∈ (selectInput inp keep root).boxes, m.id ≠ "" := by
  intro m hm
  simp only [selectInput, List.mem_map, List.mem_filter] at hm
  obtain ⟨q, ⟨hq, _⟩, rfl⟩ := hm
  have hmem : q.1 ∈ inp.boxes :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq)
  split
  · exact hids q.1 hmem
  · exact hids q.1 hmem

/-- `layoutRecursive` preserves C2 given the flat clause for leaf layouts —
exactly `layout_c2`'s premises, so the family seam discharges `hflat` with it —
well-formedness of the sub-inputs each expansion recurses into, nonempty box
ids of the input (`modelWellFormed` does not check them, so they are a premise
on the input, carried to both sub-inputs by `selectInput_ids_nonempty`), and,
for every expansion the recursion performs, the `ExpandChildC2Step` facts under
the `ExpandChildCallContext` the recursion supplies.  Well-formedness itself is
taken for the top-level input only: `hsub` re-establishes it at every recursive
call. -/
theorem layoutRecursive_c2_of_flat (hflat : FlatC2)
    (hsub : SubInputWellFormedC2)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      (∀ m ∈ inp.boxes, m.id ≠ "") →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildC2Step P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → (∀ m ∈ inp.boxes, m.id ≠ "") →
      layoutRecursive fuel inp o = .ok res → Validator.C2 res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hwf _ h
      exact hflat inp o res hwf h
  | succ fuel ih =>
      intro inp o res hwf hidsCur h
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
      · exact hflat inp o res hwf hlayout
      · have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
        have hcovered : RoutesCovered inp := inputRoutesCoveredC2 hwf
        obtain ⟨P, _metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
            _hP, _hm, hchild, _hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
        obtain ⟨hchildWf, hparentWf⟩ := hsub inp o group hwf
        have hstep := hgeo fuel P inp o group titleLines _ parent child res hexpandAt hidsCur
          ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
        refine expandChild_c2 (ih _ _ _ hchildWf ?_ hchild)
          (ih _ _ _ (hparentWf _ _ _) ?_ hparentAt) hstep hexpandAt
        · exact selectInput_ids_nonempty hidsCur
            (fun box => Compound.inside inp.boxes group.id box.id) group.id
        · exact selectInput_ids_nonempty hidsCur
            (fun box => !Compound.inside inp.boxes group.id box.id) ""

end Elegant.Layered.PipelineImpl
