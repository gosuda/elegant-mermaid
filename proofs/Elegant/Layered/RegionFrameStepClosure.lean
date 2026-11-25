import Elegant.Layered.RegionCanvasMargins
import Elegant.Layered.RegionNotesFitClosure
import Elegant.Layered.RegionC8aGroupPlainCutover
import Elegant.Layered.RegionPartSizingClosed
import Elegant.Layered.RegionStepAssemblers
import Elegant.Layered.RegionStepGeometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Elegant.Layered.PipelineImpl

private abbrev frameRegionBase (exactIds : List String) (idSets : List (String × List String)) :
    Input → Options → Except LayoutError FamilyResult :=
  fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o

private structure FrameMetadata (inp : Input) (res : FamilyResult) : Prop where
  ids : res.scene.boxes.map (·.id) = inp.boxes.map (·.id)
  sources : ∀ b ∈ res.scene.boxes, ∃ m ∈ inp.boxes,
    b.id = m.id ∧ b.parent = m.parent ∧ b.role = m.role.id
  fixed : FixedBoxDimensions inp res

private theorem selectedFrameSource (inp : Input) (keep : ModelBox → Bool) (root : String)
    {b : ModelBox} (hb : b ∈ (selectInput inp keep root).boxes) :
    ∃ m ∈ inp.boxes, keep m = true ∧ b.id = m.id ∧
      b.parent = (if m.parent == root then "" else m.parent) ∧ b.role = m.role := by
  obtain ⟨m, hm, hk, he⟩ := selectInput_box_source inp keep root b hb
  refine ⟨m, hm, hk, ?_⟩
  rw [he]
  by_cases h : (m.parent == root) = true <;> simp [h]

private theorem recursiveFrameMetadata
    (base : Input → Options → Except LayoutError FamilyResult)
    (leaf : ∀ inp o res, base inp o = .ok res → NotesBoxMirror inp res ∧ FixedBoxDimensions inp res)
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (h : layoutRecursiveB base fuel inp o = .ok res) :
    FrameMetadata inp res := by
  have flat : ∀ {sub opts out}, base sub opts = .ok out → FrameMetadata sub out := by
    intro sub opts out hout
    obtain ⟨hm, hd⟩ := leaf sub opts out hout
    refine ⟨hm.1, ?_, hd⟩
    intro b hb
    obtain ⟨m, hmem, hid, hp, _, hr⟩ := hm.2 b hb
    exact ⟨m, hmem, hid, hp, hr⟩
  induction fuel generalizing inp o res with
  | zero => exact flat h
  | succ fuel ih =>
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hflat⟩ |
      ⟨group, P, _, child, titleLines, parent, _, _, _, hchild, _, hparent, hexpand⟩
    · exact flat hflat
    change layoutRecursiveB base fuel (childSubInput inp group) (childSubOptions o group) =
      .ok child at hchild
    change layoutRecursiveB base fuel (parentSubInput inp group P titleLines child) o =
      .ok parent at hparent
    obtain ⟨hwfc, hwfp⟩ := subInputWellFormedC2 inp o group hwf
    have hcm := ih hwfc hchild
    have hpm := ih (hwfp _ _ _) hparent
    obtain ⟨_, _, _, _, dx, dy, _, _, _, _, _, _, _, hboxes⟩ := expandChild_sources hexpand
    let inside := fun b : ModelBox => Compound.inside inp.boxes group.id b.id
    let merged := child.scene.boxes.map (embedBox group.id dx dy) ++ parent.scene.boxes
    have hcIds : child.scene.boxes.map (·.id) = (inp.boxes.filter inside).map (·.id) :=
      hcm.ids.trans (selectInput_box_ids inp inside group.id)
    have hpIds : parent.scene.boxes.map (·.id) = (inp.boxes.filter fun b => !inside b).map (·.id) :=
      hpm.ids.trans (selectInput_box_ids inp (fun b => !inside b) "")
    have cover : ∀ id ∈ inp.boxes.map (·.id), ∃ b ∈ merged, b.id = id := by
      intro id hid
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hid
      by_cases hin : inside m = true
      · have hmem : m.id ∈ child.scene.boxes.map (·.id) := by
          rw [hcIds]
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, hin⟩)
        obtain ⟨b, hb, he⟩ := List.mem_map.mp hmem
        exact ⟨embedBox group.id dx dy b, List.mem_append_left _ (List.mem_map_of_mem hb), he⟩
      · have hmem : m.id ∈ parent.scene.boxes.map (·.id) := by
          rw [hpIds]
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, by simpa using hin⟩)
        obtain ⟨b, hb, he⟩ := List.mem_map.mp hmem
        exact ⟨b, List.mem_append_right _ hb, he⟩
    have ids : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
      rw [hboxes]
      exact filterMap_find_ids Box.id (inp.boxes.map (·.id)) merged cover inp.boxes ModelBox.id rfl
    have source (b : Box) (hb : b ∈ res.scene.boxes) :
        (∃ c ∈ child.scene.boxes, embedBox group.id dx dy c = b) ∨ b ∈ parent.scene.boxes := by
      rw [hboxes] at hb
      obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hb
      have hm := List.mem_of_find?_eq_some hfind
      change b ∈ child.scene.boxes.map (embedBox group.id dx dy) ++ parent.scene.boxes at hm
      exact (List.mem_append.mp hm).imp List.mem_map.mp id
    refine ⟨ids, ?_, ?_⟩
    · intro b hb
      rcases source b hb with ⟨c, hc, rfl⟩ | hp
      · obtain ⟨s, hs, hid, hpar, hrole⟩ := hcm.sources c hc
        obtain ⟨m, hm, hkeep, hsid, hsp, hsr⟩ := selectedFrameSource inp inside group.id hs
        have hne := inside_parent_ne_empty (Model.boxIds_nodup hwf) hkeep hm rfl
        refine ⟨m, hm, hid.trans hsid, ?_, hrole.trans (congrArg BoxRole.id hsr)⟩
        change (if c.parent == "" then group.id else c.parent) = m.parent
        rw [hpar, hsp]
        exact embed_parent_eq hne
      · obtain ⟨s, hs, hid, hpar, hrole⟩ := hpm.sources b hp
        obtain ⟨m, hm, _, hsid, hsp, hsr⟩ := selectedFrameSource inp (fun m => !inside m) "" hs
        exact ⟨m, hm, hid.trans hsid, hpar.trans (hsp.trans (selectInput_parent_root m.parent)),
          hrole.trans (congrArg BoxRole.id hsr)⟩
    · intro b hb entry hfixed
      rcases source b hb with ⟨c, hc, rfl⟩ | hp
      · exact hcm.fixed c hc entry hfixed
      · apply hpm.fixed b hp entry
        change (inp.fixedSizes ++ _).find? (fun row => row.1 == b.id) = some entry
        simp [List.find?_append, hfixed]

private theorem frameRegionLeaf (exactIds : List String) (idSets : List (String × List String))
    (inp : Input) (o : Options) (res : FamilyResult)
    (h : frameRegionBase exactIds idSets inp o = .ok res) :
    NotesBoxMirror inp res ∧ FixedBoxDimensions inp res :=
  ⟨layoutRIds_boxes_mirror h,
    layoutRegionNotes_fixedBoxDimensions idSets (exactIds := exactIds) (outerFuel := 0) h⟩

private theorem frameRegionMetadata (exactIds : List String)
    (idSets : List (String × List String)) (fuel : Nat)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (h : layoutRecursiveB (frameRegionBase exactIds idSets) fuel inp o = .ok res) :
    FrameMetadata inp res :=
  recursiveFrameMetadata _ (frameRegionLeaf exactIds idSets) fuel hwf h

private theorem absentAncestor_of_absentParent (d : LayoutDump) (target : String)
    (h : ∀ b ∈ d.boxes, b.parent ≠ "" → b.parent ≠ target) :
    ∀ (fuel : Nat) (start : String), target ∉ LayoutDump.ancestors.go d fuel start := by
  intro fuel
  induction fuel with
  | zero => intro start; simp [LayoutDump.ancestors.go]
  | succ fuel ih =>
    intro start
    cases hb : d.box? start with
    | none => simp [LayoutDump.ancestors.go, hb]
    | some b =>
      have hm : b ∈ d.boxes := List.mem_of_find?_eq_some hb
      by_cases hp : b.parent = ""
      · simp [LayoutDump.ancestors.go, hb, hp]
      · simp only [LayoutDump.ancestors.go, hb, hp, ↓reduceIte, List.mem_cons, not_or]
        exact ⟨Ne.symm (h b hm hp), ih b.parent⟩

private theorem stepC8aGroupIsolated_of_metadata
    {inp : Input} {o : Options} {group : ModelBox} {P : Params}
    {titleLines : List Measure.Line} {parent child : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hgroup : group ∈ inp.boxes)
    (parentMetadata : FrameMetadata (parentSubInput inp group P titleLines child) parent) :
    ∀ b ∈ parent.scene.boxes, b.id ≠ group.id →
      group.id ∉ parent.scene.layoutDump.ancestors b.id := by
  intro b _ _
  change group.id ∉ LayoutDump.ancestors.go parent.scene.layoutDump
    parent.scene.layoutDump.boxes.length b.id
  apply absentAncestor_of_absentParent
  intro pb hpb hne heq
  obtain ⟨m, hm, _, hpar, _⟩ := parentMetadata.sources pb hpb
  change m ∈ (selectInput inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes at hm
  obtain ⟨original, horiginal, hkept, _, hp⟩ := selectInput_box_spec inp
    (fun m => !Compound.inside inp.boxes group.id m.id) "" hm
  have hparentEq : pb.parent = original.parent :=
    hpar.trans (hp.trans (selectInput_parent_root original.parent))
  have hneOriginal : original.parent ≠ "" := fun h => hne (hparentEq.trans h)
  have hin := inside_of_parent (Model.boxIds_nodup hwf) hgroup
    horiginal (heq.symm.trans hparentEq) hneOriginal
  change Compound.inside inp.boxes group.id original.id = true at hin
  change (!Compound.inside inp.boxes group.id original.id) = true at hkept
  simp only [hin, Bool.not_true, Bool.false_eq_true] at hkept

theorem r_stepC8aGroupIsolated_closed (exactIds : List String)
    (idSets : List (String × List String)) : R_StepC8aGroupIsolatedB exactIds idSets := by
  intro fuel P inp o group titleLines titleHeight parent child res _ _ hctx _
  obtain ⟨hwf, hgroup, _, _, hparent, _⟩ := hctx
  obtain ⟨_, hwfp⟩ := subInputWellFormedC2 inp o group hwf
  exact stepC8aGroupIsolated_of_metadata (P := P) (titleLines := titleLines) (child := child)
    hwf (List.mem_of_find?_eq_some hgroup)
    (frameRegionMetadata exactIds idSets fuel (hwfp _ _ _) hparent)

theorem r_childInset_closed (exactIds : List String)
    (idSets : List (String × List String)) : RSG_ChildInsetB exactIds idSets := by
  intro fuel P inp o group titleLines titleHeight parent child res _ hfp hctx hparams
  obtain ⟨hwf, _, _, hchild, _, _⟩ := hctx
  have hwfc := (subInputWellFormedC2 inp o group hwf).1
  have hfc := (framedParentsSub inp o group hwf hfp).1
  have hP : checkedParams (childSubOptions o group).profile (childSubInput inp group).kind =
      .ok P := hparams.1
  exact (layoutRecursiveB_inset (frameRegionBase exactIds idSets)
    (flatInsetB_layoutRIds_reindex exactIds idSets
      (fun sub => R_partSizingRResidual_holds exactIds (reindexRegionSets idSets sub)))
    subInputWellFormedC2 (expandChildFitClosedB_region exactIds idSets)
    fuel _ _ _ hwfc hfc hchild P hP).2

private theorem nonnegativeTitleWidth (lines : List Measure.Line) :
    0 ≤ lines.foldl (fun width line => max width line.width) 0 := by
  suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
      0 ≤ ls.foldl (fun width line => max width line.width) acc by
    exact key lines 0 (by omega)
  intro ls acc hac
  induction ls generalizing acc with
  | nil => exact hac
  | cons line ls ih =>
    simp only [List.foldl_cons]
    exact ih _ (Int.le_trans hac (Int.le_max_left _ _))

private theorem r_stepFrameStrict (exactIds : List String) (idSets : List (String × List String))
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hfp : framedParents inp = true)
    (hctx : ExpandChildCallContextB (frameRegionBase exactIds idSets) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun b => b.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).x - P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).y - P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      ∀ r : Rect,
      (⟨P.canvasMargin, P.canvasMargin, child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained r →
      frame.rect.StrictInside (shiftRect dx dy r) := by
  intro frame tl dx dy hf hx hy hwrap r hr
  obtain ⟨hP, hheight, metric, hm, ht⟩ := hparams
  obtain ⟨metric', hm', ht'⟩ := hwrap
  have heqMetric : metric' = metric := Except.ok.inj (hm'.symm.trans hm)
  rw [heqMetric] at ht'
  have heqLines : tl = titleLines := Except.ok.inj (ht'.symm.trans ht)
  subst tl
  obtain ⟨hwf, hg, _, _, hparent, _⟩ := hctx
  obtain ⟨_, hwfp⟩ := subInputWellFormedC2 inp o group hwf
  have hdim := (frameRegionMetadata exactIds idSets fuel (hwfp _ _ _) hparent).fixed
  have hnotFixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    have htest := List.find?_some hg
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at htest
    exact htest.2
  have hnone : inp.fixedSizes.find? (fun row => row.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hnotFixed)
  have hid : frame.id = group.id := by simpa using List.find?_some hf
  let tw := titleLines.foldl (fun width line => max width line.width) 0
  let childArea : Size := ⟨child.scene.canvas.w - 2 * P.canvasMargin,
    child.scene.canvas.h - 2 * P.canvasMargin⟩
  let reserved := childFrameSize group.direction P.clusterPad tw titleHeight childArea
  have hfixed : (parentSubInput inp group P titleLines child).fixedSizes.find?
      (fun row => row.1 == frame.id) = some (group.id, reserved) := by
    change (inp.fixedSizes ++ [(group.id, childFrameSize group.direction P.clusterPad tw
      ((max 1 titleLines.length : Int) * P.lineH) childArea)]).find?
      (fun row => row.1 == frame.id) = some (group.id, reserved)
    simp [List.find?_append, hid, hnone, reserved, hheight]
  obtain ⟨hw, hh⟩ := hdim frame (List.mem_of_find?_eq_some hf) _ hfixed
  have hth : 0 ≤ titleHeight := by
    rw [hheight]
    exact Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
  have hstrict : frame.rect.StrictInside
      (shiftRect dx dy ⟨P.canvasMargin, P.canvasMargin, childArea.w, childArea.h⟩) := by
    rw [hx, hy]
    exact childInsetContent_strict (checkedParams_clusterPad_pos hP)
      (nonnegativeTitleWidth titleLines) hth hw hh
  have hshift : (shiftRect dx dy ⟨P.canvasMargin, P.canvasMargin, childArea.w, childArea.h⟩).Contained
      (shiftRect dx dy r) := (contained_shiftRect dx dy).mpr hr
  unfold Rect.StrictInside at hstrict ⊢
  unfold Rect.Contained at hshift
  omega

theorem r_stepC8aGeometry_closed (exactIds : List String)
    (idSets : List (String × List String)) :
    RecursiveStepFactsB (frameRegionBase exactIds idSets) ExpandChildC8aGeometry :=
  rsg_stepC8aGeometry_region exactIds idSets (r_stepFrameStrict exactIds idSets)
    (r_childInset_closed exactIds idSets)

private theorem parentWalkTransport {before after : LayoutDump}
    (hlookup : ∀ b : Box, before.box? b.id = some b → after.box? b.id = some b)
    (n : Nat) : ∀ (fuel : Nat) (start : String), n ≤ fuel →
      LayoutDump.ancestors.go before n start ⊆ LayoutDump.ancestors.go after fuel start := by
  induction n with
  | zero => intro fuel start _ x hx; simp [LayoutDump.ancestors.go] at hx
  | succ n ih =>
    intro fuel start hle x hx
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases hbox : before.box? start with
      | none => simp [LayoutDump.ancestors.go, hbox] at hx
      | some b =>
        by_cases hp : b.parent = ""
        · simp [LayoutDump.ancestors.go, hbox, hp] at hx
        · have hid := boxLookupId hbox
          have hafter := hlookup b (by rw [hid]; exact hbox)
          rw [hid] at hafter
          simp only [LayoutDump.ancestors.go, hbox, hp, ↓reduceIte] at hx
          simp only [LayoutDump.ancestors.go, hafter, hp, ↓reduceIte]
          rcases List.mem_cons.mp hx with he | htail
          · exact List.mem_cons.mpr (Or.inl he)
          · exact List.mem_cons.mpr (Or.inr (ih fuel b.parent (by omega) htail))

private theorem childWalkRejoinsParent {before after parent : LayoutDump}
    {boxes : List ModelBox} {groupId : String} {dx dy : Int}
    (lookup : ∀ m ∈ boxes, ∃ b : Box, before.box? m.id = some b ∧ b.parent = m.parent)
    (embed : ∀ b : Box, before.box? b.id = some b →
      after.box? b.id = some (embedBox groupId dx dy b))
    (keep : ∀ b : Box, parent.box? b.id = some b → after.box? b.id = some b)
    (root : ∀ m ∈ boxes, m.parent = "" → groupId ≠ "") (n : Nat) :
    ∀ (m : ModelBox), m ∈ boxes → ParentReaches boxes n m.parent →
      ∀ (fuel : Nat), n + 1 + parent.boxes.length ≤ fuel →
      ∀ x ∈ groupId :: parent.ancestors groupId,
        x ∈ LayoutDump.ancestors.go after fuel m.id := by
  have image (m : ModelBox) (hm : m ∈ boxes) :
      ∃ b : Box, after.box? m.id = some (embedBox groupId dx dy b) ∧ b.parent = m.parent := by
    obtain ⟨b, hb, hp⟩ := lookup m hm
    have hid := boxLookupId hb
    have he := embed b (by rw [hid]; exact hb)
    rw [hid] at he
    exact ⟨b, he, hp⟩
  have atRoot (m : ModelBox) (hm : m ∈ boxes) (hp : m.parent = "") (fuel : Nat)
      (hle : parent.boxes.length + 1 ≤ fuel) :
      ∀ x ∈ groupId :: parent.ancestors groupId,
        x ∈ LayoutDump.ancestors.go after fuel m.id := by
    intro x hx
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨b, hb, hpar⟩ := image m hm
      have he : (embedBox groupId dx dy b).parent = groupId := by simp [embedBox, hpar, hp]
      have hne := root m hm hp
      simp only [LayoutDump.ancestors.go, hb, he, hne, ↓reduceIte]
      rcases List.mem_cons.mp hx with hx | hx
      · exact List.mem_cons.mpr (Or.inl hx)
      · refine List.mem_cons.mpr (Or.inr ?_)
        exact parentWalkTransport keep parent.boxes.length fuel groupId (by omega) hx
  induction n with
  | zero =>
    intro m hm hterm fuel hle
    by_cases hp : m.parent = ""
    · exact atRoot m hm hp fuel (by omega)
    · simp only [ParentReaches.eq_2 boxes m.parent hp] at hterm
  | succ n ih =>
    intro m hm hterm fuel hle x hx
    by_cases hp : m.parent = ""
    · exact atRoot m hm hp fuel (by omega) x hx
    · rw [ParentReaches.eq_3 boxes m.parent n hp] at hterm
      obtain ⟨p, hfind, hnext⟩ := hterm
      have hpid : p.id = m.parent := by simpa using List.find?_some hfind
      cases fuel with
      | zero => omega
      | succ fuel =>
        obtain ⟨b, hb, hpar⟩ := image m hm
        have hbeq : (m.parent == "") = false := beq_eq_false_iff_ne.mpr hp
        have he : (embedBox groupId dx dy b).parent = m.parent := by
          simp [embedBox, hpar, hbeq]
        have htail := ih p (List.mem_of_find?_eq_some hfind) hnext fuel (by omega) x hx
        rw [hpid] at htail
        simp only [LayoutDump.ancestors.go, hb, he, hp, ↓reduceIte]
        exact List.mem_cons.mpr (Or.inr htail)

private theorem selectedCounts {α : Type} (keep : α → Bool) (items : List α) :
    (items.filter keep).length + (items.filter fun a => !keep a).length = items.length := by
  induction items with
  | nil => rfl
  | cons a items ih => cases h : keep a <;> simp [h] <;> omega

private theorem stepC8aMergeFacts
    (base : Input → Options → Except LayoutError FamilyResult)
    (leaf : ∀ inp o res, base inp o = .ok res → NotesBoxMirror inp res ∧ FixedBoxDimensions inp res)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hctx : ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hfit : ExpandChildFitsInset P inp o group titleHeight parent child res) :
    child.scene.boxes.length ≤ res.scene.boxes.length ∧
    parent.scene.boxes.length ≤ res.scene.boxes.length ∧
    (∀ cb ∈ child.scene.boxes, ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
      x ∈ res.scene.layoutDump.ancestors cb.id) := by
  obtain ⟨frame, metric, tl, _, dx, dy, hf, hm, ht, _, hdx, hdy, _, _⟩ :=
    expandChild_sources hexpand
  obtain ⟨_, hEmbed, hKeep⟩ := hfit frame tl dx dy hf hdx hdy ⟨metric, hm, ht⟩
  obtain ⟨hwf, hg, _, hchild, hparent, _⟩ := hctx
  obtain ⟨hwfc, hwfp⟩ := subInputWellFormedC2 inp o group hwf
  have hrun : layoutRecursiveB base (fuel + 1) inp o = .ok res := by
    obtain ⟨hP, hheight, mm, hmetric, htitle⟩ := hparams
    subst titleHeight
    simp only [childSubInput, childSubOptions] at hchild
    simp only [parentSubInput] at hparent
    unfold layoutRecursiveB
    rw [hg]
    simp only [hP, hmetric, hchild, htitle, hparent, hexpand, Bind.bind, Except.bind]
  have childMeta : FrameMetadata (childSubInput inp group) child :=
    recursiveFrameMetadata base leaf fuel hwfc hchild
  have parentMeta : FrameMetadata (parentSubInput inp group P titleLines child) parent :=
    recursiveFrameMetadata base leaf fuel (hwfp _ _ _) hparent
  have mergedMeta := recursiveFrameMetadata base leaf (fuel + 1) hwf hrun
  let keep := fun b : ModelBox => Compound.inside inp.boxes group.id b.id
  have hpids : parent.scene.boxes.map (·.id) = (inp.boxes.filter fun b => !keep b).map (·.id) := by
    rw [parentMeta.ids]
    change (selectInput inp (fun b => !keep b) "").boxes.map (·.id) =
      (inp.boxes.filter fun b => !keep b).map (·.id)
    exact selectInput_box_ids inp (fun b => !keep b) ""
  have hclen' : (childSubInput inp group).boxes.length = (inp.boxes.filter keep).length := by
    change (selectInput inp keep group.id).boxes.length = (inp.boxes.filter keep).length
    simpa only [List.length_map] using
      congrArg List.length (selectInput_box_ids inp keep group.id)
  have hplen : parent.scene.boxes.length = (inp.boxes.filter fun b => !keep b).length := by
    simpa only [List.length_map] using congrArg List.length hpids
  have hmlen : res.scene.boxes.length = inp.boxes.length := by
    simpa only [List.length_map] using congrArg List.length mergedMeta.ids
  have hsum : (childSubInput inp group).boxes.length + parent.scene.layoutDump.boxes.length =
      res.scene.layoutDump.boxes.length := by
    change (childSubInput inp group).boxes.length + parent.scene.boxes.length =
      res.scene.boxes.length
    rw [hclen', hplen, hmlen]
    exact selectedCounts keep inp.boxes
  have hchildLen : child.scene.boxes.length = (childSubInput inp group).boxes.length := by
    simpa only [List.length_map] using congrArg List.length childMeta.ids
  have hsum' : child.scene.boxes.length + parent.scene.boxes.length = res.scene.boxes.length := by
    rw [hchildLen]
    exact hsum
  refine ⟨by omega, by omega, ?_⟩
  have childFacts : InputFacts (childSubInput inp group) :=
    inputFacts_of_wellFormed (o := childSubOptions o group) hwfc
  have hchildNd := childFacts.nodup
  have hlookup : ∀ m ∈ (childSubInput inp group).boxes,
      ∃ b : Box, child.scene.layoutDump.box? m.id = some b ∧ b.parent = m.parent := by
    intro m hm
    have hmem : m.id ∈ child.scene.boxes.map (·.id) := by
      rw [childMeta.ids]
      exact List.mem_map_of_mem hm
    obtain ⟨b, hb, hid⟩ := List.mem_map.mp hmem
    obtain ⟨s, hs, hbs, hp, _⟩ := childMeta.sources b hb
    have he : s = m := eq_of_mem_id hchildNd hs hm (hbs.symm.trans hid)
    have hnd : (child.scene.boxes.map (·.id)).Nodup := by
      rw [childMeta.ids]
      exact hchildNd
    have hfind := Assembly.keyed_lookup_eq Box.id child.scene.boxes hnd b hb
    rw [hid] at hfind
    exact ⟨b, hfind, hp.trans (congrArg ModelBox.parent he)⟩
  have hroot : ∀ m ∈ (childSubInput inp group).boxes, m.parent = "" → group.id ≠ "" := by
    intro m hm hp
    obtain ⟨src, hs, hin, _, hpar⟩ := selectInput_box_spec inp keep group.id hm
    have hne := inside_parent_ne_empty (Model.boxIds_nodup hwf) hin hs rfl
    by_cases he : src.parent = group.id
    · exact fun hgEmpty => hne (he.trans hgEmpty)
    · have hb : (src.parent == group.id) = false := beq_eq_false_iff_ne.mpr he
      exact (hne (by simpa [hpar, hb] using hp)).elim
  intro cb hcb x hx
  obtain ⟨m, hm, hid, _, _⟩ := childMeta.sources cb hcb
  let n := (childSubInput inp group).boxes.length - 1
  have hpos : 0 < (childSubInput inp group).boxes.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem hm)
  have hlength : n + 1 = (childSubInput inp group).boxes.length := by
    dsimp only [n]
    omega
  have hterm : ParentReaches (childSubInput inp group).boxes n m.parent :=
    chainTerm_parentReaches hchildNd n m.parent
      (childFacts.term m hm n (Nat.le_of_eq hlength.symm))
  have hfuel : n + 1 + parent.scene.layoutDump.boxes.length ≤
      res.scene.layoutDump.boxes.length :=
    Nat.le_of_eq (by rw [hlength, hsum])
  change x ∈ LayoutDump.ancestors.go res.scene.layoutDump res.scene.layoutDump.boxes.length cb.id
  rw [hid]
  exact childWalkRejoinsParent hlookup hEmbed hKeep hroot n m hm hterm _ hfuel x hx

theorem r_stepC8aMergedAnchors_closed (exactIds : List String)
    (idSets : List (String × List String)) : R_StepC8aMergedAnchorsB exactIds idSets := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand _hfp hctx hparams
  have hfit := (expandChildFitClosedB_region exactIds idSets fuel P inp o group titleLines
    titleHeight parent child res hexpand hctx hparams).1
  exact (stepC8aMergeFacts _ (frameRegionLeaf exactIds idSets) hexpand hctx hparams hfit).2.2

/-- Exact box identity/metadata and fixed reservations at the flat leaf,
    together with its executed inset, close the recursive C8a merge. -/
theorem stepC8aB_of_boxMirror
    (base : Input → Options → Except LayoutError FamilyResult)
    (leaf : ∀ inp o res, base inp o = .ok res → NotesBoxMirror inp res ∧ FixedBoxDimensions inp res)
    (hFlat : FlatInsetB base) : RecursiveStepFactsB base ExpandChildC8aStep := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hfp hctx hparams
  have hAllFit := expandChildFitClosedB_of_fixedBoxDimensions base leaf
  have hfit := (hAllFit fuel P inp o group titleLines titleHeight parent child res
    hexpand hctx hparams).1
  obtain ⟨hchildLen, hparentLen, hanchors⟩ := stepC8aMergeFacts base leaf
    hexpand hctx hparams hfit
  obtain ⟨hwf, hg, _, hchild, hparent, _⟩ := hctx
  obtain ⟨hwfc, hwfp⟩ := subInputWellFormedC2 inp o group hwf
  have hfc := (framedParentsSub inp o group hwf hfp).1
  have hP : checkedParams (childSubOptions o group).profile (childSubInput inp group).kind =
      .ok P := hparams.1
  have hChildInset := (layoutRecursiveB_inset base hFlat subInputWellFormedC2 hAllFit
    fuel _ _ _ hwfc hfc hchild P hP).2
  have parentMeta := recursiveFrameMetadata base leaf fuel (hwfp _ _ _) hparent
  have childMeta := recursiveFrameMetadata base leaf fuel hwfc hchild
  have hgmem := List.mem_of_find?_eq_some hg
  have hisolated := stepC8aGroupIsolated_of_metadata (P := P) (titleLines := titleLines)
    (child := child) hwf hgmem parentMeta
  have hgrole : group.role = .group := by
    have htest := List.find?_some hg
    simp only [Bool.and_eq_true] at htest
    have hi := htest.1
    unfold Compound.independent at hi
    simp only [Bool.and_eq_true] at hi
    exact beq_iff_eq.mp hi.1.1
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨hcontains, hembed, hkeep⟩ := hfit frame tl dx dy hframe hdx hdy hwrap
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  obtain ⟨src, hsrc, hid, _, hrole⟩ := parentMeta.sources frame (List.mem_of_find?_eq_some hframe)
  obtain ⟨m, hm, hnotin, hsid, _, hsr⟩ := selectedFrameSource inp
    (fun b => !Compound.inside inp.boxes group.id b.id) "" hsrc
  have hmid : m.id = group.id := (hid.trans hsid).symm.trans hframeId
  have hsource : m = group := eq_of_mem_id (Model.boxIds_nodup hwf) hm hgmem hmid
  have hframeRole : frame.role = "group" := by
    rw [hrole, hsr, hsource, hgrole] <;> rfl
  refine ⟨hembed, hkeep, hchildLen, hparentLen, hframeRole, ?_, ?_, hanchors, hisolated⟩
  · intro cb hcb heq
    obtain ⟨s, hs, hci, _, _⟩ := childMeta.sources cb hcb
    obtain ⟨n, _, hin, hsi, _⟩ := selectInput_box_spec inp
      (fun b => Compound.inside inp.boxes group.id b.id) group.id hs
    have hni : n.id = m.id := (hci.trans hsi).symm.trans (heq.trans hmid.symm)
    change Compound.inside inp.boxes group.id n.id = true at hin
    rw [hni] at hin
    change (!Compound.inside inp.boxes group.id m.id) = true at hnotin
    simp [hin] at hnotin
  · intro cb hcb
    exact hcontains.trans ((contained_shiftRect dx dy).mpr (hChildInset cb hcb))

theorem r_layoutRecursive_c8a_closed (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB (frameRegionBase exactIds idSets) fuel inp o = .ok res →
      Validator.C8a res.scene.layoutDump :=
  layoutRecursiveB_c8a (frameRegionBase exactIds idSets)
    (flatC8aB_layoutRIds_reindex_closed exactIds idSets)
    (subInputWellFormedB_layoutRIds exactIds idSets)
    (stepC8a_layoutRIds exactIds idSets (r_stepC8aGeometry_closed exactIds idSets)
      (stepC8aAncestry_layoutRIds exactIds idSets
        (r_stepC8aMergedAnchors_closed exactIds idSets)
        (r_stepC8aGroupIsolated_closed exactIds idSets)))

theorem r_layoutFamily_c8a_closed {exactIds : List String} {sets : List ModelRegionSet}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamilyR exactIds sets inp o = .ok res) : Validator.C8a res.scene.layoutDump := by
  unfold layoutFamilyR at h
  cases he : RegionImpl.graphRegions inp sets with
  | error err => simp [he] at h
  | ok idSets =>
    have hB : layoutFamilyB (frameRegionBase exactIds idSets) inp o = .ok res := by
      simpa only [he] using h
    obtain ⟨hwf, hrun⟩ := layoutFamilyB_success hB
    exact r_layoutRecursive_c8a_closed exactIds idSets _ inp o res
      hwf (layoutFamilyB_framed_parents hB) hrun

end Elegant.Layered.PipelineImpl
