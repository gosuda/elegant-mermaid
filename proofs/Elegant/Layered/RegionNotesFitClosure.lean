import Elegant.Layered.NotesDimensionsInduction
import Elegant.Layered.NotesGeomC68Proof
import Elegant.Layered.RegionFixedBoxDominance
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.SubInputWellFormedFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- A box drawn for an id with a fixed reservation is at least as large as
    the first reservation for that id. This also makes sense on contracted
    inputs that no longer satisfy `WellFormed`. -/
def FixedBoxDimensions (inp : Input) (res : FamilyResult) : Prop :=
  ∀ box ∈ res.scene.boxes, ∀ entry : String × Size,
    inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = some entry →
    entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h

private theorem notesFit_mapM_mem {α β : Type} {f : α → Except LayoutError β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = .ok y := by
  obtain ⟨hlen, hruns⟩ := mapM_getElem? f xs ys h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hy
  have hx : i < xs.length := hlen ▸ (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨val, hrun, hval⟩ := hruns i xs[i] (List.getElem?_eq_getElem hx)
  have hEq : val = y := Option.some.inj (hval.symm.trans hi)
  subst val
  exact ⟨xs[i], List.getElem_mem hx, hrun⟩

private theorem contractFold_keeps_fixed_lookup (layouts : List BundleLayout)
    (inp : Input) {id : String} {entry : String × Size}
    (hnotTop : ∀ l ∈ layouts, id ≠ l.top.id)
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == id) = some entry) :
    (layouts.foldl contractOne inp).fixedSizes.find? (fun row => row.1 == id) = some entry := by
  induction layouts generalizing inp with
  | nil => exact hfixed
  | cons l rest ih =>
    rw [List.foldl_cons]
    apply ih (contractOne inp l) (fun other ho => hnotTop other (List.mem_cons_of_mem _ ho))
    have hne := hnotTop l List.mem_cons_self
    have hfilter : (inp.fixedSizes.filter (·.1 != l.top.id)).find?
        (fun row => row.1 == id) = some entry := by
      rw [List.find?_filter, ← hfixed]
      congr 1
      funext row
      by_cases he : row.1 = id <;> simp [he, hne]
    change ((inp.fixedSizes.filter (·.1 != l.top.id)) ++ [(l.top.id, l.footprint.size)]).find?
      (fun row => row.1 == id) = some entry
    simp [List.find?_append, hfilter]

/-- Executed note placement preserves fixed-size minima supplied by the flat
    worker, even though contracting a bundle replaces its top's reservation.
    Every such top has a placed fragment and therefore cannot use that
    replacement as a fallback rectangle. -/
theorem layoutNotes_fixedBoxDimensions
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (hMirror : ∀ ids inp o res, base ids inp o = .ok res → NotesBoxMirror inp res)
    (hDim : ∀ ids inp o res, base ids inp o = .ok res → FixedBoxDimensions inp res)
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutNotes base exactIds fuel inp o = .ok res) : FixedBoxDimensions inp res := by
  induction fuel generalizing inp o res with
  | zero => exact hDim exactIds inp o res h
  | succ fuel ih =>
    rcases layoutNotes_success_phases h with ⟨_, hflat⟩ | ⟨⟨e⟩⟩
    · exact hDim exactIds inp o res hflat
    intro box hb entry hfixed
    obtain ⟨source, _, hid, _, _, _, hrect⟩ := e.boxes_mem box hb
    rw [← hid] at hrect
    rcases classifyRect hrect with ⟨p, hp, hplaced⟩ | ⟨hnone, b, hb, hbid, hbrect⟩
    · obtain ⟨l, hl, hplace⟩ := placedFlatten_mem e.placed_eq hp
      obtain ⟨_, _, hrun⟩ := notesFit_mapM_mem e.layouts_eq hl
      obtain ⟨hpart, hnotes⟩ := bundleLayout_part_note_runs hrun
      obtain ⟨sb, hsb, hsid, hshift⟩ := Placed.rect_scene_box hplaced
      have hfixedSb : inp.fixedSizes.find? (fun row => row.1 == sb.id) = some entry := by
        rwa [hsid]
      rcases placedOf_scene hplace with hs | ⟨q, hq, hs⟩
      · rw [hs] at hsb
        rw [← hshift]
        exact ih hpart sb hsb entry hfixedSb
      · rw [hs] at hsb
        rw [← hshift]
        exact hDim _ _ _ _ (hnotes q hq) sb hsb entry hfixedSb
    · have hfound := notesC8aFragFound_of_base e (notesBaseFrag_of_box_mirror hMirror e)
      have hnotTop : ∀ l ∈ e.layouts, box.id ≠ l.top.id := by
        intro l hl heq
        have hf : fragmentIdOf inp l box.id = true := by simp [fragmentIdOf, heq]
        obtain ⟨p, hp, hh⟩ := List.any_eq_true.mp (hfound l hl box.id hf)
        obtain ⟨b', hb', ht⟩ := List.any_eq_true.mp hh
        have hhas : (p.scene.boxes.find? (fun candidate => candidate.id == box.id)).isSome = true :=
          List.find?_isSome.mpr ⟨b', hb', ht⟩
        cases hlookup : p.scene.boxes.find? (fun candidate => candidate.id == box.id) with
        | none => simp [hlookup] at hhas
        | some found =>
          exact hnone p (placedOf_mem_flatten e.placed_eq hl hp)
            (shiftRect p.dx p.dy found.rect) (by simp [Placed.rect, hlookup])
      have hfixedCon : e.contractedInput.fixedSizes.find? (fun row => row.1 == b.id) = some entry := by
        rw [e.contractedInput_eq, hbid]
        exact contractFold_keeps_fixed_lookup e.layouts inp hnotTop hfixed
      rw [← hbrect]
      exact hDim _ _ _ _ e.contracted_eq b hb entry hfixedCon

private theorem layoutRIds_fixedBoxDimensions
    {ids : List String} {sets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRIds ids sets inp o = .ok res) : FixedBoxDimensions inp res := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  intro box hb entry hfixed
  obtain ⟨i, hbi⟩ := List.mem_iff_getElem?.mp hb
  have hlookup := hbi
  rw [execution.boxes_eq_mapR, List.getElem?_map, List.getElem?_zipIdx] at hlookup
  cases hs : inp.boxes[i]? with
  | none => simp [hs] at hlookup
  | some source =>
    simp only [hs, Option.map_some, Option.some.injEq, Nat.zero_add] at hlookup
    have hid : source.id = box.id := congrArg Box.id hlookup
    rw [← hid] at hfixed
    exact R_fixedBoxDominates_holds ids sets execution hbi hs hfixed

private theorem noteFit_regionBoxMirror (idSets : List (String × List String))
    (ids : List String) (inp : Input) (o : Options) (res : FamilyResult)
    (h : layoutRIds ids (reindexRegionSets idSets inp) inp o = .ok res) :
    NotesBoxMirror inp res :=
  layoutRIds_boxes_mirror h

/-- Successful note-wrapped region layouts honor fixed-size reservations. -/
theorem layoutRegionNotes_fixedBoxDimensions (idSets : List (String × List String))
    {exactIds : List String} {outerFuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutNotes (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds outerFuel inp o = .ok res) : FixedBoxDimensions inp res :=
  layoutNotes_fixedBoxDimensions (noteFit_regionBoxMirror idSets)
    (fun _ _ _ _ hRegion => layoutRIds_fixedBoxDimensions hRegion) h

private structure RecursiveFitBoxFacts (inp : Input) (res : FamilyResult) : Prop where
  ids : res.scene.boxes.map (·.id) = inp.boxes.map (·.id)
  parentMirror : ∀ b ∈ res.scene.boxes, ∃ src ∈ inp.boxes, b.id = src.id ∧ b.parent = src.parent
  fixed : FixedBoxDimensions inp res

private theorem recursiveB_fitBoxFacts
    (base : Input → Options → Except LayoutError FamilyResult)
    (hBase : ∀ inp o res, base inp o = .ok res → NotesBoxMirror inp res ∧ FixedBoxDimensions inp res)
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (h : layoutRecursiveB base fuel inp o = .ok res) :
    RecursiveFitBoxFacts inp res := by
  have leaf : ∀ {i opts r}, base i opts = .ok r → RecursiveFitBoxFacts i r := by
    intro i opts r hflat
    obtain ⟨hm, hd⟩ := hBase i opts r hflat
    refine ⟨hm.1, ?_, hd⟩
    intro b hb
    obtain ⟨s, hs, hid, hp, _, _⟩ := hm.2 b hb
    exact ⟨s, hs, hid, hp⟩
  induction fuel generalizing inp o res with
  | zero => exact leaf h
  | succ fuel ih =>
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hflat⟩ |
      ⟨group, P, _, child, titleLines, parent, _, _, _, hchild, _, hparent, hexpand⟩
    · exact leaf hflat
    change layoutRecursiveB base fuel (childSubInput inp group) (childSubOptions o group) =
      .ok child at hchild
    change layoutRecursiveB base fuel (parentSubInput inp group P titleLines child) o =
      .ok parent at hparent
    obtain ⟨hwfc, hwfp⟩ := subInputWellFormedC2 inp o group hwf
    have hc := ih hwfc hchild
    have hp := ih (hwfp _ _ _) hparent
    obtain ⟨_, _, _, _, dx, dy, _, _, _, _, _, _, _, hboxes⟩ := expandChild_sources hexpand
    let inside := fun b : ModelBox => Compound.inside inp.boxes group.id b.id
    let merged := child.scene.boxes.map (embedBox group.id dx dy) ++ parent.scene.boxes
    change res.scene.boxes = inp.boxes.filterMap
      (fun src => merged.find? (fun b => b.id == src.id)) at hboxes
    have hcids : child.scene.boxes.map (·.id) = (inp.boxes.filter inside).map (·.id) :=
      hc.ids.trans (selectInput_box_ids inp inside group.id)
    have hpids : parent.scene.boxes.map (·.id) =
        (inp.boxes.filter fun b => !inside b).map (·.id) :=
      hp.ids.trans (selectInput_box_ids inp (fun b => !inside b) "")
    have hcover : ∀ id ∈ inp.boxes.map (·.id), ∃ b ∈ merged, b.id = id := by
      intro id hid
      obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hid
      by_cases hin : inside src = true
      · have hmem : src.id ∈ child.scene.boxes.map (·.id) := by
          rw [hcids]
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hsrc, hin⟩)
        obtain ⟨b, hb, hid⟩ := List.mem_map.mp hmem
        exact ⟨embedBox group.id dx dy b, List.mem_append_left _ (List.mem_map_of_mem hb), hid⟩
      · have hmem : src.id ∈ parent.scene.boxes.map (·.id) := by
          rw [hpids]
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hsrc, by simpa using hin⟩)
        obtain ⟨b, hb, hid⟩ := List.mem_map.mp hmem
        exact ⟨b, List.mem_append_right _ hb, hid⟩
    have hids : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
      rw [hboxes]
      exact filterMap_find_ids Box.id (inp.boxes.map (·.id)) merged hcover
        inp.boxes ModelBox.id rfl
    have horigin : ∀ b ∈ res.scene.boxes,
        (∃ c ∈ child.scene.boxes, embedBox group.id dx dy c = b) ∨ b ∈ parent.scene.boxes := by
      intro b hb
      rw [hboxes] at hb
      obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hb
      have hm := List.mem_of_find?_eq_some hfind
      change b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++ parent.scene.boxes at hm
      exact (List.mem_append.mp hm).imp List.mem_map.mp id
    refine ⟨hids, ?_, ?_⟩
    · intro b hb
      rcases horigin b hb with ⟨c, hcm, rfl⟩ | hpm
      · obtain ⟨s, hs, hsid, hsp⟩ := hc.parentMirror c hcm
        obtain ⟨m, hm, hkept, hmid, hmp⟩ := selectInput_box_spec inp inside group.id hs
        have hne := inside_parent_ne_empty (Model.boxIds_nodup hwf)
          (show Compound.inside inp.boxes group.id m.id = true from hkept) hm rfl
        refine ⟨m, hm, hsid.trans hmid, ?_⟩
        change (if c.parent == "" then group.id else c.parent) = m.parent
        rw [hsp, hmp]
        exact embed_parent_eq hne
      · obtain ⟨s, hs, hsid, hsp⟩ := hp.parentMirror b hpm
        obtain ⟨m, hm, _, hmid, hmp⟩ := selectInput_box_spec inp (fun q => !inside q) "" hs
        exact ⟨m, hm, hsid.trans hmid, hsp.trans (hmp.trans (selectInput_parent_root m.parent))⟩
    · intro b hb entry hfixed
      rcases horigin b hb with ⟨c, hcm, rfl⟩ | hpm
      · exact hc.fixed c hcm entry hfixed
      · apply hp.fixed b hpm entry
        change (inp.fixedSizes ++ _).find? (fun row => row.1 == b.id) = some entry
        simp [List.find?_append, hfixed]

private theorem RecursiveFitBoxFacts.parentClosed {inp : Input} {o : Options}
    {res : FamilyResult} (facts : RecursiveFitBoxFacts inp res)
    (hwf : WellFormed (inputModel inp o)) : SceneParentClosed res.scene := by
  intro b hb
  obtain ⟨s, hs, _, hparent⟩ := facts.parentMirror b hb
  rw [hparent]
  rcases (inputFacts_of_wellFormed hwf).parents s hs with hroot | ⟨p, hp, heq⟩
  · exact Or.inl hroot
  · have hid : p.id ∈ res.scene.boxes.map (·.id) := by
      rw [facts.ids]
      exact List.mem_map_of_mem hp
    obtain ⟨parent, hparent, hid⟩ := List.mem_map.mp hid
    exact Or.inr ⟨parent, hparent, hid.trans heq⟩

private theorem fitBoxLookupTransport {inp : Input} {group : ModelBox}
    {child parent res : FamilyResult} {dx dy : Int}
    (hboxes : res.scene.boxes = inp.boxes.filterMap (fun src =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++ parent.scene.boxes).find?
        (fun b => b.id == src.id)))
    (hc : child.scene.boxes.map (·.id) =
      (inp.boxes.filter (fun q => Compound.inside inp.boxes group.id q.id)).map (·.id))
    (hp : parent.scene.boxes.map (·.id) =
      (inp.boxes.filter (fun q => !Compound.inside inp.boxes group.id q.id)).map (·.id))
    (hdistinct : (res.scene.boxes.map (·.id)).Nodup) :
    (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some (embedBox group.id dx dy box)) ∧
    (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some box) := by
  let merge := child.scene.boxes.map (embedBox group.id dx dy) ++ parent.scene.boxes
  have emit (box : Box) (hId : box.id ∈ inp.boxes.map (·.id))
      (hFound : merge.find? (fun b => b.id == box.id) = some box) :
      res.scene.layoutDump.box? box.id = some box := by
    obtain ⟨src, hs, hsid⟩ := List.mem_map.mp hId
    have hm : box ∈ res.scene.boxes := by
      rw [hboxes]
      apply List.mem_filterMap.mpr
      refine ⟨src, hs, ?_⟩
      change merge.find? (fun b => b.id == src.id) = some box
      rw [hsid]
      exact hFound
    exact Assembly.keyed_lookup_eq Box.id res.scene.boxes hdistinct box hm
  constructor
  · intro box hbox
    change child.scene.boxes.find? (fun b => b.id == box.id) = some box at hbox
    have hi : box.id ∈ child.scene.boxes.map (·.id) :=
      List.mem_map_of_mem (List.mem_of_find?_eq_some hbox)
    rw [hc] at hi
    obtain ⟨src, hsrc, hsid⟩ := List.mem_map.mp hi
    have hid : (embedBox group.id dx dy box).id ∈ inp.boxes.map (·.id) :=
      List.mem_map.mpr ⟨src, (List.mem_filter.mp hsrc).1, hsid⟩
    apply emit _ hid
    change ((child.scene.boxes.map (embedBox group.id dx dy)) ++ parent.scene.boxes).find?
      (fun b => b.id == box.id) = some (embedBox group.id dx dy box)
    have hm : (child.scene.boxes.map (embedBox group.id dx dy)).find?
        (fun b => b.id == box.id) = some (embedBox group.id dx dy box) := by
      rw [List.find?_map]
      change (child.scene.boxes.find? (fun b => b.id == box.id)).map
        (embedBox group.id dx dy) = some (embedBox group.id dx dy box)
      simp only [hbox, Option.map_some]
    simp [List.find?_append, hm]
  · intro box hbox
    change parent.scene.boxes.find? (fun b => b.id == box.id) = some box at hbox
    have hi : box.id ∈ parent.scene.boxes.map (·.id) :=
      List.mem_map_of_mem (List.mem_of_find?_eq_some hbox)
    rw [hp] at hi
    obtain ⟨src, hsrc, hsid⟩ := List.mem_map.mp hi
    obtain ⟨hsrc, hout⟩ := List.mem_filter.mp hsrc
    apply emit box (List.mem_map.mpr ⟨src, hsrc, hsid⟩)
    have hnone : (child.scene.boxes.map (embedBox group.id dx dy)).find?
        (fun b => b.id == box.id) = none := by
      apply List.find?_eq_none.mpr
      intro b hb htest
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hb
      have hcid : c.id = box.id := beq_iff_eq.mp htest
      have hci : c.id ∈ child.scene.boxes.map (·.id) := List.mem_map_of_mem hcm
      rw [hc] at hci
      obtain ⟨cs, hcs, hcsid⟩ := List.mem_map.mp hci
      have hin := (List.mem_filter.mp hcs).2
      rw [hcsid, hcid, ← hsid] at hin
      simp [hin] at hout
    change ((child.scene.boxes.map (embedBox group.id dx dy)) ++ parent.scene.boxes).find?
      (fun b => b.id == box.id) = some box
    simp [List.find?_append, hnone, hbox]

/-- Fit and closure only need an id/parent mirror and a fixed-size minimum at
    the successful flat leaf. No route or flat C3 hypothesis is needed. -/
theorem expandChildFitClosedB_of_fixedBoxDimensions
    (base : Input → Options → Except LayoutError FamilyResult)
    (hBase : ∀ inp o res, base inp o = .ok res → NotesBoxMirror inp res ∧ FixedBoxDimensions inp res) :
    ExpandChildFitClosedB base := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hctx hparams
  obtain ⟨hP, htH, metric, hm, ht⟩ := hparams
  subst titleHeight
  obtain ⟨hwf, hg, _, hchild, hparent, _⟩ := hctx
  obtain ⟨hwfc, hwfp⟩ := subInputWellFormedC2 inp o group hwf
  have hwfParent : WellFormed (inputModel (parentSubInput inp group P titleLines child) o) :=
    hwfp _ _ _
  have hc := recursiveB_fitBoxFacts base hBase fuel hwfc hchild
  have hp := recursiveB_fitBoxFacts base hBase fuel hwfParent hparent
  have hrun : layoutRecursiveB base (fuel + 1) inp o = .ok res := by
    simp only [childSubInput, childSubOptions] at hchild
    simp only [parentSubInput] at hparent
    unfold layoutRecursiveB
    rw [hg]
    simp only [hP, hm, hchild, ht, hparent, hexpand, Bind.bind, Except.bind]
  have hres := recursiveB_fitBoxFacts base hBase (fuel + 1) hwf hrun
  have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hres.ids]
    exact Model.boxIds_nodup hwf
  refine ⟨?_, hp.parentClosed hwfParent, hc.parentClosed hwfc⟩
  intro frame tls dx dy hframe hdx hdy hwrap
  obtain ⟨metric', hm', ht'⟩ := hwrap
  have hmetric : metric' = metric := Except.ok.inj (hm'.symm.trans hm)
  rw [hmetric] at ht'
  have htl : tls = titleLines := Except.ok.inj (ht'.symm.trans ht)
  subst tls
  let tw := titleLines.foldl (fun width line => max width line.width) 0
  let th : Int := (max 1 titleLines.length : Int) * P.lineH
  let size := childFrameSize group.direction P.clusterPad tw th
    ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩
  have hnotFixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    have htest := List.find?_some hg
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at htest
    exact htest.2
  have hnone : inp.fixedSizes.find? (fun row => row.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hnotFixed)
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hfixed : (parentSubInput inp group P titleLines child).fixedSizes.find?
      (fun row => row.1 == frame.id) = some (group.id, size) := by
    change (inp.fixedSizes ++ [(group.id, size)]).find?
      (fun row => row.1 == frame.id) = some (group.id, size)
    simp [List.find?_append, hframeId, hnone]
  obtain ⟨hw, hh⟩ := hp.fixed frame (List.mem_of_find?_eq_some hframe) _ hfixed
  have htw : 0 ≤ tw := by
    suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
        0 ≤ ls.foldl (fun width line => max width line.width) acc by
      exact key titleLines 0 (by omega)
    intro ls
    induction ls with
    | nil => intro acc hacc; exact hacc
    | cons line rest ih =>
      intro acc hacc
      exact ih _ (Int.le_trans hacc (Int.le_max_left _ _))
  have hth : 0 ≤ th := Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
  refine ⟨?_, ?_⟩
  · rw [hdx, hdy]
    exact childInsetCanvas_contained htw hth (checkedParams_clusterPad_nonneg hP) hw hh
  · obtain ⟨frame', metric', tls, _, dx', dy', hf', hm', ht', _, hdx', hdy', _, hboxes⟩ :=
      expandChild_sources hexpand
    have hmf : metric' = metric := Except.ok.inj (hm'.symm.trans hm)
    rw [hmf] at ht'
    have hls : tls = titleLines := Except.ok.inj (ht'.symm.trans ht)
    have hfr : frame' = frame := Option.some.inj (hf'.symm.trans hframe)
    rw [hfr, hls] at hdx' hdy'
    rw [hdx.trans hdx'.symm, hdy.trans hdy'.symm]
    have hpids : (parentSubInput inp group P titleLines child).boxes.map (·.id) =
        (inp.boxes.filter fun q => !Compound.inside inp.boxes group.id q.id).map (·.id) := by
      have hsel := selectInput_box_ids inp
        (fun q => !Compound.inside inp.boxes group.id q.id) ""
      rw [show (parentSubInput inp group P titleLines child).boxes =
        (selectInput inp (fun q => !Compound.inside inp.boxes group.id q.id) "").boxes
        from rfl]
      exact hsel
    exact fitBoxLookupTransport hboxes
      (hc.ids.trans (selectInput_box_ids inp _ _))
      (hp.ids.trans hpids) hnodup

theorem expandChildFitClosedB_region (exactIds : List String)
    (idSets : List (String × List String)) :
    ExpandChildFitClosedB (fun sub opts =>
      layoutRIds exactIds (reindexRegionSets idSets sub) sub opts) := by
  apply expandChildFitClosedB_of_fixedBoxDimensions
  intro inp o res h
  exact ⟨layoutRIds_boxes_mirror h, layoutRIds_fixedBoxDimensions h⟩

/-- Recursive expansion over the note-wrapped region base fits the child inset
    inside its frame and preserves lookup and parent closure. -/
theorem expandChildFitClosedB_regionNotes (exactIds : List String)
    (idSets : List (String × List String)) (outerFuel : Nat) :
    ExpandChildFitClosedB (layoutNotes
      (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds outerFuel) := by
  apply expandChildFitClosedB_of_fixedBoxDimensions
  intro inp o res h
  exact ⟨layoutNotes_boxes_mirror (noteFit_regionBoxMirror idSets) outerFuel h,
    layoutRegionNotes_fixedBoxDimensions idSets h⟩

end Elegant.Layered.PipelineImpl
