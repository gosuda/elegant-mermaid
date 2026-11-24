import Elegant.Layered.NotesLabelGeomFacts
import Elegant.Layered.RegionNotesCanvasMargins
import Elegant.Layered.RegionNotesFitClosure
import Elegant.Layered.RegionPartSizingClosed
import Elegant.Layered.NotesGeomC68Proof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private abbrev regionNoteBase (idSets : List (String × List String)) :
    List String → Input → Options → Except LayoutError FamilyResult :=
  fun ids sub o => layoutRIds ids (reindexRegionSets idSets sub) sub o

private def noteSizes (margin : Int) (l : BundleLayout) : List (Size × Bool) :=
  (l.notes.zip l.bundle.notes).map fun q => (sceneSize margin q.1.2.scene, q.2.right)

private theorem mapMRunsOfMem {α β : Type} {f : α → Except LayoutError β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = .ok y := by
  obtain ⟨hlen, hruns⟩ := mapM_getElem? f xs ys h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hy
  have hbound : i < xs.length := hlen ▸ (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨z, hrun, hz⟩ := hruns i xs[i] (List.getElem?_eq_getElem hbound)
  have heq : z = y := Option.some.inj (hz.symm.trans hi)
  exact ⟨xs[i], List.getElem_mem hbound, hrun.trans (congrArg Except.ok heq)⟩

private theorem bundleSource {recur base : Input → Options → Except LayoutError FamilyResult}
    {inp : Input} {o : Options} {m g : Int} {b : Bundle} {l : BundleLayout}
    (h : bundleLayout recur base inp o m g b = .ok l) :
    inp.boxes[b.target]? = some l.top ∧
      l.footprint = footprint g (sceneSize m l.part.scene) (noteSizes m l) := by
  unfold bundleLayout at h
  cases htop : inp.boxes[b.target]? with
  | none => rw [htop] at h; simp at h
  | some top =>
    rw [htop] at h
    obtain ⟨part, _, h⟩ := bind_ok' h
    obtain ⟨notes, _, h⟩ := bind_ok' h
    have hl : (⟨top, b, part, notes, _⟩ : BundleLayout) = l := Except.ok.inj h
    subst l
    exact ⟨rfl, rfl⟩

private theorem bundleStartsWithAttach {boxes : List ModelBox} {atts : List Attach}
    (acc : List Bundle) (remaining : List Attach) {b : Bundle}
    (hb : b ∈ remaining.foldl (fun acc a =>
      if isNested boxes atts a.target || acc.any (·.target == a.target) then acc
      else acc ++ [⟨a.target, atts.filter (·.target == a.target)⟩]) acc) :
    b ∈ acc ∨ ∃ a ∈ remaining, b = ⟨a.target, atts.filter (·.target == a.target)⟩ := by
  induction remaining generalizing acc with
  | nil => exact Or.inl hb
  | cons a remaining ih =>
    rw [List.foldl_cons] at hb
    split at hb
    · rcases ih acc hb with hm | ⟨a', ha', heq⟩
      · exact Or.inl hm
      · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', heq⟩
    · rcases ih _ hb with hm | ⟨a', ha', heq⟩
      · rcases List.mem_append.mp hm with hacc | hnew
        · exact Or.inl hacc
        · exact Or.inr ⟨a, List.mem_cons_self, List.mem_singleton.mp hnew⟩
      · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', heq⟩

private theorem bundleCanonical {boxes : List ModelBox} {b : Bundle} {top : ModelBox}
    (hb : b ∈ bundlesOf boxes (attachmentsOf boxes)) (htop : boxes[b.target]? = some top) :
    boxes.findIdx? (·.id == top.id) = some b.target ∧
      b.notes = (attachmentsOf boxes).filter (·.target == b.target) := by
  rcases bundleStartsWithAttach (boxes := boxes) [] (attachmentsOf boxes) hb with
    hn | ⟨a, ha, rfl⟩
  · simp at hn
  refine ⟨?_, rfl⟩
  change boxes[a.target]? = some top at htop
  unfold attachmentsOf at ha
  obtain ⟨q, _, hrow⟩ := List.mem_filterMap.mp ha
  change (if q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right") then
    (noteTargetId q.1.id).bind fun id =>
      (boxes.findIdx? (·.id == id)).map fun i => ⟨i, q.2, q.1.direction == "right"⟩
    else none) = some a at hrow
  split at hrow
  · obtain ⟨id, _, hindex⟩ := Option.bind_eq_some_iff.mp hrow
    obtain ⟨i, hi, hattach⟩ := Option.map_eq_some_iff.mp hindex
    have ht : a.target = i := (congrArg Attach.target hattach).symm
    rw [ht] at htop ⊢
    obtain ⟨hiBound, hiMatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
    have heq : boxes[i] = top := Option.some.inj ((List.getElem?_eq_getElem hiBound).symm.trans htop)
    have hid : top.id = id := by
      change (boxes[i].id == id) = true at hiMatch
      rw [heq] at hiMatch
      exact beq_iff_eq.mp hiMatch
    rw [hid]
    exact hi
  · simp at hrow

private theorem sameTopLayout {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {a b : BundleLayout}
    (ha : a ∈ e.layouts) (hb : b ∈ e.layouts) (hid : a.top.id = b.top.id) : a = b := by
  obtain ⟨x, hx, hrunx⟩ := mapMRunsOfMem e.layouts_eq ha
  obtain ⟨y, hy, hruny⟩ := mapMRunsOfMem e.layouts_eq hb
  rw [e.bundles_eq, e.atts_eq] at hx hy
  obtain ⟨hix, hnx⟩ := bundleCanonical hx (bundleSource hrunx).1
  obtain ⟨hiy, hny⟩ := bundleCanonical hy (bundleSource hruny).1
  rw [hid] at hix
  have ht : x.target = y.target := Option.some.inj (hix.symm.trans hiy)
  have hn : x.notes = y.notes := by rw [hnx, hny, ht]
  have heq : x = y := by
    cases x with
    | mk tx nx =>
      cases y with
      | mk ty ny =>
        change tx = ty at ht
        change nx = ny at hn
        cases ht
        cases hn
        rfl
  subst y
  exact Except.ok.inj (hrunx.symm.trans hruny)

private theorem contractReservation (ls : List BundleLayout) (inp : Input) (l : BundleLayout)
    (heq : ∀ k ∈ ls, k.top.id = l.top.id → k = l)
    (h : l ∈ ls ∨ (inp.fixedSizes.find? (·.1 == l.top.id)) = some (l.top.id, l.footprint.size)) :
    (ls.foldl contractOne inp).fixedSizes.find? (·.1 == l.top.id) =
      some (l.top.id, l.footprint.size) := by
  induction ls generalizing inp with
  | nil => exact h.resolve_left (by simp)
  | cons k ls ih =>
    rw [List.foldl_cons]
    refine ih _ (fun q hq => heq q (List.mem_cons_of_mem _ hq)) ?_
    by_cases hk : k.top.id = l.top.id
    · have he := heq k List.mem_cons_self hk
      subst k
      apply Or.inr
      change ((inp.fixedSizes.filter (·.1 != l.top.id)) ++ [(l.top.id, l.footprint.size)]).find?
        (·.1 == l.top.id) = some (l.top.id, l.footprint.size)
      rw [List.find?_append]
      have hf : (inp.fixedSizes.filter (·.1 != l.top.id)).find? (·.1 == l.top.id) = none := by
        rw [List.find?_filter, List.find?_eq_none]
        intro row _
        by_cases hid : row.1 = l.top.id <;> simp [hid]
      simp [hf]
    · rcases h with hm | hf
      · exact Or.inl ((List.mem_cons.mp hm).resolve_left
          (fun hkl => hk (congrArg (fun q : BundleLayout => q.top.id) hkl).symm))
      · apply Or.inr
        have hfiltered : (inp.fixedSizes.filter (·.1 != k.top.id)).find? (·.1 == l.top.id) =
            some (l.top.id, l.footprint.size) := by
          rw [List.find?_filter, ← hf]
          congr 1
          funext row
          by_cases hrow : row.1 = l.top.id <;> simp [hrow, Ne.symm hk]
        change ((inp.fixedSizes.filter (·.1 != k.top.id)) ++ [(k.top.id, k.footprint.size)]).find?
          (·.1 == l.top.id) = some (l.top.id, l.footprint.size)
        simp [List.find?_append, hfiltered]

private theorem footprintOfExecution {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNoteBase idSets) exactIds fuel inp o res)
    {l : BundleLayout} (hl : l ∈ e.layouts) :
    l.footprint = footprint e.gap (sceneSize e.margin l.part.scene) (noteSizes e.margin l) ∧
    (l.footprint.target :: l.footprint.notes).Pairwise Disjoint ∧
    ∀ r ∈ l.footprint.target :: l.footprint.notes,
      (Rect.mk 0 0 l.footprint.size.w l.footprint.size.h).Contained r := by
  obtain ⟨_, _, hrun⟩ := mapMRunsOfMem e.layouts_eq hl
  have heq := (bundleSource hrun).2
  obtain ⟨hpart, hnotes⟩ := bundleLayout_part_note_runs hrun
  have hpartW : 0 ≤ (sceneSize e.margin l.part.scene).w := by
    have hb := (canvasMarginsN_rngNotesBase exactIds idSets fuel) 0 _ o l.part hpart
      e.params (by exact e.checked)
    have hw := hb.1
    simp only [sceneSize, e.margin_eq]
    omega
  have hnotesSize : ∀ n ∈ noteSizes e.margin l, 0 ≤ n.1.w ∧ 0 ≤ n.1.h := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
    have hNoteMem : q.1 ∈ l.notes := (List.of_mem_zip hq).1
    have hb := (canvasMarginsN_rngNotesBase exactIds idSets 0) 0 _ o q.1.2
      (hnotes q.1 hNoteMem) e.params (by exact e.checked)
    simp only [sceneSize, e.margin_eq]
    exact ⟨by have hw := hb.1; omega, by have hh := hb.2; omega⟩
  have hgap : 0 < e.gap := by
    have hslot := (checkedParams_valid e.checked).2.2.1
    rw [e.gap_eq]
    omega
  refine ⟨heq, ?_⟩
  rw [heq]
  obtain ⟨hpartNote, hnoteNote, hfit⟩ := footprint_notes_disjoint_target _ hgap _ _ hpartW hnotesSize
  exact ⟨List.pairwise_cons.mpr ⟨hpartNote, hnoteNote⟩, hfit⟩

private def placeFrom (origin : Rect) (margin : Int) (r : Rect) (scene : Scene) : Placed :=
  ⟨scene, origin.x + r.x - margin, origin.y + r.y - margin⟩

private theorem placedIndexSource {contracted : Scene} {l : BundleLayout} {m g : Int}
    {envelope : Box} {i : Nat} {p : Placed}
    (hEnv : contracted.boxes.find? (·.id == l.top.id) = some envelope)
    (hFoot : l.footprint = footprint g (sceneSize m l.part.scene) (noteSizes m l))
    (hp : (placedOf' m contracted l)[i]? = some p) :
    ∃ r, (l.footprint.target :: l.footprint.notes)[i]? = some r ∧
      p = placeFrom envelope.rect m r p.scene ∧
      r.w = p.scene.canvas.w - 2 * m ∧ r.h = p.scene.canvas.h - 2 * m := by
  have hlist : placedOf' m contracted l =
      placeFrom envelope.rect m l.footprint.target l.part.scene ::
      (l.notes.zip l.footprint.notes).map (fun q => placeFrom envelope.rect m q.2 q.1.2.scene) := by
    simp only [placedOf', placedFragments, hEnv, pure, Except.pure, placeFrom]
  rw [hlist] at hp
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst p
    exact ⟨l.footprint.target, rfl, rfl,
      by simp only [hFoot, footprint_target, sceneSize, placeFrom],
      by simp only [hFoot, footprint_target, sceneSize, placeFrom]⟩
  | succ i =>
    rw [List.getElem?_cons_succ, List.getElem?_map] at hp
    obtain ⟨pair, hpair, hplaced⟩ := Option.map_eq_some_iff.mp hp
    subst p
    obtain ⟨hnote, hrect⟩ := List.getElem?_zip_eq_some.mp hpair
    refine ⟨pair.2, hrect, rfl, ?_⟩
    rw [hFoot, footprint_notes, List.getElem?_mapIdx] at hrect
    obtain ⟨sz, hsz, hrectangle⟩ := Option.map_eq_some_iff.mp hrect
    rw [noteSizes, List.getElem?_map] at hsz
    obtain ⟨source, hsource, hsize⟩ := Option.map_eq_some_iff.mp hsz
    have hsame : source.1 = pair.1 :=
      Option.some.inj ((List.getElem?_zip_eq_some.mp hsource).1.symm.trans hnote)
    rw [← hrectangle, ← hsize]
    simp [noteRect, sceneSize, placeFrom, hsame]

private theorem shiftedBoxInFootprint {m : Int} {origin r : Rect} {p : Placed} {b : Box}
    (hp : p = placeFrom origin m r p.scene)
    (hw : r.w = p.scene.canvas.w - 2 * m) (hh : r.h = p.scene.canvas.h - 2 * m)
    (hbox : (insetRect p.scene.canvas m).Contained b.rect) :
    (shiftRect origin.x origin.y r).Contained (shiftRect p.dx p.dy b.rect) := by
  have hx : p.dx = origin.x + r.x - m := congrArg Placed.dx hp
  have hy : p.dy = origin.y + r.y - m := congrArg Placed.dy hp
  unfold Rect.Contained insetRect at hbox
  unfold Rect.Contained shiftRect
  dsimp only at hbox ⊢
  omega

private theorem shiftedSubrectsDisjoint {origin r s a b : Rect} (h : Disjoint r s)
    (ha : (shiftRect origin.x origin.y r).Contained a)
    (hb : (shiftRect origin.x origin.y s).Contained b) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior at h ⊢
  unfold Rect.Contained shiftRect at ha hb
  dsimp only at ha hb
  intro hab
  apply h
  omega

private theorem regionFlatInset (ids : List String) (idSets : List (String × List String)) :
    FlatInsetB (regionNoteBase idSets ids) :=
  flatInsetB_layoutRIds_reindex ids idSets (fun inp =>
    R_partSizingRResidual_holds ids (reindexRegionSets idSets inp))

private theorem insetAtMargin {profile : Profile} {kind : String} {P : Params} {m : Int}
    {s : Scene} (hP : checkedParams profile kind = .ok P) (hm : m = P.canvasMargin)
    (h : ∃ Q : Params, checkedParams profile kind = .ok Q ∧
      0 ≤ Q.canvasMargin ∧ InsetC1 s Q.canvasMargin) : InsetC1 s m := by
  obtain ⟨Q, hQ, _, hfit⟩ := h
  have heq : Q = P := Except.ok.inj (hQ.symm.trans hP)
  subst Q
  rwa [hm]

private theorem fragmentInsets {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNoteBase idSets) exactIds fuel inp o res)
    (hPart : FlatInsetB (layoutNotes (regionNoteBase idSets) exactIds fuel))
    {l : BundleLayout} (hl : l ∈ e.layouts)
    {p : Placed} (hp : p ∈ placedOf' e.margin e.contracted.scene l) : InsetC1 p.scene e.margin := by
  obtain ⟨_, _, hrun⟩ := mapMRunsOfMem e.layouts_eq hl
  obtain ⟨hpart, hnotes⟩ := bundleLayout_part_note_runs hrun
  rcases placedOf_scene hp with hscene | ⟨q, hq, hscene⟩
  · rw [hscene]
    let partInput := subInput inp
      (fun x => x.id == l.top.id || Compound.inside inp.boxes l.top.id x.id) l.top.id
    have hInset := hPart partInput o l.part hpart
    have hKind : partInput.kind = inp.kind := rfl
    have hChecked : checkedParams o.profile partInput.kind = .ok e.params := by
      rw [hKind]
      exact e.checked
    exact insetAtMargin hChecked e.margin_eq hInset
  · rw [hscene]
    let noteInput := subInput inp (fun x => x.id == q.1.id) q.1.id
    have hFlat := regionFlatInset exactIds idSets
    have hInset := hFlat noteInput o q.2 (hnotes q hq)
    have hKind : noteInput.kind = inp.kind := rfl
    have hChecked : checkedParams o.profile noteInput.kind = .ok e.params := by
      rw [hKind]
      exact e.checked
    exact insetAtMargin hChecked e.margin_eq hInset

private theorem contractKind (ls : List BundleLayout) (inp : Input) :
    (ls.foldl contractOne inp).kind = inp.kind := by
  induction ls generalizing inp with
  | nil => rfl
  | cons _ _ ih => exact ih _

private theorem noPlacedWithoutEnvelope {m : Int} {contracted : Scene} {l : BundleLayout}
    {p : Placed} (hp : p ∈ placedOf' m contracted l)
    (hEnv : contracted.boxes.find? (fun b : Box => b.id == l.top.id) = none) : False := by
  simp only [placedOf'] at hp
  unfold placedFragments at hp
  rw [hEnv] at hp
  exact absurd (show p ∈ ([] : List Placed) from hp) (by simp)

private theorem fragmentInEnvelope {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNoteBase idSets) exactIds fuel inp o res)
    (hPart : FlatInsetB (layoutNotes (regionNoteBase idSets) exactIds fuel))
    {l : BundleLayout} (hl : l ∈ e.layouts) {p : Placed}
    (hp : p ∈ placedOf' e.margin e.contracted.scene l) {sb : Box} (hsb : sb ∈ p.scene.boxes)
    {env : Box} (hEnv : e.contracted.scene.boxes.find? (·.id == l.top.id) = some env) :
    env.rect.Contained (shiftRect p.dx p.dy sb.rect) := by
  have hmem := List.mem_of_find?_eq_some hEnv
  have hid : env.id = l.top.id := beq_iff_eq.mp
    (List.find?_some (p := fun candidate : Box => candidate.id == l.top.id) hEnv)
  have hfixed : e.contractedInput.fixedSizes.find? (·.1 == env.id) =
      some (l.top.id, l.footprint.size) := by
    rw [hid, e.contractedInput_eq]
    exact contractReservation _ _ l (fun k hk h => sameTopLayout e hk hl h) (Or.inl hl)
  have hDims := layoutRegionNotes_fixedBoxDimensions idSets (outerFuel := 0)
    (exactIds := exactIds ++ e.layouts.map (·.top.id)) (inp := e.contractedInput)
    (o := o) (res := e.contracted) e.contracted_eq env hmem _ hfixed
  obtain ⟨hFoot, _, hFit⟩ := footprintOfExecution e hl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  obtain ⟨r, hr, hplace, hw, hh⟩ := placedIndexSource hEnv hFoot hi
  have hLocal := hFit r (List.mem_of_getElem? hr)
  have hEnvFit : env.rect.Contained (shiftRect env.rect.x env.rect.y r) := by
    unfold Rect.Contained at hLocal ⊢
    unfold shiftRect at ⊢
    dsimp only at hLocal ⊢
    have hW : l.footprint.size.w ≤ env.rect.w := hDims.1
    have hH : l.footprint.size.h ≤ env.rect.h := hDims.2
    omega
  exact hEnvFit.trans (shiftedBoxInFootprint hplace hw hh (fragmentInsets e hPart hl hp sb hsb))

private theorem noteRunInset {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNoteBase idSets) exactIds fuel inp o res)
    (hPart : FlatInsetB (layoutNotes (regionNoteBase idSets) exactIds fuel)) :
    InsetC1 res.scene e.margin := by
  have hKind : e.contractedInput.kind = inp.kind := by rw [e.contractedInput_eq, contractKind]
  have hContract : InsetC1 e.contracted.scene e.margin :=
    insetAtMargin (kind := e.contractedInput.kind) (by rw [hKind]; exact e.checked) e.margin_eq
      (regionFlatInset (exactIds ++ e.layouts.map (·.top.id)) idSets _ _ _ e.contracted_eq)
  intro b hb
  obtain ⟨_, _, _, _, _, _, hrect⟩ := e.boxes_mem b hb
  rcases classifyRect hrect with ⟨p, hp, hlookup⟩ | ⟨_, cb, hcb, _, hceq⟩
  · obtain ⟨sb, hsb, _, hshift⟩ := Placed.rect_scene_box hlookup
    obtain ⟨l, hl, hpl⟩ := placedFlatten_mem e.placed_eq hp
    cases hEnv : e.contracted.scene.boxes.find? (·.id == l.top.id) with
    | none => exact (noPlacedWithoutEnvelope hpl hEnv).elim
    | some env =>
      rw [← hshift, e.canvas_eq]
      exact (hContract env (List.mem_of_find?_eq_some hEnv)).trans
        (fragmentInEnvelope e hPart hl hpl hsb hEnv)
  · rw [← hceq, e.canvas_eq]
    exact hContract _ hcb

/-- Executed region-note layouts preserve the margin inset at every note fuel. -/
theorem flatInsetB_regionNotes (idSets : List (String × List String)) (exactIds : List String)
    (fuel : Nat) : FlatInsetB (layoutNotes (regionNoteBase idSets) exactIds fuel) := by
  induction fuel with
  | zero => exact regionFlatInset exactIds idSets
  | succ fuel ih =>
    intro inp o res h
    rcases layoutNotes_success_phases h with ⟨_, hbase⟩ | ⟨⟨e⟩⟩
    · exact regionFlatInset exactIds idSets inp o res hbase
    · refine ⟨e.params, e.checked, ?_, ?_⟩
      · have hm := checkedParams_canvasMargin_ge_one e.checked
        omega
      · rw [← e.margin_eq]
        exact noteRunInset e ih

/-- Every placed fragment box lies in its executed contracted envelope. -/
theorem regionNotes_envelope_contains {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res) : NotesC8aEnv e := by
  intro l hl p hp sb hsb
  cases hEnv : e.contracted.scene.boxes.find? (·.id == l.top.id) with
  | none => exact (noPlacedWithoutEnvelope hp hEnv).elim
  | some env =>
    rw [envRect, hEnv]
    exact fragmentInEnvelope e (flatInsetB_regionNotes idSets exactIds fuel) hl hp hsb hEnv

theorem regionNotes_sameBundle_disjoint {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res) :
    ∀ l ∈ e.layouts, ∀ pa ∈ placedOf' e.margin e.contracted.scene l,
      ∀ pb ∈ placedOf' e.margin e.contracted.scene l, pa ≠ pb →
      ∀ sa ∈ pa.scene.boxes, ∀ sb ∈ pb.scene.boxes,
        Disjoint (shiftRect pa.dx pa.dy sa.rect) (shiftRect pb.dx pb.dy sb.rect) := by
  intro l hl pa hpa pb hpb hne sa hsa sb hsb
  cases hEnv : e.contracted.scene.boxes.find? (·.id == l.top.id) with
  | none => exact (noPlacedWithoutEnvelope hpa hEnv).elim
  | some env =>
    obtain ⟨heq, hsep, _⟩ := footprintOfExecution e hl
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpa
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hpb
    obtain ⟨r, hr, hplacea, hwa, hha⟩ := placedIndexSource hEnv heq hi
    obtain ⟨s, hs, hplaceb, hwb, hhb⟩ := placedIndexSource hEnv heq hj
    have hij : i ≠ j := by
      intro he
      subst j
      exact hne (Option.some.inj (hi.symm.trans hj))
    obtain ⟨hir, hri⟩ := List.getElem?_eq_some_iff.mp hr
    obtain ⟨hjs, hsj⟩ := List.getElem?_eq_some_iff.mp hs
    have hrs : Disjoint r s := by
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · rw [← hri, ← hsj]
        exact List.pairwise_iff_getElem.mp hsep i j hir hjs hlt
      · apply (Disjoint.comm s r).mp
        rw [← hri, ← hsj]
        exact List.pairwise_iff_getElem.mp hsep j i hjs hir hgt
    have hinset := flatInsetB_regionNotes idSets exactIds fuel
    exact shiftedSubrectsDisjoint hrs
      (shiftedBoxInFootprint hplacea hwa hha (fragmentInsets e hinset hl hpa sa hsa))
      (shiftedBoxInFootprint hplaceb hwb hhb (fragmentInsets e hinset hl hpb sb hsb))

theorem regionNotes_sameBundle_c8aFragDisj {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res) : NotesC8aFragDisj e := by
  intro l hl pa hpa pb hpb sa hsa sb hsb hne _
  exact regionNotes_sameBundle_disjoint e l hl pa hpa pb hpb hne sa hsa sb hsb

theorem regionNotes_c8aGeomT_of_clearance {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hClear : NotesC8aClear e) (hEnv : NotesC8aEnv e) (hEnvDisj : NotesC8aEnvDisj e) :
    NotesC8aGeomT e :=
  _root_.nc68C8aGeomT_layoutR (idSets := idSets) e hwf
    ⟨hClear, regionNotes_sameBundle_c8aFragDisj (idSets := idSets) e, hEnv, hEnvDisj⟩

end Elegant.Layered.PipelineImpl
