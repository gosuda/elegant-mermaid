import Elegant.Layered.RegionNotesCanvasMargins
import Elegant.Layered.RegionNotesFitClosure
import Elegant.Layered.RegionSeams
import Elegant.Layered.NotesFlatAssembly
import Elegant.Layered.RegionNotesDimensions
import Elegant.Layered.NotesGeomC68Proof
import Elegant.Layered.RegionNotesFamilyC8aAligned
import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.StatePipeline
import Elegant.Layered.RegionPipeline
import Elegant.Layered.AttachPipeline
import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.SubInputWellFormedFacts
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Region-and-note family seams.

`layoutFamilyRN` (StatePipeline) resolves the model region sets once, then runs
`layoutFamilyB` over the note-wrapped region base
`layoutNotes (rnNotesBase idSets) exactIds (inp.boxes.length + 1)`, where
`rnNotesBase idSets` runs `layoutRIds` at each sub-input's reindexed sets.
The ordinary flat facts are lifted from `regionBaseSeams`. For C8a,
the guarded lift uses attachment-parent alignment from family admission.
-/

/-- The region base the note wrapper runs: `layoutRIds` at each sub-input's
reindexed region sets. -/
private abbrev rnNotesBase (idSets : List (String × List String)) :
    List String → Input → Options → Except LayoutError FamilyResult :=
  fun ids sub o => layoutRIds ids (reindexRegionSets idSets sub) sub o

/-- Region-and-note seams: the raw region seams, note geometry residuals,
the per-execution clause premises, and the expansion-step facts. -/
structure RegionNotesSeams (exactIds : List String)
    (idSets : List (String × List String)) : Prop where
  /-- The region seams at these ids: supplies every `BaseSeams` flat fact of
  the underlying region base through `regionBaseSeams`. -/
  region : RegionSeams exactIds idSets
  /-- Note-stage geometric, flag, and endpoint-box lookup residuals over every
  note execution on the region base. -/
  notesFacts : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    NotesFlatFacts e
  /-- OPEN CLAUSE: per-execution contracted inset fact for `notes_flatInsetB`. -/
  insetContracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    InsetC1 e.contracted.scene e.margin
  /-- OPEN CLAUSE: per-execution fragment inset facts for `notes_flatInsetB`. -/
  insetFragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ l ∈ e.layouts,
      InsetC1 l.part.scene e.margin ∧
        ∀ q ∈ l.notes, InsetC1 q.2.scene e.margin
  /-- OPEN CLAUSE: per-execution contracted C3 for `notes_flatC3B`. -/
  c3Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    Validator.C3 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE: per-execution fragment C3 facts for `notes_flatC3B`. -/
  c3Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ l ∈ e.layouts,
      Validator.C3 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C3 q.2.scene.layoutDump
  /-- OPEN CLAUSE: per-execution contracted C2 for `notes_flatC2B`. -/
  c2Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    Validator.C2 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE: per-execution fragment C2 facts for `notes_flatC2B`. -/
  c2Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ l ∈ e.layouts,
      Validator.C2 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C2 q.2.scene.layoutDump
  /-- OPEN CLAUSE: per-execution contracted orthogonality for `notes_flatC4B`. -/
  orthoContracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ cr ∈ e.contracted.scene.routes,
      Polyline.isOrthogonal cr.points = true
  /-- OPEN CLAUSE: per-execution fragment orthogonality for `notes_flatC4B`. -/
  orthoFragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, ∀ fr ∈ p.scene.routes,
      Polyline.isOrthogonal fr.points = true
  /-- OPEN CLAUSE: per-execution group-endpoint invariant for `notes_flatC5B`. -/
  groupEndpoints : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (_ : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    GroupEndpointInvariantMeasured inp res.scene
  /-- OPEN CLAUSE: per-execution contracted C6 for `notes_flatC6B`. -/
  c6Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    Validator.C6 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE: per-execution fragment C6 facts for `notes_flatC6B`. -/
  c6Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C6 p.scene.layoutDump
  /-- OPEN CLAUSE: per-execution contracted C7 for `notes_flatC7B`. -/
  c7Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    Validator.C7 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE: per-execution fragment C7 facts for `notes_flatC7B`. -/
  c7Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C7 p.scene.layoutDump
  /-- OPEN CLAUSE: per-execution contracted C8b for `notes_flatC8bB`. -/
  c8bContracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    Validator.C8b e.contracted.scene.layoutDump
  /-- OPEN CLAUSE: per-execution fragment C8b facts for `notes_flatC8bB`. -/
  c8bFragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C8b p.scene.layoutDump
  /-- OPEN CLAUSE: per-execution contracted C1 for `notes_validate_none`. -/
  c1Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    Validator.C1 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE: per-execution fragment C1 facts for `notes_validate_none`. -/
  c1Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ l ∈ e.layouts,
      Validator.C1 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C1 q.2.scene.layoutDump
  /-- OPEN CLAUSE: per-execution contracted C4 for `notes_validate_none`. -/
  c4Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    Validator.C4 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE: per-execution fragment C4 facts for `notes_validate_none`. -/
  c4Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C4 p.scene.layoutDump
  /-- OPEN CLAUSE: per-execution contracted C5 for `notes_validate_none`. -/
  c5Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    Validator.C5 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE: per-execution fragment C5 facts for `notes_validate_none`. -/
  c5Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C5 p.scene.layoutDump
  /-- OPEN CLAUSE: no finished notes module; the `stepC2` clause itself at the
  note-wrapped base. -/
  stepC2N : ∀ (outerFuel fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    (∀ m ∈ inp.boxes, m.id ≠ "") →
    ExpandChildCallContextB (layoutNotes (rnNotesBase idSets) exactIds outerFuel)
      fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC2Step P inp o group titleHeight parent child res
  /-- OPEN CLAUSE: no finished notes module; the `stepC6` clause itself at the
  note-wrapped base. -/
  stepC6N : ∀ (outerFuel fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutNotes (rnNotesBase idSets) exactIds outerFuel)
      fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC6Step P inp o group titleHeight parent child res
  /-- OPEN CLAUSE: no finished notes module; the `stepC7` clause itself at the
  note-wrapped base. -/
  stepC7N : ∀ (outerFuel fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true → BoxRouteIdsDisjoint inp →
    InputFixedFit inp o →
    ExpandChildCallContextB (layoutNotes (rnNotesBase idSets) exactIds outerFuel)
      fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7Step P inp o group titleHeight parent child res
  /-- OPEN CLAUSE: no finished notes module; the `stepC8b` clause itself at the
  note-wrapped base. -/
  stepC8bN : ∀ (outerFuel fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    InputFixedFit inp o →
    ExpandChildCallContextB (layoutNotes (rnNotesBase idSets) exactIds outerFuel)
      fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC8bStep P inp o group titleHeight parent child res

/-- The shared family seams at the note-wrapped region base. The family
assembles C8a separately from the guarded note and group recursions. -/
theorem rnNotesBaseSeams {exactIds : List String}
    {idSets : List (String × List String)}
    (S : RegionNotesSeams exactIds idSets) (outerFuel : Nat) :
    BaseSeamsCore (layoutNotes (rnNotesBase idSets) exactIds outerFuel) where
  flatInset := by
    cases outerFuel with
    | zero => exact (regionBaseSeams S.region).flatInset
    | succ n =>
      exact notes_flatInsetB exactIds n (S.notesFacts n)
        (regionBaseSeams S.region).flatInset
        (S.insetContracted n) (S.insetFragments n)
  flatC3 := by
    cases outerFuel with
    | zero => exact (regionBaseSeams S.region).flatC3
    | succ n =>
      exact notes_flatC3B exactIds n (S.notesFacts n)
        (regionBaseSeams S.region).flatC3
        (S.c3Contracted n) (S.c3Fragments n)
  flatC2 := by
    cases outerFuel with
    | zero => exact (regionBaseSeams S.region).flatC2
    | succ n =>
      exact notes_flatC2B exactIds n (fun e => (S.notesFacts n e).c2Geom)
        (regionBaseSeams S.region).flatC2
        (S.c2Contracted n) (fun e l hl => (S.c2Fragments n e l hl).1)
  flatC4 := by
    cases outerFuel with
    | zero => exact (regionBaseSeams S.region).flatC4
    | succ n =>
      exact notes_flatC4B exactIds n
        (regionBaseSeams S.region).flatC4
        (S.orthoContracted n) (S.orthoFragments n)
  flatC5 := by
    cases outerFuel with
    | zero => exact (regionBaseSeams S.region).flatC5
    | succ n =>
      exact notes_flatC5B exactIds n
        (regionBaseSeams S.region).flatC5 (S.groupEndpoints n)
  flatC6 := by
    cases outerFuel with
    | zero => exact (regionBaseSeams S.region).flatC6
    | succ n =>
      exact notes_flatC6B exactIds n (S.notesFacts n)
        (fun _ _ _ _ h => layoutRIds_routes_mirror h) (regionBaseSeams S.region).flatC6
        (S.c6Contracted n) (S.c6Fragments n)
  flatC7 := by
    cases outerFuel with
    | zero => exact (regionBaseSeams S.region).flatC7
    | succ n =>
      exact notes_flatC7B exactIds n (S.notesFacts n)
        (regionBaseSeams S.region).flatC7
        (S.c7Contracted n) (S.c7Fragments n)
  flatC8b := by
    cases outerFuel with
    | zero => exact (regionBaseSeams S.region).flatC8b
    | succ n =>
      exact notes_flatC8bB exactIds n (S.notesFacts n)
        (regionBaseSeams S.region).flatC8b
        (S.c8bContracted n) (S.c8bFragments n)
  canvasMargins := canvasMarginsN_rngNotesBase exactIds idSets outerFuel
  frameClear := (regionBaseSeams S.region).frameClear
  partsSep := (regionBaseSeams S.region).partsSep
  labelRuns := (regionBaseSeams S.region).labelRuns
  captions := (regionBaseSeams S.region).captions
  subInputC2 := subInputWellFormedC2
  subInputB := subInputWellFormedB_of _
  fitClosed := expandChildFitClosedB_regionNotes exactIds idSets outerFuel
  stepC2 := S.stepC2N outerFuel
  stepC6 := S.stepC6N outerFuel
  stepC7 := S.stepC7N outerFuel
  stepC8b := S.stepC8bN outerFuel

/-- Validate a local note execution. Unlike the family entry, the execution
record does not attest that the framed-parent and alignment checks passed. -/
theorem rnNotesValidateNone {exactIds : List String}
    {idSets : List (String × List String)}
    (S : RegionNotesSeams exactIds idSets) (fuel : Nat)
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rnNotesBase idSets) exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hparents : attachedNoteParents inp = true) :
    Validator.validate res.scene.layoutDump = none := by
  have hcontract := regionNotes_contractedC8aAligned (idSets := idSets) fuel e hwf hfp hparents
  have hparts := e.partsC8a_of_flatAligned
    (regionNotes_flatC8aAligned (exactIds := exactIds) (idSets := idSets) fuel) hwf hfp hparents
  exact notes_validate_none e (S.notesFacts fuel e) hwf
    (regionNotes_c8aGeomT_of_attachedNoteParents (idSets := idSets) e hwf hparents hcontract)
    (fun _ _ hLookup => e.region_rects_lookup_nonneg (idSets := idSets) hLookup)
    (fun _ _ _ _ h => layoutRIds_routes_mirror h)
    (S.c1Contracted fuel e) (S.c1Fragments fuel e)
    (S.c2Contracted fuel e) (S.c2Fragments fuel e)
    (S.c3Contracted fuel e) (S.c3Fragments fuel e)
    (S.c4Contracted fuel e) (S.c4Fragments fuel e)
    (S.c5Contracted fuel e) (S.c5Fragments fuel e)
    (S.c6Contracted fuel e) (S.c6Fragments fuel e)
    (S.c7Contracted fuel e) (S.c7Fragments fuel e)
    hcontract hparts (regionNotes_individualC8a (idSets := idSets) e)
    (S.c8bContracted fuel e) (S.c8bFragments fuel e)

/-- Region-and-note family validity from the seams: the executed
`layoutFamilyRN` run over the resolved id sets satisfies the hard constraints.
The guarded C8a lift uses existing family admission; the common assembly
consumes its result alongside the other clause proofs. -/
theorem layoutFamilyRN_valid_of_seams {exactIds : List String}
    {sets : List ModelRegionSet} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (S : RegionNotesSeams exactIds idSets)
    (hgraph : RegionImpl.graphRegions inp sets = .ok idSets)
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hfix : InputFixedFit inp o) (hpos : FixedSizesPositive inp)
    (hdisj : BoxRouteIdsDisjoint inp)
    (h : Elegant.Layered.layoutFamilyRN exactIds sets inp o = .ok res) :
    HardConstraints res.scene.layoutDump := by
  have hB : layoutFamilyB
      (layoutNotes (rnNotesBase idSets) exactIds (inp.boxes.length + 1)) inp o
      = .ok res := by
    have h2 := h
    simp only [Elegant.Layered.layoutFamilyRN, hgraph] at h2
    exact h2
  exact layoutFamilyB_valid_of_core_and_c8a (rnNotesBaseSeams S _) hids hfix hpos hdisj hB
    (layoutFamilyRN_c8a hgraph h)

end PipelineImpl
end Layered
end Elegant
