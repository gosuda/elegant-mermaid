import Elegant.Layered.NotesFlatBoxClauses
import Elegant.Layered.NotesFlatRouteClauses
import Elegant.Layered.NotesFlatLabelClauses
import Elegant.Layered.NotesMirrorFacts
import Elegant.Layered.NotesC8aRoleRepair
import Elegant.Layered.NotesRouteFacts
import Elegant.Layered.NotesRoutePortTransport
import Elegant.Layered.NotesKeptFlagExecution
import Elegant.Layered.FamilyAssemblyB
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Flat assembly for the note base.

`layoutNotes base exactIds (fuel + 1)` is the state base the family entry
`layoutFamilyN` runs (`AttachPipeline.lean`). The per-execution clause theorems
(`notes_c1`, `notes_c2`, `notes_c3`, `notes_inset` in `NotesFlatBoxClauses`;
`notes_c4`, `notes_c5` in `NotesFlatRouteClauses`; `notes_c6`, `notes_c7`,
`notes_c8a`, `notes_c8b` in `NotesFlatLabelClauses`) discharge every
`Validator` clause over a `NotesExecution`, modulo base-clause facts on the
contracted and fragment scenes plus the geometric/bridge residuals below.
`NotesPlacementFacts` and `NotesMirrorFacts` close some residuals from narrower
premises. `NotesFlatFacts` collects the shared residuals. The C8a geometry
residual is separate because its consumers have local well-formedness.

The router facts are not fields here: `notesRouterOrtho_holds` proves
orthogonality unconditionally for arbitrary rects, and endpoint membership of
successful `routeAround` output is unconditional port transport, which yields
`notesRouterEnds` once the looked-up rectangles have nonnegative dimensions.

Probed: `proofs/wip/Probe/NotesFlatAssemblyT_probe.lean` evaluates a Bool
mirror of every field on two executed state inputs with notes. -/

/-- Shared note-stage geometry and endpoint-box lookup residuals over one
execution. C8a geometry is supplied separately at its consumers. -/
structure NotesFlatFacts
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop where
  c1Fit : NotesC1Fit e
  c2Geom : NotesC2Geom e
  c3Geom : NotesC3Geom e
  keptBox : ∀ r ∈ inp.routes, notesKept inp e.layouts r →
    notesKeptBoxContracted e.placed r
  fragBox : ∀ r ∈ inp.routes, ∀ a : Nat, notesSameBundleAt inp e.layouts a r →
    notesFragBoxFirst e.fragments r
  c6Geom : NotesC6Geom e
  c7Geom : NotesC7Geom e
  c8bGeom : NotesC8bGeom e

/-! ### Per-execution orthogonality (the `FlatC4B` conclusion shape) -/

/-- Every composed route has orthogonal points. Kept routes reuse the
contracted all-orthogonal fact, fragment routes reuse the fragment fact
transported through the point shift, and cross routes use
`notesRouterOrtho_holds`. `FlatC4B` needs this unconditional fact; `notes_c4`
proves only the conditional `Validator.C4`. -/
theorem notes_exec_orthogonal
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hCb : ∀ cr ∈ e.contracted.scene.routes,
      Polyline.isOrthogonal cr.points = true)
    (hFb : ∀ p ∈ e.fragments, ∀ fr ∈ p.scene.routes,
      Polyline.isOrthogonal fr.points = true) :
    ∀ rt ∈ res.scene.routes, Polyline.isOrthogonal rt.points = true := by
  intro rt hrt
  obtain ⟨x, hx, _, _, _, _, hcases⟩ := notes_route_cases e hrt
  rcases hcases with ⟨_, cr, hcr, _, hpts⟩ | ⟨_, _, p, hp, fr, hfrmem, _, hpts⟩ |
    ⟨_, pts, hpts, hroute⟩
  · rw [hpts]
    exact hCb cr hcr
  · rw [hpts, notesShiftPoint_orthogonal]
    exact hFb p hp fr hfrmem
  · rw [hpts]
    exact notesRouterOrtho_holds inp e.atts (notesFrameOf e.contracted o e.margin)
      (notesRectsOf res.scene.boxes) (notesLabelsOf e.fragments e.contracted inp)
      (notesTitlesOf e.fragments e.contracted) x hx pts hroute

/-! ### Flat facts for the note base -/

/-- The note base keeps the inset fact: with no bundles the underlying base
fact applies; otherwise `notes_inset` runs on the execution with the
contracted/fragment inset facts and the `NotesC1Fit` residual. -/
theorem notes_flatInsetB
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (F : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), NotesFlatFacts e)
    (hFlat : FlatInsetB (base exactIds))
    (hContract : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      InsetC1 e.contracted.scene e.margin)
    (hFrag : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), ∀ l ∈ e.layouts,
      InsetC1 l.part.scene e.margin ∧
        ∀ q ∈ l.notes, InsetC1 q.2.scene e.margin) :
    FlatInsetB (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hok
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat inp o res hempty.2
  · obtain ⟨e⟩ := hne
    exact notes_inset e (hContract e) (hFrag e) (F e).c1Fit

/-- The note base keeps flat C3: with no bundles the underlying base fact
applies; otherwise `notes_c3` runs on the execution with the contracted and
fragment C3 facts, input nodup from well-formedness, and the `NotesC3Geom`
residual. -/
theorem notes_flatC3B
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (F : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), NotesFlatFacts e)
    (hFlat : FlatC3B (base exactIds))
    (hContract : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      Validator.C3 e.contracted.scene.layoutDump)
    (hFrag : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), ∀ l ∈ e.layouts,
      Validator.C3 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C3 q.2.scene.layoutDump) :
    FlatC3B (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hwf hfp hok
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat inp o res hwf hfp hempty.2
  · obtain ⟨e⟩ := hne
    exact notes_c3 e (hContract e) (hFrag e)
      (Model.boxIds_nodup hwf) (F e).c3Geom

/-- The note base keeps flat C2: with no bundles the underlying base fact
applies; otherwise `notes_c2` uses original well-formedness, contracted and
part C2, and `NotesC2Geom`. -/
theorem notes_flatC2B
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (hGeom : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), NotesC2Geom e)
    (hFlat : FlatC2B (base exactIds))
    (hContract : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      Validator.C2 e.contracted.scene.layoutDump)
    (hFrag : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), ∀ l ∈ e.layouts,
      Validator.C2 l.part.scene.layoutDump) :
    FlatC2B (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hwf hok
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat inp o res hwf hempty.2
  · obtain ⟨e⟩ := hne
    exact notes_c2 e hwf (hContract e) (hFrag e) (hGeom e)

/-- The note base keeps flat C4: with no bundles the underlying base fact
applies; otherwise `notes_exec_orthogonal` runs on the execution with the
contracted and fragment all-orthogonal facts. -/
theorem notes_flatC4B
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (hFlat : FlatC4B (base exactIds))
    (hContract : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      ∀ cr ∈ e.contracted.scene.routes,
        Polyline.isOrthogonal cr.points = true)
    (hFrag : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      ∀ p ∈ e.fragments, ∀ fr ∈ p.scene.routes,
        Polyline.isOrthogonal fr.points = true) :
    FlatC4B (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hok rt hrt
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat inp o res hempty.2 rt hrt
  · obtain ⟨e⟩ := hne
    exact notes_exec_orthogonal e (hContract e) (hFrag e) rt hrt

/-- The note base keeps flat C5: with no bundles the underlying base fact
applies; otherwise the box and route id equalities are the structural
`NotesExecution.boxes_ids`/`routes_ids` facts (no residual needed), and only
the measured group-endpoint invariant stays open as an explicit hypothesis. -/
theorem notes_flatC5B
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (hFlat : FlatC5B (base exactIds))
    (hGEP : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (_ : NotesExecution base exactIds fuel inp o res),
      GroupEndpointInvariantMeasured inp res.scene) :
    FlatC5B (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hwf hfp hok
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat hwf hfp hempty.2
  · obtain ⟨e⟩ := hne
    exact ⟨e.boxes_ids, e.routes_ids, hGEP e⟩

/-- The note base keeps flat C6: with no bundles the underlying base fact
applies (threading the frame-clearance seam); otherwise `notes_c6` runs on
the execution with the contracted/fragment C6 facts and the `NotesC6Geom`
residual. -/
theorem notes_flatC6B
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (F : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), NotesFlatFacts e)
    (hRouteBase : ∀ ids inp o res, base ids inp o = .ok res → NotesRouteMirror inp res)
    (hFlat : FlatC6B (base exactIds))
    (hContract : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      Validator.C6 e.contracted.scene.layoutDump)
    (hFrag : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      ∀ p ∈ e.fragments, Validator.C6 p.scene.layoutDump) :
    FlatC6B (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hwf hfp hpos hframe hok
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat inp o res hwf hfp hpos hframe hempty.2
  · obtain ⟨e⟩ := hne
    have hFlags := notesFlagsKept_of_route_mirror e hwf
      (hRouteBase _ _ _ _ e.contracted_eq)
    have hFlagsFrag := notesFlagsFragment_of_route_mirror hRouteBase e (Model.routeIds_nodup hwf)
    exact notes_c6 e (hContract e) (hFrag e) hFlags hFlagsFrag (F e).c6Geom

/-- The note base keeps flat C7: with no bundles the underlying base fact
applies (threading the fit and clearance seams); otherwise `notes_c7` runs on
the execution with the contracted/fragment C7 facts and the `NotesC7Geom`
residual. -/
theorem notes_flatC7B
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (F : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), NotesFlatFacts e)
    (hFlat : FlatC7B (base exactIds))
    (hContract : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      Validator.C7 e.contracted.scene.layoutDump)
    (hFrag : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      ∀ p ∈ e.fragments, Validator.C7 p.scene.layoutDump) :
    FlatC7B (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hwf hfp hfit hsep hruns hcap hok
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat inp o res hwf hfp hfit hsep hruns hcap hempty.2
  · obtain ⟨e⟩ := hne
    exact notes_c7 e (hContract e) (hFrag e) (F e).c7Geom
/-- The note base keeps flat C8a: with no bundles the underlying base fact
applies; otherwise `notes_c8a'` runs on the execution with the contracted,
fragment-part, and fragment-note C8a facts, well-formedness, and the
`NotesC8aGeomT` residual. -/
theorem notes_flatC8aB
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (hGeom : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      WellFormed (inputModel inp o) → NotesC8aGeomT e)
    (hFlat : FlatC8aB (base exactIds))
    (hContract : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      Validator.C8a e.contracted.scene.layoutDump)
    (hFragP : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), ∀ l ∈ e.layouts,
      Validator.C8a l.part.scene.layoutDump)
    (hFragN : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), ∀ l ∈ e.layouts,
      ∀ q ∈ l.notes, Validator.C8a q.2.scene.layoutDump) :
    FlatC8aB (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hwf hfp hok
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat inp o res hwf hfp hempty.2
  · obtain ⟨e⟩ := hne
    exact notes_c8a' e hwf (hContract e) (hFragP e) (hFragN e) (hGeom e hwf)

/-- The note base keeps flat C8b: with no bundles the underlying base fact
applies (threading the fixed-size fit); otherwise `notes_c8b` runs on the
execution with the contracted/fragment C8b facts, well-formedness, and the
`NotesC8bGeom` residual. -/
theorem notes_flatC8bB
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (exactIds : List String) (fuel : Nat)
    (F : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res), NotesFlatFacts e)
    (hFlat : FlatC8bB (base exactIds))
    (hContract : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      Validator.C8b e.contracted.scene.layoutDump)
    (hFrag : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base exactIds fuel inp o res),
      ∀ p ∈ e.fragments, Validator.C8b p.scene.layoutDump) :
    FlatC8bB (layoutNotes base exactIds (fuel + 1)) := by
  intro inp o res hwf hfp hfit hok
  obtain hempty | hne := layoutNotes_success_phases hok
  · exact hFlat inp o res hwf hfp hfit hempty.2
  · obtain ⟨e⟩ := hne
    exact notes_c8b e hwf (hContract e) (hFrag e) (F e).c8bGeom

/-! ### Flat-scene validation -/

/-- The flat note scene validates from the contracted and fragment clauses,
the remaining note-stage facts, and the base route mirror. Well-formedness
gives endpoint membership, and nonnegative dimensions of the looked-up
rectangles give cross-route boundary endpoints. Endpoint membership itself is
unconditional (`NotesRoutePortTransport.routeAround_endpoints_mem`); for
actual regional note executions `hRectDims` comes from
`RegionNotesDimensions.region_rects_lookup_nonneg`. -/
theorem notes_validate_none
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (F : NotesFlatFacts e)
    (hwf : WellFormed (inputModel inp o))
    (hC8aGeom : NotesC8aGeomT e)
    (hRectDims : ∀ (id : String) (rect : Rect),
      (notesRectsOf res.scene.boxes).lookup id = some rect → 0 ≤ rect.w ∧ 0 ≤ rect.h)
    (hRouteBase : ∀ ids inp o res, base ids inp o = .ok res → NotesRouteMirror inp res)
    (hC1b : Validator.C1 e.contracted.scene.layoutDump)
    (hC1f : ∀ l ∈ e.layouts, Validator.C1 l.part.scene.layoutDump ∧
      ∀ q ∈ l.notes, Validator.C1 q.2.scene.layoutDump)
    (hC2b : Validator.C2 e.contracted.scene.layoutDump)
    (hC2f : ∀ l ∈ e.layouts, Validator.C2 l.part.scene.layoutDump ∧
      ∀ q ∈ l.notes, Validator.C2 q.2.scene.layoutDump)
    (hC3b : Validator.C3 e.contracted.scene.layoutDump)
    (hC3f : ∀ l ∈ e.layouts, Validator.C3 l.part.scene.layoutDump ∧
      ∀ q ∈ l.notes, Validator.C3 q.2.scene.layoutDump)
    (hC4b : Validator.C4 e.contracted.scene.layoutDump)
    (hC4f : ∀ p ∈ e.fragments, Validator.C4 p.scene.layoutDump)
    (hC5b : Validator.C5 e.contracted.scene.layoutDump)
    (hC5f : ∀ p ∈ e.fragments, Validator.C5 p.scene.layoutDump)
    (hC6b : Validator.C6 e.contracted.scene.layoutDump)
    (hC6f : ∀ p ∈ e.fragments, Validator.C6 p.scene.layoutDump)
    (hC7b : Validator.C7 e.contracted.scene.layoutDump)
    (hC7f : ∀ p ∈ e.fragments, Validator.C7 p.scene.layoutDump)
    (hC8ab : Validator.C8a e.contracted.scene.layoutDump)
    (hC8aPf : ∀ l ∈ e.layouts, Validator.C8a l.part.scene.layoutDump)
    (hC8aNf : ∀ l ∈ e.layouts, ∀ q ∈ l.notes,
      Validator.C8a q.2.scene.layoutDump)
    (hC8bb : Validator.C8b e.contracted.scene.layoutDump)
    (hC8bf : ∀ p ∈ e.fragments, Validator.C8b p.scene.layoutDump) :
    Validator.validate res.scene.layoutDump = none := by
  rw [Validator.validate_none_iff]
  have hnd := Model.boxIds_nodup hwf
  have hFlags := notesFlagsKept_of_route_mirror e hwf
    (hRouteBase _ _ _ _ e.contracted_eq)
  have hFlagsFrag := notesFlagsFragment_of_route_mirror hRouteBase e (Model.routeIds_nodup hwf)
  have hRouterOrtho := notesRouterOrtho_holds inp e.atts (notesFrameOf e.contracted o e.margin)
    (notesRectsOf res.scene.boxes) (notesLabelsOf e.fragments e.contracted inp)
    (notesTitlesOf e.fragments e.contracted)
  have hRouterPath := nriRouterPathExec_of_rects_lookup_nonneg inp o res
    e.contracted e.fragments e.atts e.margin hRectDims
  have hRouterEnds := nriRouterEndsExec_of_parts inp o res
    e.contracted e.fragments e.atts e.margin hRouterPath hwf
  exact ⟨notes_c1 e hC1b hC1f F.c1Fit,
    notes_c2 e hwf hC2b (fun l hl => (hC2f l hl).1) F.c2Geom,
    notes_c3 e hC3b hC3f hnd F.c3Geom,
    notes_c4 e hC4b hC4f hFlags hFlagsFrag hRouterOrtho,
    notes_c5 e (notesEndsInBoxes_holds hwf) hC5b hC5f hFlags hFlagsFrag F.keptBox
      F.fragBox hRouterEnds,
    notes_c6 e hC6b hC6f hFlags hFlagsFrag F.c6Geom,
    notes_c7 e hC7b hC7f F.c7Geom,
    notes_c8a' e hwf hC8ab hC8aPf hC8aNf hC8aGeom,
    notes_c8b e hwf hC8bb hC8bf F.c8bGeom⟩

end PipelineImpl
end Layered
end Elegant
