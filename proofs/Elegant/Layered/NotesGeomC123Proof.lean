import Elegant.Layered.NotesPlacementFacts
import Elegant.Layered.NotesMirrorFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Note-stage C1/C2/C3 geometry from placement bridges.

Proved: `NotesC1Fit` from the envelope placement (`Ngc1PlaceW`) plus the
contracted C1 tower fact; `NotesC2Geom` and `NotesC3Geom` from one bridge def
each (`Ngc2BridgeW`, `Ngc3BridgeW`) plus tower facts (contracted C2 and
fragment C1 for C2, fragment C1 and local well-formedness for C3). Each
bridge describes fragment/envelope/input facts, not the composed scene.

Open: `Ngc1PlaceW`, `Ngc2BridgeW`, `Ngc3BridgeW` (one narrow def per clause).
The footprint gap separation underneath `hSame`/`hPlace` is pure rect
arithmetic (`NoteFootprintDisjoint.footprint_notes_disjoint_target`); the
envelope-size equation needs the base fixed-size fact, so the bridges stay.

Truth: `proofs/wip/Probe/NotesGeomAT_probe.lean` prints `c1place`,
`c2bridge`, `c3bridge` all `true` on five executed well-formed inputs
(state note, note on a group, two notes on one box, empty-text note,
self-loop). The duplicate-id input still executes with `c1place=true` but
`self=false`, so both bridges are `false` there; the reductions below take
local `WellFormed` (hence input nodup), which that input lacks.
-/

/-- Fragment canvases sit inside their bundle envelopes: the footprint
placement consequence. With contracted C1 this gives `NotesC1Fit`. -/
def Ngc1PlaceW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    (envRect e.contracted.scene l).Contained ⟨p.dx, p.dy, p.scene.canvas.w, p.scene.canvas.h⟩

/-- C1 fit from the envelope placement and the contracted C1 tower fact. -/
theorem ngc1Fit_of_placeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C1 e.contracted.scene.layoutDump)
    (hW : Ngc1PlaceW e) :
    NotesC1Fit e :=
  notesC1Fit_holds e hBase hW

/-- C2 bridge: base box metadata, fragment lookup uniqueness (holding rect
and cross-fragment absence), envelope canvas placement, same-layout
footprint separation, and the two envelope C2 applicabilities. With
contracted C2 and fragment C1 this gives `NotesC2Geom`. -/
def Ngc2BridgeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesBaseContract e ∧ NotesBaseFrag e ∧
    (∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
      p.rect sb.id = some (shiftRect p.dx p.dy sb.rect)) ∧
    (∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
      ∀ sb ∈ p.scene.boxes, q.rect sb.id = none) ∧
    (∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      (envRect e.contracted.scene l).Contained ⟨p.dx, p.dy, p.scene.canvas.w, p.scene.canvas.h⟩) ∧
    (∀ l ∈ e.layouts, ∀ pa ∈ placedOf' e.margin e.contracted.scene l,
      ∀ pb ∈ placedOf' e.margin e.contracted.scene l, pa ≠ pb →
      ∀ sa ∈ pa.scene.boxes, ∀ sb ∈ pb.scene.boxes,
        Disjoint (shiftRect pa.dx pa.dy sa.rect) (shiftRect pb.dx pb.dy sb.rect)) ∧
    (∀ la ∈ e.layouts, ∀ lb ∈ e.layouts, la ≠ lb →
      ∀ ea ∈ e.contracted.scene.boxes, ea.id = la.top.id →
      ∀ eb ∈ e.contracted.scene.boxes, eb.id = lb.top.id →
        ea.id ≠ eb.id ∧ ea.exclusive = true ∧ eb.exclusive = true ∧ ea.parent = eb.parent) ∧
    (∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cb ∈ e.contracted.scene.boxes,
        (∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) →
        cb.id ≠ eb.id ∧ cb.exclusive = true ∧ eb.exclusive = true ∧ cb.parent = eb.parent)

/-- C2 geometry from the bridge and the contracted C2 and fragment C1 tower
facts. -/
theorem ngc2Geom_of_bridgeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C2 e.contracted.scene.layoutDump)
    (hFragC1 : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      Validator.C1 p.scene.layoutDump)
    (hW : Ngc2BridgeW e) :
    NotesC2Geom e := by
  obtain ⟨hBC, hBF, hSelf, hCross, hPlace, hSame, hAppl, hApplF⟩ := hW
  have hFM : NotesFirstMatch e := notesFirstMatch_holds e hSelf hCross
  have hCM : NotesContractMirror e := notesContractMirror_holds e hBC
  have hSources : NotesFragBoxSources e := by
    intro l hl
    exact ⟨(hBF l hl).1.2, fun q hq => ((hBF l hl).2 q hq).2⟩
  have hEnv : NotesEnvFit e := notesEnvFit_holds e hPlace hFragC1
  have hPD : NotesPlacedDisjoint e := notesPlacedDisjoint_holds e hBase hAppl hEnv hSame
  have hFC : NotesForeignClear e := notesForeignClear_holds e hBase hApplF hEnv
  exact ⟨hFM, hCM, hSources, hPD, hFC⟩

/-- C3 bridge: base id preservation and roots, note/parent closure
(bundle-note alignment and kept-input parent closure), fragment lookup
uniqueness (holding rect and cross-fragment absence), and envelope canvas
placement. With the fragment C1 tower fact plus local well-formedness this
gives every `NotesC3Geom` conjunct. -/
def Ngc3BridgeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesBaseContract e ∧ NotesBaseFrag e ∧ NotesFragRoots e ∧
    NotesBundleNoteParent e ∧ NotesKeptParent e ∧
    (∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
      p.rect sb.id = some (shiftRect p.dx p.dy sb.rect)) ∧
    (∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
      ∀ sb ∈ p.scene.boxes, q.rect sb.id = none) ∧
    (∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      (envRect e.contracted.scene l).Contained ⟨p.dx, p.dy, p.scene.canvas.w, p.scene.canvas.h⟩)

/-- C3 geometry from the bridge, the fragment C1 tower fact, and local
well-formedness (for input nodup). -/
theorem ngc3Geom_of_bridgeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hFragC1 : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      Validator.C1 p.scene.layoutDump)
    (hW : Ngc3BridgeW e) :
    NotesC3Geom e := by
  obtain ⟨hBC, hBF, hRoots, hNotePar, hKept, hSelf, hCross, hPlace⟩ := hW
  have hnd : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hFM : NotesFirstMatch e := notesFirstMatch_holds e hSelf hCross
  have hCM : NotesContractMirror e := notesContractMirror_holds e hBC
  have hFRM : NotesFragMirror e := notesFragMirror_holds e hBF hRoots hnd
  have hEnv : NotesEnvFit e := notesEnvFit_holds e hPlace hFragC1
  have hPA : NotesParentAlign e := notesParentAlign_holds e hBC hNotePar hnd
  have hPL : NotesParentLocal e := notesParentLocal_holds e hBF hnd
  have hKC : NotesKeptClosed e := notesKeptClosed_holds e hBC hKept
  have hCBE : NotesContractBoxEq e := notesContractBoxEq_holds e hBC hnd
  have hFBE : NotesFragBoxEq e := notesFragBoxEq_holds e hBF hnd
  exact ⟨hFM, hCM, hFRM, hEnv, hPA, hPL, hKC, hCBE, hFBE⟩

end PipelineImpl
end Layered
end Elegant
