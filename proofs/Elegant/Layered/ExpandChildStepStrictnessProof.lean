import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.Pipeline
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildCanvasFitProof
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# ExpandChild step strictness: widening core proved, universal strictness obstructed.

Proved here:
* `ecss_c1_widen_strict`: from the parent C1 clause plus a positive pad, every
  parent box lies strictly inside the parent canvas widened by that pad on
  every side (pure `omega` arithmetic over `Rect.Contained` / `Rect.StrictInside`).
* `ecss_parent_widen_strict`: the same core with the pad supplied by the call's
  checked parameters (`callParams_clusterPad_pos`), so the arithmetic half of
  the task holds for the validated parent scene. Both statements quantify over
  the parent dump only, with no recursion base in sight, hence the plain and
  the exact (`layoutX`) call sites use them unchanged.
* `ecss_hardConstraints_not_strictStep` and `ecss_hardConstraints_not_frameStrict`:
  `HardConstraints` (the `XSRP_ParentSceneValid` bundle) does NOT imply either
  open fact. Witness `ecss_flushParent` (flush equal rects, child parented to
  the group) satisfies the full eight-clause check yet breaks the strict step;
  witness `ecss_lblParent` (small foreign-owned label strictly inside the frame)
  satisfies the check through the C8b second disjunct yet breaks frame
  strictness. Both checks and both violations are closed by `decide`.

Open (not closed here):
* `ExpandChildParentFrameStrict` and `ExpandChildParentStrictStep` as universal
  consequences of the validated scene plus checked params: false as stated, by
  the witnesses above. What the step leaves need is the executed-call form.
* `ECSS_FrameStrictBoxCallB`: the strictly narrower executed-call residual kept
  for the C8b lift — frame strictness restricted to box-owned labels whose
  owner stays outside the strict descendants of the expanded group, stated over
  the base-parametric call context so both bases instantiate it. True on all
  seven executed `expandChild` calls of
  `proofs/wip/Probe/StepStrictnessTProbe.lean` (`StepStrictnessTCalls`:
  edgeIntoTitled, selfLoopGroup, nestedCross, noEdges, captionNested twice,
  zeroFixedCaption; every call reports `stepStrict=true frameStrict=true`);
  the betweenGroups input performs no call.
-/

/-- Arithmetic core: C1 plus a positive pad gives strict containment in the
widened canvas. Base-free, so both recursion bases use it. -/
theorem ecss_c1_widen_strict {d : LayoutDump} (hC1 : Validator.C1 d)
    {pad : Int} (hpad : 0 < pad) {b : Box} (hb : b ∈ d.boxes) :
    (⟨-pad, -pad, d.canvas.w + 2 * pad, d.canvas.h + 2 * pad⟩ : Rect).StrictInside
      b.rect := by
  have hc := hC1 b hb
  unfold Validator.canvasRect at hc
  simp only [Rect.Contained, Rect.StrictInside] at hc ⊢
  omega

/-- The core with the pad from the call's checked parameters. -/
theorem ecss_parent_widen_strict {P : Params} {o : Elegant.Options}
    {inp : Elegant.Layered.Input} (hP : checkedParams o.profile inp.kind = .ok P)
    {d : LayoutDump} (hC1 : Validator.C1 d) {b : Box} (hb : b ∈ d.boxes) :
    (⟨-P.clusterPad, -P.clusterPad, d.canvas.w + 2 * P.clusterPad,
      d.canvas.h + 2 * P.clusterPad⟩ : Rect).StrictInside b.rect := by
  have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
  exact ecss_c1_widen_strict hC1 hpad hb

/-- Flush witness: equal rects, child parented to the group. -/
private def ecss_flushParent : Elegant.Layered.FamilyResult :=
  { scene :=
    { kind := "flowchart"
      canvas := ⟨10, 10⟩
      boxes :=
        [ { id := "p", role := "group", rect := ⟨0, 0, 10, 10⟩, parent := "", exclusive := false }
        , { id := "b", role := "node", rect := ⟨0, 0, 10, 10⟩, parent := "p", exclusive := false } ]
      routes := []
      labels := [] }
    budgetExhausted := false }

private def ecss_flushDump : LayoutDump := ecss_flushParent.scene.layoutDump

/-- Obstruction: the validated scene does not imply the strict step. -/
theorem ecss_hardConstraints_not_strictStep :
    ∃ parent : Elegant.Layered.FamilyResult,
      HardConstraints parent.scene.layoutDump ∧
      ¬ ExpandChildParentStrictStep parent := by
  refine ⟨ecss_flushParent, ?_, ?_⟩
  · have h : Validator.check ecss_flushDump = true := by decide
    exact (Validator.check_iff ecss_flushDump).mp h
  · intro h
    have hb : (⟨"b", "node", ⟨0, 0, 10, 10⟩, "p", false⟩ : Box) ∈
        ecss_flushParent.scene.boxes := by decide
    have hpar : (⟨"b", "node", ⟨0, 0, 10, 10⟩, "p", false⟩ : Box).parent ≠ "" := by decide
    have hlook : ecss_flushParent.scene.layoutDump.box? "p" =
        some (⟨"p", "group", ⟨0, 0, 10, 10⟩, "", false⟩ : Box) := by decide
    have hrole : (⟨"p", "group", ⟨0, 0, 10, 10⟩, "", false⟩ : Box).role = "group" := rfl
    have hSI := h _ hb hpar _ hlook hrole
    exact absurd hSI (by decide)

private def ecss_frameG : Box := ⟨"G", "group", ⟨0, 0, 20, 20⟩, "", false⟩

private def ecss_lblX : Elegant.SceneLabel :=
  { id := "lx", owner := "x", rect := ⟨5, 5, 4, 4⟩, lines := [], text := "" }

/-- Label-inside witness: small foreign-owned label strictly inside the frame. -/
private def ecss_lblParent : Elegant.Layered.FamilyResult :=
  { scene :=
    { kind := "flowchart"
      canvas := ⟨20, 20⟩
      boxes := [ecss_frameG]
      routes := []
      labels := [ecss_lblX] }
    budgetExhausted := false }

private def ecss_lblDump : LayoutDump := ecss_lblParent.scene.layoutDump

/-- Obstruction: the validated scene does not imply frame strictness. -/
theorem ecss_hardConstraints_not_frameStrict :
    ∃ (group : Elegant.ModelBox) (parent : Elegant.Layered.FamilyResult),
      HardConstraints parent.scene.layoutDump ∧
      ¬ ExpandChildParentFrameStrict group parent := by
  refine ⟨{ id := "G", role := Elegant.BoxRole.group }, ecss_lblParent, ?_, ?_⟩
  · have h : Validator.check ecss_lblDump = true := by decide
    exact (Validator.check_iff ecss_lblDump).mp h
  · intro h
    have hfind : ecss_lblParent.scene.boxes.find? (fun box => box.id == "G") =
        some ecss_frameG := by decide
    have hmem : ecss_lblX ∈ ecss_lblParent.scene.labels := by decide
    have hown : ecss_lblX.owner ≠ "G" := by decide
    have hneg := h _ hfind _ hmem hown
    apply hneg
    decide

/-- Narrower residual for the C8b lift: frame strictness for box-owned labels
whose owner stays outside the strict descendants of the expanded group, over
one executed `expandChild` call at an arbitrary recursion base. Strictly
narrower than the open universal (one label class, descendant-scoped, call
scoped); true on every executed probe call. -/
def ECSS_FrameStrictBoxCallB
    (base : Elegant.Layered.Input → Elegant.Options → Except LayoutError
      Elegant.Layered.FamilyResult) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Elegant.Layered.Input) (o : Elegant.Options)
    (group : Elegant.ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : Elegant.Layered.FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
        (∃ b ∈ parent.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") →
        group.id ∉ parent.scene.layoutDump.ancestors pl.owner →
        ¬ frame.rect.StrictInside pl.rect

#eval Validator.check ecss_flushDump

#eval Validator.check ecss_lblDump

end Elegant.Layered.PipelineImpl
