import Elegant.Layered.NotesFlatBoxClauses

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Placement residuals for the note stage, closed over `NotesExecution`.

Probed truth before proving (all `true`, so no witness is recorded):
`proofs/wip/Probe/NotesPlacementFactsT_probe.lean` prints
`"dbl: bundles=2 frags=4 hPlace=true hFragC1=true hSelf=true hCross=true
hSame=true hAppl=true hApplF=true hSep=true hSepF=true"`;
`proofs/wip/Probe/NotesFlatBoxT_probe.lean` prints `boxFit/canvasFit/envFit/
envDisj/firstMatch/crossDisjointExceptTops/foreignClear/placedDisj` all `true`
on the state/group/two/empty inputs.

Each theorem closes one `NotesFlatBoxClauses` residual (`NotesC1Fit`,
`NotesEnvFit`, `NotesFirstMatch`, `NotesPlacedDisjoint`, `NotesForeignClear`)
from the execution record plus narrowly stated geometric premises. Every
premise is strictly narrower than its goal (fragment/envelope-level lookup or
containment facts, never a claim about `res`); the base-clause premises are
named `hBase` (`Validator.C1`/`Validator.C2` on `e.contracted`), as instructed.
-/

/-! ### Private plumbing (prefixed copies: other modules' privates do not resolve) -/

private theorem npf_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem npf_mapM_ok_of_mem {α β : Type} {f : α → Except LayoutError β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ {a : α}, a ∈ xs →
      ∃ b, f a = .ok b
  | [], _, _, _, ha => by simp at ha
  | _ :: _, _, h, _, ha => by
    simp only [List.mem_cons] at ha
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := npf_bind_ok h
    obtain ⟨bs, hbs, _⟩ := npf_bind_ok h
    rcases ha with rfl | ha'
    · exact ⟨b, hfb⟩
    · exact npf_mapM_ok_of_mem hbs ha'

/-- Every bundle layout has its footprint envelope box in the contracted scene:
`placedFragments` succeeded, so the top lookup succeeded. -/
private theorem npf_envelope_mem {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {l : BundleLayout} (hl : l ∈ e.layouts) :
    ∃ eb ∈ e.contracted.scene.boxes,
      eb.id = l.top.id ∧ eb.rect = envRect e.contracted.scene l := by
  obtain ⟨ps, hps⟩ := npf_mapM_ok_of_mem e.placed_eq hl
  cases hfind : e.contracted.scene.boxes.find? (fun b => b.id == l.top.id) with
  | none =>
    unfold placedFragments at hps
    rw [hfind] at hps
    simp at hps
  | some eb =>
    refine ⟨eb, List.mem_of_find?_eq_some hfind, ?_, ?_⟩
    · have hbe := List.find?_some hfind
      simpa only [beq_iff_eq] using hbe
    · simp only [envRect, hfind]

/-- `findSome?` returns the unique matching entry's value. -/
private theorem npf_findSome?_of_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (a : α) (v : β), a ∈ l → f a = some v →
      (∀ b ∈ l, b ≠ a → f b = none) → l.findSome? f = some v
  | [], _, _, ha, _, _ => by simp at ha
  | x :: xs, a, v, ha, hself, hothers => by
    simp only [List.mem_cons] at ha
    cases hfx : f x with
    | some w =>
      have hxa : x = a :=
        Classical.byContradiction fun hne => by
          have hnone := hothers x List.mem_cons_self hne
          rw [hfx] at hnone
          simp at hnone
      subst hxa
      have heq : w = v := Option.some.inj (hfx.symm.trans hself)
      subst heq
      rw [List.findSome?_cons, hself]
    | none =>
      rw [List.findSome?_cons, hfx]
      have hxa : x ≠ a := by
        intro h
        subst h
        rw [hself] at hfx
        simp at hfx
      exact npf_findSome?_of_mem f xs a v (ha.resolve_left (fun h => hxa h.symm))
        hself (fun b hb hne => hothers b (List.mem_cons_of_mem x hb) hne)

private theorem npf_meets_contained {i o x : Rect} (hc : o.Contained i)
    (h : i.meetsInterior x) : o.meetsInterior x := by
  unfold Rect.Contained Rect.meetsInterior at *
  omega

/-- Disjointness transports through containment on both sides. -/
private theorem npf_disjoint_of_subset {a' b' a b : Rect} (h : Disjoint a' b')
    (ha : a'.Contained a) (hb : b'.Contained b) : Disjoint a b := by
  unfold Disjoint at h ⊢
  intro hm
  exact h (npf_meets_contained ha ((Rect.meetsInterior_comm b' a).mp
    (npf_meets_contained hb ((Rect.meetsInterior_comm a b).mp hm))))

/-! ### The five placement facts -/

/-- The contracted canvas contains every placed fragment canvas. Needs the base
C1 (`hBase`: `Validator.C1` on `e.contracted`, named as instructed) and the
canvas-in-envelope placement fact (`hPlace`: each shifted fragment canvas lies
in its bundle envelope, i.e. the footprint-equation consequence). -/
theorem notesC1Fit_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C1 e.contracted.scene.layoutDump)
    (hPlace : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      (envRect e.contracted.scene l).Contained ⟨p.dx, p.dy, p.scene.canvas.w, p.scene.canvas.h⟩) :
    NotesC1Fit e := by
  intro p hp
  rw [e.fragments_eq] at hp
  obtain ⟨l, hl, hpl⟩ := placedFlatten_mem e.placed_eq hp
  obtain ⟨eb, heb, _, hebrect⟩ := npf_envelope_mem e hl
  have hc := hBase eb heb
  rw [hebrect] at hc
  have hpl2 := hPlace l hl p hpl
  simp only [Validator.canvasRect, Scene.layoutDump, Rect.Contained] at hc hpl2 ⊢
  omega

/-- Every shifted fragment box lies in its bundle envelope. Needs the same
canvas-in-envelope placement fact (`hPlace`) and fragment C1 (`hFrag`). -/
theorem notesEnvFit_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hPlace : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      (envRect e.contracted.scene l).Contained ⟨p.dx, p.dy, p.scene.canvas.w, p.scene.canvas.h⟩)
    (hFrag : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      Validator.C1 p.scene.layoutDump) :
    NotesEnvFit e := by
  intro l hl p hpl sb hsb
  have hC1 := hFrag l hl p hpl sb hsb
  have hpl2 := hPlace l hl p hpl
  simp only [Validator.canvasRect, Scene.layoutDump, shiftRect, Rect.Contained] at hC1 hpl2 ⊢
  omega

/-- The first fragment that knows a box id is the fragment holding it. Needs
fragment lookup uniqueness: the holding fragment resolves the id to its own
shifted rect (`hSelf`) and no other fragment resolves it (`hCross`, the
id-disjointness shape that `notes_boxes_nodup` proves for `res`). -/
theorem notesFirstMatch_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hSelf : ∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
      p.rect sb.id = some (shiftRect p.dx p.dy sb.rect))
    (hCross : ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
      ∀ sb ∈ p.scene.boxes, q.rect sb.id = none) :
    NotesFirstMatch e := by
  intro p hp sb hsb
  exact npf_findSome?_of_mem _ _ p _ hp (hSelf p hp sb hsb)
    (fun q hq hne => hCross p hp q hq (fun h => hne h.symm) sb hsb)

/-- Boxes of two different placed fragments are disjoint. Same-layout pairs use
the footprint separation (`hSame`); cross-layout pairs go through the base C2
clause (`hBase`: `Validator.C2` on `e.contracted`, named as instructed) applied
to the two envelope boxes, whose C2-applicability is `hAppl`, chaining through
the envelope fit (`hFit`). -/
theorem notesPlacedDisjoint_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C2 e.contracted.scene.layoutDump)
    (hAppl : ∀ la ∈ e.layouts, ∀ lb ∈ e.layouts, la ≠ lb →
      ∀ ea ∈ e.contracted.scene.boxes, ea.id = la.top.id →
      ∀ eb ∈ e.contracted.scene.boxes, eb.id = lb.top.id →
        ea.id ≠ eb.id ∧ ea.exclusive = true ∧ eb.exclusive = true ∧ ea.parent = eb.parent)
    (hFit : NotesEnvFit e)
    (hSame : ∀ l ∈ e.layouts, ∀ pa ∈ placedOf' e.margin e.contracted.scene l,
      ∀ pb ∈ placedOf' e.margin e.contracted.scene l, pa ≠ pb →
      ∀ sa ∈ pa.scene.boxes, ∀ sb ∈ pb.scene.boxes,
        Disjoint (shiftRect pa.dx pa.dy sa.rect) (shiftRect pb.dx pb.dy sb.rect)) :
    NotesPlacedDisjoint e := by
  intro pa hpa pb hpb hne sa hsa sb hsb
  rw [e.fragments_eq] at hpa hpb
  obtain ⟨la, hla, hpla⟩ := placedFlatten_mem e.placed_eq hpa
  obtain ⟨lb, hlb, hplb⟩ := placedFlatten_mem e.placed_eq hpb
  by_cases hll : la = lb
  · subst hll
    exact hSame la hla pa hpla pb hplb hne sa hsa sb hsb
  · obtain ⟨ea, hea, hidea, hrecta⟩ := npf_envelope_mem e hla
    obtain ⟨eb, heb, hideb, hrectb⟩ := npf_envelope_mem e hlb
    obtain ⟨hne_id, hexA, hexB, hpar⟩ := hAppl la hla lb hlb hll ea hea hidea eb heb hideb
    have hC2 := hBase ea hea eb heb hne_id hexA hexB hpar
    rw [hrecta, hrectb] at hC2
    have hfa := hFit la hla pa hpla sa hsa
    have hfb := hFit lb hlb pb hplb sb hsb
    exact npf_disjoint_of_subset hC2 hfa hfb

/-- A contracted box that no fragment claims is disjoint from every placed
fragment box. Goes through the base C2 clause (`hBase`) applied to the foreign
box and the fragment's envelope (applicability `hApplF`), chaining through the
envelope fit (`hFit`). -/
theorem notesForeignClear_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C2 e.contracted.scene.layoutDump)
    (hApplF : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cb ∈ e.contracted.scene.boxes,
        (∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) →
        cb.id ≠ eb.id ∧ cb.exclusive = true ∧ eb.exclusive = true ∧ cb.parent = eb.parent)
    (hFit : NotesEnvFit e) :
    NotesForeignClear e := by
  intro l hl p hpl sb hsb cb hcb hfor
  obtain ⟨eb, heb, hideb, hrectb⟩ := npf_envelope_mem e hl
  obtain ⟨hne_id, hexC, hexE, hpar⟩ := hApplF l hl eb heb hideb cb hcb hfor
  have hC2 := hBase cb hcb eb heb hne_id hexC hexE hpar
  rw [hrectb] at hC2
  have hfb := hFit l hl p hpl sb hsb
  exact npf_disjoint_of_subset ((Disjoint.comm _ _).mp hC2) hfb (Rect.Contained.refl _)
