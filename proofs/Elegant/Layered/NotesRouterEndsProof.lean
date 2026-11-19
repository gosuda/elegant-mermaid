import Elegant.Layered.NotesRouterInvariantProof
import Elegant.GridFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Note-stage router ends: endpoint keeping proved, search step residual.

Proves the endpoint-keeping halves of `notesRouterEnds` (the C5 router fact
consumed by `notes_c5`): `Visibility.compress` keeps the first and last
point (`nrep_compress_endpoints`, by fold induction following the `simplify`
endpoint pattern in `Elegant.GridSimplify`); `Visibility.Grid.chain` ends at
its target and its head does not depend on the accumulator
(`nrep_chain_getLast`, `nrep_chain_head_acc`, so a chain that reaches a seed
within its fuel runs from that seed to the target); every
`Visibility.ports` point lies on its rect boundary for nonnegative dims
(`nrep_ports_mem_boundary`, via `Elegant.Grid.fdiv_fmod_nonneg`); `Frame`
framing keeps dimensions nonnegative and `Frame.output` maps framed-boundary
points back onto the source boundary (`nrep_frame_rect_nonneg`,
`nrep_frame_output_boundary`, combined in `nrep_map_ports_boundary`).

Stays open as ONE public named residual: `nriRouterPathExec` (executed
`layoutNotes` arguments). It states rect nonnegativity and that every
successful `routeAround` output starts and ends in the mapped port sets. It
is a lemma on the way to `notesRouterEnds` (membership in the mapped ports,
not yet boundary), strictly narrower than the tracked open def
`nriRouterEndsExec`, and true on the probe below. Its future proof carries
the search-completeness half that is not attempted here: the `Grid.run`
found-end containment and the dist-decrease fuel-sufficiency theory that lets
the `nrep_chain_*` lemmas fire on executed runs. The unguarded form is known
to be false: `NotesRouteFacts` records that the negative-width rect
`("a", (0, 0, -5, 4))` routes successfully while no point satisfies
`onBoundary`, so the nonnegativity premise cannot be dropped.

Probe (`proofs/wip/Probe/NotesRouterEndsT_probe.lean`): residual Bool image
(nonneg rects; successful outputs start and end in the mapped ports) is true
for state, group, two-notes, empty-text (no-space), and zero-size-fixed
inputs via executed `layoutNotes`, and for the synthetic self-loop
`routeAround` with manual rects; `nested` is rejected by `layoutNotes` with
`LayoutError.domain` as in the ortho probe.

Assembly: `nriRouterEndsExec_of_parts` derives `nriRouterEndsExec` from the
residual plus the proved port/frame bridge.
-/

/-! ### `compress` keeps the first and last point -/

private theorem nrep_step_head (acc : List Point) (p : Point) :
    (Visibility.compressStep acc p).head? = some p := by
  cases acc with
  | nil => rfl
  | cons c t =>
    cases t with
    | nil => rfl
    | cons b rest =>
      simp only [Visibility.compressStep]
      by_cases hc : Visibility.collinear b c p = true
      · rw [ite_eq_left hc]
        rfl
      · rw [ite_eq_right hc]
        rfl

private theorem nrep_step_last (acc : List Point) (p : Point) :
    (Visibility.compressStep acc p).getLast? =
      (if acc = [] then some p else acc.getLast?) := by
  cases acc with
  | nil => rfl
  | cons c t =>
    cases t with
    | nil => rfl
    | cons b rest =>
      have hne : (c :: b :: rest : List Point) ≠ [] := by simp
      simp only [Visibility.compressStep]
      by_cases hc : Visibility.collinear b c p = true
      · rw [ite_eq_left hc]
        simp only [hne, ite_false, List.getLast?_cons_cons]
      · rw [ite_eq_right hc]
        simp only [hne, ite_false, List.getLast?_cons_cons]

private theorem nrep_fold_head :
    ∀ (ps acc : List Point), (ps.foldl Visibility.compressStep acc).head? =
      (match ps.getLast? with | some p => some p | none => acc.head?) := by
  intro ps
  induction ps with
  | nil => intro acc; rfl
  | cons p ps ih =>
    intro acc
    simp only [List.foldl_cons, ih]
    cases ps with
    | nil => exact nrep_step_head acc p
    | cons q tail =>
      simp only [List.getLast?_cons_cons]
      cases hl : (q :: tail).getLast? with
      | none =>
        have hempty := List.getLast?_eq_none_iff.mp hl
        contradiction
      | some _last => rfl

private theorem nrep_fold_last :
    ∀ (ps acc : List Point), (ps.foldl Visibility.compressStep acc).getLast? =
      (if acc = [] then ps.head? else acc.getLast?) := by
  intro ps
  induction ps with
  | nil =>
    intro acc
    cases acc <;> simp
  | cons p ps ih =>
    intro acc
    rw [List.foldl_cons, ih]
    have hnonempty : Visibility.compressStep acc p ≠ [] := by
      intro he
      have hh := nrep_step_head acc p
      rw [he] at hh
      contradiction
    simp only [hnonempty, ite_false]
    rw [nrep_step_last]
    cases acc <;> simp

private theorem nrep_compress_endpoints (pts : List Point) :
    (Visibility.compress pts).head? = pts.head? ∧
      (Visibility.compress pts).getLast? = pts.getLast? := by
  rw [Visibility.compress_eq_foldl]
  constructor
  · rw [List.head?_reverse]
    exact nrep_fold_last pts []
  · change (pts.foldl Visibility.compressStep []).reverse.getLast? = pts.getLast?
    rw [List.getLast?_reverse, nrep_fold_head]
    cases pts.getLast? <;> rfl

/-! ### `chain` runs from its root to its target -/

private theorem nrep_chain_getLast (g : Visibility.Grid)
    (prev : Std.HashMap Visibility.Vertex Visibility.Vertex) :
    ∀ (fuel : Nat) (v : Visibility.Vertex) (acc : List Point),
    (g.chain prev fuel v acc).getLast? = (g.point v :: acc).getLast? := by
  intro fuel
  induction fuel with
  | zero =>
    intro v acc
    rfl
  | succ f ih =>
    intro v acc
    show (match prev[v]? with
      | none => g.point v :: acc
      | some parent => g.chain prev f parent (g.point v :: acc)).getLast? = _
    cases hv : prev[v]? with
    | none => rfl
    | some parent =>
      rw [ih]
      simp only [List.getLast?_cons_cons]

private theorem nrep_chain_head_acc (g : Visibility.Grid)
    (prev : Std.HashMap Visibility.Vertex Visibility.Vertex) :
    ∀ (fuel : Nat) (v : Visibility.Vertex) (acc1 acc2 : List Point),
    (g.chain prev fuel v acc1).head? = (g.chain prev fuel v acc2).head? := by
  intro fuel
  induction fuel with
  | zero =>
    intro v acc1 acc2
    rfl
  | succ f ih =>
    intro v acc1 acc2
    show (match prev[v]? with
      | none => g.point v :: acc1
      | some parent => g.chain prev f parent (g.point v :: acc1)).head? =
      (match prev[v]? with
      | none => g.point v :: acc2
      | some parent => g.chain prev f parent (g.point v :: acc2)).head?
    cases hv : prev[v]? with
    | none => rfl
    | some parent => exact ih _ _ _

private theorem nrep_ports_mem_boundary (r : Rect) (hw : 0 ≤ r.w) (hh : 0 ≤ r.h)
    (p : Point) (hm : p ∈ Visibility.ports r) :
    Validator.onBoundary p r := by
  have hwd := Elegant.Grid.fdiv_fmod_nonneg (pos := r.w) (columns := 2) hw (by omega)
  have hhd := Elegant.Grid.fdiv_fmod_nonneg (pos := r.h) (columns := 2) hh (by omega)
  unfold Visibility.ports at hm
  dsimp only at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · simp only [Validator.onBoundary]
    refine ⟨by omega, by omega, by omega, by omega, Or.inl trivial⟩
  · simp only [Validator.onBoundary]
    refine ⟨by omega, by omega, by omega, by omega, Or.inr (Or.inl trivial)⟩
  · simp only [Validator.onBoundary]
    refine ⟨by omega, by omega, by omega, by omega, Or.inr (Or.inr (Or.inl trivial))⟩
  · simp only [Validator.onBoundary]
    refine ⟨by omega, by omega, by omega, by omega, Or.inr (Or.inr (Or.inr trivial))⟩

private theorem nrep_frame_rect_nonneg (f : Frame) (r : Rect)
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) :
    0 ≤ (f.rect r).w ∧ 0 ≤ (f.rect r).h := by
  obtain ⟨dir, _, _⟩ := f
  cases dir <;> simp only [Frame.rect] <;> omega

private theorem nrep_frame_output_boundary (f : Frame) (r : Rect) (q : Point)
    (h : Validator.onBoundary q (f.rect r)) :
    Validator.onBoundary (f.output q) r := by
  obtain ⟨dir, _, _⟩ := f
  cases dir <;>
    simp only [Frame.rect, Frame.output, Validator.onBoundary, orientPoint] at h ⊢ <;>
    omega

private theorem nrep_map_ports_boundary (f : Frame) (r : Rect)
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) (p : Point)
    (hm : p ∈ (Visibility.ports (f.rect r)).map f.output) :
    Validator.onBoundary p r := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  have hnn := nrep_frame_rect_nonneg f r hw hh
  exact nrep_frame_output_boundary f r q
    (nrep_ports_mem_boundary (f.rect r) hnn.1 hnn.2 q hq)

/-! ### The single residual and the assembly -/

/-- Residual for `notesRouterEnds`: executed `layoutNotes` arguments.
Rect nonnegativity plus mapped-port endpoint membership of every successful
`routeAround` output. Strictly narrower than `nriRouterEndsExec` (membership,
not yet boundary); true on the probe inputs. -/
def nriRouterPathExec (inp : Input) (o : Options) (res : FamilyResult)
    (contracted : FamilyResult) (fragments : List Placed) (atts : List Attach)
    (margin : Int) : Prop :=
  ∀ r ∈ inp.routes, ∀ from_ to_ : Rect,
    (notesRectsOf res.scene.boxes).lookup r.fromId = some from_ →
    (notesRectsOf res.scene.boxes).lookup r.toId = some to_ →
    0 ≤ from_.w ∧ 0 ≤ from_.h ∧ 0 ≤ to_.w ∧ 0 ≤ to_.h ∧
    ∀ pts : List Point,
      routeAround inp atts (notesFrameOf contracted o margin)
        (notesRectsOf res.scene.boxes)
        (notesLabelsOf fragments contracted inp)
        (notesTitlesOf fragments contracted) r = .ok pts →
      ∃ p0 q0 : Point, pts.head? = some p0 ∧ pts.getLast? = some q0 ∧
        p0 ∈ (Visibility.ports ((notesFrameOf contracted o margin).rect from_)).map
          (notesFrameOf contracted o margin).output ∧
        q0 ∈ (Visibility.ports ((notesFrameOf contracted o margin).rect to_)).map
          (notesFrameOf contracted o margin).output

theorem nriRouterEndsExec_of_parts (inp : Input) (o : Options) (res : FamilyResult)
    (contracted : FamilyResult) (fragments : List Placed) (atts : List Attach)
    (margin : Int)
    (hRes : nriRouterPathExec inp o res contracted fragments atts margin) :
    nriRouterEndsExec inp o res contracted fragments atts margin := by
  intro _ r hr pts hroute
  have hpair : ∃ from_ to_ : Rect,
      (notesRectsOf res.scene.boxes).lookup r.fromId = some from_ ∧
      (notesRectsOf res.scene.boxes).lookup r.toId = some to_ := by
    have hrc := hroute
    unfold routeAround at hrc
    cases hfrom : (notesRectsOf res.scene.boxes).lookup r.fromId with
    | none => simp [hfrom] at hrc
    | some from_ =>
      cases hto : (notesRectsOf res.scene.boxes).lookup r.toId with
      | none => simp [hfrom, hto] at hrc
      | some to_ => exact ⟨from_, to_, rfl, rfl⟩
  obtain ⟨from_, to_, hfrom, hto⟩ := hpair
  have hR := hRes r hr from_ to_ hfrom hto
  obtain ⟨hfw, hfh, htw, hth, hmem⟩ := hR
  obtain ⟨p, q, hhead, hlast, hpmem, hqmem⟩ := hmem pts hroute
  exact ⟨from_, to_, p, q, hfrom, hto, hhead, hlast,
    nrep_map_ports_boundary _ _ hfw hfh _ hpmem,
    nrep_map_ports_boundary _ _ htw hth _ hqmem⟩

end PipelineImpl

end Layered
end Elegant
