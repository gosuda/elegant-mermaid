import Elegant.Layered.NotesFlatRouteClauses
import Elegant.Layered.VisibilityClearance

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Note-stage router invariant (orthogonality discharged).

Proves `notesRouterOrtho` from `NotesFlatRouteClauses.lean` for arbitrary
rectangles (router clause C4: every successful `routeAround` output is
orthogonal), so the flat record `NotesFlatFacts` carries no router field. The
consumer is `notes_c4`, which applies `notesRouterOrtho_holds` to the executed
arguments `e.atts`, `notesFrameOf e.contracted o e.margin`,
`notesRectsOf res.scene.boxes`, `notesLabelsOf`, `notesTitlesOf`.

Router invariant (W form, only local premises): every `prev` edge written by
`Grid.relax`/`Grid.run` is an axis-aligned cleared neighbour step
(`Visibility.PrevOK`, already proved preserved by `relax_prev`/`run_prev`).
The reconstructed `Grid.chain` is hence orthogonal by induction on its fuel
(each new head shares `x` or `y` with the accumulator head); `compress` keeps
orthogonality by induction on its fold (collinear middles are dropped, outer
endpoints kept); `Frame.output` (shift after orient) keeps orthogonality by
`isOrthogonal_shift_orient`. No global `WellFormed` premise is used for
orthogonality: the statement is unconditional and true for arbitrary rects.

Probes (`proofs/wip/Probe/NotesRouterInvariantT_probe.lean`): executed
`routeAround` on `res.scene.boxes` rects gives `ortho=true ends=true` for
state note, group note, two notes on one box, empty-text note, and zero-size
fixed box; `self` (self-loop on a note) and `nested` (note on inner group with
foreign parent) are rejected by `layoutNotes` with `LayoutError.domain` (no
false success); synthetic `routeAround` on the self-loop with manual rects
succeeds with one point `[{x:=12,y:=2}]` (orthogonal, on the note boundary).

Status of each remaining fact, all true on the probes above and on
`NotesRouteFacts2T_probe` which shows all seven Bool images true on
state/group/two/empty:
* Router ends are settled for actual executions: `nriRouterPathExec` gets
  endpoint membership from `NotesRoutePortTransport.routeAround_endpoints_mem`
  and seed starts from `VisibilityShortestSource`; `nriRouterEndsExec` then
  needs only nonnegative looked-up dims, which `RegionNotesDimensions` supplies
  for regional note runs. General arbitrary rectangles still require
  nonnegative dims (negative-width witness in `NotesRouteFacts`).
* `notesFlagsKept`: residual `nriFlagsKeptW` (same statement on the executed
  `e.layouts`/`e.contracted` plus local `WellFormed`; future proof needs the
  base-side kept premise plus `contractOne`/fuel induction).
* `notesFlagsFragment`: residual `nriFlagsFragmentW` (executed fragments plus
  local `WellFormed`; same base-side induction as above).
* `notesKeptBoxContracted`: residual `nriKeptBoxW` (executed `e.placed` plus
  local `WellFormed`; future proof needs kept ends to avoid every layout note
  id, i.e. footprint disjointness).
The proved `notesEndsInBoxes_holds`/`notesFragBoxFirst_holds` are reused, not
restated.
-/

/-- Narrowed form of `notesRouterEnds` for executed router arguments: the
unconditional tracked def instantiated at `notesFrameOf`/`notesRectsOf`/
`notesLabelsOf`/`notesTitlesOf`, under local `WellFormed`. Proved for regional
note executions by `RegionNotesRouterEnds.region_router_ends`. -/
def nriRouterEndsExec (inp : Input) (o : Options) (res : FamilyResult)
    (contracted : FamilyResult) (fragments : List Placed) (atts : List Attach)
    (margin : Int) : Prop :=
  WellFormed (inputModel inp o) →
    notesRouterEnds inp atts (notesFrameOf contracted o margin)
      (notesRectsOf res.scene.boxes) (notesLabelsOf fragments contracted inp)
      (notesTitlesOf fragments contracted)

/-- Narrowed residual for `notesFlagsKept`: executed layouts/contracted plus
local `WellFormed`. -/
def nriFlagsKeptW (inp : Input) (o : Options) (layouts : List BundleLayout)
    (contracted : FamilyResult) : Prop :=
  WellFormed (inputModel inp o) → notesFlagsKept inp layouts contracted

/-- Narrowed residual for `notesFlagsFragment`: executed fragments plus local
`WellFormed`. -/
def nriFlagsFragmentW (inp : Input) (o : Options) (layouts : List BundleLayout)
    (fragments : List Placed) : Prop :=
  WellFormed (inputModel inp o) → notesFlagsFragment inp layouts fragments

/-- Narrowed residual for `notesKeptBoxContracted`: executed placement plus
local `WellFormed`. -/
def nriKeptBoxW (inp : Input) (o : Options) (placed : List (List Placed))
    (r : ModelRoute) : Prop :=
  WellFormed (inputModel inp o) → notesKeptBoxContracted placed r

private theorem nri_collinear_aligned {b c p : Point}
    (h : Visibility.collinear b c p = true) :
    b.x = p.x ∨ b.y = p.y := by
  unfold Visibility.collinear at h
  rw [Bool.or_eq_true] at h
  rcases h with hx | hy
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hx
    exact Or.inl (hx.1.trans hx.2)
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hy
    exact Or.inr (hy.1.trans hy.2)

private theorem nri_chain_ortho (g : Visibility.Grid)
    (prev : Std.HashMap Visibility.Vertex Visibility.Vertex)
    (haxis : ∀ v w, prev[v]? = some w →
      (g.point w).x = (g.point v).x ∨ (g.point w).y = (g.point v).y) :
    ∀ (fuel : Nat) (v : Visibility.Vertex) (acc : List Point),
      Polyline.isOrthogonal acc = true →
      (∀ a, acc.head? = some a →
        (g.point v).x = a.x ∨ (g.point v).y = a.y) →
      Polyline.isOrthogonal (g.chain prev fuel v acc) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro v acc hacc hhead
      show Polyline.isOrthogonal (g.point v :: acc) = true
      cases acc with
      | nil => rfl
      | cons a t =>
          have hal := hhead a (by simp)
          rw [Polyline.isOrthogonal_cons]
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
          exact ⟨hal, hacc⟩
  | succ f ih =>
      intro v acc hacc hhead
      show Polyline.isOrthogonal (match prev[v]? with
        | none => g.point v :: acc
        | some p => g.chain prev f p (g.point v :: acc)) = true
      cases hv : prev[v]? with
      | none =>
          cases acc with
          | nil => rfl
          | cons a t =>
              have hal := hhead a (by simp)
              rw [Polyline.isOrthogonal_cons]
              simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
              exact ⟨hal, hacc⟩
      | some p =>
          have hcons : Polyline.isOrthogonal (g.point v :: acc) = true := by
            cases acc with
            | nil => rfl
            | cons a t =>
                have hal := hhead a (by simp)
                rw [Polyline.isOrthogonal_cons]
                simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
                exact ⟨hal, hacc⟩
          have hhead2 : ∀ a, (g.point v :: acc).head? = some a →
              (g.point p).x = a.x ∨ (g.point p).y = a.y := by
            intro a ha
            have hhd : (g.point v :: acc).head? = some (g.point v) := rfl
            have hea : g.point v = a := Option.some.inj (hhd.symm.trans ha)
            subst hea
            exact haxis v p hv
          exact ih p (g.point v :: acc) hcons hhead2

private theorem nri_pairs_remove_mid (P : Point → Point → Prop)
    (A : List Point) (b c p : Point) (B : List Point)
    (hal : P b p)
    (h : RouteImpl.pairsAll P (A ++ [b, c, p] ++ B)) :
    RouteImpl.pairsAll P (A ++ [b, p] ++ B) := by
  induction A with
  | nil =>
      have h2 : RouteImpl.pairsAll P (b :: c :: p :: B) := by simpa using h
      have htail : RouteImpl.pairsAll P (p :: B) := h2.2.2
      show RouteImpl.pairsAll P (b :: p :: B)
      exact ⟨hal, htail⟩
  | cons x xs ih =>
      cases xs with
      | nil =>
          have h2 : RouteImpl.pairsAll P (x :: b :: c :: p :: B) := by simpa using h
          have htail : RouteImpl.pairsAll P (p :: B) := h2.2.2.2
          show RouteImpl.pairsAll P (x :: b :: p :: B)
          exact ⟨h2.1, hal, htail⟩
      | cons y rest =>
          have h2 : P x y ∧ RouteImpl.pairsAll P ((y :: rest) ++ [b, c, p] ++ B) := h
          have ihr := ih h2.2
          show RouteImpl.pairsAll P (x :: ((y :: rest) ++ [b, p] ++ B))
          exact ⟨h2.1, ihr⟩

private theorem nri_compressStep_ortho (acc : List Point) (p : Point)
    (pts : List Point)
    (hP : Polyline.isOrthogonal (acc.reverse ++ p :: pts) = true) :
    Polyline.isOrthogonal ((Visibility.compressStep acc p).reverse ++ pts) = true := by
  cases acc with
  | nil =>
      simp only [Visibility.compressStep]
      simpa using hP
  | cons a acc' =>
      cases acc' with
      | nil =>
          simp only [Visibility.compressStep]
          simpa using hP
      | cons b rest =>
          simp only [Visibility.compressStep]
          by_cases hc : Visibility.collinear b a p = true
          · rw [ite_eq_left hc]
            have hnorm : Polyline.isOrthogonal
                (rest.reverse ++ [b, a, p] ++ pts) = true := by
              simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
                List.nil_append] using hP
            have hal : b.x = p.x ∨ b.y = p.y := nri_collinear_aligned hc
            have hpair := (RouteImpl.isOrthogonal_iff _).mp hnorm
            have hres := nri_pairs_remove_mid _ _ b a p _ hal hpair
            have hback := (RouteImpl.isOrthogonal_iff _).mpr hres
            simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
              List.nil_append] using hback
          · rw [ite_eq_right hc]
            simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
              List.nil_append] using hP


private theorem nri_compress_ortho (pts : List Point)
    (h : Polyline.isOrthogonal pts = true) :
    Polyline.isOrthogonal (Visibility.compress pts) = true := by
  rw [Visibility.compress_eq_foldl]
  suffices key : ∀ (acc pts : List Point),
      Polyline.isOrthogonal (acc.reverse ++ pts) = true →
      Polyline.isOrthogonal ((List.foldl Visibility.compressStep acc pts).reverse) = true by
    have := key [] pts (by simpa using h)
    simpa using this
  intro acc pts hP
  induction pts generalizing acc with
  | nil =>
      simpa using hP
  | cons p pts ih =>
      rw [List.foldl_cons]
      exact ih _ (nri_compressStep_ortho acc p pts hP)

private theorem nri_shortest_ortho (g : Visibility.Grid)
    (starts ends : List Point) (pts : List Point)
    (h : g.shortest starts ends = some pts) :
    Polyline.isOrthogonal pts = true := by
  unfold Visibility.Grid.shortest at h
  obtain ⟨seeded, hseed, hrest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨last, s⟩, hrun, hG⟩ := Option.bind_eq_some_iff.mp hrest
  have hpts : Visibility.compress (g.chain s.prev (s.prev.size + 1) last []) = pts :=
    Option.some.inj hG
  have hprev0 : Visibility.PrevOK g seeded := by
    intro v w hvw
    rw [Visibility.seed_prev_empty hseed] at hvw
    simp at hvw
  have hprev : Visibility.PrevOK g s :=
    Visibility.run_prev g ends _ seeded hprev0 last s hrun
  have haxis : ∀ v w, s.prev[v]? = some w →
      (g.point w).x = (g.point v).x ∨ (g.point w).y = (g.point v).y :=
    fun v w hvw => (hprev v w hvw).2
  have hchain : Polyline.isOrthogonal
      (g.chain s.prev (s.prev.size + 1) last []) = true :=
    nri_chain_ortho g s.prev haxis _ last [] (by simp [Polyline.isOrthogonal])
      (fun a ha => by simp at ha)
  have hcomp : Polyline.isOrthogonal
      (Visibility.compress (g.chain s.prev (s.prev.size + 1) last [])) = true :=
    nri_compress_ortho _ hchain
  rw [hpts] at hcomp
  exact hcomp

private theorem nri_frame_output_ortho (frame : Frame) (pts : List Point)
    (h : Polyline.isOrthogonal pts = true) :
    Polyline.isOrthogonal (pts.map frame.output) = true := by
  have heq : pts.map frame.output =
      pts.map (fun p => shiftPoint frame.margin frame.margin
        (orientPoint frame.direction frame.height p)) := rfl
  rw [heq]
  exact (isOrthogonal_shift_orient frame.direction frame.height
    frame.margin frame.margin pts).mpr h

theorem notesRouterOrtho_holds (inp : Input) (atts : List Attach)
    (frame : Frame) (rects : List (String × Rect))
    (labels : List SceneLabel) (titles : List (String × Rect)) :
    notesRouterOrtho inp atts frame rects labels titles := by
  intro r hr pts hroute
  unfold routeAround at hroute
  cases hfrom : rects.lookup r.fromId with
  | none => simp [hfrom] at hroute
  | some from_ =>
      cases hto : rects.lookup r.toId with
      | none => simp [hfrom, hto] at hroute
      | some to_ =>
          simp only [hfrom, hto] at hroute
          split at hroute
          · simp at hroute
          · next points heq =>
              have hpts : points.map frame.output = pts := Except.ok.inj hroute
              rw [← hpts]
              exact nri_frame_output_ortho frame points
                (nri_shortest_ortho _ _ _ _ heq)

end PipelineImpl

end Layered
end Elegant
