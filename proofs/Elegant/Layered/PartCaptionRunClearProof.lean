import Elegant.Layered.Pipeline
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.PartFrameCoresProof
import Elegant.Layered.LabelsC8b
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.LabelsC8bFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl
/-! # Bounded run-level caption clearance

`CaptionRunClear` (`Elegant/Layered/PartFrameCoresProof.lean`) now carries
the bound `pos < cg.nodes.length`, excluding the out-of-bounds `frameRect`
default-node case the probe `proofs/wip/Probe/PartCaptionRunClear.lean`
refuted (case A, vector `TB`: title
`(0, { x := 1992, y := 1024, w := 672, h := 1280 })` against
`pos = 4 = cg.nodes.length` with
`frameRect = { x := 1992, y := 0, w := 672, h := 2304 }`). All 330 probe
violations are of that shape; all 2850 in-bounds pairs satisfy the
disjunction, including the vector LR/RL directions.

`CaptionLocalClear` is the single local residual: for every executed run,
self strictness plus clearance against every related frame position (same
declaration or a declaration containment either way, covering ancestors,
descendants, members, and markers of the same group). It is pinned to
executed runs (the `measuredGraph`/`components`/`componentRun` equations
are antecedents), strictly simpler than the goal (no foreign-span content),
used below, and tested by the probe over 11 inputs and 6 direction/profile
configs (`self`/`rel`/`anc`/`desc`/`mem` tallies: 510 self-strict, 2400
related of which 180 ancestor-frame, 180 descendant-frame and 1530 member,
zero violations).

`captionRunClear` discharges the bounded statement from the residual and
one seam-composition hypothesis, `ForeignSpansClear` for the executed run,
which is exactly what `foreignSpansClear_of_run` produces from the two open
seams `ForeignBorderSpansSeparated` and `ForeignNonGroupSpansClear`. Step-2
partial: `captionSelfTop` proves the top edge of self-strictness (frame top
below the caption by one positive `clusterPad`); the other three edges, the
ancestor case, and the descendant/member cases stay in the residual pending
marker/member band geometry.
The seam step is taken in that composed form while `ForeignSpansFacts` is
blocked by another worker's `RecursiveC78.lean:456` type mismatch; the
switch to the two named seam hypotheses is a pure restatement once that
module builds. -/
/-- The transport's measured caption size at a component index: the
`titleCaptionSize` block of the group's wrapped text lines. `CaptionRunClear`
is only claimed at these sizes (an arbitrary `capSize` is false in general:
an oversized caption need not fit its frame). -/
def transportCapSize (P : Params) (o : Options)
    (lines : List (List Measure.Line)) (comp : List Nat) (i : Nat) :
    Int × Int :=
  ((titleCaptionSize P o (lines.getD (comp.getD i 0) [])).w,
    (titleCaptionSize P o (lines.getD (comp.getD i 0) [])).h)

/-- The installed title caption resized to the transport's measured size. -/
def transportCaption (P : Params) (o : Options)
    (lines : List (List Measure.Line)) (comp : List Nat) (i : Nat)
    (stored0 : Rect) : Rect :=
  { stored0 with
    w := (transportCapSize P o lines comp i).1,
    h := (transportCapSize P o lines comp i).2 }

/-- Residual (local title-band clearance): for every executed component run,
every installed title caption at the transport's measured size is strictly
inside its own frame, and is clear of every related frame position (same
declaration, or a declaration containment either way). Unrelated positions
are not mentioned; they go through the foreign-span seam hypothesis. -/
def CaptionLocalClear (P : Params) : Prop :=
  ∀ {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph},
  measuredGraph P inp o lines = .ok graph →
  ∀ {comp : List Nat}, comp ∈ components graph →
  ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions},
  componentRun P (componentCandidate graph comp candidate) labels
    orderOptions = .ok run →
  (∀ (i : Nat) (stored0 : Rect) (tNode : Node),
    (i, stored0) ∈ componentTitles P
      (componentCandidate graph comp candidate) run →
      (componentCandidate graph comp candidate).nodes[i]? = some tNode →
      tNode.border = -2 →
      (frameRect P (componentCandidate graph comp candidate) run i).StrictInside
        (transportCaption P o lines comp i stored0)) ∧
  (∀ (i : Nat) (stored0 : Rect) (tNode : Node),
    (i, stored0) ∈ componentTitles P
      (componentCandidate graph comp candidate) run →
      (componentCandidate graph comp candidate).nodes[i]? = some tNode →
      tNode.border = -2 →
      ∀ (pos : Nat) (fNode : Node) (g0 : Rect),
        (componentCandidate graph comp candidate).nodes[pos]? = some fNode →
        (tNode.decl = fNode.decl ∨
          fNode.clusterPath.contains tNode.decl = true ∨
          tNode.clusterPath.contains fNode.decl = true) →
        frameRect P (componentCandidate graph comp candidate) run pos = g0 →
        Disjoint g0 (transportCaption P o lines comp i stored0) ∨
        g0.StrictInside (transportCaption P o lines comp i stored0))
/-- Strict inside implies contained, over the four bounds. -/
private theorem strictInside_contained {o i : Rect}
    (h : o.StrictInside i) : o.Contained i := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- Run-level caption clearance for executed runs: related frames by
the residual, unrelated frames by seam disjointness transported through
caption containment in the own frame. -/
theorem captionRunClear {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hg : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (hclear : ForeignSpansClear P (componentCandidate graph comp candidate)
      run)
    (hlocal : CaptionLocalClear P) :
    CaptionRunClear P (componentCandidate graph comp candidate) run
      (transportCapSize P o lines comp) := by
  unfold CaptionRunClear
  intro i stored0 tNode hmem hnode hborder pos g0 hpos hframe
  have hinst := hlocal hg hcomp hrun
  cases hfn : (componentCandidate graph comp candidate).nodes[pos]? with
  | none =>
    rw [List.getElem?_eq_none_iff] at hfn
    omega
  | some fNode =>
    by_cases hrel : tNode.decl = fNode.decl ∨
        fNode.clusterPath.contains tNode.decl = true ∨
        tNode.clusterPath.contains fNode.decl = true
    · exact hinst.2 i stored0 tNode hmem hnode hborder pos fNode g0
        hfn hrel hframe
    · have hne : tNode.decl ≠ fNode.decl := fun h => hrel (Or.inl h)
      have hpathW : fNode.clusterPath.contains tNode.decl = false := by
        cases hc : fNode.clusterPath.contains tNode.decl with
        | true => exact absurd (Or.inr (Or.inl hc)) hrel
        | false => rfl
      have hpathU : tNode.clusterPath.contains fNode.decl = false := by
        cases hc : tNode.clusterPath.contains fNode.decl with
        | true => exact absurd (Or.inr (Or.inr hc)) hrel
        | false => rfl
      have hdisj := hclear i pos tNode fNode hnode hfn hborder hne
        hpathW hpathU
      have hself := hinst.1 i stored0 tNode hmem hnode hborder
      have hcont := strictInside_contained hself
      rw [hframe] at hdisj
      exact Or.inl ((Disjoint.comm _ _).mp (disjoint_of_sub_disjoint hcont hdisj))

/-- Title-index uniqueness for installed titles (local copy of the private
`CaptionWidthFacts.component_caption_indices_nodup`): titles install at most
one rect per component index. -/
private theorem captionTitles_keys_nodup (P : Params) (cg : Graph) (run : Run) :
    ((componentTitles P cg run).map Prod.fst).Nodup := by
  let emit : Node × Nat → Option (Nat × Rect) := fun top => do
    if top.1.border != -2 then none else do
      let title ← run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath)
      let frame := frameRect P cg run top.2
      pure (top.2, Rect.mk
        (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
        (frame.y + P.clusterPad) top.1.w (top.1.h - P.clusterPad))
  have identity : ∀ top caption, emit top = some caption → caption.1 = top.2 := by
    intro top caption he
    unfold emit at he
    split at he
    · contradiction
    · cases hf : run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
      | none => simp [hf] at he
      | some title =>
        simp [hf] at he
        subst caption
        rfl
  have hindices : (cg.nodes.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hp := List.pairwise_map.mp hindices
  change ((componentTitles P cg run).map Prod.fst).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  change (cg.nodes.zipIdx.filterMap emit).Pairwise (fun a b => a.1 ≠ b.1)
  apply List.Pairwise.filterMap emit _ hp
  intro a b hne ca hca cb hcb
  rw [identity a ca hca, identity b cb hcb]
  exact hne

/-- Two installed titles at one index agree. -/
theorem captionTitles_at_inj {l : List (Nat × Rect)}
    (hn : (l.map Prod.fst).Nodup) {i : Nat} {a b : Rect}
    (h1 : (i, a) ∈ l) (h2 : (i, b) ∈ l) : a = b := by
  revert hn h1 h2
  induction l with
  | nil => intro hn h1 h2; simp at h1
  | cons hd tl ih =>
    intro hn h1 h2
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hne, hnodup⟩ := hn
    simp only [List.mem_cons] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact congrArg Prod.snd (h1.trans h2.symm)
    · subst h1
      exact absurd (List.mem_map.mpr ⟨(i, b), h2, rfl⟩) hne
    · subst h2
      exact absurd (List.mem_map.mpr ⟨(i, a), h1, rfl⟩) hne
    · exact ih hnodup h1 h2

/-- The installed title caption starts strictly below its own frame top, by
one positive `clusterPad` (Step-2 partial: the top edge of self-strictness;
the remaining three edges need marker/member geometry). -/
theorem captionSelfTop {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (_hg : measuredGraph P inp o lines = .ok graph) (hchecked : checkedParams o.profile inp.kind = .ok P)
    {comp : List Nat} (_hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {i : Nat} {stored0 : Rect} {tNode : Node}
    (hmem : (i, stored0) ∈ componentTitles P
      (componentCandidate graph comp candidate) run)
    (hnode : (componentCandidate graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2) :
    (frameRect P (componentCandidate graph comp candidate) run i).y <
      (transportCaption P o lines comp i stored0).y := by
  obtain ⟨_, _, _, _, _, hplace⟩ :=
    componentRun_group_caption_placement_source hrun hnode hborder
  have hnodup :=
    captionTitles_keys_nodup P (componentCandidate graph comp candidate) run
  have huniq := captionTitles_at_inj hnodup hmem hplace
  have hpad := checkedParams_clusterPad_pos hchecked
  unfold transportCaption transportCapSize
  rw [huniq]

  show (frameRect P (componentCandidate graph comp candidate) run i).y <
    (frameRect P (componentCandidate graph comp candidate) run i).y + P.clusterPad
  omega

end Elegant.Layered.PipelineImpl
