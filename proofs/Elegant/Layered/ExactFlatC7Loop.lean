import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.LabelsC7RunLocal

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Exact flat C7 loop branch.

Proves `X_RunLocalLoopSeparation` by replaying `runLocalLoopSeparation`
over `componentRunX`. The plain proof uses no `componentRunX_spec` or
`coordinateGraph` facts: only the slot bound, measured nonnegativity, the
loop envelope equation, envelope-in-footprint containment, and the
containment transport. The exact counterparts of the first two exist
(`componentRunX_slot_nonneg`, `SceneExecutionX.measured_nonneg`); the
envelope lemmas need file-prefixed copies because the exact run carries a
nonempty `run.exact` in general, so the envelope branch is decided by the
`run.exact.contains e.tail` boolean instead of `run.exact = []`.

The footprint half stays the named residual `X_RunLocalLoopFootprint`,
the mirror of the plain `RunLocalLoopFootprint` (assumed by
`runLocalLoopSeparation` at `RunLocalSeparationsProof.lean:989` and
discharged in the plain pipeline only modulo the top/beyond residuals by
`runLocalLoopFootprint_executed` at `RunLocalLoopFootprintProof.lean:87`).
Both the plain-width and the exact-width envelope branches are contained
in the (branch-matching) footprint given the same reservation, so the one
residual covers both.
-/

/-- X loop-footprint residual: mirror of `RunLocalLoopFootprint` over
`componentRunX`. The loop reservation holds and the footprint misses every
in-scope real box. `loopFootprint` already branches on
`run.exact.contains`, so this one statement serves both the plain-width
and the exact-width envelope branches. -/
def X_RunLocalLoopFootprint (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (loopSizes cg.edges execution.measured e.tail cg.slot).length *
        Loops.band cg.slot (loopSizes cg.edges execution.measured e.tail cg.slot) ≤
      (frameRect execution.params cg run e.tail).h ∧
    ¬ (loopFootprint cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Invert the plain-width loop `labelEnvelope` branch over an exact run
(copy of `loop_envelope_eq` with the `contains = false` boolean in place
of `run.exact = []`). -/
private theorem XLoop_envelope_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hloop : e.tail = e.head) (hnoex : run.exact.contains e.tail = false)
    (henv : labelEnvelope P cg run labels k e = some env) :
    env = (Loops.placement (frameRect P cg run e.tail) cg.slot
      (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
      (loopEdges cg.edges e.tail).length
      (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
      (stackSize cg.slot (routeLabels labels e.decl))).label := by
  unfold labelEnvelope at henv
  obtain ⟨_first, _hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (e.tail == e.head) = true := by simp [hloop]
  simp only [hb, hnoex] at hrest
  exact (Option.some.inj hrest).symm

/-- Invert the exact-width loop `labelEnvelope` branch over an exact run
(`run.exact.contains e.tail = true` selects `Loops.exactPlacement`). -/
private theorem XLoop_exact_envelope_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hloop : e.tail = e.head) (hex : run.exact.contains e.tail = true)
    (henv : labelEnvelope P cg run labels k e = some env) :
    env = (Loops.exactPlacement (frameRect P cg run e.tail) cg.slot
      (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
      (loopEdges cg.edges e.tail).length
      (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
      (stackSize cg.slot (routeLabels labels e.decl))).label := by
  unfold labelEnvelope at henv
  obtain ⟨_first, _hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (e.tail == e.head) = true := by simp [hloop]
  simp only [hb, hex] at hrest
  exact (Option.some.inj hrest).symm

/-- The plain-width loop envelope is contained in the plain loop footprint,
given the loop reservation (copy of `loop_envelope_contained` with the
`contains = false` boolean in place of `run.exact = []`). -/
private theorem XLoop_envelope_contained {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hnoex : run.exact.contains e.tail = false)
    (hk : cg.edges[k]? = some e) (hloop : e.tail = e.head)
    (henv_eq : env = (Loops.placement (frameRect P cg run e.tail) cg.slot
      (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
      (loopEdges cg.edges e.tail).length
      (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
      (stackSize cg.slot (routeLabels labels e.decl))).label)
    (hrsv : (loopSizes cg.edges labels e.tail cg.slot).length *
        Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot) ≤
      (frameRect P cg run e.tail).h) :
    (loopFootprint cg run labels e.tail).Contained env := by
  have he0 : e ∈ loopEdges cg.edges e.tail := by
    have hkm : e ∈ cg.edges := List.mem_of_getElem? hk
    apply List.mem_filter.mpr
    exact ⟨hkm, by simp [hloop]⟩
  have hnn : ∀ s ∈ loopSizes cg.edges labels e.tail cg.slot, 0 ≤ s.width ∧ 0 ≤ s.height := by
    intro s hs
    obtain ⟨e', _he', rfl⟩ := List.mem_map.mp hs
    rw [stackSize_width_eq, stackSize_height_eq]
    refine ⟨Labels.stackWidth_nonneg _, ?_⟩
    exact Labels.stackHeight_nonneg _ hslot (fun t ht => by
      obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp ht
      exact (hlab l (List.mem_filter.mp hlm).1).2.1)
  obtain ⟨F, hF⟩ : ∃ F, F = frameRect P cg run e.tail := ⟨_, rfl⟩
  obtain ⟨sizes, hsizes⟩ : ∃ sizes, sizes = loopSizes cg.edges labels e.tail cg.slot := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = sizes.length := ⟨_, rfl⟩
  obtain ⟨band, hband⟩ : ∃ band, band = Loops.band cg.slot sizes := ⟨_, rfl⟩
  obtain ⟨idx, hidx⟩ : ∃ idx, idx = ((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl := ⟨_, rfl⟩
  obtain ⟨sz, hsz⟩ : ∃ sz, sz = stackSize cg.slot (routeLabels labels e.decl) := ⟨_, rfl⟩
  rw [← hF, ← hsizes, ← hband, ← hidx, ← hsz] at henv_eq
  rw [← hF, ← hsizes, ← hband] at hrsv
  rw [← hsizes] at hnn
  have hmem : sz ∈ sizes := by
    rw [hsizes, hsz]
    exact List.mem_map.mpr ⟨e, he0, rfl⟩
  have hnlen : (loopEdges cg.edges e.tail).length = n := by
    rw [hn, hsizes]
    exact (List.length_map _).symm
  have hidx : idx < n := by
    rw [hidx]
    have hmemd : e.decl ∈ (loopEdges cg.edges e.tail).map (·.decl) :=
     List.mem_map.mpr ⟨e, he0, rfl⟩
    have hlt := List.idxOf_lt_length_of_mem hmemd
    have hlen2 : ((loopEdges cg.edges e.tail).map (·.decl)).length = n :=
     (List.length_map _).trans hnlen
    rwa [hlen2] at hlt
  have hcount : 1 ≤ n := by omega
  have hband_nn : 0 ≤ band := by
    rw [hband]
    unfold Loops.band
    exact Int.le_trans (Int.mul_nonneg (by decide : (0 : Int) ≤ 2) hslot)
     (foldl_max_height_ge _ _)
  have hsz_band : sz.height ≤ band := by
    rw [hband]
    exact loopBand_ge_mem_aux _ _ _ hmem
  have hszw : ∀ s ∈ sizes, 0 ≤ s.width := fun s hs => (hnn s hs).1
  have hext := extent_ge_lane_width hslot hszw hmem (hn ▸ hcount)
  have hFirrel : frameRect P cg run e.tail = frameRect default cg run e.tail := rfl
  have hfp : loopFootprint cg run labels e.tail =
      ⟨F.x + F.w, F.y, Loops.extent cg.slot sizes, F.h⟩ := by
    rw [hF]
    have h1 : run.exact.contains e.tail = false := hnoex
    unfold loopFootprint
    simp only [h1, hFirrel, Bool.false_eq_true, ↓reduceIte]
    rw [← hsizes]
  have hpx : env.x = F.x + F.w + cg.slot * ((n : Int) + 1) := by
    rw [henv_eq]
    simp only [Loops.placement]
    rw [hnlen]
  have hpy : env.y = F.y + (idx : Int) * band + Int.fdiv band 2 -
      Int.fdiv sz.height 2 := by
    rw [henv_eq]
    simp only [Loops.placement]
  have hpw : env.w = sz.width := by
    rw [henv_eq]
    rfl
  have hph : env.h = sz.height := by
    rw [henv_eq]
    rfl
  have eband : Int.fdiv band 2 = band / 2 := fdiv2_ediv band
  have ehsz : Int.fdiv sz.height 2 = sz.height / 2 := fdiv2_ediv _
  have hA_nn : 0 ≤ (idx : Int) * band := Int.mul_nonneg (Int.natCast_nonneg _) hband_nn
  have hrow : (idx : Int) * band + band ≤ (n : Int) * band := by
    have h1 : ((idx : Int) + 1) * band ≤ (n : Int) * band :=
      Int.mul_le_mul_of_nonneg_right (by omega) hband_nn
    have h2 : ((idx : Int) + 1) * band = (idx : Int) * band + band := by
      rw [Int.add_mul, Int.one_mul]
    omega
  rw [← hn] at hrsv hext
  have hup : env.y + env.h ≤ F.y + F.h := by
    rw [hpy, hph, eband, ehsz]
    have hle : band / 2 - sz.height / 2 + sz.height ≤ band := by omega
    omega
  have hlo : F.y ≤ env.y := by
    rw [hpy, eband, ehsz]
    have hge : sz.height / 2 ≤ band / 2 := by omega
    omega
  have hleft : F.x + F.w ≤ env.x := by
    rw [hpx]
    have hpos : 0 ≤ cg.slot * ((n : Int) + 1) :=
      Int.mul_nonneg hslot (by omega)
    omega
  have hright : env.x + env.w ≤ F.x + F.w + Loops.extent cg.slot sizes := by
    rw [hpx, hpw]
    omega
  rw [hfp]
  unfold Rect.Contained
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
  · exact hleft
  · exact hright
  · exact hlo
  · exact hup

/-- Foldl max lower bound for loop label widths. -/
private theorem XLoop_foldl_max_width_ge (sizes : List LoopLabel) (acc : Int) :
    acc ≤ sizes.foldl (fun w l => max w l.width) acc := by
  induction sizes generalizing acc with
  | nil => exact Int.le_refl _
  | cons s rest ih =>
    simp only [List.foldl]
    exact Int.le_trans (Int.le_max_left acc s.width) (ih (max acc s.width))

/-- Foldl max over widths is monotone in its accumulator. -/
private theorem XLoop_foldl_max_width_mono (l : List LoopLabel) (acc acc' : Int)
    (h : acc ≤ acc') :
    l.foldl (fun w l => max w l.width) acc ≤
      l.foldl (fun w l => max w l.width) acc' := by
  induction l generalizing acc acc' with
  | nil => exact h
  | cons b rest ih =>
    simp only [List.foldl]
    exact ih _ _ (by omega)

/-- Every member width is bounded by the folded widest width. -/
private theorem XLoop_width_le_widest (sizes : List LoopLabel) (s : LoopLabel)
    (hmem : s ∈ sizes) :
    s.width ≤ sizes.foldl (fun w l => max w l.width) 0 := by
  induction sizes with
  | nil => simp at hmem
  | cons a rest ih =>
    simp only [List.foldl]
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Int.le_trans (Int.le_max_right _ _) (XLoop_foldl_max_width_ge rest _)
    · exact Int.le_trans (ih hmem)
        (XLoop_foldl_max_width_mono rest _ _ (Int.le_max_left _ _))

/-- The exact footprint covers the exact lane offset plus any member width:
`slot * (2 * n + 1) + s.width ≤ exactExtent`. -/
private theorem XLoop_exactExtent_lower {slot : Int} {sizes : List LoopLabel}
    {s : LoopLabel} (hmem : s ∈ sizes) (n : Nat) (hn : n = sizes.length) :
    slot * (2 * (n : Int) + 1) + s.width ≤ Loops.exactExtent slot sizes := by
  have hwide : s.width ≤ sizes.foldl (fun w l => max w l.width) 0 :=
    XLoop_width_le_widest sizes s hmem
  have hne : sizes.isEmpty = false := by
    cases sizes with
    | nil => simp at hmem
    | cons _ _ => rfl
  have hneg : ¬ (sizes.isEmpty = true) := by rw [hne]; decide
  have hexact : Loops.exactExtent slot sizes =
      slot * (2 * (sizes.length : Int) + 1) +
        sizes.foldl (fun w l => max w l.width) 0 := by
    unfold Loops.exactExtent
    simp only [hne, reduceCtorEq, ↓reduceIte]
  rw [hexact, ← hn]
  omega
/-- The exact-width loop envelope is contained in the exact loop footprint,
given the loop reservation (the label `y` argument is shared with the
plain branch; the `x` argument uses the widest-width bound). -/
private theorem XLoop_exact_envelope_contained {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hk : cg.edges[k]? = some e) (hloop : e.tail = e.head)
    (henv_eq : env = (Loops.exactPlacement (frameRect P cg run e.tail) cg.slot
      (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
      (loopEdges cg.edges e.tail).length
      (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
      (stackSize cg.slot (routeLabels labels e.decl))).label)
    (hrsv : (loopSizes cg.edges labels e.tail cg.slot).length *
        Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot) ≤
      (frameRect P cg run e.tail).h)
    (hex : run.exact.contains e.tail = true) :
    (loopFootprint cg run labels e.tail).Contained env := by
  have he0 : e ∈ loopEdges cg.edges e.tail := by
    have hkm : e ∈ cg.edges := List.mem_of_getElem? hk
    apply List.mem_filter.mpr
    exact ⟨hkm, by simp [hloop]⟩
  have hnn : ∀ s ∈ loopSizes cg.edges labels e.tail cg.slot, 0 ≤ s.width ∧ 0 ≤ s.height := by
    intro s hs
    obtain ⟨e', _he', rfl⟩ := List.mem_map.mp hs
    rw [stackSize_width_eq, stackSize_height_eq]
    refine ⟨Labels.stackWidth_nonneg _, ?_⟩
    exact Labels.stackHeight_nonneg _ hslot (fun t ht => by
      obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp ht
      exact (hlab l (List.mem_filter.mp hlm).1).2.1)
  obtain ⟨F, hF⟩ : ∃ F, F = frameRect P cg run e.tail := ⟨_, rfl⟩
  obtain ⟨sizes, hsizes⟩ : ∃ sizes, sizes = loopSizes cg.edges labels e.tail cg.slot := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = sizes.length := ⟨_, rfl⟩
  obtain ⟨band, hband⟩ : ∃ band, band = Loops.band cg.slot sizes := ⟨_, rfl⟩
  obtain ⟨idx, hidx⟩ : ∃ idx, idx = ((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl := ⟨_, rfl⟩
  obtain ⟨sz, hsz⟩ : ∃ sz, sz = stackSize cg.slot (routeLabels labels e.decl) := ⟨_, rfl⟩
  rw [← hF, ← hsizes, ← hband, ← hidx, ← hsz] at henv_eq
  rw [← hF, ← hsizes, ← hband] at hrsv
  rw [← hsizes] at hnn
  have hmem : sz ∈ sizes := by
    rw [hsizes, hsz]
    exact List.mem_map.mpr ⟨e, he0, rfl⟩
  have hnlen : (loopEdges cg.edges e.tail).length = n := by
    rw [hn, hsizes]
    exact (List.length_map _).symm
  have hidx : idx < n := by
    rw [hidx]
    have hmemd : e.decl ∈ (loopEdges cg.edges e.tail).map (·.decl) :=
     List.mem_map.mpr ⟨e, he0, rfl⟩
    have hlt := List.idxOf_lt_length_of_mem hmemd
    have hlen2 : ((loopEdges cg.edges e.tail).map (·.decl)).length = n :=
     (List.length_map _).trans hnlen
    rwa [hlen2] at hlt
  have hcount : 1 ≤ n := by omega
  have hband_nn : 0 ≤ band := by
    rw [hband]
    unfold Loops.band
    exact Int.le_trans (Int.mul_nonneg (by decide : (0 : Int) ≤ 2) hslot)
     (foldl_max_height_ge _ _)
  have hsz_band : sz.height ≤ band := by
    rw [hband]
    exact loopBand_ge_mem_aux _ _ _ hmem
  have hextX := XLoop_exactExtent_lower (slot := cg.slot) hmem n hn
  have hFirrel : frameRect P cg run e.tail = frameRect default cg run e.tail := rfl
  have hfp : loopFootprint cg run labels e.tail =
      ⟨F.x + F.w, F.y, Loops.exactExtent cg.slot sizes, F.h⟩ := by
    rw [hF]
    unfold loopFootprint
    simp only [hex, hFirrel, ↓reduceIte]
    rw [← hsizes]
  have hpx : env.x = F.x + F.w + cg.slot * (2 * (n : Int) + 1) := by
    rw [henv_eq]
    simp only [Loops.exactPlacement]
    rw [hnlen]
  have hpy : env.y = F.y + (idx : Int) * band + Int.fdiv band 2 -
      Int.fdiv sz.height 2 := by
    rw [henv_eq]
    simp only [Loops.exactPlacement]
  have hpw : env.w = sz.width := by
    rw [henv_eq]
    rfl
  have hph : env.h = sz.height := by
    rw [henv_eq]
    rfl
  have eband : Int.fdiv band 2 = band / 2 := fdiv2_ediv band
  have ehsz : Int.fdiv sz.height 2 = sz.height / 2 := fdiv2_ediv _
  have hA_nn : 0 ≤ (idx : Int) * band := Int.mul_nonneg (Int.natCast_nonneg _) hband_nn
  have hrow : (idx : Int) * band + band ≤ (n : Int) * band := by
    have h1 : ((idx : Int) + 1) * band ≤ (n : Int) * band :=
      Int.mul_le_mul_of_nonneg_right (by omega) hband_nn
    have h2 : ((idx : Int) + 1) * band = (idx : Int) * band + band := by
      rw [Int.add_mul, Int.one_mul]
    omega
  rw [← hn] at hrsv
  have hup : env.y + env.h ≤ F.y + F.h := by
    rw [hpy, hph, eband, ehsz]
    have hle : band / 2 - sz.height / 2 + sz.height ≤ band := by omega
    omega
  have hlo : F.y ≤ env.y := by
    rw [hpy, eband, ehsz]
    have hge : sz.height / 2 ≤ band / 2 := by omega
    omega
  have hleft : F.x + F.w ≤ env.x := by
    rw [hpx]
    have hpos : 0 ≤ cg.slot * (2 * (n : Int) + 1) :=
      Int.mul_nonneg hslot (by omega)
    omega
  have hright : env.x + env.w ≤ F.x + F.w + Loops.exactExtent cg.slot sizes := by
    rw [hpx, hpw]
    omega
  rw [hfp]
  unfold Rect.Contained
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
  · exact hleft
  · exact hright
  · exact hlo
  · exact hup

/-- Loop separation over the exact run: the envelope is contained in the
footprint in both width branches, and the footprint misses every in-scope
box by the residual. -/
theorem x_runLocalLoopSeparation_holds (exactIds : List String)
    (hres : X_RunLocalLoopFootprint exactIds) :
    X_RunLocalLoopSeparation exactIds := by
  unfold X_RunLocalLoopSeparation
  intro inp o res execution comp candidate run orderOptions cg k e env v
    hcomp hcg hrun hk hloop henv hv hreal hscope₀ hscope₁
  have hslot := componentRunX_slot_nonneg hrun
  have hlab := execution.measured_nonneg

  obtain ⟨hrsv, hsep⟩ := hres inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁
  by_cases htrue : run.exact.contains e.tail = true
  · have henv_eq := XLoop_exact_envelope_eq hloop htrue henv
    have hcont := XLoop_exact_envelope_contained hslot hlab hk hloop henv_eq hrsv htrue
    exact Elegant.Layered.not_meetsInterior_of_contained hcont hsep
  · have hfalse : run.exact.contains e.tail = false := by
      cases he : run.exact.contains e.tail with
      | true => exact absurd he htrue
      | false => rfl
    have henv_eq := XLoop_envelope_eq hloop hfalse henv
    have hcont := XLoop_envelope_contained hslot hlab hfalse hk hloop henv_eq hrsv
    exact Elegant.Layered.not_meetsInterior_of_contained hcont hsep

end PipelineImpl
end Layered
end Elegant
