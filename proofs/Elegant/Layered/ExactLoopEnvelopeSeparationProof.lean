import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.Pipeline

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Exact loop-envelope separation from the extended footprint miss.

Engine truth (`proofs/wip/Probe/ExactLoopEnvelopeTProbe.lean`, 27 cases: 1-3
labelled self-loops on a node fixed at 200x100, 10x10, 0x0, each with a node in
the next rank below, a same-rank sibling, and a group-with-title parent; plus
the 7 earlier `ExactC7LoopT2Probe` cases): every executed exact layout passes
`Validator.check`, every self-loop envelope misses every in-scope real box, the
plain footprint misses too, and the extended footprint below misses as well,
while the reservation `n * band ≤ frame.h` is false throughout (band 1536
against frame heights 100, 10, 0).

The old residual `X_RunLocalLoopFootprint` is therefore false on exact runs:
its reservation conjunct is used only to fit the label envelope vertically
inside the plain footprint. Both `Loops.placement` and `Loops.exactPlacement`
centre the label at `frame.y + idx * band + band / 2`, so the envelope always
fits vertically inside the footprint widened to `max frame.h (n * band)` — the
reserved rank height `reserveExactRanks` grants an exact loop node. The single
replacement residual `X_LoopEnvelopeMiss` states that this extended footprint
misses every in-scope real box; it holds on all 34 probe cases. -/

/-- Extended loop footprint: the `loopFootprint` rectangle widened to the
reserved rank height `max frame.h (n * band)`, which `reserveExactRanks` grants
an exact loop node. -/
def loopFootprintExt (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (v : Nat) : Rect :=
  let f := frameRect default cg run v
  let sizes := loopSizes cg.edges labels v cg.slot
  ⟨f.x + f.w, f.y,
    (if run.exact.contains v then Loops.exactExtent else Loops.extent) cg.slot sizes,
    max f.h (((sizes.length : Int)) * Loops.band cg.slot sizes)⟩

/-- Replacement loop-footprint residual: the extended footprint of a self-loop
node misses every in-scope real box of its run. No reservation conjunct. -/
def X_LoopEnvelopeMiss (exactIds : List String) : Prop :=
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
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- The plain footprint sits inside the extended footprint: same origin and
width, with `frame.h ≤ max frame.h (n * band)`. Hence the replacement residual
implies the old footprint-miss half. -/
theorem X_loopFootprint_in_ext {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v : Nat} :
    (loopFootprintExt cg run labels v).Contained
      (loopFootprint cg run labels v) := by
  unfold loopFootprint loopFootprintExt Rect.Contained
  dsimp only
  refine ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _, ?_⟩
  have hle : (frameRect default cg run v).h ≤ max (frameRect default cg run v).h
      (((loopSizes cg.edges labels v cg.slot).length : Int) *
        Loops.band cg.slot (loopSizes cg.edges labels v cg.slot)) :=
    Int.le_max_left _ _
  omega

/-- The replacement residual implies the old footprint-miss half. -/
theorem X_envelopeMiss_implies_footprintMiss (exactIds : List String)
    (h : X_LoopEnvelopeMiss exactIds)
    (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat)
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run)
    (hk : cg.edges[k]? = some e) (hloop : e.tail = e.head)
    (hv : v < run.proper.nodes.length)
    (hreal : RouteImpl.IsReal run.proper v)
    (hscope₀ : RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [])
    (hscope₁ : RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD []) :
    ¬ (loopFootprint cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  have hmiss := h inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁
  exact Elegant.Layered.not_meetsInterior_of_contained
    X_loopFootprint_in_ext hmiss

/-- Invert the plain-width loop `labelEnvelope` branch over an exact run
(prefixed copy of `XLoop_envelope_eq`). -/
private theorem XEnvT_envelope_eq {P : Params} {cg : Graph} {run : Run}
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
(prefixed copy of `XLoop_exact_envelope_eq`). -/
private theorem XEnvT_exact_envelope_eq {P : Params} {cg : Graph} {run : Run}
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

/-- Foldl max lower bound for loop label widths (prefixed copy). -/
private theorem XEnvT_foldl_max_width_ge (sizes : List LoopLabel) (acc : Int) :
    acc ≤ sizes.foldl (fun w l => max w l.width) acc := by
  induction sizes generalizing acc with
  | nil => exact Int.le_refl _
  | cons s rest ih =>
    simp only [List.foldl]
    exact Int.le_trans (Int.le_max_left acc s.width) (ih (max acc s.width))

/-- Foldl max over widths is monotone in its accumulator (prefixed copy). -/
private theorem XEnvT_foldl_max_width_mono (l : List LoopLabel) (acc acc' : Int)
    (h : acc ≤ acc') :
    l.foldl (fun w l => max w l.width) acc ≤
      l.foldl (fun w l => max w l.width) acc' := by
  induction l generalizing acc acc' with
  | nil => exact h
  | cons b rest ih =>
    simp only [List.foldl]
    exact ih _ _ (by omega)

/-- Every member width is bounded by the folded widest width (prefixed copy). -/
private theorem XEnvT_width_le_widest (sizes : List LoopLabel) (s : LoopLabel)
    (hmem : s ∈ sizes) :
    s.width ≤ sizes.foldl (fun w l => max w l.width) 0 := by
  induction sizes with
  | nil => simp at hmem
  | cons a rest ih =>
    simp only [List.foldl]
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Int.le_trans (Int.le_max_right _ _) (XEnvT_foldl_max_width_ge rest _)
    · exact Int.le_trans (ih hmem)
        (XEnvT_foldl_max_width_mono rest _ _ (Int.le_max_left _ _))

/-- The exact footprint covers the exact lane offset plus any member width
(prefixed copy of `XLoop_exactExtent_lower`). -/
private theorem XEnvT_exactExtent_lower {slot : Int} {sizes : List LoopLabel}
    {s : LoopLabel} (hmem : s ∈ sizes) (n : Nat) (hn : n = sizes.length) :
    slot * (2 * (n : Int) + 1) + s.width ≤ Loops.exactExtent slot sizes := by
  have hwide : s.width ≤ sizes.foldl (fun w l => max w l.width) 0 :=
    XEnvT_width_le_widest sizes s hmem
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

/-- The plain-width loop envelope is contained in the extended footprint, with
no reservation hypothesis: the label centre `frame.y + idx * band + band / 2`
lies in row `idx` of the `n * band` stack. -/
theorem X_loopEnvelope_containedExt {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hnoex : run.exact.contains e.tail = false)
    (hk : cg.edges[k]? = some e) (hloop : e.tail = e.head)
    (henv_eq : env = (Loops.placement (frameRect P cg run e.tail) cg.slot
      (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
      (loopEdges cg.edges e.tail).length
      (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
      (stackSize cg.slot (routeLabels labels e.decl))).label) :
    (loopFootprintExt cg run labels e.tail).Contained env := by
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
  have hfp : loopFootprintExt cg run labels e.tail =
      ⟨F.x + F.w, F.y, Loops.extent cg.slot sizes,
        max F.h (((n : Int)) * band)⟩ := by
    rw [hF]
    have h1 : run.exact.contains e.tail = false := hnoex
    unfold loopFootprintExt
    simp only [h1, hFirrel, Bool.false_eq_true, ↓reduceIte]
    rw [← hsizes, ← hn, ← hband]
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
  rw [← hn] at hext
  have hmax : (n : Int) * band ≤ max F.h (((n : Int)) * band) :=
    Int.le_max_right _ _
  have hup : env.y + env.h ≤ F.y + max F.h (((n : Int)) * band) := by
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

/-- The exact-width loop envelope is contained in the extended footprint, with
no reservation hypothesis (the label `y` argument is shared with the plain
branch; the `x` argument uses the widest-width bound). -/
theorem X_loopExactEnvelope_containedExt {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hk : cg.edges[k]? = some e) (hloop : e.tail = e.head)
    (henv_eq : env = (Loops.exactPlacement (frameRect P cg run e.tail) cg.slot
      (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
      (loopEdges cg.edges e.tail).length
      (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
      (stackSize cg.slot (routeLabels labels e.decl))).label)
    (hex : run.exact.contains e.tail = true) :
    (loopFootprintExt cg run labels e.tail).Contained env := by
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
  have hextX := XEnvT_exactExtent_lower (slot := cg.slot) hmem n hn
  have hFirrel : frameRect P cg run e.tail = frameRect default cg run e.tail := rfl
  have hfp : loopFootprintExt cg run labels e.tail =
      ⟨F.x + F.w, F.y, Loops.exactExtent cg.slot sizes,
        max F.h (((n : Int)) * band)⟩ := by
    rw [hF]
    unfold loopFootprintExt
    simp only [hex, hFirrel, ↓reduceIte]
    rw [← hsizes, ← hn, ← hband]
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
  have hmax : (n : Int) * band ≤ max F.h (((n : Int)) * band) :=
    Int.le_max_right _ _
  have hup : env.y + env.h ≤ F.y + max F.h (((n : Int)) * band) := by
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

/-- Loop separation over the exact run from the extended footprint miss: the
envelope is contained in the extended footprint in both width branches, and
the residual keeps that footprint off every in-scope box. -/
theorem X_runLocalLoopSeparation_of_envelopeMiss (exactIds : List String)
    (h : X_LoopEnvelopeMiss exactIds) :
    X_RunLocalLoopSeparation exactIds := by
  unfold X_RunLocalLoopSeparation
  intro inp o res execution comp candidate run orderOptions cg k e env v
    hcomp hcg hrun hk hloop henv hv hreal hscope₀ hscope₁
  have hslot := componentRunX_slot_nonneg hrun
  have hlab := execution.measured_nonneg
  have hmiss := h inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁
  by_cases htrue : run.exact.contains e.tail = true
  · have henv_eq := XEnvT_exact_envelope_eq hloop htrue henv
    have hcont := X_loopExactEnvelope_containedExt hslot hlab hk hloop henv_eq htrue
    exact Elegant.Layered.not_meetsInterior_of_contained hcont hmiss
  · have hfalse : run.exact.contains e.tail = false := by
      cases he : run.exact.contains e.tail with
      | true => exact absurd he htrue
      | false => rfl
    have henv_eq := XEnvT_envelope_eq hloop hfalse henv
    have hcont := X_loopEnvelope_containedExt hslot hlab hfalse hk hloop henv_eq
    exact Elegant.Layered.not_meetsInterior_of_contained hcont hmiss

end PipelineImpl
end Layered
end Elegant
