import Elegant.Layered.ExactCaptionRunClearProof
import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactForeignNonGroupSpansProof
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.Compound
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ComponentCoverage

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Exact caption ancestor clearance

Targets: `XC_AncestorGroupFrameX`, `XC_AncestorMarkerX`, `XC_AncestorOtherX`,
and `XC_ForeignSpansX` (`ExactCaptionRunClearProof.lean`), the four per-run
premises `hnest`, `hmarkAnc`, `hotherAnc`, `hclear` of `XF_captionRunClearX_holds`.

Plain originals (closed): `CaptionAncestorGroupFrameStrict`
(`CaptionLocalClearProof.lean:143`), `CaptionAncestorMarkerClear` (`:159`),
and `CaptionAncestorOtherClear` (`:180`) with `captionAncestorClear_executed`
(`:854`); the foreign per-run assembly is `foreignSpansClear_of_run`
(`ForeignSpansFacts.lean:335`). The older plain `CaptionAncestorFrameStrict`
is false for an ancestor bottom marker; this file follows the closed route.

Replacement table (`ExactCaptionRunClearProof.lean:57-71`):
group via `X_ReserveBands_holds` plus `componentRunX_node_band`;
marker via `X_ReserveBands_holds` plus `componentRunX_positions_disjoint`;
other via `X_componentCandidate_marker_shape` transported across `exactGraph`;
foreign from `XB_foreignBorderSpansSeparated_holds` and
`XN_foreignNonGroupSpansClear_holds` under `X_ForeignBorderChainXAligned`.

Each ancestor conclusion below is reduced to a named single-fact residual that
is strictly narrower than its goal (one link, one direction, or vacuous
absence), with probe evidence in
`proofs/wip/Probe/ExactCaptionAncestorsTProbe.lean` (flat, nested, sane fixed,
wider-than-slot fixed). Admission (`WellFormed`, `framedParents`) is carried
as per-execution premises `XCA_WellFormedX` / `XCA_FramedX`, discharged at the
family level where `layoutFamilyX` already ensures both.
-/

/-- Admission: every executed exact layout input is well-formed. -/
def XCA_WellFormedX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o)

/-- Admission: every executed exact layout input has framed parents. -/
def XCA_FramedX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionX exactIds inp o res),
    framedParents inp = true

/-- Narrow residual (group, one link): a direct parent group frame strictly
contains its direct child group frame over one exact run. Strictly narrower
than `XC_AncestorGroupFrameX` (one link vs transitive chain). Probe:
`ExactCaptionAncestorsTProbe` counts direct-parent pairs on flat, nested, sane
fixed, and wider-than-slot inputs, all strictly nested, zero violations. -/
def XCA_GroupLinkX (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {parentIndex childIndex : Nat} {parent child : Node}
      {parentBox childBox : ModelBox},
    (componentCandidate graph comp candidate).nodes[parentIndex]? = some parent →
    parent.border = -2 →
    (componentCandidate graph comp candidate).nodes[childIndex]? = some child →
    child.border = -2 →
    inp.boxes[parent.decl]? = some parentBox →
    inp.boxes[child.decl]? = some childBox →
    childBox.parent = parentBox.id → childBox.parent ≠ "" →
    (frameRect P (componentCandidate graph comp candidate) run parentIndex).StrictInside
      (frameRect P (componentCandidate graph comp candidate) run childIndex)

/-- Narrow residual (marker, one direction): an ancestor bottom marker lies
below the transported caption over one exact run. Strictly narrower than
`XC_AncestorMarkerX` (one y-direction vs full disjointness). Probe:
`ExactCaptionAncestorsTProbe` observes bottom-marker ancestor pairs on nested
inputs (plus flat/sane-fixed/wider-than-slot rows), all with caption bottom at
or above marker top, zero violations. -/
def XCA_MarkerBelowX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
    (i, stored0) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run →
    (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
    tNode.border = -2 →
    ∀ (pos : Nat) (fNode : Node),
    (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode →
    tNode.decl ≠ fNode.decl →
    tNode.clusterPath.contains fNode.decl = true →
    fNode.border = 2 →
    (transportCaption execution.params o execution.lines comp i stored0).y +
      (transportCaption execution.params o execution.lines comp i stored0).h ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).y

/-- Narrow residual (other, vacuous): no plain ancestor exists over one exact
run. Strictly narrower than `XC_AncestorOtherX` (absence vs
disjoint-or-inside). Probe: `ExactCaptionAncestorsTProbe` observes zero plain
ancestor pairs on flat, nested, sane fixed, and wider-than-slot inputs. -/
def XCA_PlainAncestorImpossibleX (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {tNode fNode : Node} {tIdx fIdx : Nat},
    (componentCandidate graph comp candidate).nodes[tIdx]? = some tNode →
    tNode.border = -2 →
    (componentCandidate graph comp candidate).nodes[fIdx]? = some fNode →
    fNode.border = 0 →
    tNode.decl ≠ fNode.decl →
    tNode.clusterPath.contains fNode.decl = true →
    False

/-- Copy of `sceneExecutionX_lines_len` (`ExactFlatFacts.lean`): exact lines
cover every input box. -/
private theorem xca_lines_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  unfold boxLines at h
  have h2 := (mapM_getElem? _ _ _ h).1
  have hzip : (inp.boxes.zipIdx).length = inp.boxes.length := List.length_zipIdx
  omega

/-- Copy of `ancDemoteId` (`CaptionAncestorFrameProof.lean`): demotion keeps ids. -/
private theorem xca_demoteId {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) b).id = b.id := by
  intro b _
  dsimp only
  split <;> rfl

/-- Copy of `ancDemoteParent`: demotion keeps parents. -/
private theorem xca_demoteParent {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) b).parent = b.parent := by
  intro b _
  dsimp only
  split <;> rfl

/-- Copy of `ancDemoteLookup`: inverting a fixed-boxes lookup recovers the
original box and its demotion facts. -/
private theorem xca_demoteLookup {inp : Input} {i : Nat} {b : ModelBox}
    (h : (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)[i]? = some b) :
    ∃ orig : ModelBox, inp.boxes[i]? = some orig ∧ b.id = orig.id ∧ b.parent = orig.parent ∧
      (b.role = .group → ¬(inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) = true)) ∧
      b = (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then { orig with role := .node } else orig) := by
  rw [List.getElem?_map] at h
  cases hop : inp.boxes[i]? with
  | none => rw [hop] at h; simp at h
  | some orig =>
    rw [hop, Option.map_some, Option.some.injEq] at h
    by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == orig.id)
    · have hd : b = ({ orig with role := .node } : ModelBox) := h.symm.trans (ite_eq_left hfixed)
      refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_, by rw [hd, ite_eq_left hfixed]⟩
      intro hrole
      rw [hd] at hrole
      simp at hrole
    · have hd : b = orig := h.symm.trans (ite_eq_right (by simp [hfixed]))
      refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_, by rw [hd, ite_eq_right hfixed]⟩
      intro _
      exact hfixed

/-- A nonempty list splits off its last element (copy of `ancPeelLast`). -/
private theorem xca_peelLast {α : Type} {l : List α} (hne : l ≠ []) :
    ∃ (pre : List α) (last : α), l = pre ++ [last] := by
  induction l with
  | nil => exact absurd rfl hne
  | cons s ss ih =>
    by_cases hss : ss = []
    · subst hss
      exact ⟨[], s, by simp⟩
    · obtain ⟨pre, last, hpl⟩ := ih hss
      exact ⟨s :: pre, last, by rw [hpl]; rfl⟩

/-- The ancestor base path is nonempty (copy of `ancBaseNe`). -/
private theorem xca_baseNe {inp : Input} {origF : ModelBox} {f : Nat} :
    Compound.path inp.boxes origF ++ [f] ≠ [] := by
  intro hcon
  have hlen := congrArg List.length hcon
  simp at hlen

/-- Direct-parent evidence for a box on the ancestor chain (copy of
`ancParentLink`): the parent box is a non-demoted group and the unmapped path
grows by exactly its index. -/
private theorem xca_parentLink {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {c : Nat} {cbO : ModelBox} (hcbO : inp.boxes[c]? = some cbO)
    (hpathNe : Compound.path inp.boxes cbO ≠ []) :
    ∃ (p : Nat) (boxP : ModelBox), inp.boxes[p]? = some boxP ∧ boxP.role = .group ∧
      cbO.parent = boxP.id ∧ cbO.parent ≠ "" ∧
      (inp.fixedSizes.any (fun fixed => fixed.1 == boxP.id) = false) ∧
      ((inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)[p]? = some boxP) ∧
      Compound.path inp.boxes boxP ++ [p] = Compound.path inp.boxes cbO := by
  have hparNe : cbO.parent ≠ "" := by
    intro hempty
    apply hpathNe
    unfold Compound.path
    rw [hempty]
    cases hlen : inp.boxes.length with
    | zero => simp [Compound.ancestors]
    | succ n => simp [Compound.ancestors]
  have hboxMem : cbO ∈ inp.boxes := List.mem_of_getElem? hcbO
  obtain ⟨boxP, hmemP, hpid, hpgroup, hpnotfixed⟩ :=
    framedParents_parent hframed hboxMem hparNe
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hmemP
  have hnp : ¬(inp.fixedSizes.any (fun fixed => fixed.1 == boxP.id) = true) := by
    intro hc
    rw [hc] at hpnotfixed
    simp at hpnotfixed
  have heffP : (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)[p]? = some boxP := by
    simp only [List.getElem?_map, hp, Option.map_some, ite_eq_right hnp]
  have hstep : Compound.path inp.boxes cbO =
      Compound.path inp.boxes boxP ++ [p] :=
    Compound.path_of_parent (inputModel inp o) hwf hp hcbO (by rw [hpid]) hparNe
  exact ⟨p, boxP, hp, hpgroup, hpid.symm, hparNe, hpnotfixed, heffP, hstep.symm⟩

/-- Copy of `X_exactGraph_node_key_rev` (`ExactFlatC5Rank.lean`): drop from an
exact node back to its measured source. -/
private theorem xca_key_rev {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g')
    {v : Nat} {nd' : Node} (hv : g'.nodes[v]? = some nd') :
    ∃ nd, g.nodes[v]? = some nd ∧ nd'.border = nd.border ∧
      nd'.clusterPath = nd.clusterPath ∧ nd'.decl = nd.decl := by
  have hlen : g'.nodes.length = g.nodes.length := exactGraph_length h
  have hvlt : v < g.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have hmem : g.nodes[v]? = some g.nodes[v] := List.getElem?_eq_getElem hvlt
  obtain ⟨nd'', hnd'', hb, hc, hd⟩ := exactGraph_node_key h hmem
  have heq : nd'' = nd' := Option.some.inj (hnd''.symm.trans hv)
  subst heq
  exact ⟨g.nodes[v], hmem, hb, hc, hd⟩

/-- Copy of `X_find?_transport` (`ExactFlatC5Rank.lean`): transport a
key-predicate `find?` hit from the measured graph to the exact graph. -/
private theorem xca_find_transport {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {graph0 graph : Graph}
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (pred : Node × Nat → Bool)
    (hcong : ∀ (n n0 : Node) (i : Nat), n.border = n0.border → n.decl = n0.decl →
      n.clusterPath = n0.clusterPath → pred (n, i) = pred (n0, i))
    {b : Node × Nat} (hb : b ∈ graph0.nodes.zipIdx) (hpred_b : pred b = true) :
    ∃ b' : Node × Nat, graph.nodes.zipIdx.find? pred = some b' := by
  have hlook : graph0.nodes[b.2]? = some b.1 := List.mem_zipIdx_iff_getElem?.mp hb
  obtain ⟨e, heelook, heb, hed, hep⟩ := exactGraph_node_key h hlook
  have hmem : (e, b.2) ∈ graph.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr heelook
  have hpred_e : pred (e, b.2) = true := by
    have hbe := hcong e b.1 b.2 heb hep hed
    rw [hbe]; exact hpred_b
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨(e, b.2), hmem, hpred_e⟩)
  exact ⟨b', hb'⟩

/-- Copy of `ancFindSomeOfMember`: a member satisfying the predicate yields a
`find?` hit. -/
private theorem xca_findSomeOfMember {l : List (Node × Nat)} {pred : Node × Nat → Bool}
    {entry : Node × Nat} (hmem : entry ∈ l) (hp : pred entry = true) :
    ∃ b : Node × Nat, l.find? pred = some b :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hp⟩)

/-- Graph0 group-top find (copy of `ancGroupTopFind` over the measured graph):
every measured-graph group top finds its paired bottom marker by declaration. -/
private theorem xca_graph0_groupTopFind {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph0 : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hlines : lines.length = inp.boxes.length)
    {t : Node × Nat} (htop : t ∈ graph0.nodes.zipIdx) (hgroup : t.1.border = -2) :
    ∃ b : Node × Nat,
      graph0.nodes.zipIdx.find? (fun e => e.1.border == 2 && e.1.decl == t.1.decl) = some b := by
  have hlookup : graph0.nodes[t.2]? = some t.1 := List.mem_zipIdx_iff_getElem?.mp htop
  obtain ⟨hdecl, box, hbox, hrole, _⟩ := measuredGraph_group_origin h0 hlookup hgroup
  have hbound : t.1.decl < lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hbox).1
    rw [List.length_map] at hi
    omega
  obtain ⟨_, bottom, _, hbmem, _, hbborder, _, hbdecl, _, _, _, _⟩ :=
    measuredGraph_paired_markers h0 hbound hbox hrole
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hbmem
  have hp : ((fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl)
      (bottom, idx)) = true := by
    simp [hbborder, hbdecl]
  exact xca_findSomeOfMember (List.mem_zipIdx_iff_getElem?.mpr hidx) hp

/-- Exact group-top find: transport of the graph0 find across `exactGraph`. -/
private theorem xca_groupTopFind {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {t : Node × Nat} (htop : t ∈ graph.nodes.zipIdx) (hgroup : t.1.border = -2) :
    ∃ b : Node × Nat,
      graph.nodes.zipIdx.find? (fun e => e.1.border == 2 && e.1.decl == t.1.decl) = some b := by
  have hlook : graph.nodes[t.2]? = some t.1 := List.mem_zipIdx_iff_getElem?.mp htop
  obtain ⟨nd0, hnd0, hb0, _, hd0⟩ := xca_key_rev h hlook
  have hb0' : nd0.border = -2 := hb0.symm.trans hgroup
  have htop0 : (nd0, t.2) ∈ graph0.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hnd0
  obtain ⟨b0, hb0find⟩ := xca_graph0_groupTopFind h0 hlines htop0 hb0'
  have hmem0 : b0 ∈ graph0.nodes.zipIdx := List.mem_of_find?_eq_some hb0find
  have hpred0 : (fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl) b0 = true := by
    have h := List.find?_some hb0find
    simpa [hd0] using h
  have hcong : ∀ (n n0 : Node) (i : Nat), n.border = n0.border → n.decl = n0.decl →
      n.clusterPath = n0.clusterPath →
      (fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl) (n, i) =
        (fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl) (n0, i) := by
    intro n n0 i hb hd _
    simp [hb, hd]
  exact xca_find_transport h _ hcong hmem0 hpred0

/-- Exact constraints bounded (copy of `ancConstraintsBounded` over the exact
graph, via `exactGraph_edges`). -/
private theorem xca_constraintsBounded {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length) :
    ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length := by
  intro e he
  have hedge : graph.edges = graph0.edges := exactGraph_edges h
  have hlen : graph.nodes.length = graph0.nodes.length := exactGraph_length h
  rcases List.mem_append.mp he with he | he
  · rw [hedge] at he
    have hbd := measuredGraph_edges_bounded h0 hlines e he
    omega
  · have hbd := constraints_bounded graph e he
    exact hbd

/-- Direct single-link step for the exact chain (mirror of `ancDirectStep`):
when the current box path is exactly the ancestor base, one `XCA_GroupLinkX`
link suffices. -/
private theorem xca_directStep {exactIds : List String} {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hlink : XCA_GroupLinkX exactIds)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {pos : Nat} {fNode : Node}
    (hfn : (componentCandidate graph comp candidate).nodes[pos]? = some fNode)
    (hfborder : fNode.border = -2)
    {origF : ModelBox} (horigF : inp.boxes[fNode.decl]? = some origF)
    {cIdx c : Nat} {cn : Node}
    (hcn : (componentCandidate graph comp candidate).nodes[cIdx]? = some cn)
    (hbord : cn.border = -2) (hdecl : cn.decl = c)
    {cbO : ModelBox} (hcbO : inp.boxes[c]? = some cbO)
    (hpath : Compound.path inp.boxes cbO =
      Compound.path inp.boxes origF ++ [fNode.decl]) :
    (frameRect P (componentCandidate graph comp candidate) run pos).StrictInside
      (frameRect P (componentCandidate graph comp candidate) run cIdx) := by
  obtain ⟨p, boxP, hboxP, _, hrefP, hneP, _, _, hstepP⟩ :=
    xca_parentLink hwf hframed hcbO (by rw [hpath]; exact xca_baseNe)
  have hEq : Compound.path inp.boxes boxP ++ [p] =
      Compound.path inp.boxes origF ++ [fNode.decl] := hstepP.trans hpath
  have hpf : p = fNode.decl := by
    have hlast := congrArg List.getLast? hEq
    rw [List.getLast?_append, List.getLast?_append] at hlast
    simpa using hlast
  have hPOEq : boxP = origF := by
    have hboxP' : inp.boxes[fNode.decl]? = some boxP := by rwa [hpf] at hboxP
    exact Option.some.inj (hboxP'.symm.trans horigF)
  subst hPOEq
  exact hlink h0 h hlines hwf hframed hcomp hrun hfn hfborder hcn hbord horigF (hdecl ▸ hcbO) hrefP hneP

/-- Ancestor-chain induction for exact runs (mirror of `ancChain`): from the
path equation, every group on the chain nests by one `XCA_GroupLinkX` link per
parent edge plus `captionStrictInside_trans`. -/
private theorem xca_chain {exactIds : List String} {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hlink : XCA_GroupLinkX exactIds)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {pos : Nat} {fNode : Node}
    (hfn : (componentCandidate graph comp candidate).nodes[pos]? = some fNode)
    (hfborder : fNode.border = -2)
    {origF : ModelBox} (horigF : inp.boxes[fNode.decl]? = some origF) :
    ∀ (n : Nat) (rest : List Nat) (cIdx c : Nat) (cn : Node),
    rest.length ≤ n →
    (componentCandidate graph comp candidate).nodes[cIdx]? = some cn →
    cn.border = -2 → cn.decl = c →
    ∀ (cbO : ModelBox), inp.boxes[c]? = some cbO →
    Compound.path inp.boxes cbO =
      (Compound.path inp.boxes origF ++ [fNode.decl]) ++ rest →
    (frameRect P (componentCandidate graph comp candidate) run pos).StrictInside
      (frameRect P (componentCandidate graph comp candidate) run cIdx) := by
  intro n
  induction n with
  | zero =>
    intro rest cIdx c cn hlen hcn hbord hdecl cbO hcbO hpath
    have hrNil : rest = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hrNil, List.append_nil] at hpath
    exact xca_directStep h0 h hlines hwf hframed hlink hcomp hrun hfn hfborder horigF
      hcn hbord hdecl hcbO hpath
  | succ n ih =>
    intro rest cIdx c cn hlen hcn hbord hdecl cbO hcbO hpath
    by_cases hrest : rest = []
    · subst hrest
      rw [List.append_nil] at hpath
      exact xca_directStep h0 h hlines hwf hframed hlink hcomp hrun hfn hfborder horigF
        hcn hbord hdecl hcbO hpath
    · obtain ⟨rest', p, hrpeel⟩ := xca_peelLast hrest
      have hlen' : rest'.length ≤ n := by
        have h := hlen
        rw [hrpeel] at h
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        omega
      obtain ⟨origC, hcompC, hsourceC⟩ :=
        componentCandidate_nonplain_source hcn (by omega)
      obtain ⟨nd0, hnd0, hb0, hp0, hd0⟩ := xca_key_rev h hsourceC
      have hb0' : nd0.border = -2 := hb0.symm.trans hbord
      obtain ⟨hdeclC, boxCE, hboxCE, _, hpathCE⟩ :=
        measuredGraph_group_origin h0 hnd0 hb0'
      have hcorig : c = origC := hdecl.symm.trans (hd0.trans hdeclC)
      have hoIn : origC ∈ comp := List.mem_of_getElem? hcompC
      obtain ⟨origCE, horigCE, _, _, _, hdemCE⟩ := xca_demoteLookup hboxCE
      have horigCE' : inp.boxes[cn.decl]? = some origCE := hd0 ▸ horigCE
      have hcbOEq : origCE = cbO := by
        have h1 : inp.boxes[cn.decl]? = some origCE := horigCE'
        rw [hdecl] at h1
        exact Option.some.inj (h1.symm.trans hcbO)
      have hpathMap : Compound.path (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) boxCE =
          Compound.path inp.boxes cbO := by
        have hpm := Compound.path_map inp.boxes
          (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)
          xca_demoteId xca_demoteParent (List.mem_of_getElem? horigCE)
        rw [← hdemCE, hcbOEq] at hpm
        exact hpm
      have hcnPath : cn.clusterPath = Compound.path inp.boxes cbO ++ [c] := by
        rw [hp0, hpathCE, hpathMap, ← hd0, hdecl]
      obtain ⟨q, boxQ, hboxQ, hroleQ, hrefQ, hneQ, hnonfixQ, heffQ, hstepQ⟩ :=
        xca_parentLink hwf hframed hcbO (by
          rw [hpath]
          intro hcon
          have hlen := congrArg List.length hcon
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen
          omega)
      have hEq : Compound.path inp.boxes boxQ ++ [q] =
          (Compound.path inp.boxes origF ++ [fNode.decl] ++ rest') ++ [p] := by
        rw [hstepQ, hpath, hrpeel, ← List.append_assoc]
      have hqq : q = p := by
        have hlast := congrArg List.getLast? hEq
        rw [List.getLast?_append, List.getLast?_append] at hlast
        simpa using hlast
      have hdropQ : Compound.path inp.boxes boxQ =
          Compound.path inp.boxes origF ++ [fNode.decl] ++ rest' := by
        have hdrop := congrArg List.dropLast hEq
        rw [List.dropLast_append_of_ne_nil (l := [q]) (by simp),
          List.dropLast_append_of_ne_nil (l := [p]) (by simp)] at hdrop
        simpa using hdrop
      have hpathSnoc : Compound.path inp.boxes cbO =
          (Compound.path inp.boxes origF ++ [fNode.decl] ++ rest') ++ [q] := by
        rw [hpath, hrpeel, ← hqq]
        simp [List.append_assoc]
      have hqlt : q < lines.length := by
        have h1 := (List.getElem?_eq_some_iff.mp hboxQ).1
        omega
      obtain ⟨pn0, _, hpn0, _, hpnBord0, _, hpnDecl0, _, hpnPath0, _, _, _⟩ :=
        measuredGraph_paired_markers h0 hqlt heffQ hroleQ
      obtain ⟨pn, hpnLookup, hpnBord, hpnPath, hpnDecl⟩ := exactGraph_node_key h hpn0
      have hpnBord' : pn.border = -2 := hpnBord.trans hpnBord0
      have hpnDecl' : pn.decl = q := hpnDecl.trans hpnDecl0
      have hdemQ : (if inp.fixedSizes.any (fun fixed => fixed.1 == boxQ.id) then { boxQ with role := .node } else boxQ) = boxQ := by
        have hne : ¬(inp.fixedSizes.any (fun fixed => fixed.1 == boxQ.id) = true) := by
          rw [hnonfixQ]; decide
        exact ite_eq_right hne
      have hboxQMap : Compound.path (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) boxQ =
          Compound.path inp.boxes boxQ := by
        have hpm := Compound.path_map inp.boxes
          (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)
          xca_demoteId xca_demoteParent (List.mem_of_getElem? hboxQ)
        rwa [hdemQ] at hpm
      have hpnPath' : pn.clusterPath = Compound.path inp.boxes boxQ ++ [q] := by
        rw [hpnPath, hpnPath0, hboxQMap]
      have hpathEdge : cn.clusterPath.dropLast = pn.clusterPath := by
        show cn.clusterPath.dropLast = pn.clusterPath
        rw [hcnPath, hpnPath', hpathSnoc, hdropQ]
        rw [List.dropLast_append_of_ne_nil (l := [c]) (by simp)]
        simp
      have hparZip : (pn, q) ∈ graph.nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hpnLookup
      have hchildZip : (cn, origC) ∈ graph.nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hsourceC
      obtain ⟨botP, hfindP⟩ := xca_groupTopFind h0 h hlines hparZip hpnBord'
      obtain ⟨botC, hfindC⟩ := xca_groupTopFind h0 h hlines hchildZip hbord
      obtain ⟨heP, _⟩ := compound_child_constraint_edges hparZip hpnBord' hfindP
        hchildZip hbord hpathEdge hfindC
      have hbd := xca_constraintsBounded h0 h hlines
      obtain ⟨c', hcMem, hcP, hcO⟩ :=
        components_edge_endpoints hbd (List.mem_append_right _ heP)
      have hcEq : c' = comp := components_shared_member_eq hcMem hcomp hcO hoIn
      have hpinComp : q ∈ comp := hcEq ▸ hcP
      have htopPin : pn ∈ (componentCandidate graph comp candidate).nodes := by
        rw [componentCandidate_nodes]
        exact List.mem_map.mpr ⟨q, hpinComp, by
          rw [List.getD_eq_getElem?_getD, hpnLookup]
          rfl⟩
      obtain ⟨cpIdx, hcpIdx⟩ := List.mem_iff_getElem?.mp htopPin
      have hstep : (frameRect P (componentCandidate graph comp candidate) run cpIdx).StrictInside
          (frameRect P (componentCandidate graph comp candidate) run cIdx) := by
        have hpar : inp.boxes[pn.decl]? = some boxQ := hpnDecl' ▸ hboxQ
        have hch : inp.boxes[cn.decl]? = some cbO := hdecl ▸ hcbO
        exact hlink h0 h hlines hwf hframed hcomp hrun hcpIdx hpnBord' hcn hbord hpar hch hrefQ hneQ
      have hIH := ih rest' cpIdx q pn hlen' hcpIdx hpnBord' hpnDecl' boxQ hboxQ hdropQ
      exact captionStrictInside_trans hIH hstep

/-- Exact ancestor-group-frame clearance from the one-link residual. -/
theorem XC_ancestorGroupFrameX_holds (exactIds : List String)
    (hwellformed : XCA_WellFormedX exactIds)
    (hframed : XCA_FramedX exactIds)
    (hlink : XCA_GroupLinkX exactIds) :
    XC_AncestorGroupFrameX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun i pos tNode fNode hnode hborder hfn hfborder hne hmem
  have hwf := hwellformed execution
  have hfp := hframed execution
  have hlines := xca_lines_len execution
  obtain ⟨_, hcompTi, hsourceT⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨ndT0, hndT0, hbT0, hpT0, hdT0⟩ := xca_key_rev execution.graph_eq hsourceT
  have hbT0' : ndT0.border = -2 := hbT0.symm.trans hborder
  obtain ⟨_, boxT, hboxT, _, hpathT⟩ :=
    measuredGraph_group_origin execution.graph0_eq hndT0 hbT0'
  obtain ⟨_, _, hsourceF⟩ :=
    componentCandidate_nonplain_source hfn (by omega)
  obtain ⟨ndF0, hndF0, hbF0, _hpF0, hdF0⟩ := xca_key_rev execution.graph_eq hsourceF
  have hbF0' : ndF0.border = -2 := hbF0.symm.trans hfborder
  obtain ⟨_, boxF, hboxF, _, _⟩ :=
    measuredGraph_group_origin execution.graph0_eq hndF0 hbF0'
  obtain ⟨origT, horigT, _, _, _, hdemT⟩ := xca_demoteLookup hboxT
  obtain ⟨origF, horigF, _, _, _, _⟩ := xca_demoteLookup hboxF
  have hpmU : Compound.path (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) boxT =
      Compound.path inp.boxes origT := by
    have hpm := Compound.path_map inp.boxes
      (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)
      xca_demoteId xca_demoteParent (List.mem_of_getElem? horigT)
    rw [← hdemT] at hpm
    exact hpm
  have hpathTEq : tNode.clusterPath = Compound.path inp.boxes origT ++ [tNode.decl] := by
    rw [hpT0, hpathT, ← hdT0, hpmU]
  have hmemT : fNode.decl ∈ tNode.clusterPath := by
    have h2 : decide (fNode.decl ∈ tNode.clusterPath) = true := by
      rw [← List.contains_eq_mem]
      exact hmem
    exact of_decide_eq_true h2
  have hmemU : fNode.decl ∈ Compound.path inp.boxes origT := by
    have h2 : fNode.decl ∈ Compound.path inp.boxes origT ++ [tNode.decl] := by
      rw [← hpathTEq]
      exact hmemT
    rcases List.mem_append.mp h2 with h | h
    · exact h
    · exact absurd (List.mem_singleton.mp h).symm hne
  have horigF' : (inputModel inp o).boxes[fNode.decl]? = some origF := hdF0 ▸ horigF
  have horigT' : (inputModel inp o).boxes[tNode.decl]? = some origT := hdT0 ▸ horigT
  have hpre := Compound.path_ancestor_prefix (inputModel inp o) hwf horigF' horigT' hmemU
  obtain ⟨rest, hr⟩ := hpre
  have horigF_exact : inp.boxes[fNode.decl]? = some origF := hdF0 ▸ horigF
  have horigT_exact : inp.boxes[tNode.decl]? = some origT := hdT0 ▸ horigT
  exact xca_chain execution.graph0_eq execution.graph_eq hlines hwf hfp hlink hcomp hrun
    hfn hfborder horigF_exact rest.length rest i tNode.decl tNode (Nat.le_refl _) hnode hborder rfl origT horigT_exact hr.symm

/-- Exact ancestor-marker clearance from the below residual. -/
theorem XC_ancestorMarkerX_holds (exactIds : List String)
    (hbelow : XCA_MarkerBelowX exactIds) :
    XC_AncestorMarkerX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun i stored0 tNode hmem hnode hborder pos fNode g0 hfn hne hancrel hbor2 hframe
  have hle := hbelow execution hcomp hrun i stored0 tNode hmem hnode hborder pos fNode hfn hne hancrel hbor2
  rw [hframe] at hle
  unfold Disjoint
  intro hcon
  obtain ⟨_, hy⟩ := hcon
  omega

/-- Exact ancestor-other clearance: vacuous over candidate shapes. -/
theorem XC_ancestorOtherX_holds (exactIds : List String)
    (hwellformed : XCA_WellFormedX exactIds)
    (hframed : XCA_FramedX exactIds)
    (himpossible : XCA_PlainAncestorImpossibleX exactIds) :
    XC_AncestorOtherX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun _i _stored0 tNode _hmem hnode hborder pos fNode _g0 hfn hne hancrel hne2 hneB2 _hframe
  have hwf := hwellformed execution
  have hfp := hframed execution
  have hlines := xca_lines_len execution
  have hshape := (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq hfn).1
  rcases hshape with h0 | hm2 | h2
  · have hfalse := himpossible execution.graph0_eq execution.graph_eq hlines hwf hfp hcomp hnode hborder hfn h0 hne hancrel
    exact False.elim hfalse
  · exact absurd hm2 hne2
  · exact absurd h2 hneB2

/-- Exact foreign-span clearance from the two exact span seams, mirroring
`foreignSpansClear_of_run`. -/
theorem XC_foreignSpansX_of_spans (exactIds : List String)
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halignB : XB_ForeignBorderChainXAligned exactIds)
    (hord : XB_OrderedIntervals exactIds)
    (htop : XB_TopNonneg exactIds)
    (hmem : XB_MemberNonempty exactIds)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplain : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds)
    (_hchain : X_ForeignBorderChainXAligned exactIds)
    (hwellformed : XCA_WellFormedX exactIds)
    (hframed : XCA_FramedX exactIds) :
    XC_ForeignSpansX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun u w uNode wNode hu hw hgroupU hne hpathW hpathU
  have hwf := hwellformed execution
  have hfp := hframed execution
  have hlines := xca_lines_len execution
  have hgroups : XB_ForeignBorderSpansSeparated exactIds :=
    XB_foreignBorderSpansSeparated_holds exactIds hspans horder halignB hord htop hmem
  have hothers : XN_ForeignNonGroupSpansClear exactIds :=
    XN_foreignNonGroupSpansClear_holds exactIds hbracket hplain halignN
  by_cases hgroupW : wNode.border = -2
  · exact frameRect_disjoint_of_hulls hu hgroupU hw hgroupW
      (hgroups execution.graph0_eq execution.graph_eq hlines hwf hfp hcomp hrun hu hw hgroupU
        hgroupW hne hpathW hpathU)
  · exact hothers execution.graph0_eq execution.graph_eq hlines hwf hfp hcomp hrun hu hw hgroupU
      hgroupW hne hpathW hpathU

end Elegant.Layered.PipelineImpl
