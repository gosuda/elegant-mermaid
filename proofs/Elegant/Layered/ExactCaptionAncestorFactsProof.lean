import Elegant.Layered.ExactCaptionAncestorsProof
import Elegant.Layered.ExactCaptionMembersProof
import Elegant.Layered.CaptionRunClearClosed
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ComponentRunGen
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.Compound
import Elegant.Layered.PipelineFacts
import Elegant.Layered.FamilyC5B
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExecutedFrameClearanceFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact caption ancestor facts (`XCA_` residuals discharged)

Proves the three narrow residuals of `ExactCaptionAncestorsProof.lean`:

* `XCA_GroupLinkX` (line 66): direct parent group frame strictly contains its
  direct child group frame over one exact run. No exact strict-frame lemma
  exists yet (`ExactRunFrameNestingProof` proves only `Contained`), so the
  fact is reduced to its four single-inequality sides (`XCA_LinkLeftX`,
  `XCA_LinkRightX`, `XCA_LinkTopX`, `XCA_LinkBotX`), each a single fact over
  executed runs, true on the probe
  (`proofs/wip/Probe/ExactCaptionAncestorFactsTProbe.lean`).
* `XCA_MarkerBelowX` (line 98): ancestor bottom marker below the transported
  caption. Reduced to the shared caption-band residual `XC_CapBandX`
  (`ExactCaptionMembersProof.lean:389`) plus one single-inequality band fact
  (`XCA_MarkerBandBelowX`), both over executed runs and probe-true.
* `XCA_PlainAncestorImpossibleX` (line 124): no plain ancestor over one exact
  run. Proved fully: pure declaration-index reasoning transported across
  `exactGraph`, replaying `captionAncestorOtherClear_executed`
  (`CaptionRunClearClosed.lean:205`).

Verdict on the two global premise defs (`XCA_WellFormedX`, line 50, and
`XCA_FramedX`, line 56): they are admission facts, not provable from a bare
`layoutX` run (`layoutX` in `ExactPipeline.lean:126` checks no admission
guards; the guards live in `layoutFamilyB`, lines 187-199). They are supplied
per instance by the family entry: `layoutFamilyB_success`
(`FamilyC5B.lean:330`) yields `WellFormed (inputModel inp o)` and
`layoutFamilyB_framed_parents` (`ExactPipeline.lean:206`) yields
`framedParents inp = true`, for any base including `layoutX exactIds`
(`layoutFamilyX`). This is the same route the plain caption theorems take:
`captionAncestorGroupFrameStrict_executed` and friends take `hwf`/`hframed`
from `layoutFamilyB_valid_of_seams` (`FamilyAssemblyB.lean:168`). -/

/-- Instance bridge: a successful exact family entry yields well-formedness. -/
theorem XCA_WellFormedX_of_family {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (h : layoutFamilyX exactIds inp o = .ok res) :
    WellFormed (inputModel inp o) :=
  (layoutFamilyB_success h).1

/-- Instance bridge: a successful exact family entry yields framed parents. -/
theorem XCA_FramedX_of_family {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (h : layoutFamilyX exactIds inp o = .ok res) :
    framedParents inp = true :=
  layoutFamilyB_framed_parents h

/-- Narrower residual (group link, left side): single strict inequality. -/
def XCA_LinkLeftX (exactIds : List String) : Prop :=
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
    (frameRect P (componentCandidate graph comp candidate) run parentIndex).x <
      (frameRect P (componentCandidate graph comp candidate) run childIndex).x

/-- Narrower residual (group link, right side): single strict inequality. -/
def XCA_LinkRightX (exactIds : List String) : Prop :=
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
    (frameRect P (componentCandidate graph comp candidate) run childIndex).x +
      (frameRect P (componentCandidate graph comp candidate) run childIndex).w <
      (frameRect P (componentCandidate graph comp candidate) run parentIndex).x +
        (frameRect P (componentCandidate graph comp candidate) run parentIndex).w

/-- Narrower residual (group link, top side): single strict inequality. -/
def XCA_LinkTopX (exactIds : List String) : Prop :=
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
    (frameRect P (componentCandidate graph comp candidate) run parentIndex).y <
      (frameRect P (componentCandidate graph comp candidate) run childIndex).y

/-- Narrower residual (group link, bottom side): single strict inequality. -/
def XCA_LinkBotX (exactIds : List String) : Prop :=
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
    (frameRect P (componentCandidate graph comp candidate) run childIndex).y +
      (frameRect P (componentCandidate graph comp candidate) run childIndex).h <
      (frameRect P (componentCandidate graph comp candidate) run parentIndex).y +
        (frameRect P (componentCandidate graph comp candidate) run parentIndex).h

/-- Group-link residual from its four sides: the exact direct-parent link is
strict on each side, hence strictly inside. -/
theorem XCA_groupLinkX_holds (exactIds : List String)
    (hleft : XCA_LinkLeftX exactIds)
    (hright : XCA_LinkRightX exactIds)
    (htop : XCA_LinkTopX exactIds)
    (hbot : XCA_LinkBotX exactIds) :
    XCA_GroupLinkX exactIds := by
  intro P inp o lines measured graph0 graph h0 hgraph hlines hwf hframed
  intro comp hcomp candidate run labels orderOptions hrun
  intro parentIndex childIndex parent child parentBox childBox
  intro hparent hpb hchild hcb hpbox hcbox href hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hleft h0 hgraph hlines hwf hframed hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne
  · exact hright h0 hgraph hlines hwf hframed hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne
  · exact htop h0 hgraph hlines hwf hframed hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne
  · exact hbot h0 hgraph hlines hwf hframed hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne

/-- Narrower residual (marker band): the caption rank band top lies at or
below the ancestor bottom marker top over one exact run. Single inequality;
strictly narrower than `XCA_MarkerBelowX` (band bound, no caption content).
True on the probe: every ancestor-marker pair satisfies it. -/
def XCA_MarkerBandBelowX (exactIds : List String) : Prop :=
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
    run.top.getD (rk run.coordinateProper.rank i).toNat 0 +
      CoordsImpl.layerHeight run.coordinateProper
        (run.layers.getD (rk run.coordinateProper.rank i).toNat []) ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).y

/-- Marker-below residual from the caption band and the marker band: the
transported caption bottom lies in its rank band (`XC_CapBandX`), whose top
is at or below the ancestor marker top. -/
theorem XCA_markerBelowX_holds (exactIds : List String)
    (hcap : XC_CapBandX exactIds)
    (hmark : XCA_MarkerBandBelowX exactIds) :
    XCA_MarkerBelowX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder pos fNode hfn hne hancrel hbor2
  exact Int.le_trans (hcap execution hcomp hrun i stored0 tNode hmem hnode hborder)
    (hmark execution hcomp hrun i stored0 tNode hmem hnode hborder pos fNode hfn hne hancrel hbor2)

/-- `xfa_` copy of `components_mem_bound_copy`
(`CaptionRunClearClosed.lean:45`): component members index valid nodes. -/
private theorem xfa_mem_bound {g : Graph} {comp : List Nat}
    (hmem : comp ∈ components g) {v : Nat} (hv : v ∈ comp) :
    v < g.nodes.length := by
  unfold components at hmem
  dsimp only at hmem
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hmem
  rw [← hr] at hv
  exact List.mem_range.mp (List.mem_filter.mp hv).1

/-- `xfa_` copy of `otherClear_demote_facts` (`CaptionRunClearClosed.lean:56`):
the demoted box keeps id, parent, and exclusivity. -/
private theorem xfa_demote_facts {inp : Input} (box : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).id = box.id ∧
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).parent = box.parent ∧
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).exclusive = box.exclusive := by
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- `xfa_` copy of `otherClear_getElem_unique`
(`CaptionRunClearClosed.lean:67`): injectivity of the id map on nodup lists. -/
private theorem xfa_getElem_unique {α : Type} {f : α → String} {l : List α}
    (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hid : f x = f y) :
    x = y := by
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy
  by_cases hij : i = j
  · subst hij
    exact hxi.symm.trans hyj
  · exfalso
    have hp := List.pairwise_iff_getElem.mp hnd
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · have h := hp i j (by simpa using hi) (by simpa using hj) hlt
      exact h (by simp only [List.getElem_map, hxi, hyj, hid])
    · exact absurd heq hij
    · have h := hp j i (by simpa using hj) (by simpa using hi) hgt
      exact h (by simp only [List.getElem_map, hyj, hxi, ← hid])

/-- `xfa_` copy of `xca_key_rev` (`ExactCaptionAncestorsProof.lean:247`):
drop from an exact node back to its measured source. -/
private theorem xfa_key_rev {P : Params} {exactIds : List String} {inp : Input}
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

/-- `xfa_` copy of `xca_demoteId` (`ExactCaptionAncestorsProof.lean:155`):
demotion keeps ids. -/
private theorem xfa_demoteId {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) b).id = b.id := by
  intro b _
  dsimp only
  split <;> rfl

/-- `xfa_` copy of `xca_demoteParent` (`ExactCaptionAncestorsProof.lean:162`):
demotion keeps parents. -/
private theorem xfa_demoteParent {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) b).parent = b.parent := by
  intro b _
  dsimp only
  split <;> rfl

/-- `xfa_` copy of `xca_demoteLookup`
(`ExactCaptionAncestorsProof.lean:170`): invert a fixed-boxes lookup. -/
private theorem xfa_demoteLookup {inp : Input} {i : Nat} {b : ModelBox}
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

/-- `xfa_` copy of `XCM_plain_path`
(`ExactCaptionMembersProof.lean:167`): measured-graph plain node source,
taking the graph equation and line count directly. -/
private theorem xfa_plain_path {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph0 : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hlines : lines.length = inp.boxes.length)
    {index : Nat} {node : Node} (hnode : graph0.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  obtain ⟨nodes, _edges, _titles, hprepared, hnodesLen, hmetadata⟩ :=
    measuredGraph_prepared_source h0
  have hpreparedNode := hnode
  rw [hprepared] at hpreparedNode
  have hi : index < nodes.length := by
    by_cases hi : index < nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega)
        hpreparedNode
      omega
  have hibox : index < inp.boxes.length := by
    have hlen : nodes.length = inp.boxes.length := by rw [hnodesLen, hlines]
    omega
  let box := inp.boxes[index]'hibox
  have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hibox
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨hdecl, hpath⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hplain hchangedBox
  exact ⟨box, hbox, hdecl, hpath.trans hpathMap⟩

/-- `xfa_` copy of `otherClear_path_group_role`
(`CaptionRunClearClosed.lean:87`): every member of an `ancestors` walk is a
group in the demoted box list. -/
private theorem xfa_path_group_role {inp : Input}
    (hfp : framedParents inp = true)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (eff : List ModelBox)
    (heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b)
    (fuel : Nat) (c : ModelBox) (hc : c ∈ inp.boxes) :
    ∀ i ∈ Compound.ancestors eff fuel c.parent,
      ∃ b, eff[i]? = some b ∧ b.role = .group := by
  induction fuel generalizing c with
  | zero =>
    intro i hi
    have hempty : Compound.ancestors eff 0 c.parent = [] := rfl
    rw [hempty] at hi
    simp at hi
  | succ fuel ih =>
    intro i hi
    by_cases hcp : c.parent = ""
    · have hnil : Compound.ancestors eff (fuel + 1) c.parent = [] := by
        simp [hcp, Compound.ancestors]
      rw [hnil] at hi
      simp at hi
    · have h3 := Compound.ancestors.eq_3 eff c.parent fuel hcp
      rw [h3] at hi
      cases hf : eff.findIdx? (fun box => box.id == c.parent) with
      | none =>
        simp only [hf] at hi
        simp at hi
      | some j =>
        simp only [hf] at hi
        cases hb : eff[j]? with
        | none =>
          simp only [hb] at hi
          simp at hi
        | some e =>
          simp only [hb] at hi
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have heid : e.id = c.parent := by
            rw [← hbjEq]
            exact beq_iff_eq.mp hjid
          have heffj : eff[j]? = (inp.boxes[j]?).map fun b =>
              if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
                { b with role := .node } else b := by
            rw [heff, List.getElem?_map]
          rw [heffj] at hb
          cases hjo : inp.boxes[j]? with
          | none => rw [hjo] at hb; exact absurd hb (by simp)
          | some orig =>
            rw [hjo] at hb
            have heq : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                { orig with role := .node } else orig) = e := Option.some.inj hb
            have horig : orig ∈ inp.boxes := List.mem_of_getElem? hjo
            have hdemParent : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                { orig with role := .node } else orig).parent = orig.parent :=
              (xfa_demote_facts orig).2.1
            have heid' : orig.id = c.parent := by
              have hroleD : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                  { orig with role := .node } else orig).id = orig.id :=
                (xfa_demote_facts orig).1
              have heid'' := heid
              rw [← heq] at heid''
              exact hroleD.symm.trans heid''
            have hbE : eff[j]? = some e := by
              rw [heffj, hjo]
              exact congrArg some heq
            simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with hi | rfl
            · rw [← heq, hdemParent] at hi
              exact ih orig horig i hi
            · refine ⟨e, hbE, ?_⟩
              rw [← heq]
              have hall : (c.parent == "" ||
                  inp.boxes.any fun parent =>
                    parent.id == c.parent && parent.role == .group &&
                      !inp.fixedSizes.any (fun fixed => fixed.1 == parent.id)) = true :=
                List.all_eq_true.mp hfp c hc
              have hOr : (c.parent == "") = true ∨
                  (inp.boxes.any fun parent =>
                    parent.id == c.parent && parent.role == .group &&
                      !inp.fixedSizes.any (fun fixed => fixed.1 == parent.id)) = true := by
                by_cases hblank : (c.parent == "") = true
                · exact Or.inl hblank
                · right
                  have hfalse : (c.parent == "") = false := by
                    cases h2 : (c.parent == "") with
                    | true => exact absurd h2 hblank
                    | false => rfl
                  simp only [hfalse, Bool.false_or] at hall
                  exact hall
              rcases hOr with hblank | hany
              · exact absurd (beq_iff_eq.mp hblank) hcp
              · obtain ⟨pb, hpbmem, hpb⟩ := List.any_eq_true.mp hany
                simp only [Bool.and_eq_true] at hpb
                obtain ⟨⟨hpbIdB, hpbRoleB⟩, hpbNotFixB⟩ := hpb
                have hpbId : pb.id = c.parent := beq_iff_eq.mp hpbIdB
                have hpbRole : pb.role = .group := beq_iff_eq.mp hpbRoleB
                have hnotfix : inp.fixedSizes.any
                    (fun fixed => fixed.1 == pb.id) = false := by
                  simpa using hpbNotFixB
                have horigEq : orig = pb :=
                  xfa_getElem_unique hids horig hpbmem (by
                    rw [heid']; exact hpbId.symm)
                have hdem : (if inp.fixedSizes.any (fun fixed => fixed.1 == pb.id) then
                    { pb with role := .node } else pb) = pb := by
                  simp [hnotfix]
                rw [horigEq, hdem]
                exact hpbRole

/-- Plain-ancestor impossibility over exact runs: replay of
`captionAncestorOtherClear_executed` (`CaptionRunClearClosed.lean:205`) with
the measured-graph origins transported across `exactGraph`. A border-`0`
candidate node carries its source-graph index as declaration and the input
box path as cluster path (`xfa_plain_path`); on the title's path it is an
ancestor index, hence a group in the demoted list
(`xfa_path_group_role`), while its demoted box is not a group
(`prepare_group_title_record` contrapositive). -/
theorem XCA_plainAncestorImpossibleX_holds (exactIds : List String) :
    XCA_PlainAncestorImpossibleX exactIds := by
  intro P inp o lines measured graph0 graph h0 hgraph hlines hwf hframed
  intro comp hcomp candidate tNode fNode tIdx fIdx hnode hborder hfn hb0 hne hancrel
  obtain ⟨origT, _, hsrcT⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨ndT0, hndT0, hbT0, hpT0, hdT0⟩ := xfa_key_rev hgraph hsrcT
  have hbT0' : ndT0.border = -2 := hbT0.symm.trans hborder
  obtain ⟨hdeclT0, boxTE, hboxTE, _, hpathT0⟩ :=
    measuredGraph_group_origin h0 hndT0 hbT0'
  have hdeclT : tNode.decl = origT := hdT0.trans hdeclT0
  obtain ⟨origTU, horigTU, _, _, _, hdemTU⟩ := xfa_demoteLookup hboxTE
  have horigT : inp.boxes[origT]? = some origTU := hdeclT0 ▸ horigTU
  have hpmU : Compound.path (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) boxTE =
      Compound.path inp.boxes origTU := by
    have hpm := Compound.path_map inp.boxes
      (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)
      xfa_demoteId xfa_demoteParent (List.mem_of_getElem? horigTU)
    rw [← hdemTU] at hpm
    exact hpm
  have hpathTEq : tNode.clusterPath = Compound.path inp.boxes origTU ++ [tNode.decl] := by
    rw [hpT0, hpathT0, hpmU, ← hdT0]
  rw [componentCandidate_nodes] at hfn
  have hmap : (componentGraph graph comp).nodes =
      comp.map (fun v => graph.nodes.getD v default) := rfl
  rw [hmap, List.getElem?_map] at hfn
  obtain ⟨origP, hcompP, hgetP⟩ := Option.map_eq_some_iff.mp hfn
  have hmemP : origP ∈ comp := List.mem_of_getElem? hcompP
  have hltP : origP < graph.nodes.length :=
    xfa_mem_bound hcomp hmemP
  obtain ⟨n, hn⟩ : ∃ n, graph.nodes[origP]? = some n :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨hltP, rfl⟩⟩
  have hget : graph.nodes.getD origP default = n := by
    simp [List.getD_eq_getElem?_getD, hn]
  rw [hget] at hgetP
  rw [hgetP] at hn
  obtain ⟨ndP0, hndP0, hbP0, _hpP0, hdP0⟩ := xfa_key_rev hgraph hn
  have hbP0' : ndP0.border = 0 := hbP0.symm.trans hb0
  obtain ⟨boxP, hboxP, hdeclP, _hpathP⟩ := xfa_plain_path h0 hlines hndP0 hbP0'
  have hdeclP' : fNode.decl = origP := hdP0.trans hdeclP
  rw [hpathTEq, hdeclP', hdeclT] at hancrel
  have hnePO : origP ≠ origT :=
    fun hcon => hne (hdeclT.trans (hcon.symm.trans hdeclP'.symm))
  have hmemAppend : origP ∈ Compound.path inp.boxes origTU ++ [origT] := by
    have hdec : decide (origP ∈ Compound.path inp.boxes origTU ++ [origT]) = true := by
      rw [← List.contains_eq_mem]
      exact hancrel
    exact of_decide_eq_true hdec
  rcases List.mem_append.mp hmemAppend with hleft | hright
  · let eff : List ModelBox := inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b
    let chT : ModelBox := (if inp.fixedSizes.any (fun fixed => fixed.1 == origTU.id) then
      { origTU with role := .node } else origTU)
    let chP : ModelBox := (if inp.fixedSizes.any (fun fixed => fixed.1 == boxP.id) then
      { boxP with role := .node } else boxP)
    obtain ⟨_, heffP, _⟩ := fixedSizes_path_index inp hboxP
    obtain ⟨_, _, hpathMapT⟩ := fixedSizes_path_index inp horigT
    have hpathT_eq : Compound.path eff chT = Compound.path inp.boxes origTU :=
      hpathMapT
    have heffP' : eff[origP]? = some chP := heffP
    have hdemT : chT.parent = origTU.parent := (xfa_demote_facts origTU).2.1
    have hmemFuel : origP ∈ Compound.ancestors eff eff.length origTU.parent := by
      have hmemChT : origP ∈ Compound.path eff chT := by
        rw [hpathT_eq]
        exact hleft
      rw [← hdemT]
      exact hmemChT
    have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
    obtain ⟨b, hb, hrole⟩ := xfa_path_group_role hframed hids eff rfl
      eff.length origTU (List.mem_of_getElem? horigT) origP hmemFuel
    have hbeq : b = chP := Option.some.inj (hb.symm.trans heffP')
    subst hbeq
    obtain ⟨nodes, edges, titles, hprepared, hnodesLen, _⟩ :=
      measuredGraph_prepared_source h0
    have hltLen : origP < nodes.length := by
      rw [hnodesLen, hlines]
      exact (List.getElem?_eq_some_iff.mp hboxP).1
    have hpreparedNode : (Compound.prepare eff P.clusterPad titles
        { nodes := nodes, edges := edges,
          slot := P.slot }).nodes[origP]? = some ndP0 := by
      have h := hndP0
      rw [hprepared] at h
      exact h
    have hroleNe : chP.role ≠ .group := by
      intro hgroup
      have hrec := Compound.prepare_group_title_record eff P.clusterPad
        titles { nodes := nodes, edges := edges, slot := P.slot }
        hltLen heffP' hgroup
      have heq := Option.some.inj (hpreparedNode.symm.trans hrec)
      have hb2 : ndP0.border = -2 := congrArg Node.border heq
      rw [hbP0'] at hb2
      omega
    exact absurd hrole hroleNe
  · have hsingleton : origP = origT := List.mem_singleton.mp hright
    exact absurd hsingleton hnePO
