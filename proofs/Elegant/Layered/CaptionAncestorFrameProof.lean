import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.ChildFrameStrictRankProof
import Elegant.Layered.BottomClearanceNesting
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.GroupBottomBoundaryProof
import Elegant.Layered.GroupWidthFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Ancestor frame strictness for executed runs

The former `CaptionLocalClearProof.CaptionAncestorFrameStrict` quantified over
every node whose declaration lies on the title node's cluster path. That
statement is FALSE as written: the ancestor's bottom marker (border `2`) has
the ancestor declaration, but its frame is a zero-height rect at the bottom
band while the child group hull is large. Minimal witness
(`proofs/wip/Probe/CaptionAncestorFrameCheck.lean`, input B below):

* boxes `[O group, I group-in-O, a in I, b in I]`, vector TB profile,
  component `0`, candidate `0`;
* title `i = 1` (group `I`, decl `1`, path `[0, 1]`),
  `pos = 4` (bottom marker of `O`, decl `0`, border `2`, path `[0]`);
* `(frameRect P cg run pos).StrictInside (frameRect P cg run i)` is false:
  `frP = { x := -256, y := 19200, w := 11826, h := 0 }`,
  `frI = { x := 1280, y := 5376, w := 8754, h := 10752 }`
  (needs `19200 < 5376`). The reverse nesting is false too.

The def now lives in `CaptionLocalClearProof`, split in two. The group half
`CaptionAncestorGroupFrameStrict` restricts the ancestor position to group
nodes (border `-2`): the child group frame lies strictly inside each ancestor
group frame (`captionAncestorGroupFrameStrict_executed` below). The marker half
`CaptionAncestorMarkerClear` covers non-group ancestor positions: in the
candidate graph those have border `0` or `2` (`componentCandidate_marker_shape`;
side markers `±1` and title copies `3` do not occur), and the transported
caption is disjoint from their frame rects (`captionAncestorMarkerClear_executed`
below). Probe: `proofs/wip/Probe/CaptionAncestorMarkerTProbe.lean` — 3 nested
inputs × 4 direction/profile configs: 60 bottom-marker ancestor pairs, all
disjoint, none strictly inside; zero plain-ancestor pairs observed.

Proof plan (group half): one-link strictness is the closed
`SceneExecution.component_child_frame_strictInside''` (no rank residuals;
`framedParents` discharges them). `ancParentLink` derives the `ModelBox`
parent evidence for the direct parent of any box on the chain from
`clusterPath` containment via `framedParents_parent` and
`Compound.path_of_parent`. `ancChain` inducts on the length of the path
suffix below the ancestor, threading component membership of each
intermediate group through its compound-constraint edge
(`compound_child_constraint_edges`, `components_edge_endpoints`,
`components_shared_member_eq`), and closes each link with transitivity of
`Rect.StrictInside`.

Proof plan (marker half): the caption lies in its own top band
(`captionInTopBand_executed`), the child's own bottom marker ranks strictly
below the title (`componentRun_group_top_lt_bottom`), and a descendant
group's bottom marker ranks at or below its ancestor's bottom marker
(`bottomNestedBottomRankLe`), so the ancestor's bottom marker band lies
strictly below the caption bottom (`rankAxis_band_top_strict` with
`fbs_run_node_band`). A plain (`0`) ancestor position is impossible: its box
would both be a non-group (plain origin) and a group (ancestor-path
membership). Remaining borders are ruled out by `componentCandidate_marker_shape`.
-/

/-- Copy of the private `BottomClearanceExistence.demote_lookup`: inverting a
fixed-boxes lookup recovers the original box and its demotion facts. -/
private theorem ancDemoteLookup {inp : Input} {i : Nat} {b : ModelBox}
    (h : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[i]? = some b) :
    ∃ orig : ModelBox, inp.boxes[i]? = some orig ∧ b.id = orig.id ∧ b.parent = orig.parent ∧
      (b.role = .group →
        ¬(inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) = true)) ∧
      b = (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
            { orig with role := .node } else orig) := by
  rw [List.getElem?_map] at h
  cases hop : inp.boxes[i]? with
  | none => rw [hop] at h; simp at h
  | some orig =>
    rw [hop, Option.map_some, Option.some.injEq] at h
    by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == orig.id)
    · have hd : b = ({ orig with role := .node } : ModelBox) :=
        h.symm.trans (ite_eq_left hfixed)
      refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_,
        by rw [hd, ite_eq_left hfixed]⟩
      intro hrole
      rw [hd] at hrole
      simp at hrole
    · have hd : b = orig :=
        h.symm.trans (ite_eq_right (by simp [hfixed]))
      refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_,
        by rw [hd, ite_eq_right hfixed]⟩
      intro _
      exact hfixed

/-- Copy of the private `BottomClearanceExistence.demote_id`. -/
private theorem ancDemoteId {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) b).id = b.id := by
  intro b _
  dsimp only
  split <;> rfl

/-- Copy of the private `BottomClearanceExistence.demote_parent`. -/
private theorem ancDemoteParent {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) b).parent = b.parent := by
  intro b _
  dsimp only
  split <;> rfl

/-- Copy of the private `BottomClearanceExistence.measuredConstraintsBounded`. -/
private theorem ancConstraintsBounded {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hgraph : measuredGraph P inp o lines = .ok g)
    (hlines : lines.length = inp.boxes.length) :
    ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact measuredGraph_edges_bounded hgraph hlines e he
  · exact constraints_bounded g e he

/-- Copy of the private `BottomClearanceExistence.findSomeOfMember`. -/
private theorem ancFindSomeOfMember {l : List (Node × Nat)} {pred : Node × Nat → Bool}
    {entry : Node × Nat} (hmem : entry ∈ l) (hp : pred entry = true) :
    ∃ b : Node × Nat, l.find? pred = some b :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hp⟩)

/-- Copy of the private `BottomClearanceExistence.groupTopFind?_some`: every
measured-graph group top finds its paired bottom marker by declaration. -/
private theorem ancGroupTopFind {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {t : Node × Nat} (htop : t ∈ graph.nodes.zipIdx) (hgroup : t.1.border = -2) :
    ∃ b : Node × Nat,
      graph.nodes.zipIdx.find? (fun e => e.1.border == 2 && e.1.decl == t.1.decl) = some b := by
  have hlookup : graph.nodes[t.2]? = some t.1 := List.mem_zipIdx_iff_getElem?.mp htop
  obtain ⟨hdecl, box, hbox, hrole, _⟩ := measuredGraph_group_origin hgraph hlookup hgroup
  have hbound : t.1.decl < lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hbox).1
    rw [List.length_map] at hi
    omega
  obtain ⟨_, bottom, _, hbmem, _, hbborder, _, hbdecl, _, _, _, _⟩ :=
    measuredGraph_paired_markers hgraph hbound hbox hrole
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hbmem
  have hp : ((fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl)
      (bottom, idx)) = true := by
    simp [hbborder, hbdecl]
  exact ancFindSomeOfMember (List.mem_zipIdx_iff_getElem?.mpr hidx) hp

/-- A nonempty list splits off its last element. -/
private theorem ancPeelLast {α : Type} {l : List α} (hne : l ≠ []) :
    ∃ (pre : List α) (last : α), l = pre ++ [last] := by
  induction l with
  | nil => exact absurd rfl hne
  | cons s ss ih =>
    by_cases hss : ss = []
    · subst hss
      exact ⟨[], s, by simp⟩
    · obtain ⟨pre, last, hpl⟩ := ih hss
      exact ⟨s :: pre, last, by rw [hpl]; rfl⟩

/-- Executed lines cover every input box. -/
private theorem ancHlines {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := (mapM_getElem? _ _ _ execution.lines_eq).1
  simpa only [List.length_zipIdx] using h

/-- Direct-parent evidence for a box on the ancestor chain: the parent box
is a non-demoted group, and the unmapped path grows by exactly its index.
This is step (1) of the task: `ModelBox` parent evidence for consecutive
entries of a node's cluster path. -/
private theorem ancParentLink {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {c : Nat} {cbO : ModelBox} (hcbO : inp.boxes[c]? = some cbO)
    (hpathNe : Compound.path inp.boxes cbO ≠ []) :
    ∃ (p : Nat) (boxP : ModelBox), inp.boxes[p]? = some boxP ∧ boxP.role = .group ∧
      cbO.parent = boxP.id ∧ cbO.parent ≠ "" ∧
      (inp.fixedSizes.any (fun fixed => fixed.1 == boxP.id) = false) ∧
      ((inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[p]? = some boxP) ∧
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
  have heffP : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[p]? = some boxP := by
    simp only [List.getElem?_map, hp, Option.map_some, ite_eq_right hnp]
  have hstep : Compound.path inp.boxes cbO =
      Compound.path inp.boxes boxP ++ [p] :=
    Compound.path_of_parent (inputModel inp o) hwf hp hcbO (by rw [hpid]) hparNe
  exact ⟨p, boxP, hp, hpgroup, hpid.symm, hparNe, hpnotfixed, heffP, hstep.symm⟩
/-- The ancestor base path is nonempty: it ends with the ancestor declaration. -/
private theorem ancBaseNe {inp : Input} {origF : ModelBox} {f : Nat} :
    Compound.path inp.boxes origF ++ [f] ≠ [] := by
  intro hcon
  have hlen := congrArg List.length hcon
  simp at hlen

/-- Direct single-link step: when the current box's unmapped path is exactly
the ancestor base, its direct parent is the ancestor group itself, so one
application of the closed single-step strictness suffices. -/
private theorem ancDirectStep {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {pos : Nat} {fNode : Node}
    (hfn : (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode)
    (hfborder : fNode.border = -2)
    {origF : ModelBox} (horigF : inp.boxes[fNode.decl]? = some origF)
    {cIdx c : Nat} {cn : Node}
    (hcn : (componentCandidate execution.graph comp candidate).nodes[cIdx]? = some cn)
    (hbord : cn.border = -2) (hdecl : cn.decl = c)
    {cbO : ModelBox} (hcbO : inp.boxes[c]? = some cbO)
    (hpath : Compound.path inp.boxes cbO =
      Compound.path inp.boxes origF ++ [fNode.decl]) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).StrictInside
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run cIdx) := by
  obtain ⟨p, boxP, hboxP, _, hrefP, hneP, _, _, hstepP⟩ :=
    ancParentLink hwf hframed hcbO (by rw [hpath]; exact ancBaseNe)
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
  exact SceneExecution.component_child_frame_strictInside'' execution hwf hframed hcomp hrun
    hfn hfborder hcn hbord horigF (by rwa [hdecl]) hrefP hneP

/-- Ancestor-chain induction (step (2) of the task): from the path equation
`path cbO = base ++ rest`, every group on the chain nests strictly, by one
closed single-step link per parent edge and transitivity of
`Rect.StrictInside`. Component membership of each intermediate group comes
from its compound-constraint edge to the child. -/
private theorem ancChain {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {pos : Nat} {fNode : Node}
    (hfn : (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode)
    (hfborder : fNode.border = -2)
    {origF : ModelBox} (horigF : inp.boxes[fNode.decl]? = some origF) :
    ∀ (n : Nat) (rest : List Nat) (cIdx c : Nat) (cn : Node),
    rest.length ≤ n →
    (componentCandidate execution.graph comp candidate).nodes[cIdx]? = some cn →
    cn.border = -2 → cn.decl = c →
    ∀ (cbO : ModelBox), inp.boxes[c]? = some cbO →
    Compound.path inp.boxes cbO =
      (Compound.path inp.boxes origF ++ [fNode.decl]) ++ rest →
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).StrictInside
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run cIdx) := by
  intro n
  induction n with
  | zero =>
    intro rest cIdx c cn hlen hcn hbord hdecl cbO hcbO hpath
    have hrNil : rest = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hrNil, List.append_nil] at hpath
    exact ancDirectStep execution hwf hframed hcomp hrun hfn hfborder horigF
      hcn hbord hdecl hcbO hpath
  | succ n ih =>
    intro rest cIdx c cn hlen hcn hbord hdecl cbO hcbO hpath
    by_cases hrest : rest = []
    · subst hrest
      rw [List.append_nil] at hpath
      exact ancDirectStep execution hwf hframed hcomp hrun hfn hfborder horigF
        hcn hbord hdecl hcbO hpath
    · obtain ⟨rest', p, hrpeel⟩ := ancPeelLast hrest
      have hlen' : rest'.length ≤ n := by
        have h := hlen
        rw [hrpeel] at h
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        omega
      obtain ⟨origC, hcompC, hsourceC⟩ :=
        componentCandidate_nonplain_source hcn (by omega)
      obtain ⟨hdeclC, boxCE, hboxCE, hroleCE, hpathCE⟩ :=
        measuredGraph_group_origin execution.graph_eq hsourceC hbord
      have hcorig : c = origC := hdecl.symm.trans hdeclC
      have hoIn : origC ∈ comp := List.mem_of_getElem? hcompC
      obtain ⟨origCE, horigCE, _, _, _, hdemCE⟩ := ancDemoteLookup hboxCE
      have hcbOEq : origCE = cbO := by
        have h1 : inp.boxes[cn.decl]? = some origCE := horigCE
        rw [hdecl] at h1
        exact Option.some.inj (h1.symm.trans hcbO)
      have hpathMap : Compound.path (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) boxCE =
          Compound.path inp.boxes cbO := by
        have hpm := Compound.path_map inp.boxes
          (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)
          ancDemoteId ancDemoteParent (List.mem_of_getElem? horigCE)
        rw [← hdemCE, hcbOEq] at hpm
        exact hpm
      have hcnPath : cn.clusterPath = Compound.path inp.boxes cbO ++ [c] := by
        rw [hpathCE, hpathMap, hdecl]
      obtain ⟨q, boxQ, hboxQ, hroleQ, hrefQ, hneQ, hnonfixQ, heffQ, hstepQ⟩ :=
        ancParentLink hwf hframed hcbO (by
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
      have hpq : p = q := hqq.symm
      subst hpq
      have hlines := ancHlines execution
      have hplt : p < execution.lines.length := by
        have h1 := (List.getElem?_eq_some_iff.mp hboxQ).1
        omega
      obtain ⟨pn, _, hpnLookup, _, hpnBord, _, hpnDecl, _, hpnPath, _, _, _⟩ :=
        measuredGraph_paired_markers execution.graph_eq hplt heffQ hroleQ
      have hdemQ : (if inp.fixedSizes.any (fun fixed => fixed.1 == boxQ.id) then
          { boxQ with role := .node } else boxQ) = boxQ := by
        have h : ¬(inp.fixedSizes.any (fun fixed => fixed.1 == boxQ.id) = true) := by
          rw [hnonfixQ]; decide
        exact ite_eq_right h
      have hboxQMap : Compound.path (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) boxQ =
          Compound.path inp.boxes boxQ := by
        have hpm := Compound.path_map inp.boxes
          (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)
          ancDemoteId ancDemoteParent (List.mem_of_getElem? hboxQ)
        rwa [hdemQ] at hpm
      have hpathSnoc : Compound.path inp.boxes cbO =
          (Compound.path inp.boxes origF ++ [fNode.decl] ++ rest') ++ [p] := by
        rw [hpath, hrpeel, ← List.append_assoc]
      have hpathEdge : (cn, origC).1.clusterPath.dropLast = (pn, p).1.clusterPath := by
        show cn.clusterPath.dropLast = pn.clusterPath
        rw [hcnPath, hpnPath, hboxQMap, hpathSnoc, hdropQ]
        rw [List.dropLast_append_of_ne_nil (l := [c]) (by simp)]
        simp
      have hparZip : (pn, p) ∈ execution.graph.nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hpnLookup
      have hchildZip : (cn, origC) ∈ execution.graph.nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hsourceC
      obtain ⟨botP, hbotP⟩ := ancGroupTopFind execution.graph_eq hlines hparZip hpnBord
      obtain ⟨botC, hbotC⟩ := ancGroupTopFind execution.graph_eq hlines hchildZip hbord
      obtain ⟨heP, _⟩ := compound_child_constraint_edges hparZip hpnBord hbotP
        hchildZip hbord hpathEdge hbotC
      have hbd := ancConstraintsBounded execution.graph_eq hlines
      obtain ⟨c', hcMem, hcP, hcO⟩ :=
        components_edge_endpoints hbd (List.mem_append_right _ heP)
      have hcEq : c' = comp := components_shared_member_eq hcMem hcomp hcO hoIn
      have hpinComp : p ∈ comp := hcEq ▸ hcP
      have htopPin : pn ∈ (componentCandidate execution.graph comp candidate).nodes := by
        rw [componentCandidate_nodes]
        exact List.mem_map.mpr ⟨p, hpinComp, by
          rw [List.getD_eq_getElem?_getD, hpnLookup]
          rfl⟩
      obtain ⟨cpIdx, hcpIdx⟩ := List.mem_iff_getElem?.mp htopPin
      have hstep := SceneExecution.component_child_frame_strictInside'' execution hwf
        hframed hcomp hrun hcpIdx hpnBord hcn hbord (by rwa [hpnDecl])
        (by rwa [hdecl]) hrefQ hneQ
      have hIH := ih rest' cpIdx p pn hlen' hcpIdx hpnBord hpnDecl boxQ hboxQ hdropQ
      exact captionStrictInside_trans hIH hstep
/-- Executed ancestor-group frame strictness: in an executed run, the frame
of a group lies strictly inside the frame of each of its ancestor groups.
Same binders as `captionLocalClear_executed` passes to
`CaptionAncestorGroupFrameStrict`. -/
theorem captionAncestorGroupFrameStrict_executed {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run) :
    CaptionAncestorGroupFrameStrict execution.params
      (componentCandidate execution.graph comp candidate) run := by
  intro i pos tNode fNode hnode hborder hfn hfborder hne hmem
  obtain ⟨_, hcompTi, hsourceT⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨_, boxT, hboxT, _, hpathT⟩ :=
    measuredGraph_group_origin execution.graph_eq hsourceT hborder
  obtain ⟨_, _, hsourceF⟩ :=
    componentCandidate_nonplain_source hfn (by omega)
  obtain ⟨_, boxF, hboxF, _, _⟩ :=
    measuredGraph_group_origin execution.graph_eq hsourceF hfborder
  obtain ⟨origT, horigT, _, _, _, hdemT⟩ := ancDemoteLookup hboxT
  obtain ⟨origF, horigF, _, _, _, _⟩ := ancDemoteLookup hboxF
  have hpmU : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) boxT =
      Compound.path inp.boxes origT := by
    have hpm := Compound.path_map inp.boxes
      (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
      ancDemoteId ancDemoteParent (List.mem_of_getElem? horigT)
    rw [← hdemT] at hpm
    exact hpm
  have hpathTEq : tNode.clusterPath = Compound.path inp.boxes origT ++ [tNode.decl] := by
    rw [hpathT, hpmU]
  have hmemT : fNode.decl ∈ tNode.clusterPath := by
    have h2 : decide (fNode.decl ∈ tNode.clusterPath) = true := by
      rw [← List.contains_eq_mem]
      exact hmem
    exact of_decide_eq_true h2
  have hmemU : fNode.decl ∈ Compound.path inp.boxes origT := by
    have h2 : fNode.decl ∈ Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) boxT ++ [tNode.decl] := by
      rw [← hpathT]
      exact hmemT
    rcases List.mem_append.mp h2 with h | h
    · rwa [hpmU] at h
    · exact absurd (List.mem_singleton.mp h).symm hne
  have horigF' : (inputModel inp o).boxes[fNode.decl]? = some origF := horigF
  have horigT' : (inputModel inp o).boxes[tNode.decl]? = some origT := horigT
  have hpre := Compound.path_ancestor_prefix (inputModel inp o) hwf horigF' horigT' hmemU
  obtain ⟨rest, hr⟩ := hpre
  exact ancChain execution hwf hframed hcomp hrun hfn hfborder horigF
    rest.length rest i tNode.decl tNode (Nat.le_refl _) hnode hborder rfl origT horigT hr.symm
/-- Copy of the private `CaptionLocalClearProof.run_rank_eq_coordinate_copy`:
executed proper rank equals coordinate rank. -/
private theorem ancRunRankEq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (i : Nat) :
    rk run.proper.rank i = rk run.coordinateProper.rank i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]

/-- Executed ancestor-marker clearance: the ancestor's bottom marker is
disjoint from the transported caption. The caption sits in its own top band
(`captionInTopBand_executed`); the child's own bottom marker ranks strictly
below the title (`componentRun_group_top_lt_bottom`) while a descendant
group's bottom marker ranks at or below its ancestor's bottom marker
(`bottomNestedBottomRankLe`), so the ancestor marker's band lies strictly
below the caption bottom (`rankAxis_band_top_strict` with `fbs_run_node_band`). -/
theorem captionAncestorMarkerClear_executed {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {i : Nat} {stored0 : Rect} {tNode : Node}
    (hmem : (i, stored0) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2)
    {pos : Nat} {fNode : Node} {g0 : Rect}
    (hfn : (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode)
    (hne : tNode.decl ≠ fNode.decl)
    (hancrel : tNode.clusterPath.contains fNode.decl = true)
    (hbor2 : fNode.border = 2)
    (hframe : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos = g0) :
    Disjoint g0 (transportCaption execution.params o execution.lines comp i stored0) := by
  have hlines : execution.lines.length = inp.boxes.length := ancHlines execution
  obtain ⟨childBot, hfindChild⟩ :=
    componentRun_cg_bottom_find execution.graph_eq hlines hcomp hnode hborder
  have hcondC := List.find?_some hfindChild
  simp only [Bool.and_eq_true, beq_iff_eq] at hcondC
  obtain ⟨hborChild, hdeclChild⟩ := hcondC
  have hnodeB : (componentCandidate execution.graph comp candidate).nodes[childBot.2]? =
      some childBot.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfindChild)
  obtain ⟨ancTop, hfindAnc⟩ :=
    componentRun_cg_top_of_bottom execution.graph_eq hlines hcomp hfn hbor2
  have hcondA := List.find?_some hfindAnc
  simp only [Bool.and_eq_true, beq_iff_eq] at hcondA
  obtain ⟨hbordAnc, hpathAnc⟩ := hcondA
  have htopGet : (componentCandidate execution.graph comp candidate).nodes[ancTop.2]? =
      some ancTop.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfindAnc)
  obtain ⟨origA, _, hsrcA⟩ :=
    componentCandidate_nonplain_source htopGet (by rw [hbordAnc]; decide)
  obtain ⟨_, boxA, hboxA, _, hpathA⟩ :=
    measuredGraph_group_origin execution.graph_eq hsrcA hbordAnc
  obtain ⟨_, _, hsrcF⟩ :=
    componentCandidate_nonplain_source hfn (by rw [hbor2]; decide)
  obtain ⟨_, hboxF, _, hpathF, _, _⟩ :=
    measuredGraph_bottom_origin execution.graph_eq (List.mem_of_getElem? hsrcF) hbor2
  have eAnc1 : ancTop.1.clusterPath.getLast? = some ancTop.1.decl := by rw [hpathA]; simp
  have eAnc2 : fNode.clusterPath.getLast? = some fNode.decl := by rw [hpathF]; simp
  rw [hpathAnc] at eAnc1
  have hdeclEq : ancTop.1.decl = fNode.decl := Option.some.inj (eAnc1.symm.trans eAnc2)
  obtain ⟨_, _, hsrcTi⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨_, boxTi, hboxTi, _, hpathTi⟩ :=
    measuredGraph_group_origin execution.graph_eq hsrcTi hborder
  have hmemT : fNode.decl ∈ tNode.clusterPath := by
    have h2 : decide (fNode.decl ∈ tNode.clusterPath) = true := by
      rw [← List.contains_eq_mem]
      exact hancrel
    exact of_decide_eq_true h2
  have hmemU : fNode.decl ∈ Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) boxTi := by
    have h2 : fNode.decl ∈ Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) boxTi ++ [tNode.decl] := by
      rw [← hpathTi]
      exact hmemT
    rcases List.mem_append.mp h2 with h | h
    · exact h
    · exact absurd (List.mem_singleton.mp h).symm hne
  obtain ⟨origU, horigU, _, _, _, hdemU⟩ := ancDemoteLookup hboxTi
  have hpmU : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) boxTi =
      Compound.path inp.boxes origU := by
    have hpm := Compound.path_map inp.boxes
      (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
      ancDemoteId ancDemoteParent (List.mem_of_getElem? horigU)
    rw [← hdemU] at hpm
    exact hpm
  obtain ⟨_, _, hsrcCB⟩ := componentCandidate_nonplain_source hnodeB (by rw [hborChild]; decide)
  obtain ⟨boxCB, hboxCB, _, hpathCB, _, _⟩ :=
    measuredGraph_bottom_origin execution.graph_eq (List.mem_of_getElem? hsrcCB) hborChild
  have hboxEq : boxCB = boxTi := by
    rw [hdeclChild] at hboxCB
    exact Option.some.inj (hboxCB.symm.trans hboxTi)
  have hcontCB : childBot.1.clusterPath.contains ancTop.1.decl = true := by
    have hmemCB : ancTop.1.decl ∈ childBot.1.clusterPath := by
      rw [hpathCB, hboxEq, hdeclEq]
      exact List.mem_append_left _ (hpmU ▸ hmemU)
    rw [List.contains_eq_mem]
    exact decide_eq_true hmemCB
  have hneCB : childBot.1.decl ≠ ancTop.1.decl := by
    rw [hdeclChild, hdeclEq]
    exact hne
  have hle : rk run.coordinateProper.rank childBot.2 ≤ rk run.coordinateProper.rank pos :=
    bottomNestedBottomRankLe execution.params execution.graph execution.graph_eq hlines hwf
      hframed hcomp hrun hfn htopGet hbor2 hbordAnc hdeclEq.symm hnodeB hborChild hneCB
      hcontCB
  have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hbotLt : childBot.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnodeB).1
  have hposLt : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hfn).1
  obtain ⟨rrB, _, hrrB, hcB, _, _, hranksB, hlt⟩ :=
    componentRun_group_top_lt_bottom execution.graph_eq hcomp hrun
  have htopLtBot := hlt i tNode childBot hnode hborder hfindChild
  have eTop : rk run.coordinateProper.rank i = rk rrB.ranks i := by
    have h2 := prepared_coordinate_original_rk (P := execution.params) hrrB hranksB hindexLt
    rw [hcB] at h2
    exact h2
  have eChild : rk run.coordinateProper.rank childBot.2 = rk rrB.ranks childBot.2 := by
    have h2 := prepared_coordinate_original_rk (P := execution.params) hrrB hranksB hbotLt
    rw [hcB] at h2
    exact h2
  have rEqT := ancRunRankEq hrun i
  have rEqP := ancRunRankEq hrun pos
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, hry, _, _⟩ :=
    componentRun_spec hrun
  have hindexLen : i < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun i hindexLt
  have hposLen : pos < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun pos hposLt
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
  obtain ⟨ltP, hlyP, _, hnnM⟩ := hcov pos hposLen
  rw [rEqT] at hlyT hnnT
  rw [rEqP] at hlyP hnnM
  have hltTP : (rk run.coordinateProper.rank i).toNat <
      (rk run.coordinateProper.rank pos).toNat := by
    have h1 := eTop
    have h2 := eChild
    have h3 : rk rrB.ranks i + 1 ≤ rk rrB.ranks childBot.2 := htopLtBot
    have h4 := hnnT
    have h5 := hnnM
    have h6 := hle
    omega
  have hbandTP := rankAxis_band_top_strict hry _ _ _ _ hltTP hlyT hlyP
  have hbandLo := (fbs_run_node_band hrun pos hposLen).1
  rw [rEqP] at hbandLo
  have hcap := (captionInTopBand_executed execution hcomp hrun hmem hnode hborder).2
  have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
    simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
  have hposGet : (componentCandidate execution.graph comp candidate).nodes.getD pos default =
      fNode := by
    simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
  have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos =
      nodeRect (componentCandidate execution.graph comp candidate) run pos := by
    unfold frameRect
    simp only []
    rw [hposGet, hbor2]
    rfl
  have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run pos).y =
      run.ys.getD pos 0 := rfl
  rw [← hframe, hfr]
  unfold Disjoint
  intro hcon
  obtain ⟨-, hy⟩ := hcon
  rw [hltTget] at hcap
  omega
end Elegant.Layered.PipelineImpl
