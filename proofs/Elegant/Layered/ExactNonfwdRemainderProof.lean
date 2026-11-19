import Elegant.Layered.ExactNonfwdAncHullProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CgShape
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.GroupWidthFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact non-forward hull remainders, narrowed (W form)

Targets: the two residuals of `ExactNonfwdAncHullProof`,
`XNonfwd_AncRemXW` (plain-owner strict upgrade given proved frame containment,
AND group-owner ancestor `StrictInside`) and `XNonfwd_NonAncRemXW` (foreign
disjointness sub-case AND nested containment `(frame t).Contained (frame pos)`).

Truth (`wip/Probe/ExactNonfwdAncHullTProbe.lean`, 10 executed inputs x 5
candidates): 55 ancestor/nested/foreign checks, zero violations. Ancestor pairs
are `StrictInside` with the ancestor hull containing the owner frame
(`ancCont = true`, plain and group owners, zero-size included). Nested pairs
(group owner with child group) are `Disjoint` with the child frame in the
owner frame (`nestCont = true`). Foreign pairs (connected siblings) are
`Disjoint` with the footprint kept left of the hull (`keep = true`).
Ill-formed and split-component inputs contribute no pairs.

Proved here, outright (group owners, the only occurring nested/ancestor
owner case on every probe):
* nested containment, by chaining `exactRunFrameNesting.2` down the cluster
  path (induction on the descendant path length; each step is one direct
  `ModelBox` parent link threaded through `compound_child_constraint_edges`
  into the same component);
* the group-owner ancestor containment core (`frame pos` contains `frame t`),
  by the same chain upward.
Each is strictly narrower than its target conjunct in the only way that
matters here: it concludes `Contained` (a lemma on the way) rather than the
footprint claim.

Staying open, as strictly smaller residuals:
* plain-owner strict upgrade (needs `LoopHullRightCover`, non-plain part
  `LoopResGroupHullRight`, plus positive hull margins);
* group-owner `StrictInside` given the now-proved containment (needs the same
  hull-right cover);
* foreign disjointness (needs `LoopHullRightNeighborCover` through
  `R3ExtentFitGap` with the foreign-span seams);
* nested containment for non-group owners (`nt.border != -2`: plain owners
  whose decl lies in a group path are demoted fixed groups, bottom owners
  carry a group decl; loop ownership there is absent on every probe and its
  vacuity is unproved, so both stay as narrow sub-cases);
* ancestor `StrictInside` for bottom owners (`nt.border = 2`, same reason).
-/

/-- Executed exact lines cover every input box (copy of the `ancHlines`
pattern used across the ancestor proofs). -/
private theorem xnr_lines_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := (mapM_getElem? _ _ _ execution.lines_eq).1
  simpa only [List.length_zipIdx] using h

/-- A `find?` hit exposes the entry (copy of the `findSomeOfMember` pattern;
private lemmas of other modules do not resolve). -/
private theorem xnr_findSomeOfMember {l : List (Node × Nat)}
    {pred : (Node × Nat) → Bool}
    {entry : Node × Nat} (hmem : entry ∈ l) (hp : pred entry = true) :
    ∃ b : Node × Nat, l.find? pred = some b :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hp⟩)

/-- Fixed-size demotion preserves ids (copy of the `demote_id` pattern;
private lemmas of other modules do not resolve). -/
private theorem xnr_demote_id {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) b).id = b.id := by
  intro b _
  dsimp only
  split <;> rfl

/-- Fixed-size demotion preserves parents (copy of the `demote_parent`
pattern; private lemmas of other modules do not resolve). -/
private theorem xnr_demote_parent {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) b).parent = b.parent := by
  intro b _
  dsimp only
  split <;> rfl

/-- Direct-parent `ModelBox` evidence for a box on the ancestor chain: the
parent of a box with nonempty path is a non-demoted group, and the path grows
by exactly its index (first half of the `ancParentLink` pattern). -/
private theorem xnr_parent_box {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {idx : Nat} {boxB : ModelBox} (hboxB : inp.boxes[idx]? = some boxB)
    {ancDecl : Nat} (hmemB : ancDecl ∈ Compound.path inp.boxes boxB) :
    ∃ (parentBox : ModelBox) (p₀ : Nat), inp.boxes[p₀]? = some parentBox ∧
      Compound.path inp.boxes boxB = Compound.path inp.boxes parentBox ++ [p₀] ∧
      boxB.parent = parentBox.id ∧ boxB.parent ≠ "" ∧
      parentBox.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == parentBox.id) = false := by
  have hpathNe : Compound.path inp.boxes boxB ≠ [] :=
    List.ne_nil_of_mem hmemB
  have hparNe : boxB.parent ≠ "" := by
    intro hempty
    apply hpathNe
    unfold Compound.path
    rw [hempty]
    cases hlen : inp.boxes.length with
    | zero => simp [Compound.ancestors]
    | succ n => simp [Compound.ancestors]
  obtain ⟨parentBox, hmemP, hpid, hpgroup, hpnotfixed⟩ :=
    framedParents_parent hframed (List.mem_of_getElem? hboxB) hparNe
  obtain ⟨p₀, hp₀⟩ := List.mem_iff_getElem?.mp hmemP
  refine ⟨parentBox, p₀, hp₀, ?_, hpid.symm, hparNe, hpgroup, hpnotfixed⟩
  exact Compound.path_of_parent (inputModel inp o) hwf hp₀ hboxB
    (by rw [hpid]) hparNe

/-- Parent group step over an exact run: the direct `ModelBox` parent of a
group node's box appears as a `-2` candidate node whose path is the node's
dropped path, with the box evidence needed for `ExactRunFrameNesting.2`. -/
private theorem xnr_parent_step {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat}
    {didx : Nat} {desc : Node}
    (hd : (componentCandidate execution.graph comp candidate).nodes[didx]? = some desc)
    (hdb : desc.border = -2)
    {boxB parentBox : ModelBox} {p₀ : Nat} (hp₀ : inp.boxes[p₀]? = some parentBox)
    (hpathStep : Compound.path inp.boxes boxB =
      Compound.path inp.boxes parentBox ++ [p₀])
    (hpgroup : parentBox.role = .group)
    (hnfP : inp.fixedSizes.any (fun fixed => fixed.1 == parentBox.id) = false)
    (hdrop : desc.clusterPath.dropLast = Compound.path inp.boxes boxB)
    (hrefP : boxB.parent = parentBox.id) (hneP : boxB.parent ≠ "") :
    ∃ (pIdx : Nat) (up : Node),
      (componentCandidate execution.graph comp candidate).nodes[pIdx]? = some up ∧
      up.border = -2 ∧ up.clusterPath = desc.clusterPath.dropLast ∧
      inp.boxes[up.decl]? = some parentBox ∧
      Compound.path inp.boxes boxB = Compound.path inp.boxes parentBox ++ [up.decl] ∧
      boxB.parent = parentBox.id ∧ boxB.parent ≠ "" := by
  have hlines := xnr_lines_len execution
  have hnp : ¬(inp.fixedSizes.any (fun fixed => fixed.1 == parentBox.id) = true) := by
    intro hc
    rw [hc] at hnfP
    simp at hnfP
  have hfbp : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[p₀]? = some parentBox := by
    simp only [List.getElem?_map, hp₀, Option.map_some, ite_eq_right hnp]
  have hp₀bound : p₀ < execution.lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hfbp).1
    rw [List.length_map] at hi
    omega
  obtain ⟨topP, bottomP, htopPlookup, _, htopPborder, _, _, _, htopPpath, _⟩ :=
    measuredGraph_paired_markers execution.graph0_eq hp₀bound hfbp hpgroup
  obtain ⟨topE, htopElook, htopEbord, htopEpath, htopEdecl⟩ :=
    exactGraph_node_key execution.graph_eq htopPlookup
  have htopEb : topE.border = -2 := by
    rw [htopEbord]; exact htopPborder
  have hpathParent : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) parentBox =
      Compound.path inp.boxes parentBox := by
    have h := Compound.path_map inp.boxes (fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) xnr_demote_id xnr_demote_parent
      (List.mem_of_getElem? hp₀)
    have hfP : (if inp.fixedSizes.any (fun fixed => fixed.1 == parentBox.id) then
        ({ parentBox with role := .node } : ModelBox) else parentBox) =
        parentBox := by
      have h : ¬(inp.fixedSizes.any (fun fixed => fixed.1 == parentBox.id) =
          true) := by
        rw [hnfP]; decide
      exact ite_eq_right h
    rwa [hfP] at h
  have htopEdrop : topE.clusterPath = desc.clusterPath.dropLast := by
    rw [htopEpath, htopPpath, hpathParent, ← hpathStep, ← hdrop]
  have htopEzip : (topE, p₀) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopElook
  obtain ⟨oIdxD, hoD, hsourceD⟩ := componentCandidate_nonplain_source hd (by omega)
  have hoIn : oIdxD ∈ comp := List.mem_of_getElem? hoD
  have hdescZip : (desc, oIdxD) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hsourceD
  obtain ⟨botP, hbotPfind⟩ := X_groupTopFind?_some execution.graph0_eq
    execution.graph_eq hlines htopEzip htopEb
  obtain ⟨botD, hbotDfind⟩ := X_groupTopFind?_some execution.graph0_eq
    execution.graph_eq hlines hdescZip hdb
  obtain ⟨heP, _⟩ := compound_child_constraint_edges htopEzip htopEb hbotPfind
    hdescZip hdb htopEdrop.symm hbotDfind
  have hbd := X_exactConstraintsBounded execution.graph0_eq execution.graph_eq hlines
  obtain ⟨c, hcMem, hcP, hcO⟩ :=
    components_edge_endpoints hbd (List.mem_append_right _ heP)
  have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcO hoIn
  rw [hcEq] at hcP
  have htopPin : topE ∈ (componentCandidate execution.graph comp candidate).nodes := by
    rw [componentCandidate_nodes]
    exact List.mem_map.mpr ⟨p₀, hcP, by
      rw [List.getD_eq_getElem?_getD, htopElook]
      rfl⟩
  obtain ⟨pIdx, hpIdx⟩ := List.mem_iff_getElem?.mp htopPin
  have hpred : ((fun entry : Node × Nat =>
      entry.1.border == -2 && entry.1.clusterPath == desc.clusterPath.dropLast)
      (topE, pIdx)) = true := by
    simp [htopEb, htopEdrop]
  obtain ⟨u, hu⟩ := xnr_findSomeOfMember (pred := fun entry : Node × Nat =>
      entry.1.border == -2 && entry.1.clusterPath == desc.clusterPath.dropLast)
    (List.mem_zipIdx_iff_getElem?.mpr hpIdx) hpred
  have huPred := List.find?_some hu
  simp only [Bool.and_eq_true, beq_iff_eq] at huPred
  obtain ⟨huBorder, huPath⟩ := huPred
  have huMem : u ∈ (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
    List.mem_of_find?_eq_some hu
  have huLookup : (componentCandidate execution.graph comp candidate).nodes[u.2]? =
      some u.1 :=
    List.mem_zipIdx_iff_getElem?.mp huMem
  obtain ⟨boxU, hboxU, hpathU⟩ :=
    X_cg_group_box execution.graph0_eq execution.graph_eq huLookup huBorder
  have hEq : Compound.path inp.boxes boxU ++ [u.1.decl] =
      Compound.path inp.boxes parentBox ++ [p₀] :=
    hpathU.symm.trans (huPath.trans (hdrop.trans hpathStep))
  have hdeclEq : u.1.decl = p₀ := by
    have hlast := congrArg List.getLast? hEq
    rw [List.getLast?_append, List.getLast?_append] at hlast
    simpa using hlast
  have hboxU' : inp.boxes[u.1.decl]? = some parentBox := by
    rw [hdeclEq]; exact hp₀
  refine ⟨u.2, u.1, huLookup, huBorder, huPath, hboxU', ?_, hrefP, hneP⟩
  rw [hdeclEq]; exact hpathStep

/-- Transitive ancestor-frame containment over an exact run: a group frame
contains every descendant group frame whose path carries its declaration.
Induction on the descendant path length; each step is one direct `ModelBox`
parent link (`xnr_parent_step`) closed by `ExactRunFrameNesting.2`, chained by
`Rect.Contained.trans`. -/
private theorem xnr_chain_contained {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    ∀ (len b : Nat) (nb : Node),
    (componentCandidate execution.graph comp candidate).nodes[b]? = some nb →
    nb.border = -2 → nb.clusterPath.length = len →
    ∀ (ancDecl : Nat), ancDecl ∈ nb.clusterPath →
    ∀ (a : Nat) (na : Node),
    (componentCandidate execution.graph comp candidate).nodes[a]? = some na →
    na.border = -2 → na.decl = ancDecl →
    (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run a).Contained
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run b) := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro b nb hb hbb hlenB ancDecl hmemA a na ha hba hdeclA
    by_cases heq : nb.decl = ancDecl
    · obtain ⟨boxB, hboxB, hpathB⟩ :=
        X_cg_group_box execution.graph0_eq execution.graph_eq hb hbb
      obtain ⟨boxA, hboxA, hpathA⟩ :=
        X_cg_group_box execution.graph0_eq execution.graph_eq ha hba
      have hboxEq : boxA = boxB := by
        have h1 : inp.boxes[na.decl]? = some boxA := hboxA
        rw [hdeclA, ← heq] at h1
        exact Option.some.inj (h1.symm.trans hboxB)
      have hpathEq : na.clusterPath = nb.clusterPath := by
        rw [hpathA, hpathB, hboxEq, hdeclA, ← heq]
      have hab : a = b := X_cg_top_unique execution.graph0_eq execution.graph_eq
        hcomp ha hb hba hbb hpathEq
      subst hab
      exact Rect.Contained.refl _
    · obtain ⟨boxB, hboxB, hpathB⟩ :=
        X_cg_group_box execution.graph0_eq execution.graph_eq hb hbb
      have hmemB : ancDecl ∈ Compound.path inp.boxes boxB := by
        rw [hpathB] at hmemA
        rcases List.mem_append.mp hmemA with h | h
        · exact h
        · have hsing : ancDecl = nb.decl := List.mem_singleton.mp h
          exact (heq hsing.symm).elim
      obtain ⟨parentBox, p₀, hp₀, hpathStep, hrefP, hneP, hpgroup, hnfP⟩ :=
        xnr_parent_box hwf hframed hboxB hmemB
      have hdrop : nb.clusterPath.dropLast = Compound.path inp.boxes boxB := by
        rw [hpathB, List.dropLast_append_of_ne_nil (l := [nb.decl]) (by simp)]
        simp
      obtain ⟨pIdx, up, huLookup, huBorder, huPath, hupBox, hupStep, hupRef,
          hupNe⟩ :=
        xnr_parent_step execution hcomp hb hbb hp₀ hpathStep hpgroup hnfP hdrop
          hrefP hneP
      have hmemU : ancDecl ∈ up.clusterPath := by
        rw [huPath, hdrop]; exact hmemB
      have hpathNe : nb.clusterPath ≠ [] :=
        (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq
          hb).2 hbb
      have hlenU : up.clusterPath.length = len - 1 := by
        rw [huPath, List.length_dropLast, hlenB]
      have hlt : len - 1 < len := by
        have hpos : 0 < nb.clusterPath.length := List.length_pos_iff.mpr hpathNe
        rw [hlenB] at hpos; omega
      have hIH := ih (len - 1) hlt pIdx up huLookup huBorder hlenU ancDecl
        hmemU a na ha hba hdeclA
      have hstep := (exactRunFrameNesting execution hwf hframed).2 comp candidate
        run orderOptions hcomp hrun pIdx b up nb huLookup huBorder hb hbb
        parentBox boxB hupBox hboxB hupRef hupNe
      exact Rect.Contained.trans hIH hstep

/-- Nested containment for group loop owners, proved outright: the owner
frame contains every descendant group frame whose path carries the owner
declaration. One chain application; plain and bottom owners stay in the
smaller residual. -/
theorem XNonfwd_nestedGroup_holds (exactIds : List String) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border = -2 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      nt.decl ∈ gn.clusterPath →
      (frameRect execution.params cg run t).Contained
        (frameRect execution.params cg run pos) := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun het hpos hne nt hgrp hnt gn hg hgrpG hmem
  subst hcg
  exact xnr_chain_contained execution hwf hfp hcomp hrun
    gn.clusterPath.length pos gn hg hgrpG rfl nt.decl hmem t nt hnt hgrp rfl

/-- Group-owner ancestor containment core, proved outright: an ancestor group
frame contains the group loop-owner frame. Same chain, upward. The strict
upgrade stays in the smaller residual. -/
theorem XNonfwd_groupContain_holds (exactIds : List String) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border = -2 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∈ nt.clusterPath →
      (frameRect execution.params cg run pos).Contained
        (frameRect execution.params cg run t) := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun het hpos hne nt hgrp hnt gn hg hgrpG hmem
  subst hcg
  exact xnr_chain_contained execution hwf hfp hcomp hrun
    nt.clusterPath.length t nt hnt hgrp rfl gn.decl hmem pos gn hg hgrpG rfl

/-- Smaller ancestor residual: the plain-owner strict upgrade unchanged, the
group-owner `StrictInside` with the now-proved containment as an extra
premise, and the bottom-owner (`border = 2`) sub-case alone. Each conjunct is
strictly narrower than the corresponding `XNonfwd_AncRemXW` conjunct (extra
containment premise; `border = -2` / `border = 2` restrictions); together they
imply it once the group containment is supplied. -/
def XNonfwd_AncRemSmallXW (exactIds : List String) : Prop :=
  (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border = 0 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∈ nt.clusterPath →
      (frameRect execution.params cg run pos).Contained
        (frameRect execution.params cg run t) →
      (frameRect execution.params cg run pos).StrictInside
        (loopFootprintExt cg run execution.measured t))
  ∧ (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border = -2 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∈ nt.clusterPath →
      (frameRect execution.params cg run pos).Contained
        (frameRect execution.params cg run t) →
      (frameRect execution.params cg run pos).StrictInside
        (loopFootprintExt cg run execution.measured t))
  ∧ (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border = 2 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∈ nt.clusterPath →
      (frameRect execution.params cg run pos).StrictInside
        (loopFootprintExt cg run execution.measured t))

/-- Smaller non-ancestor residual: the foreign disjointness sub-case
unchanged, plus nested containment for non-group owners (`nt.border != -2`).
The group-owner nested case is proved outright (`XNonfwd_nestedGroup_holds`),
so this conjunction is strictly smaller than `XNonfwd_NonAncRemXW`. -/
def XNonfwd_NonAncRemSmallXW (exactIds : List String) : Prop :=
  (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∉ nt.clusterPath →
      nt.decl ∉ gn.clusterPath →
      Disjoint (frameRect execution.params cg run pos)
        (loopFootprintExt cg run execution.measured t))
  ∧ (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border ≠ -2 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∉ nt.clusterPath →
      nt.decl ∈ gn.clusterPath →
      (frameRect execution.params cg run t).Contained
        (frameRect execution.params cg run pos))

/-- Ancestor residual from its smaller form: the plain upgrade replays
unchanged; the group-owner case splits on the executed border trichotomy,
using the proved containment for `-2` and the narrow leftovers otherwise. -/
theorem XNonfwd_ancRem_of_parts (exactIds : List String)
    (hSmall : XNonfwd_AncRemSmallXW exactIds) :
    XNonfwd_AncRemXW exactIds := by
  obtain ⟨hPlain, hGroup, hBottom⟩ := hSmall
  constructor
  · intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
      hcomp hcg hrun het hpos hne nt hplain hnt gn hg hgrp hmem hcont
    exact hPlain inp o res execution hwf hfp comp candidate run orderOptions
      cg t pos hcomp hcg hrun het hpos hne nt hplain hnt gn hg hgrp hmem hcont
  · intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
      hcomp hcg hrun het hpos hne nt hne0 hnt gn hg hgrp hmem
    subst hcg
    have hshape := (X_componentCandidate_marker_shape execution.graph0_eq
      execution.graph_eq hnt).1
    rcases hshape with h0 | h2 | hB
    · exact (hne0 h0).elim
    · have hcont := XNonfwd_groupContain_holds exactIds inp o res execution
        hwf hfp comp candidate run orderOptions _ t pos hcomp rfl hrun het
        hpos hne nt h2 hnt gn hg hgrp hmem
      exact hGroup inp o res execution hwf hfp comp candidate run orderOptions
        _ t pos hcomp rfl hrun het hpos hne nt h2 hnt gn hg hgrp hmem hcont
    · exact hBottom inp o res execution hwf hfp comp candidate run orderOptions
        _ t pos hcomp rfl hrun het hpos hne nt hB hnt gn hg hgrp hmem

/-- Non-ancestor residual from its smaller form: the foreign case replays
unchanged; the nested case uses the proved group-owner containment and keeps
only the non-group-owner sub-case open. -/
theorem XNonfwd_nonAncRem_of_parts (exactIds : List String)
    (hSmall : XNonfwd_NonAncRemSmallXW exactIds) :
    XNonfwd_NonAncRemXW exactIds := by
  obtain ⟨hForeign, hNestOpen⟩ := hSmall
  constructor
  · intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
      hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmemF hmemN
    exact hForeign inp o res execution hwf hfp comp candidate run orderOptions
      cg t pos hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmemF hmemN
  · intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
      hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmemF hmemN
    by_cases hgrp2 : nt.border = -2
    · exact XNonfwd_nestedGroup_holds exactIds inp o res execution hwf hfp
        comp candidate run orderOptions cg t pos hcomp hcg hrun het hpos hne
        nt hgrp2 hnt gn hg hgrp hmemN
    · exact hNestOpen inp o res execution hwf hfp comp candidate run
        orderOptions cg t pos hcomp hcg hrun het hpos hne nt hgrp2 hnt gn hg
        hgrp hmemF hmemN

end PipelineImpl
end Layered
end Elegant
