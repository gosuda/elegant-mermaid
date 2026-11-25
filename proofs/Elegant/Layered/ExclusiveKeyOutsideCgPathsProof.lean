import Elegant.Layered.ExclusiveBoxBridgeProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.FlatC6ScopeResidualsProof
import Elegant.Layered.RunStageNodeFacts
import Elegant.Model

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl
private theorem getElem_unique_id {α : Type} {f : α → String} {l : List α}
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

/-- Every member of a `Compound.ancestors` walk started at a box's parent is a
group box: each member carries the id of a parent chain box, `framedParents`
supplies a group parent of that id, and id uniqueness identifies the member
with it. -/
private theorem path_member_group {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (fuel : Nat) (c : ModelBox) (hc : c ∈ inp.boxes)
    {i : Nat} (hin : i ∈ Compound.ancestors inp.boxes fuel c.parent) :
    ∃ b, inp.boxes[i]? = some b ∧ b.role = .group := by
  induction fuel generalizing c with
  | zero => simp [Compound.ancestors] at hin
  | succ fuel ih =>
    by_cases hcp : c.parent = ""
    · rw [hcp] at hin
      simp [Compound.ancestors] at hin
    · cases hf : inp.boxes.findIdx? (fun box => box.id == c.parent) with
      | none => simp [Compound.ancestors, hf] at hin
      | some k =>
        obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        cases hb : inp.boxes[k]? with
        | none => simp [Compound.ancestors, hf, hb] at hin
        | some b =>
          have hbElem : inp.boxes[k] = b :=
            Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hb)
          have he : b.id = c.parent := by
            have h := beq_iff_eq.mp hmatch
            rwa [hbElem] at h
          simp only [Compound.ancestors, hf, hb] at hin
          rcases List.mem_append.mp hin with hin | hin
          · exact ih b (List.mem_of_getElem? hb) hin
          · have hik : i = k := List.mem_singleton.mp hin
            subst hik
            have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
            have hall := List.all_eq_true.mp hframed c hc
            have hfalse : (c.parent == "") = false := by
              cases h2 : (c.parent == "") with
              | true => exact absurd (beq_iff_eq.mp h2) hcp
              | false => rfl
            rw [hfalse, Bool.false_or] at hall
            obtain ⟨pb, hpbmem, hpb⟩ := List.any_eq_true.mp hall
            obtain ⟨hpbIdRoleB, _hpbNotFixB⟩ := Bool.and_eq_true_iff.mp hpb
            obtain ⟨hpbIdB, hpbRoleB⟩ := Bool.and_eq_true_iff.mp hpbIdRoleB
            have hpbId : pb.id = c.parent := beq_iff_eq.mp hpbIdB
            have hpbRole : pb.role = .group := beq_iff_eq.mp hpbRoleB
            have heq : b = pb :=
              getElem_unique_id hids (List.mem_of_getElem? hb) hpbmem
                (he.trans hpbId.symm)
            subst heq
            exact ⟨b, hb, hpbRole⟩

/-- A demoted box with group role comes from a group-role source box: a fixed
box demotes to node role, so group role forces the unmodified branch. -/
private theorem demoted_group_role {inp : Input} {box boxD : ModelBox}
    (hmap : (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box) = boxD)
    (hrole : boxD.role = .group) : box.role = .group := by
  by_cases hfix : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
  · simp only [hfix, ↓reduceIte] at hmap
    rw [← hmap] at hrole
    simp at hrole
  · have hfix' : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
      Bool.eq_false_iff.mpr hfix
    simp only [hfix'] at hmap
    subst hmap
    exact hrole

/-- A node of a component candidate graph is the measured-graph node at its
component key, or the empty-path default when the key is out of range. -/
private theorem candidate_graph_node {g : Graph} {comp : List Nat} {candidate u : Nat}
    {nd : Node} (h : (componentCandidate g comp candidate).nodes[u]? = some nd) :
    (∃ keyU, comp[u]? = some keyU ∧ g.nodes[keyU]? = some nd) ∨
      nd.clusterPath = [] := by
  rw [componentCandidate_nodes] at h
  have hmap : (componentGraph g comp).nodes =
      comp.map (fun v => g.nodes.getD v default) := rfl
  rw [hmap, List.getElem?_map] at h
  cases hu : comp[u]? with
  | none => simp [hu] at h
  | some keyU =>
    simp only [hu, Option.map_some, Option.some.injEq] at h
    cases hgU : g.nodes[keyU]? with
    | none =>
      right
      have hnd : (default : Node) = nd := by
        simpa [List.getD_eq_getElem?_getD, hgU, Option.getD_none] using h
      rw [← hnd]
      rfl
    | some n =>
      left
      have hnn : n = nd := by
        simpa [List.getD_eq_getElem?_getD, hgU, Option.getD_some] using h
      subst hnn
      exact ⟨keyU, rfl, hgU⟩

/-- The declaration of a group-frame or bottom node of the measured graph is a
group-role box: the measured origins carry group role on the demoted box,
which transfers to the source box. -/
private theorem graph_decl_box_is_group {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {idx : Nat} {nd : Node} (hgU : execution.graph.nodes[idx]? = some nd)
    (hb : nd.border = -2 ∨ nd.border = 2)
    {source : ModelBox} (hsource : inp.boxes[nd.decl]? = some source) :
    source.role = .group := by
  rcases hb with hm2 | h2
  · obtain ⟨_, boxD, hboxD, hroleD, _⟩ :=
      measuredGraph_group_origin execution.graph_eq hgU hm2
    rw [List.getElem?_map, hsource] at hboxD
    obtain ⟨a, ha, hchange⟩ := Option.map_eq_some_iff.mp hboxD
    have har : source = a := Option.some.inj ha
    subst har
    exact demoted_group_role hchange hroleD
  · obtain ⟨boxD, hboxD, hroleD, _, _, _⟩ :=
      measuredGraph_bottom_origin execution.graph_eq (List.mem_of_getElem? hgU) h2
    rw [List.getElem?_map, hsource] at hboxD
    obtain ⟨a, ha, hchange⟩ := Option.map_eq_some_iff.mp hboxD
    have har : source = a := Option.some.inj ha
    subst har
    exact demoted_group_role hchange hroleD

/-- The cluster path of a measured-graph node never contains the index of an
exclusive source box: plain paths list ancestor indices, which are groups,
while frame and bottom paths append the declaration of a group box. -/
private theorem graph_node_clusterPath_excludes {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {key : Nat} {source : ModelBox} {nd : Node}
    (hsource : inp.boxes[key]? = some source) (hexcl : source.exclusive = true)
    {keyU : Nat} (hgU : execution.graph.nodes[keyU]? = some nd) :
    key ∉ nd.clusterPath := by
  intro hmem
  have hng : source.role ≠ .group := by
    intro hg
    obtain ⟨_, _, _, _, _, _, hgroups⟩ := (wellFormed_iff (inputModel inp o)).mp hwf
    have hexf := hgroups source (List.mem_of_getElem? hsource) hg
    rw [hexf] at hexcl
    exact Bool.noConfusion hexcl
  have htri := (measuredGraph_marker_shape execution.graph_eq hgU).1
  rcases htri with h0 | hm2 | h2
  · obtain ⟨boxU, hboxU, _, hpath⟩ := execution.plain_node_path_source hgU h0
    rw [hpath] at hmem
    obtain ⟨b, hb, hrole⟩ :=
      path_member_group hwf hframed _ _ (List.mem_of_getElem? hboxU) hmem
    have heq : b = source := Option.some.inj (hb.symm.trans hsource)
    rw [heq] at hrole
    exact hng hrole
  · obtain ⟨boxU, hboxU, hdeclU, hpath⟩ := execution.group_node_path_source hgU hm2
    rw [hpath] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · obtain ⟨b, hb, hrole⟩ :=
        path_member_group hwf hframed _ _ (List.mem_of_getElem? hboxU) hleft
      have heq : b = source := Option.some.inj (hb.symm.trans hsource)
      rw [heq] at hrole
      exact hng hrole
    · have hkeyU : key = keyU := List.mem_singleton.mp hright
      subst hkeyU
      rw [← hdeclU] at hsource
      have hrole := graph_decl_box_is_group execution hgU (Or.inl hm2) hsource
      exact hng hrole
  · obtain ⟨boxU, hboxU, hpath⟩ := execution.bottom_node_path_source hgU h2
    rw [hpath] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · obtain ⟨b, hb, hrole⟩ :=
        path_member_group hwf hframed _ _ (List.mem_of_getElem? hboxU) hleft
      have heq : b = source := Option.some.inj (hb.symm.trans hsource)
      rw [heq] at hrole
      exact hng hrole
    · have hkeyD : key = nd.decl := List.mem_singleton.mp hright
      rw [hkeyD] at hsource
      have hrole := graph_decl_box_is_group execution hgU (Or.inr h2) hsource
      exact hng hrole

/-- Residual: for a well-formed framed input, the declaration of an
exclusive-sourced box never occurs in the cluster path of any node of an
executed component candidate graph. Candidate nodes are measured-graph nodes,
whose cluster paths list ancestor indices; ancestors are groups, and an
exclusive box is never a group. -/
theorem exclusiveKeyOutsideCgPaths (inp : Input) (o : Options) (res : FamilyResult) :
    ExclusiveKeyOutsideCgPaths inp o res := by
  intro hwf hframed execution comp candidate v key source hcomp hcompv hsource hexcl u nd hnd
  rcases candidate_graph_node hnd with ⟨keyU, _, hgU⟩ | hempty
  · exact graph_node_clusterPath_excludes execution hwf hframed hsource hexcl hgU
  · simp [hempty]

/-- The exclusive box bridge with the proved run-node declaration fact: the
`ExclusiveRunNodeDecl` residual is discharged by declaration preservation
through the executed run. -/
theorem exclusiveBoxInLabelRun' {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) :
    ExclusiveBoxInLabelRun inp o res :=
  exclusiveBoxInLabelRun hwf hframed
    (exclusiveRunNodeDecl_of_preserved properDeclPreserved)
    (exclusiveKeyOutsideCgPaths inp o res)

end PipelineImpl
end Layered
end Elegant
