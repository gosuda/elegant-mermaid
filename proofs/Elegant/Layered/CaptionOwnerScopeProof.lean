import Elegant.Layered.CaptionsSeamFacts
import Elegant.Layered.CaptionDescendantFacts
import Elegant.Layered.CaptionOwnerScopeFacts
import Elegant.Layered.CaptionTitleBranchFacts
import Elegant.Layered.CaptionDescendantCore
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CgShape

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Elegant.Layered
open Elegant.Layered.Compound

/-! # Group-owner frame disjointness of the caption owner scope

Within one successfully executed packed part, the frame of an unmeasured
caption's nonexclusive group-role owner is disjoint from the frame of an
exclusive box outside the caption's dump-side owner scope and not descended
from the owner. The installed title need not be absent. -/

/-- Id uniqueness survives the fixed-size role demotion. -/
private theorem ownerScope_demote_ids {inp : Input}
    (hids : (inp.boxes.map (·.id)).Nodup) :
    ((inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box).map (·.id)).Nodup := by
  have hcongr : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box).map (·.id) =
      inp.boxes.map (·.id) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro box _
    show (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box).id = box.id
    split <;> rfl
  rw [hcongr]
  exact hids

/-- The demoted box keeps id, parent, and exclusivity. -/
private theorem ownerScope_demote_facts {inp : Input} (box : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).id = box.id ∧
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).parent = box.parent ∧
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).exclusive = box.exclusive := by
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The executed graph node of an input box: declaration index, demoted role,
and the ancestor path of the demoted box (extended by the box index for a
group frame node). -/
private theorem ownerScope_graph_node {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlinesLen : lines.length = inp.boxes.length)
    {k : Nat} {box : ModelBox} (hk : inp.boxes[k]? = some box) :
    ∃ node : Node, graph.nodes[k]? = some node ∧ node.decl = k ∧
      ((((if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box).role = .group) ∧
        node.border = -2 ∧
        node.clusterPath = Compound.path (inp.boxes.map fun b =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
            { b with role := .node } else b)
          (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) ++ [k]) ∨
      (((if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box).role ≠ .group) ∧
        node.border = 0 ∧
        node.clusterPath = Compound.path (inp.boxes.map fun b =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
            { b with role := .node } else b)
          (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box))) := by
  obtain ⟨nodes, edges, titles, hprepared, hnodesLen, hmetadata⟩ :=
    measuredGraph_prepared_source hgraph
  have hkLen : k < lines.length := by
    have hk0 : k < inp.boxes.length := (List.getElem?_eq_some_iff.mp hk).1
    omega
  have hkNodes : k < nodes.length := by
    rw [hnodesLen]
    exact hkLen
  obtain ⟨hdecl0, hb0⟩ := hmetadata k nodes[k] (List.getElem?_eq_getElem hkNodes)
  rw [hprepared]
  have heff : (inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b)[k]? = some
      (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) := by
    rw [List.getElem?_map, hk]
    rfl
  let sg := (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
    { box with role := .node } else box)
  by_cases hrole : sg.role = .group
  · have hrec := Compound.prepare_group_title_record
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)
      P.clusterPad titles { nodes := nodes, edges := edges, slot := P.slot }
      hkNodes heff hrole
    refine ⟨{ nodes[k]'hkNodes with
        clusterPath := Compound.path
          (inp.boxes.map fun b =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
              { b with role := .node } else b) sg ++ [k]
        border := -2
        w := (titles.getD k (0, 0)).1
        h := if nodes[k].loopExtent == 0 then (titles.getD k (0, 0)).2 + P.clusterPad
          else max ((titles.getD k (0, 0)).2 + P.clusterPad) nodes[k].h },
      ?_, ?_, Or.inl ⟨hrole, rfl, rfl⟩⟩
    · rw [hrec]
    · exact hdecl0
  · have hrec := Compound.prepare_plain_node_record
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)
      P.clusterPad titles { nodes := nodes, edges := edges, slot := P.slot }
      hkNodes heff hrole
    refine ⟨{ nodes[k]'hkNodes with
        clusterPath := Compound.path
          (inp.boxes.map fun b =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
              { b with role := .node } else b) sg },
      ?_, ?_, Or.inr ⟨hrole, hb0, rfl⟩⟩
    · rw [hrec]
    · exact hdecl0

local instance captionOwnerModelBoxInhabited : Inhabited ModelBox := ⟨{ id := "" }⟩

/-! ### Dump ancestors versus `Compound.ancestors`

The next two lemmas are private copies of the `ForeignFrameClearance` bridge:
a strict model ancestor index is an id of the dump ancestor walk, and a
`Compound.path` member transports to `LayoutDump.ancestors` membership. -/

/-- A strict model ancestor index is an id of the dump ancestor walk. -/
private theorem ownerScope_compound_mem_dump_go {boxes : List ModelBox} {d : LayoutDump}
    (himg : ∀ (i : Nat) (b : ModelBox), boxes[i]? = some b →
      ∃ (rect : Rect) (role : String),
        d.box? b.id = some (Box.mk b.id role rect b.parent b.exclusive))
    (_hpre : ∀ bx : Box, bx ∈ d.boxes →
      ∃ b : ModelBox, b ∈ boxes ∧ b.id = bx.id ∧ b.parent = bx.parent)
    (_hid : ∀ (a b : ModelBox), a ∈ boxes → b ∈ boxes → a.id = b.id → a = b) :
    ∀ (fuel : Nat) (s : String) (i : Nat),
      i ∈ Compound.ancestors boxes (fuel + 1) s →
      i < boxes.length →
      (boxes[i]?.getD default).id ≠ s →
      (boxes[i]?.getD default).id ∈ LayoutDump.ancestors.go d fuel s := by
  intro fuel
  induction fuel with
  | zero =>
    intro s i hmem hi hne
    by_cases hs : s = ""
    · subst s
      simp only [Compound.ancestors] at hmem
      exact absurd hmem (by simp)
    · have h3 : Compound.ancestors boxes (0 + 1) s =
          match boxes.findIdx? (fun box => box.id == s) with
        | none => []
        | some index =>
          match boxes[index]? with
          | none => []
          | some box => Compound.ancestors boxes 0 box.parent ++ [index] :=
        Compound.ancestors.eq_3 boxes s 0 hs
      rw [h3] at hmem
      cases hf : boxes.findIdx? (fun box => box.id == s) with
      | none => simp only [hf] at hmem; exact absurd hmem (by simp)
      | some j =>
        obtain ⟨hjb, hjid, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        simp only [hf] at hmem
        cases hb : boxes[j]? with
        | none => simp only [hb] at hmem; exact absurd hmem (by simp)
        | some bj =>
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          simp only [hb] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · simp only [Compound.ancestors] at hmem
            exact absurd hmem (by simp)
          · rw [hmem] at hne
            have hgd : boxes[j]?.getD default = bj := by rw [hb]; rfl
            have hjid2 : bj.id = s := by
              rw [← hbjEq]
              exact beq_iff_eq.mp hjid
            exact absurd ((congrArg (·.id) hgd).trans hjid2) hne
  | succ fuel ih =>
    intro s i hmem hi hne
    by_cases hs : s = ""
    · subst s
      simp only [Compound.ancestors] at hmem
      exact absurd hmem (by simp)
    · have h3 : Compound.ancestors boxes (fuel + 1 + 1) s =
          match boxes.findIdx? (fun box => box.id == s) with
        | none => []
        | some index =>
          match boxes[index]? with
          | none => []
          | some box => Compound.ancestors boxes (fuel + 1) box.parent ++ [index] :=
        Compound.ancestors.eq_3 boxes s (fuel + 1) hs
      rw [h3] at hmem
      cases hf : boxes.findIdx? (fun box => box.id == s) with
      | none => simp only [hf] at hmem; exact absurd hmem (by simp)
      | some j =>
        obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        simp only [hf] at hmem
        cases hb : boxes[j]? with
        | none => simp only [hb] at hmem; exact absurd hmem (by simp)
        | some bj =>
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          simp only [hb] at hmem
          have hjids : bj.id = s := by
            rw [← hbjEq]
            exact beq_iff_eq.mp hjid
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · -- i sits in the parent chain: strip one dump-walk step
            obtain ⟨rect, role, excl, hbx⟩ : ∃ (rect : Rect) (role : String)
                (excl : Bool), d.box? s = some (Box.mk s role rect bj.parent excl) := by
              obtain ⟨rect, role, hx⟩ := himg j bj hb
              rw [hjids] at hx
              exact ⟨rect, role, bj.exclusive, hx⟩
            have hparNe : bj.parent ≠ "" := by
              intro hempty
              simp only [hempty, Compound.ancestors] at hmem
              exact absurd hmem (by simp)
            cases hd : d.box? s with
            | none => rw [hd] at hbx; exact absurd hbx (by simp)
            | some bx =>
              have hbxa : bx = Box.mk s role rect bj.parent excl :=
                Option.some.inj (hd.symm.trans hbx)
              have hbpar : bx.parent = bj.parent := by rw [hbxa]
              have hgo : LayoutDump.ancestors.go d (fuel + 1) s =
                  match d.box? s with
                  | none => []
                  | some bx' =>
                    if bx'.parent = "" then []
                    else bx'.parent :: LayoutDump.ancestors.go d fuel bx'.parent := rfl
              rw [hgo]
              simp only [hd, hbpar]
              split
              · rename_i hcond
                exact absurd hcond hparNe
              · by_cases hself : (boxes[i]?.getD default).id = bj.parent
                · rw [hself]
                  exact List.mem_cons_self
                · exact List.mem_cons.mpr (Or.inr (ih bj.parent i hmem hi hself))
          · rw [hmem] at hne
            have hgd : boxes[j]?.getD default = bj := by rw [hb]; rfl
            exact absurd ((congrArg (·.id) hgd).trans hjids) hne

private theorem ownerScope_anc_of_path_mem {boxes : List ModelBox} {d : LayoutDump}
    (himg : ∀ (i : Nat) (b : ModelBox), boxes[i]? = some b →
      ∃ (rect : Rect) (role : String),
        d.box? b.id = some (Box.mk b.id role rect b.parent b.exclusive))
    (hpre : ∀ bx : Box, bx ∈ d.boxes →
      ∃ b : ModelBox, b ∈ boxes ∧ b.id = bx.id ∧ b.parent = bx.parent)
    (hid : ∀ (a b : ModelBox), a ∈ boxes → b ∈ boxes → a.id = b.id → a = b)
    (hlen : d.boxes.length = boxes.length)
    {t p : String} {idx : Nat} {s : String}
    (hroot : ∃ (role : String) (rect : Rect) (excl : Bool),
      d.box? t = some (Box.mk t role rect p excl))
    (hidx : idx < boxes.length)
    (hs : (boxes[idx]?.getD default).id = s)
    (hmem : idx ∈ Compound.ancestors boxes boxes.length p) :
    s ∈ d.ancestors t := by
  cases hlen' : boxes.length with
  | zero => rw [hlen'] at hidx; exact absurd hidx (by omega)
  | succ fuel =>
    obtain ⟨role, rect, excl, hroot⟩ := hroot
    rw [hlen'] at hmem
    have hlenSucc : d.boxes.length = fuel + 1 := by rw [hlen, hlen']
    have hgo : LayoutDump.ancestors.go d (fuel + 1) t =
        match d.box? t with
        | none => []
        | some bx =>
          if bx.parent = "" then [] else bx.parent :: LayoutDump.ancestors.go d fuel bx.parent :=
      rfl
    rw [LayoutDump.ancestors, hlenSucc, hgo]
    cases hd : d.box? t with
    | none => rw [hd] at hroot; exact absurd hroot (by simp)
    | some bx =>
      have hbxa : bx = Box.mk t role rect p excl :=
        Option.some.inj (hd.symm.trans hroot)
      have hbpar : bx.parent = p := by rw [hbxa]
      simp only [hbpar]
      split
      · rename_i hcond
        rw [hcond] at hmem
        simp only [Compound.ancestors] at hmem
        exact absurd hmem (by simp)
      · by_cases hself : (boxes[idx]?.getD default).id = p
        · rw [← hs, hself]
          exact List.mem_cons_self
        · have hgo2 := ownerScope_compound_mem_dump_go himg hpre hid fuel p idx hmem hidx hself
          rw [hs] at hgo2
          exact List.mem_cons.mpr (Or.inr hgo2)

/-- Injectivity of the id map on a nodup list (local copy of the private
`ForeignFrameClearance` helper). -/
private theorem ownerScope_getElem_unique {α : Type} {f : α → String} {l : List α}
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

/-- A component position key is the measured-graph node at that key (local copy
of the private `CaptionResidualsProof` helper). -/
private theorem ownerScope_component_node_lookup {graph : Graph} {comp : List Nat}
    {cand : Nat} {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

/-- Every member of a `Compound.ancestors` walk started at a box's parent is a
group in the demoted box list: each member is the parent of the previous chain
box, `framedParents` supplies a non-demoted group parent of that id, and id
uniqueness identifies the member with it. -/
private theorem ownerScope_path_group_role {inp : Input}
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
    have : Compound.ancestors eff 0 c.parent = [] := rfl
    rw [this] at hi
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
        simp only [hf, List.not_mem_nil] at hi
      | some j =>
        simp only [hf] at hi
        cases hb : eff[j]? with
        | none =>
          simp only [hb, List.not_mem_nil] at hi
        | some e =>
          simp only [hb] at hi
          obtain ⟨_, hej⟩ := List.getElem?_eq_some_iff.mp hb
          obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have heid : e.id = c.parent := by
            rw [← hej]
            exact beq_iff_eq.mp hjid
          -- the preimage of e in inp.boxes
          have heffj : eff[j]? = (inp.boxes[j]?).map fun b =>
              if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
                { b with role := .node } else b := by
            rw [heff, List.getElem?_map]
          have hbo := heffj.symm.trans hb
          cases hjo : inp.boxes[j]? with
          | none => simp [hjo] at hbo
          | some orig =>
            rw [hjo] at hbo
            have heq : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                { orig with role := .node } else orig) = e := Option.some.inj hbo
            have horig : orig ∈ inp.boxes := List.mem_of_getElem? hjo
            obtain ⟨hdemId, hdemParent, _⟩ := ownerScope_demote_facts (inp := inp) orig
            have heid' : orig.id = c.parent :=
              hdemId.symm.trans ((congrArg ModelBox.id heq).trans heid)
            simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with hi | rfl
            · rw [← heq, hdemParent] at hi
              exact ih orig horig i hi
            · refine ⟨e, hb, ?_⟩
              obtain ⟨pb, hpbmem, hpbId, hpbRole, hnotfix⟩ :=
                framedParents_parent hfp hc hcp
              have horigEq : orig = pb :=
                ownerScope_getElem_unique hids horig hpbmem (heid'.trans hpbId.symm)
              rw [← heq, horigEq]
              simpa [hnotfix] using hpbRole

/-- A `List.contains` miss on indices is `false`. -/
private theorem ownerScope_contains_eq_false {l : List Nat} {a : Nat}
    (h : a ∉ l) : l.contains a = false := by
  rw [List.contains_eq_mem]
  simp only [h, decide_false]

theorem ownerScopeGroupOwnerDisjoint
    (hbracket : BracketMarkersAtRank) (horder : PlainClearOfSideMarker)
    (halign : SideMarkerSpanAligned)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
  ∀ (execution : SceneExecution inp o res) (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (Elegant.Layered.captionLabel inp o res execution ownerIndex source lines) →
    source.owner ∉ res.scene.layoutDump.ancestors b.id →
    ∀ (ownerBox : ModelBox), inp.boxes[ownerIndex]? = some ownerBox →
      ownerBox.role = .group →
      ∀ (bi k posOwner posB : Nat) (part : List Nat × Part),
        res.scene.boxes[bi]? = some b →
        execution.componentsAcc.parts[k]? = some part →
        part.1[posOwner]? = some ownerIndex →
        part.1[posB]? = some bi →
        posOwner ≠ posB →
        ∀ (candidate : Nat) (run : Run),
          componentRun execution.params
            (componentCandidate execution.graph part.1 candidate)
            execution.measured (candidateOrder candidate) = .ok run →
          Disjoint
            (frameRect execution.params
              (componentCandidate execution.graph part.1 candidate) run
              posOwner)
            (frameRect execution.params
              (componentCandidate execution.graph part.1 candidate) run
              posB) := by
  intro execution index ownerIndex source lines b hsrc hmeas hfindIdx hmem hex
    hscope hd ownerBox hobox hrole bi k posOwner posB part hbi hk hposO hposB hne
    candidate run hrun
  have hlinesLen : execution.lines.length = inp.boxes.length :=
    boxLines_length execution.lines_eq
  have hpartsMap : execution.componentsAcc.parts.map (·.1) =
      components execution.graph := by
    have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ : Acc).parts = [] := rfl
    exact (actual_components_parts_geometry (P := execution.params) (inp := inp)
      (o := o) (g := execution.graph) (labels := execution.measured) hempty
      execution.components_eq).1
  have hpartMem : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hk
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hpartsMap]
    exact List.mem_map_of_mem hpartMem
  obtain ⟨sb, hsb, hbid, hsbpar, hsbex, hbrect⟩ :=
    sceneBox_source_rect execution hbi
  have hsbexTrue : sb.exclusive = true := by rw [← hsbex]; exact hex
  have hngB : sb.role ≠ .group :=
    wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsb) hsbexTrue
  have hroleB : sb.role = .node := by
    cases h : sb.role with
    | node => rfl
    | group => exact absurd h hngB
  obtain ⟨_, hpO, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfindIdx
  have hoboxGet : inp.boxes[ownerIndex] = ownerBox :=
    (List.getElem?_eq_some_iff.mp hobox).2
  rw [hoboxGet] at hpO
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpO
  obtain ⟨hownerId, hownerEx⟩ := hpO
  have hboxesEq : res.scene.layoutDump.boxes = (inp.boxes.zipIdx.map fun q =>
      Box.mk q.1.id q.1.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD q.2 default)))
        q.1.parent q.1.exclusive) := by
    simp [Scene.layoutDump, execution.boxes_eq_map]
  have hdlen : res.scene.layoutDump.boxes.length = inp.boxes.length := by
    rw [hboxesEq, List.length_map, List.length_zipIdx]
  have hidsNodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  let eff : List ModelBox := inp.boxes.map fun b =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
      { b with role := .node } else b
  have heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b := rfl
  have heffLen : eff.length = inp.boxes.length := by
    rw [heff, List.length_map]
  have heffGet : ∀ (k : Nat), eff[k]? =
      (inp.boxes[k]?).map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b := by
    intro k; rw [heff, List.getElem?_map]
  have heffNodup : (eff.map (·.id)).Nodup := by
    have hcongr : eff.map (·.id) = inp.boxes.map (·.id) := by
      rw [heff, List.map_map]
      congr 1
      funext b
      exact (ownerScope_demote_facts (inp := inp) b).1
    rw [hcongr]
    exact hidsNodup
  have heffUnique : ∀ (a b : ModelBox), a ∈ eff → b ∈ eff → a.id = b.id → a = b :=
    fun a b ha hb hid => ownerScope_getElem_unique heffNodup ha hb hid
  have himg : ∀ (k : Nat) (b : ModelBox), eff[k]? = some b →
      ∃ (rect : Rect) (role : String),
        res.scene.layoutDump.box? b.id =
          some (Box.mk b.id role rect b.parent b.exclusive) := by
    intro k b hib
    cases hin : inp.boxes[k]? with
    | none => rw [heffGet, hin] at hib; exact absurd hib (by simp)
    | some orig =>
      rw [heffGet, hin] at hib
      have hbEq : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
          { orig with role := .node } else orig) = b := Option.some.inj hib
      subst hbEq
      obtain ⟨h1, h2, h3⟩ := ownerScope_demote_facts (inp := inp) orig
      rw [h1, h2, h3]
      exact ⟨_, _, execution.source_box_lookup hwf hin⟩
  have hpre : ∀ bx : Box, bx ∈ res.scene.layoutDump.boxes →
      ∃ b : ModelBox, b ∈ eff ∧ b.id = bx.id ∧ b.parent = bx.parent := by
    intro bx hbx
    rw [hboxesEq] at hbx
    obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hbx
    have hk : inp.boxes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
    cases hin : inp.boxes[q.2]? with
    | none => rw [hin] at hk; exact absurd hk (by simp)
    | some s =>
      rw [hin] at hk
      have hsq : s = q.1 := Option.some.inj hk
      subst hsq
      have hkIn : eff[q.2]? = some
          (if inp.fixedSizes.any (fun fixed => fixed.1 == q.1.id) then
            { q.1 with role := .node } else q.1) := by
        rw [heffGet, hin, Option.map_some]
      refine ⟨_, List.mem_of_getElem? hkIn, ?_, ?_⟩
      · rw [(ownerScope_demote_facts (inp := inp) q.1).1, ← hqeq]
      · rw [(ownerScope_demote_facts (inp := inp) q.1).2.1, ← hqeq]
  have hdlen' : res.scene.layoutDump.boxes.length = eff.length := by
    rw [heffLen]; exact hdlen
  obtain ⟨uNode, huNode, huDecl, huCase⟩ :=
    ownerScope_graph_node execution.graph_eq hlinesLen hobox
  obtain ⟨wNode, hwNode, hwDecl, hwCase⟩ :=
    ownerScope_graph_node execution.graph_eq hlinesLen hsb
  have huLookup : (componentCandidate execution.graph part.1 candidate).nodes[posOwner]? =
      some uNode := ownerScope_component_node_lookup hposO huNode
  have hwLookup : (componentCandidate execution.graph part.1 candidate).nodes[posB]? =
      some wNode := ownerScope_component_node_lookup hposB hwNode
  have hbiNe : bi ≠ ownerIndex := by
    intro heq
    rw [heq] at hsb
    have hseq : sb = ownerBox := Option.some.inj (hsb.symm.trans hobox)
    have hsbFalse : b.exclusive = false := by rw [hsbex, hseq, hownerEx]
    rw [hsbFalse] at hex
    exact absurd hex (by decide)
  have hsgBrole : (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
      { sb with role := .node } else sb).role = .node := by
    split
    · rfl
    · exact hroleB
  rcases hwCase with ⟨hroleBw, hbWm2, hpathWm2⟩ | ⟨hroleB', hbW0, hpathW0⟩
  · exact absurd hroleBw (by rw [hsgBrole]; decide)
  · rcases huCase with ⟨hroleO, hbO, hpathO⟩ | ⟨hroleO', hbO0, hpathO0⟩
    · refine foreignNonGroupSpansClear hbracket horder halign
        execution.graph_eq hlinesLen hwf hfp hcomp hrun huLookup hwLookup hbO ?_ ?_ ?_ ?_
      · rw [hbW0]; decide
      · rw [huDecl, hwDecl]; exact Ne.symm hbiNe
      · rw [← heff] at hpathW0
        rw [hpathW0, huDecl]
        apply ownerScope_contains_eq_false
        intro hpmem
        unfold Compound.path at hpmem
        have hsgBpar : (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
            { sb with role := .node } else sb).parent = sb.parent :=
          (ownerScope_demote_facts (inp := inp) sb).2.1
        rw [hsgBpar, ← hsbpar] at hpmem
        have hroot : ∃ (role : String) (rect : Rect) (excl : Bool),
            res.scene.layoutDump.box? b.id =
              some (Box.mk b.id role rect b.parent excl) := by
          obtain ⟨rect, role, hx⟩ := himg bi
            (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
              { sb with role := .node } else sb)
            (by rw [heffGet, hsb, Option.map_some])
          obtain ⟨hd1, hd2, hd3⟩ := ownerScope_demote_facts (inp := inp) sb
          rw [hd1, hd2, hd3] at hx
          refine ⟨role, rect, b.exclusive, ?_⟩
          rw [hbid, hsbpar, hsbex]
          exact hx
        have hidx : ownerIndex < eff.length := by
          rw [heffLen]
          exact (List.getElem?_eq_some_iff.mp hobox).1
        have hs : (eff[ownerIndex]?.getD default).id = source.owner := by
          rw [heffGet, hobox, Option.map_some]
          show (if inp.fixedSizes.any (fun fixed => fixed.1 == ownerBox.id) then
              { ownerBox with role := .node } else ownerBox).id = source.owner
          rw [(ownerScope_demote_facts (inp := inp) ownerBox).1]
          exact hownerId
        have hIn : source.owner ∈ res.scene.layoutDump.ancestors b.id :=
          ownerScope_anc_of_path_mem himg hpre heffUnique hdlen' hroot hidx hs hpmem
        exact absurd hIn hd
      · rw [← heff] at hpathO
        rw [hpathO, hwDecl]
        apply ownerScope_contains_eq_false
        intro hpmem
        rcases List.mem_append.mp hpmem with hpmem | hpmem
        · unfold Compound.path at hpmem
          have hsgOpar : (if inp.fixedSizes.any (fun fixed => fixed.1 == ownerBox.id) then
              { ownerBox with role := .node } else ownerBox).parent = ownerBox.parent :=
            (ownerScope_demote_facts (inp := inp) ownerBox).2.1
          rw [hsgOpar] at hpmem
          obtain ⟨pb2, hpb2, hroleG⟩ := ownerScope_path_group_role hfp hidsNodup eff heff
            eff.length ownerBox (List.mem_of_getElem? hobox) bi hpmem
          have hsbEff : eff[bi]? = some
              (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
                { sb with role := .node } else sb) := by
            rw [heffGet, hsb, Option.map_some]
          have hEq : pb2 = (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
              { sb with role := .node } else sb) :=
            Option.some.inj (hpb2.symm.trans hsbEff)
          rw [hEq] at hroleG
          exact absurd hroleG (by rw [hsgBrole]; decide)
        · rw [List.mem_singleton] at hpmem
          exact absurd hpmem hbiNe
    · exact componentRun_positions_disjoint execution.graph_eq hcomp hrun
        huLookup hwLookup hbO0 hbW0 hne


end PipelineImpl

end Elegant.Layered
